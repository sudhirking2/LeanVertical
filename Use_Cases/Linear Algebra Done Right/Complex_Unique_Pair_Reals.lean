import Mathlib
open Complex

--Formalizes 1.1 in LADR4
namespace LADR4
def one.one : (∀z:ℂ,∃ a b :ℝ, z=a+b*I) ∧
  (∀ a a' b b':ℝ, a+b*I=a'+b'*I→a=a'∧b=b') ∧
  (∀a a' b b':ℝ, (a+b*I)+(a'+b'*I) = (a+a')+(b+b')*I) ∧
  (∀a a' b b':ℝ, (a+b*I)*(a'+b'*I) = (a*a'-b*b') + (a*b'+b*a')*I) := by
  constructor
  · intro z
    use z.re , z.im
    exact Eq.symm (re_add_im z)
  constructor
  · intro a a' b b' h
    let z := a + b*I
    let z' := a' + b'*I
    have h1 : z.re = z'.re := congrArg re h
    have h2 : z.im = z'.im := congrArg im h
    constructor
    · have hre : z.re = a := by unfold z; simp
      have hre' : z'.re = a' := by unfold z'; simp
      rw[← hre, ← hre']
      exact h1
    · have him : z.im = b := by unfold z; simp
      have him' : z'.im = b' := by unfold z'; simp
      rw[← him, ← him']
      exact h2
  constructor
  · intros a a' b b'
    ring
  · intros a a' b b'
    ring
    have : I^2=-1 := by simp
    rw[this]
    ring
