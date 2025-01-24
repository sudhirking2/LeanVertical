import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

variable (a b c d e : ℝ)
open Real

theorem fact1 : a*b*2 ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

theorem fact2 : -(a*b)*2 ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 + 2*a*b + b^2
  calc
    a^2 + 2*a*b + b^2 = (a + b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

example : |a*b| ≤ (a^2 + b^2)/2 := by
  have h : (0 : ℝ) < 2 := by norm_num
  apply abs_le'.mpr
  constructor
  · rw [le_div_iff₀ h]
    apply fact1
  rw [le_div_iff₀ h]
  apply fact2
