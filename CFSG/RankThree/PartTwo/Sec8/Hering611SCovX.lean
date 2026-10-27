module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

structure CoverX (X : Type*) [Group X] (Z R T : Subgroup X) (s : X) : Prop where
  Z_central : Z ≤ Subgroup.center X
  card_Z : Nat.card Z = 3
  Z_le_R : Z ≤ R
  R_le_T : R ≤ T
  T_pgroup : IsPGroup 3 T
  card_T : Nat.card T = 729
  R_central : ∀ x ∈ R, ∀ t ∈ T, x * t = t * x
  card_R : Nat.card R = 27
  R_cube : ∀ x ∈ R, x ^ 3 ∈ Z
  s_normT : s ∈ Subgroup.normalizer (T : Set X)
  s_normR : s ∈ Subgroup.normalizer (R : Set X)
  s_pow : s ^ 8 = 1
  R_fix : ∀ x ∈ R, s * x * s⁻¹ * x⁻¹ ∈ Z → x ∈ Z
  R_inv : ∀ x ∈ R, s ^ 4 * x * (s ^ 4)⁻¹ * x ∈ Z
  nonab : ∃ x ∈ T, ∃ y ∈ T, x * y * x⁻¹ * y⁻¹ ∉ R
  singer : ∀ W : Subgroup X, W ≤ T → Z ≤ W → W.relIndex T = 3 →
    s ^ 2 ∉ Subgroup.normalizer (W : Set X)

end CFSG.RankThree.PartTwo.Sec8.Hering611
