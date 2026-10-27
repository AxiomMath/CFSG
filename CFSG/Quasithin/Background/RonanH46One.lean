module

public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.HFL3Alpha
public import CFSG.Quasithin.Background.HFL3Six
public import CFSG.Quasithin.Background.RonanH44Defs

public section

namespace CFSG.Quasithin.RonanH46

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
  CFSG.Quasithin.RonanH44
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem part1 (hK : Nat.card K = (2 ^ 1) ^ 2) {M : Subgroup (MulAut (HMod 1 K))}
    (hMN : M ≤ norm hK) :
    ∀ y ∈ M, Odd (orderOf y) → rk ↥(fixV (Subgroup.zpowers y)) = 5 →
      Subgroup.zpowers y = M ⊓ centSub (fixV (Subgroup.zpowers y)) ∧ orderOf y = 3 := by
  intro y hyM hodd hrk
  have hV := CFSG.Quasithin.H.L3Nine.card_HMod (le_refl 1) hK
  have hfix : Nat.card ↥(fixV (Subgroup.zpowers y)) = 2 ^ 5 := by
    rw [CFSG.Quasithin.card_eq_two_pow (V := HMod 1 K)
      CFSG.Quasithin.H.L3Nine.sq_eq_one_HMod (fixV (Subgroup.zpowers y)), hrk]
  have hy1 : y ≠ 1 := by
    intro h
    rw [h] at hfix
    have htop : fixV (Subgroup.zpowers (1 : MulAut (HMod 1 K))) = ⊤ :=
      eq_top_iff.2 fun v _ => CFSG.Quasithin.mem_fixV_zpowers_iff.mpr rfl
    rw [htop, Subgroup.card_top, hV] at hfix
    norm_num at hfix
  have hbound := CFSG.Quasithin.H.L3Nine.card_centSub_fixV_le hK (hMN hyM) hodd hfix
  have hzC : Subgroup.zpowers y ≤ M ⊓ centSub (fixV (Subgroup.zpowers y)) := by
    refine le_inf (Subgroup.zpowers_le.mpr hyM) (Subgroup.zpowers_le.mpr ?_)
    exact CFSG.Quasithin.mem_centSub.mpr fun u hu =>
      CFSG.Quasithin.mem_fixV.mp hu y (Subgroup.mem_zpowers y)
  have hCle : Nat.card ↥(M ⊓ centSub (fixV (Subgroup.zpowers y))) ≤ 3 :=
    le_trans (Subgroup.card_le_of_le (inf_le_inf_right _ hMN)) hbound
  have hord : orderOf y = Nat.card ↥(Subgroup.zpowers y) := (Nat.card_zpowers y).symm
  have hle3 : orderOf y ≤ 3 := by
    rw [hord]
    exact le_trans (Subgroup.card_le_of_le hzC) hCle
  have hne1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
  have h3 : orderOf y = 3 := by
    have := Nat.odd_iff.mp hodd
    omega
  refine ⟨Subgroup.eq_of_le_of_card_ge hzC ?_, h3⟩
  rw [Nat.card_zpowers, h3]
  exact hCle

end CFSG.Quasithin.RonanH46
