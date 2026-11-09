
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import Certificates.Data.Kernel.Census.CatFacts.C2015Scan
import CFSG.Certificates.Kernel.Census.CatFacts.PkWordSound

public section

namespace CFSG.Certificates.Kernel.CatFacts

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Certificates Subgroup
open CFSG.Certificates.Kernel.PkEnum

theorem y45_ok : (List.range 45).all (fun j =>
    imgW [codeV y45] j != j && imgW (powW [codeV y45] 5) j == j) = true := by
  decide +kernel

theorem pkpW_powW5 (u : List (VP 45)) (k : Nat) : pkpW (powW u k) = pkpW u ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [powW, pkpW_append, ih, pow_succ']

theorem y45_fpf (j : Fin 45) : y45 j ≠ j := by
  have h := (range_all_iff _).1 y45_ok j
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  intro hj
  apply h.1
  rw [imgW_eq, pkpW_single, pkp_codeV, hj]

theorem y45_pow_five : y45 ^ 5 = 1 := by
  ext j
  have h := (range_all_iff _).1 y45_ok j
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [imgW_eq (powW _ 5), pkpW_powW5, pkpW_single, pkp_codeV] at h
  exact h.2

theorem fpf_of_sylow {G : Subgroup (Equiv.Perm (Fin 45))} (hG : Nat.card G = 25920)
    {y : Equiv.Perm (Fin 45)} (hy : y ∈ G) (hy5 : y ^ 5 = 1) (hyf : ∀ j, y j ≠ j)
    {x : Equiv.Perm (Fin 45)} (hx : x ∈ G) (h5 : x ^ 5 = 1) (h1 : x ≠ 1) (j : Fin 45) :
    x j ≠ j := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let xG : G := ⟨x, hx⟩
  let yG : G := ⟨y, hy⟩
  have hxo : orderOf xG = 5 :=
    orderOf_eq_prime (Subtype.ext h5) fun h => h1 (congrArg Subtype.val h)
  have hyo : orderOf yG = 5 :=
    orderOf_eq_prime (Subtype.ext hy5) fun h => by
      have h' : y = 1 := congrArg Subtype.val h
      exact hyf 0 (by rw [h']; rfl)
  have hpx : IsPGroup 5 (zpowers xG) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  have hpy : IsPGroup 5 (zpowers yG) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  obtain ⟨P1, hP1⟩ := hpx.exists_le_sylow
  obtain ⟨P2, hP2⟩ := hpy.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P2 P1
  have hmem : g * yG * g⁻¹ ∈ (P1 : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hP2 (mem_zpowers yG))
  have hcard : Nat.card P1 ≤ Nat.card (zpowers xG) := by
    obtain ⟨n, hn⟩ := P1.isPGroup'.exists_card_eq
    have hd := Subgroup.card_subgroup_dvd_card (P1 : Subgroup G)
    rw [hG, hn] at hd
    rw [hn, Nat.card_zpowers, hxo]
    have hn1 : n ≤ 1 := by
      by_contra h
      exact absurd (dvd_trans (pow_dvd_pow 5 (Nat.lt_of_not_le h)) hd) (by norm_num)
    calc 5 ^ n ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
      _ = 5 := rfl
  have heq := Subgroup.eq_of_le_of_card_ge hP1 hcard
  rw [← heq] at hmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
  intro hj
  have hxm : (x ^ m) j = j := Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hj m
  have hc : x ^ m = (g : Equiv.Perm (Fin 45)) * y * (g : Equiv.Perm (Fin 45))⁻¹ :=
    congrArg Subtype.val hm
  have hy' : y = (g : Equiv.Perm (Fin 45))⁻¹ * x ^ m * (g : Equiv.Perm (Fin 45)) := by
    rw [hc]
    group
  apply hyf ((g : Equiv.Perm (Fin 45))⁻¹ j)
  rw [hy']
  simp [Equiv.Perm.mul_apply, hxm]

theorem fpf_five {x : Equiv.Perm (Fin 45)} (hx : x ∈ QP45.originalSubgroup) (h5 : x ^ 5 = 1)
    (h1 : x ≠ 1) (j : Fin 45) : x j ≠ j :=
  fpf_of_sylow (by rw [card_group QP45 QP45_ok, QP45_valid.2])
    (by rw [QP45_closure]; exact subset_closure (by simp)) y45_pow_five y45_fpf hx h5 h1 j

end CFSG.Certificates.Kernel.CatFacts
