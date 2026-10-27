module

import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43Gen
import CFSG.Adapters.LinearSmallCatalog
import CFSG.Adapters.Certificate43Check
import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionAlternatingFive
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

theorem nonempty_equiv_alt5_of_isLnq {K : Subgroup G} (hK : IsLnq 2 2 2 K) :
    Nonempty (K ≃* alternatingGroup (Fin 5)) := by
  haveI := CFSG.Adapters.certificate43_holds
  obtain ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ := hK
  let _ := hF
  let _ := hFin
  have hcard' : Nat.card F = 4 := by simpa using hcard
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
    (Or.inl hcard')
  exact ⟨e.trans e5⟩

theorem sec34_a5_elem3 {K : Subgroup G} (hK : IsLnq 2 2 2 K) (V : Subgroup G) (hV : V ≤ Nor K)
    (hV3 : IsElementaryAbelian 3 ↥V) : Nat.card V ≤ 3 * Nat.card (V ⊓ CenS K : Subgroup G) := by
  obtain ⟨e⟩ := nonempty_equiv_alt5_of_isLnq hK
  let ρ : ↥V →* MulAut (alternatingGroup (Fin 5)) :=
    (normAut K e).comp (Subgroup.inclusion hV)
  have hker : ρ.ker = (V ⊓ CenS K).subgroupOf V := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : ρ x = 1 ↔ ∀ k ∈ K, (x : G) * k * (x : G)⁻¹ = k :=
      normAut_eq_one_iff K e ⟨x, hV x.2⟩
    rw [h1]
    constructor
    · intro h
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      exact ((mul_inv_eq_iff_eq_mul.mp (h k hk))).symm
    · rintro ⟨-, h⟩ k hk
      exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp h k hk).symm
  have hcard := Subgroup.card_ker_mul_card_range ρ
  rw [hker] at hcard
  have hkerc : Nat.card ↥((V ⊓ CenS K).subgroupOf V) = Nat.card ↥(V ⊓ CenS K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hkerc] at hcard
  rw [← hcard, mul_comm]
  refine Nat.mul_le_mul_right _ ?_
  have hp : IsPGroup 3 ↥V := IsElementaryAbelian.isPGroup 3 ↥V
  have hp' : IsPGroup 3 ↥ρ.range := hp.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  obtain ⟨j, hj⟩ := hp'.exists_card_eq
  have h120 : Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
    rw [← Nat.card_congr (CFSG.Semidihedral.Principal.CyclicAlternatingFive.autEquiv).toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hdvd : Nat.card ↥ρ.range ∣ 120 := h120 ▸ Subgroup.card_subgroup_dvd_card ρ.range
  rw [hj] at hdvd ⊢
  have hj1 : j ≤ 1 := by
    by_contra hj2
    have h9 : 3 ^ 2 ∣ 3 ^ j := pow_dvd_pow 3 (by omega)
    have := dvd_trans h9 hdvd
    norm_num at this
  calc 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
    _ = 3 := by norm_num

end CFSG.RankThree.PartTwo.Sec21.FF79
