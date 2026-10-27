module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTorusAbelianFamilies
public import CFSG.GroupTheory.QuasisimpleOddCenterQuotient
public import CFSG.LieType.SeitzGeneration.HyperCoverUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Blueprint (LieModel)

theorem k_SU2OddCover_holds :
    K_SU2OddCover := by
  intro K _ _ m _ _ _ hL hq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O := CFSG.Open.pCoreOf 2 (Subgroup.center K)
  have hq' : CFSG.Open.IsQuasisimple (K ⧸ O) :=
    CFSG.GroupTheory.isQuasisimple_quotient_pCoreOf_center hq
  have hodd : Odd (Nat.card (Subgroup.center (K ⧸ O))) :=
    CFSG.GroupTheory.odd_card_center_quotient_pCoreOf_center hq
  have eZ : (K ⧸ O) ⧸ Subgroup.center (K ⧸ O) ≃* K ⧸ Subgroup.center K :=
    CFSG.GroupTheory.quotientPCoreOfCenterEquiv hq
  let r := m / 2
  let ε := m % 2
  have hε : ε ≤ 1 := by
    have := Nat.mod_lt m (by norm_num : 0 < 2)
    omega
  have hm_eq : 2 * r + ε = m := by
    have := Nat.div_add_mod m 2
    simp only [r, ε]
    omega
  have hm4 : 4 ≤ m := by
    have h := CFSG.Blueprint.LieModel.admissible hL
    simp [CFSG.Open.StatedLieAdmissible] at h
    omega
  have hn4 : 4 ≤ 2 * r + ε := by omega
  have hn0 : 2 * r + ε ≠ 0 := by omega
  have : Group.IsPerfect (K ⧸ O) := ⟨hq'.1⟩
  have hL' : LieModel ((K ⧸ O) ⧸ Subgroup.center (K ⧸ O)) .PSU (2 * r + ε) 2 1 := by
    rw [hm_eq]
    exact CFSG.Blueprint.LieModel.of_mulEquiv eZ.symm hL
  obtain ⟨F, hFld, hFin, hFcard, ⟨e₀⟩⟩ :=
    (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn0 hL').2
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F :=
    ⟨Nat.prime_two, le_rfl, by rw [hFcard]; norm_num⟩
  have : CharP F 2 := hUF.charP
  let ρ : (K ⧸ O) →* StatedProj (StatedSU (2 * r + ε) (2 ^ 1) F) :=
    e₀.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (K ⧸ O)))
  have hρ : Function.Surjective ρ := e₀.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρker : ρ.ker = Subgroup.center (K ⧸ O) := by
    dsimp only [ρ]
    rw [MonoidHom.ker_comp_of_injective _ _ e₀.injective, QuotientGroup.ker_mk']
  have hcop : Even (2 * r + ε) → Nat.Coprime 2 (Nat.card ρ.ker) := by
    intro _
    rw [hρker]
    exact Nat.coprime_two_left.2 hodd
  obtain ⟨φ, hφ, hφρ⟩ :=
    CFSG.LieType.SeitzGeneration.exists_su_cover_hom (ℓ := 2) (f := 1) (n := 2 * r + ε)
      hFcard le_rfl hn4 ρ hρ (le_of_eq hρker) hcop
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) hUF
  let α : hypSU hUF r ε →* (K ⧸ O) :=
    φ.comp (hypTransport hUF hR).toMonoidHom
  have hα : Function.Surjective α := hφ.comp (hypTransport hUF hR).surjective
  have hαker : α.ker ≤ hypScalars hUF r ε := by
    intro x hx
    change φ ((hypTransport hUF hR) x) = 1 at hx
    have hx2 : (QuotientGroup.mk' ((StatedScalars (Fin (2 * r + ε)) F).subgroupOf
        (StatedSU (2 * r + ε) (2 ^ 1) F))) ((hypTransport hUF hR) x) = 1 := by
      rw [← hφρ ((hypTransport hUF hR) x), hx, map_one]
    have hmem : ((hypTransport hUF hR) x : unitarySU 2 1 F (2 * r + ε)) ∈
        (StatedScalars (Fin (2 * r + ε)) F).subgroupOf (StatedSU (2 * r + ε) (2 ^ 1) F) :=
      (QuotientGroup.eq_one_iff _).1 (by simpa [QuotientGroup.mk'_apply] using hx2)
    refine (mem_hypScalars_iff_transport hR x).2 ?_
    rw [unitaryScalars_eq (n := 2 * r + ε) hUF (by omega)]
    exact hmem
  have hoddα : Odd (Nat.card α.ker) := by
    refine Odd.of_dvd_nat (by norm_num : Odd 3) ((Subgroup.card_dvd_of_le hαker).trans ?_)
    rw [card_hypScalars (r := r) (ε := ε) hUF (by omega), show 2 ^ 1 + 1 = 3 from rfl]
    exact Nat.gcd_dvd_right _ _
  exact ⟨F, hFld, hFin, hUF, r, ε, hε, hm_eq, α, hα, hαker, hoddα⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
