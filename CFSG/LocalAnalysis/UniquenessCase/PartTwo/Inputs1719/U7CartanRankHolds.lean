module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanQuotientBridge
public import CFSG.LocalAnalysis.UniquenessCase.Lie.BorelSU
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcShared
public import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFourSupport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)
open CFSG.ClassicalGroups.UnitaryFlag

theorem k_U7CartanRank_of_two_le :
    ∀ (K : Type) [Group K] [Finite K] (f p : ℕ),
      CFSG.Open.StatedLieAdmissible .PSU 7 2 f → Odd f → 2 ≤ f →
        LieModel (K ⧸ Subgroup.center K) .PSU 7 2 f → CFSG.Open.IsQuasisimple K →
          Odd (Nat.card (Subgroup.center K)) → p.Prime → p ≠ 2 → p ∣ 2 ^ f + 1 →
            ∀ S : Subgroup K, IsSylowTwoOf S ⊤ →
              3 ≤ CFSG.pRank p (⊤ : Subgroup (normalizerQuotient S)) := by
  intro K _ _ f p _ _ hf hL hq _ hp hp2 hpd S hS
  have h7 : ¬ p ∣ 2 * 3 + 1 := by
    intro h
    have hp7 : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
    have h8 := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_two_pow_mod_seven f
    have h7' : 7 ∣ 2 ^ f + 1 := hp7 ▸ hpd
    omega
  have hW := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_borelWit_of_lieModel (r := 3)
    (ε := 1) hq (by norm_num) le_rfl (by norm_num) hf hL hp hpd h7
  have h := (le_pRank_normalizerQuotient_of_borelWit hp hp2 hW S hS).1
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
  simpa using h

theorem k_U7CartanRank_holds :
    ∀ (K : Type) [Group K] [Finite K] (f p : ℕ),
      CFSG.Open.StatedLieAdmissible .PSU 7 2 f → Odd f →
        LieModel (K ⧸ Subgroup.center K) .PSU 7 2 f → CFSG.Open.IsQuasisimple K →
          Odd (Nat.card (Subgroup.center K)) → p.Prime → p ≠ 2 → p ∣ 2 ^ f + 1 →
            ∀ S : Subgroup K, IsSylowTwoOf S ⊤ →
              3 ≤ pRank p (⊤ : Subgroup (normalizerQuotient S)) := by
  intro K _ _ f p hadm hfodd hL hq hodd hp hp2 hpd S hS
  rcases Nat.lt_or_ge f 2 with hf | hf
  · obtain ⟨k, hk⟩ := hfodd
    have hf1 : f = 1 := by omega
    subst hf1
    have hp3 : p = 3 := by
      refine (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).1 ?_
      simpa using hpd
    subst hp3
    haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hq.1
    obtain ⟨Kf, hFld, hFin, h, ⟨e⟩⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_exists_hypPSU
        (n := 1) (r := 3) (ε := 1) le_rfl (by norm_num) hL
    letI := hFld
    letI := hFin
    haveI : CharP Kf 2 := h.charP
    have hZcard : Nat.card (hypScalars h 3 1) = 1 := by
      rw [card_hypScalars h (by norm_num : 1 ≤ 2 * 3 + 1)]
      norm_num
    have hZbot : hypScalars h 3 1 = ⊥ := Subgroup.card_eq_one.mp hZcard
    have eZ : hypPSU h 3 1 ≃* hypSU h 3 1 :=
      (QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot
    have e₂ : (K ⧸ Subgroup.center K) ≃* hypSU h 3 1 := e.trans eZ
    obtain ⟨R, hR⟩ := exists_isHypTransport (h := h) (r := 3) (ε := 1)
    let Φ : hypSU h 3 1 ≃* StatedSU 7 (2 ^ 1) Kf := hypTransport h hR
    let π : K →* StatedSU 7 (2 ^ 1) Kf :=
      Φ.toMonoidHom.comp (e₂.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))
    have hπ : Function.Surjective π :=
      Φ.surjective.comp (e₂.surjective.comp (QuotientGroup.mk'_surjective _))
    have hπc : π.ker ≤ Subgroup.center K := by
      intro x hx
      have hx2 : e₂ (QuotientGroup.mk x) = 1 := by
        apply Φ.injective
        simpa [π] using hx
      exact (QuotientGroup.eq_one_iff x).1 (e₂.injective (by simpa using hx2))
    obtain ⟨s, hs⟩ :=
      CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
        (p := 2) (f := 1) (F := Kf) (n := 7) (by rw [h.card]; norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (E := K) (π := π) hπ hπc
    have hkerbot : π.ker = ⊥ :=
      CFSG.LieType.Steinberg.CentralExt.SUOdd.ker_eq_bot_of_section hπc hs
    have hcenter : Subgroup.center K = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxq : QuotientGroup.mk x = 1 := (QuotientGroup.eq_one_iff x).2 hx
      have hxπ : x ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        show Φ (e₂ (QuotientGroup.mk x)) = 1
        rw [hxq]
        simp
      rw [hkerbot] at hxπ
      simpa using hxπ
    obtain ⟨e0⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwex_equiv_quot_of_center_eq_bot hcenter
    have eK : K ≃* hypSU h 3 1 := e0.trans e₂
    obtain ⟨μ, hcardμ, hexpμ, hμ⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_exists_mu (h := h) (n := 1)
        (ℓ := 3) (by norm_num) (by norm_num)
    have hinj : ∀ x : (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_ratio μ 3 1).ker,
        eK.symm (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_hom hμ x) = 1 → x = 1 := by
      intro x hx
      apply CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_eq_one_of_hom_eq_one hμ x
      exact eK.symm.injective (by simpa using hx)
    have hW := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_borelWit_core (h := h)
      (hμ := hμ) (hℓ := by norm_num) (hodd := by decide) (hcard := hcardμ) (hexp := hexpμ)
      (r := 3) (ε := 1) (hr := by norm_num) (hε := by norm_num) (X := K)
      (α := eK.symm.toMonoidHom) (hα := eK.symm.surjective) (hinj := hinj)
    have h := (le_pRank_normalizerQuotient_of_borelWit (by norm_num : Nat.Prime 3)
      (by norm_num : (3 : ℕ) ≠ 2) hW S hS).1
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    simpa using h
  · exact k_U7CartanRank_of_two_le K f p hadm hfodd hf hL hq hodd hp hp2 hpd S hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
