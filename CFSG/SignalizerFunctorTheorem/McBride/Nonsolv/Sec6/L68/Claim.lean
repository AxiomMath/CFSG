module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L68.Setup

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L68

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem le_or_le_centralizer
    (h : Counterexample p A θ) {J W : Subgroup G}
    (hJ : J ∈ lcal (thetaOf θ A)) (hW : IsGreatestCentralizing p A θ J W) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) {L : Subgroup G} (hL : L ∈ lcal (thetaOf θ B)) :
    L ≤ W ∨ L ≤ Subgroup.centralizer (W : Set G) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hLW, hLC⟩ := hcon
  have hBA : B ≤ A := hB.1
  have hBne : B ≠ ⊥ := h.ne_bot_of_mem_E2 hB
  have hAJ : A ≤ Subgroup.centralizer (J : Set G) :=
    le_centralizer_of_le_thetaOf h (lcal_le hJ)
  obtain ⟨b, hb, hb1, hbW⟩ : ∃ b ∈ B, b ≠ 1 ∧
      ¬ W ⊓ Subgroup.centralizer {b} ≤ Subgroup.centralizer (L : Set G) := by
    by_contra hall
    push Not at hall
    apply hLC
    rw [Subgroup.le_centralizer_iff]
    calc W = ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), W ⊓ Subgroup.centralizer {b} :=
          (iSup_inf_centralizer h.prime (h.isElemAbelian_of_le hBA) hB.2.ge
            (hBA.trans hW.mem.1) hW.mem.2.1).symm
      _ ≤ _ := iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => hall b hb hb1
  have hbA : b ∈ A := hBA hb
  have hset := h.kSetting_apply hbA hb1
  have hKA := kDown_apply h hbA hb1
  have hsol := sol_apply h hbA hb1
  obtain ⟨M, hM, hLM⟩ : ∃ M ∈ lcal (θ b),
      L = CFSG.inSubgroup CFSG.generalizedFitting (smear M B) := by
    have h1 := (theorem_5_15_f hset hKA hBA).2.1
    rw [← thetaOf_eq_inf_centralizer h hBA hb hb1] at h1
    rw [h1] at hL
    exact hL
  have hLT : L ≤ orbitClosure M A := hLM ▸ fitting_smear_le_orbitClosure hBA
  have hAHJ : A ≤ Subgroup.normalizer ((θ b ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) :
      Set G) := fun a ha => mem_normalizer_inf (h.isFunctor.normalized b hbA hb1 ha)
    (Subgroup.le_normalizer (hAJ ha))
  have hCbW : W ⊓ Subgroup.centralizer {b} ≤ θ b ⊓ Subgroup.centralizer (J : Set G) :=
    le_inf (hW.mem.2.2.1 b hbA hb1) (inf_le_left.trans hW.le_centralizer)
  have hHJM : ¬ θ b ⊓ Subgroup.centralizer (J : Set G) ≤ Subgroup.centralizer (M : Set G) := by
    intro hle
    exact hbW (hCbW.trans ((le_centralizer_orbitClosure hAHJ hle).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hLT))))
  have hMA : M ∈ lcalA (θ b) A := (lcalA_eq_lcal_of_kDown_eq_bot hset hKA).symm ▸ hM
  have hDA : IsDAInvariant A (θ b) (θ b ⊓ Subgroup.centralizer (J : Set G)) := by
    refine ⟨inf_le_left, fun d hd => ?_, hAHJ⟩
    have hdD : d ∈ thetaOf θ A := by
      rw [← h.isFunctor.inf_centralizer_self hbA hb1]
      exact hd
    exact mem_normalizer_inf (Subgroup.le_normalizer hd.1)
      (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup J
        (thetaOf_le_normalizer h hJ hdD))
  have hFHJ : CFSG.inSubgroup CFSG.generalizedFitting (smear M A) ≤
      θ b ⊓ Subgroup.centralizer (J : Set G) :=
    (lemma_5_14 hset hDA hsol hMA).resolve_right hHJM
  obtain ⟨MJ, hMJ, hJeq⟩ : ∃ MJ ∈ lcal (θ b),
      J = CFSG.inSubgroup CFSG.generalizedFitting (smear MJ A) := by
    have h1 := lcal_thetaOf_eq h hbA hb1
    rw [h1] at hJ
    exact hJ
  have hne : MJ ∉ conjOrbit A M := by
    rintro ⟨a, ha, hMJa⟩
    have heq := ((theorem_5_15_f hset hKA (le_refl A)).2.2 M hM MJ hMJ).mpr ⟨a, ha, hMJa⟩
    have hJHJ : J ≤ θ b ⊓ Subgroup.centralizer (J : Set G) :=
      calc J = CFSG.inSubgroup CFSG.generalizedFitting (smear MJ A) := hJeq
        _ = CFSG.inSubgroup CFSG.generalizedFitting (smear M A) := heq.symm
        _ ≤ _ := hFHJ
    exact (mem_lcal_iff.mp hJ).2.2.2
      (Subgroup.le_centralizer_iff_isMulCommutative.mp (hJHJ.trans inf_le_right))
  have hJle : J ≤ orbitClosure MJ A :=
    calc J = CFSG.inSubgroup CFSG.generalizedFitting (smear MJ A) := hJeq
      _ ≤ orbitClosure MJ A := fitting_smear_le_orbitClosure le_rfl
  have hTJ : orbitClosure M A ≤ Subgroup.centralizer (J : Set G) :=
    Subgroup.le_centralizer_iff.mp
      (hJle.trans (orbitClosure_le_centralizer hset.normalizes hsol hM hMJ hne))
  have hYT : orbitClosure L A ≤ orbitClosure M A :=
    orbitClosure_le_of_le hLT fun a ha => mem_normalizer_orbitClosure ha
  have hYH : orbitClosure L A ≤ thetaOf θ B :=
    orbitClosure_le_of_le (lcal_le hL) (h.isFunctor.normalizes_thetaOf hBA)
  have hYmem : orbitClosure L A ∈ Msig p A θ :=
    mem_signalizers_of_le (h.thetaOf_mem_msig hBA hBne) hYH
      (fun a ha => mem_normalizer_orbitClosure ha) (fun hP => hypB_mono hYH hP)
  exact hLW ((le_orbitClosure L A).trans (hW.le_of_le _ hYmem (hYT.trans hTJ)))

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L68
