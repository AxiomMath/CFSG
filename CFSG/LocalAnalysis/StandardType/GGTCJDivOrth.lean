module

public import CFSG.LocalAnalysis.StandardType.GGTCJDivDefs
public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrthMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrthModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrthDict
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegBCLab
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorOmega

public section

namespace CFSG.StandardType.TCJ

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
  CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)

theorem tcjOrth_quotCenter_cases_of_component_conj_omega {G : Type} [Group G] [Finite G]
    {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {m f p : ℕ}
    (hG : StatedClassicalModel G t m 2 f) (hp : p.Prime) (hp2 : p ≠ 2) (a : G) (ha : a ^ p = 1)
    {J : Subgroup G} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj a))) :
    (∃ (b k : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ b ∧ Nat.card E = 2 ^ k ∧
        f ∣ k ∧ Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSL b E))) ∨
      (∃ (b k : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ : E ≃+* E)
          (hτ : ∀ y, τ (τ y) = y), 2 ≤ b ∧ (∀ y, τ y = y ^ (2 ^ k)) ∧
          Nat.card E = (2 ^ k) ^ 2 ∧ f ∣ k ∧
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
            ↥(heldSU b E τ hτ) ⧸ Subgroup.center ↥(heldSU b E τ hτ))) ∨
      (∃ (s : ℕ) (K' : Type) (_ : Field K') (_ : Finite K'), 2 ≤ s ∧ Nat.card K' = 2 ^ f ∧
        ¬(s = 2 ∧ Nat.card K' = 2) ∧
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSp s K'))) ∨
      (∃ s : ℕ, StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .POmegaPlus s 2 f ∨
        StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .POmegaMinus s 2 f) := by
  classical
  obtain ⟨X, inst, -, hXLie, hfac, -, g, hg, hker⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_lieFactor_of_component_conj_omega_card
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.omegaFactorField_holds
      hp hp2 (Or.inr ht) hG hp2 a ha J hJ
  letI := inst
  obtain ⟨eJ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
    hXLie.perfect g hg hker
  unfold CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFactorOver at hfac
  rcases hfac with hSL | hSU | hSp | hOm
  ·
    exact Or.inl (Y10GCenterQuot.linCase_of_factor eJ hSL)
  ·
    exact Or.inr (Or.inl (Y10GCenterQuot.uniCase_of_factor eJ hSU))
  ·
    obtain ⟨K', _, _, hK'card, hK'ring, s, hs2, hne, ⟨eX⟩⟩ := hSp
    have hchar : CharP K' 2 := ringChar.of_eq hK'ring
    have hne' : ¬(s = 2 ∧ Nat.card K' = 2) := fun h => hne (by rw [h.1, h.2])
    obtain ⟨eXZ⟩ := Y10GCenterQuot.nonempty_centerQuot_sp (s := s) hs2 hne' hchar eX
    exact Or.inr (Or.inr (Or.inl
      ⟨s, K', _, Finite.of_fintype K', hs2, hK'card, hne', ⟨eJ.trans eXZ⟩⟩))
  ·
    obtain ⟨K', _, _, V, _, _, _, Q, hK'card, _, hQ, hd, hT, ⟨eX⟩⟩ := hOm
    obtain ⟨s, hs⟩ :=
      Y10GInnOrthModel.exists_statedClassicalModel_quotCenter_orthDerived
        hK'card hQ hd hT eX
    rcases hs with hplus | hminus
    · exact Or.inr (Or.inr (Or.inr
        ⟨s, Or.inl (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eJ.symm hplus)⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨s, Or.inr (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eJ.symm hminus)⟩))

theorem tcjOrth_quotCenter_canonLabel_cases_of_component_conj_omega
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {m f p : ℕ}
    (hG : StatedClassicalModel G t m 2 f) (hp : p.Prime) (hp2 : p ≠ 2) (a : G) (ha : a ^ p = 1)
    {J : Subgroup G} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj a)))
    {labJ : GLALabel} (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ)) :
    (∃ b k : ℕ, 2 ≤ b ∧ f ∣ k ∧ canonLabel labJ = ⟨.A, b - 1, k⟩) ∨
      (∃ b k : ℕ, 2 ≤ b ∧ f ∣ k ∧
        (canonLabel labJ = ⟨.twA, b - 1, k⟩ ∨ canonLabel labJ = ⟨.A, 1, k⟩)) ∨
      (∃ s : ℕ, 2 ≤ s ∧ canonLabel labJ = ⟨.B, s, f⟩) ∨
      (∃ s : ℕ, canonLabel labJ = ⟨.D, s, f⟩) ∨
      (∃ s : ℕ, canonLabel labJ = ⟨.twD, s, f⟩) := by
  rcases tcjOrth_quotCenter_cases_of_component_conj_omega ht hG hp hp2 a ha hJ with
    ⟨b, k, E, hfE, hfinE, hb, hE, hfk, hφ⟩ |
    ⟨b, k, E, hfE, hfinE, τ, hτ, hb, hτk, hE, hfk, hφ⟩ |
    ⟨s, K', hfK', hfinK', hs, hK', hne, hφ⟩ |
    ⟨s, hM | hM⟩
  · letI : Field E := hfE
    letI : Finite E := hfinE
    exact Or.inl ⟨b, k, hb, hfk,
      Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig _ labJ b k E hb hE hlabJ hφ⟩
  · letI : Field E := hfE
    letI : Finite E := hfinE
    exact Or.inr (Or.inl ⟨b, k, hb, hfk,
      Y10GNegBC.uniLabel_cases hRig τ hτ hb hτk hE hlabJ hφ⟩)
  · letI : Field K' := hfK'
    letI : Finite K' := hfinK'
    obtain ⟨eφ⟩ := hφ
    exact Or.inr (Or.inr (Or.inl ⟨s, hs,
      Y10GSympLabel.canonLabel_eq_of_quot_statedSp hRig hs hK' hne hlabJ eφ⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s,
      (Y10GFldOrth.orthLabelDict_of_ggLabelRigidInput hRig _ labJ s f hlabJ).1 hM⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨s,
      (Y10GFldOrth.orthLabelDict_of_ggLabelRigidInput hRig _ labJ s f hlabJ).2 hM⟩)))

theorem tcjOrth_innDiagAllOrth_of_ggLabelRigidInput (hRig : GGLabelRigidInput) :
    InnDiagAllOn FamOrth := by
  intro S _ _ p α J labK labJ hFam hp hp2 hcen hin hα hlabJ hJ
  obtain ⟨hmodel, a, rfl⟩ := Y10GInnOrthMark.innDiagKind_orth_data hcen hFam hin
  have hap : a ^ p = 1 := by
    have hc : a ^ p ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := DFunLike.congr_fun (show MulAut.conj (a ^ p) = 1 by rw [map_pow, hα]) z
      rw [MulAut.conj_apply, MulAut.one_apply] at hz
      exact (mul_inv_eq_iff_eq_mul.mp hz).symm
    rw [hcen] at hc
    exact Subgroup.mem_bot.mp hc
  obtain ⟨t, ht, hG⟩ : ∃ t : StatedLieTag, (t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      StatedClassicalModel S t labK.rank 2 (canonLabel labK).n := by
    rcases hmodel with hG | hG
    · exact ⟨_, Or.inl rfl, hG⟩
    · exact ⟨_, Or.inr rfl, hG⟩
  rcases tcjOrth_quotCenter_canonLabel_cases_of_component_conj_omega hRig ht hG hp hp2 a hap
      ((CFSG.Assembly.isComponentOf_iff_open).mp hJ) hlabJ with
    ⟨b, k, -, hnk, hA⟩ | ⟨b, k, -, hnk, hA | hA⟩ | ⟨s, -, hB⟩ | ⟨s, hD⟩ | ⟨s, hD⟩
  ·
    simpa [hA] using hnk
  ·
    simpa [hA] using hnk
  · simpa [hA] using hnk
  ·
    simp [hB]
  ·
    simp [hD]
  ·
    simp [hD]

theorem innDiagAllOrth :
    InnDiagAllOn FamOrth :=
  tcjOrth_innDiagAllOrth_of_ggLabelRigidInput ggLabelRigidInput_holds

end CFSG.StandardType.TCJ

end
