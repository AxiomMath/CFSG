module

public import CFSG.Foundations.Basic
public import CFSG.Open.StatedDefs
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockDet
public import CFSG.RankThree.PartOne.KC.OrthogonalPrimaryPairing
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmFix
import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmSmallBlock
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryRegular
import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.RankThree.CentralLiftU.UnitaryThreeLift
import CFSG.RankThree.PartOne.K159.RowFourType
import CFSG.RankThree.PartOne.KC.OrthogonalBlockQuasisimple
import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusModel
import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSix
import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixUnitary
import CFSG.RankThree.PartOne.S11d.OrthModels
import CFSG.Open.StatedAPI
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.SectionRank.SignLines
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.RankThree.PartOne.S11d.LieGoodConclusion
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.StandardType.TCJ

open QuadraticMap CFSG.Open CFSG.RankThree.Classical2 CFSG.GroupTheory.WeirSylow

private theorem six_minus_equiv {F : Type} [Field F] [Finite F] [CharP F 2] {W : Type}
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] {R : QuadraticForm F W}
    (hR : (polarBilin R).Nondegenerate) {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hd : Module.finrank F W = 6)
    (hno : ¬ ∃ T : Submodule F W, Module.finrank F T = 3 ∧ ∀ x ∈ T, R x = 0) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = (2 ^ f) ^ 2 ∧
      Nonempty (↥(StatedSU 4 (2 ^ f) E) ≃* ↥(orthDerived R)) := by
  have hts : ∀ U : Submodule F W, Module.finrank F U = 3 → ∃ u ∈ U, R u ≠ 0 := by
    intro U hU
    by_contra hcon
    push Not at hcon
    exact hno ⟨U, hU, hcon⟩
  obtain ⟨E, _, _, D, ψ, hψ⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.exists_evenMinus_model R hR (n := 3) (by norm_num)
      (by omega) hts
  haveI : CharP E 2 := CFSG.RankThree.PartOne.KCOrthogonal.charP_two_of_algebra (K := F)
  haveI := D.finite_E
  let e1 : R.IsometryEquiv (CFSG.RankThree.PartOne.KCOrthogonal.evenNormTailForm D.N 2) :=
    { toLinearEquiv := ψ
      map_app' := fun w => hψ w }
  let e2 : R.IsometryEquiv D.sixForm := e1.trans D.sixIsometry
  obtain ⟨-, -, -, -, -, -, -, -, hinj, -, -, -, -, -, -, -, hcomm, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_unitary_derived_model D
  have hrange : orthDerived D.sixForm = D.sixRho.range := hcomm
  let e3 : D.sixSU ≃* ↥(orthDerived D.sixForm) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange.symm)
  obtain ⟨f', hU, hcard, hbar⟩ := D.exists_unitaryFieldData
  obtain ⟨e4⟩ := D.nonempty_sixSU_mulEquiv hU hbar
  obtain rfl : f' = f := Nat.pow_right_injective le_rfl (hcard.symm.trans hF)
  exact ⟨E, inferInstance, inferInstance, by rw [D.card_E, hcard],
    ⟨e4.symm.trans (e3.trans (CFSG.RankThree.PartOne.orthDerivedEquiv e2).symm)⟩⟩

open CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry in
private theorem large_model {F : Type} [Field F] [Finite F] [CharP F 2] {W : Type}
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] {R : QuadraticForm F W}
    (hR : (polarBilin R).Nondegenerate) {s f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hs : Module.finrank F W = 2 * s) (h4 : 4 ≤ s)
    (htype : IsPlusType R ↔ Even s) :
    Subgroup.center ↥(orthDerived R) = ⊥ ∧
      (StatedClassicalModel ↥(orthDerived R) .POmegaPlus s 2 f ∨
        StatedClassicalModel ↥(orthDerived R) .POmegaMinus s 2 f) := by
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := F) (M := W) (by omega)
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hF
      exact absurd hF (Finite.one_lt_card (α := F)).ne'
    · exact h0
  by_cases hev : Even s
  · obtain ⟨e⟩ := nonempty_isometry_quadPlus hR hs (htype.2 hev)
    have hT := singular_three_isometry e.symm
      (CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := F) (n := s) (by omega)).2
    exact ⟨CFSG.RankThree.PartOne.center_orthDerived_eq_bot hR hT, Or.inl
      ((CFSG.RankThree.PartOne.lieModel_of_orthDerived_plus (m := s) h4 hf hF e
        (MulEquiv.refl _)).statedClassicalModel (by decide))⟩
  · rcases exists_isometry_quadPlus_or_quadMinus R hR (by omega : 1 ≤ s) hs with
      he | ⟨b, c, hirr, ⟨e⟩⟩
    · obtain ⟨e⟩ := he
      exact absurd (htype.1 ((isPlusType_congr e).2 (isPlusType_quadPlus F s))) hev
    · have hT := singular_three_isometry e.symm
        (CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (n := s) h4 hirr).2
      exact ⟨CFSG.RankThree.PartOne.center_orthDerived_eq_bot hR hT, Or.inr
        ((CFSG.RankThree.PartOne.lieModel_of_orthDerived_minus (m := s) h4 hf hF hirr e
          (MulEquiv.refl _)).statedClassicalModel (by decide))⟩

private theorem isSubnormal_map_subtype {F : Type} [Field F] {W : Type} [AddCommGroup W]
    [Module F W] {R : QuadraticForm F W} (N : Subgroup ↥(orthDerived R)) (hN : N.Normal) :
    CFSG.Assembly.IsSubnormal (N.map (orthDerived R).subtype)
      (TauCeti.QuadraticMap.orthogonalGroup R) := by
  set O := TauCeti.QuadraticMap.orthogonalGroup R
  have hΩO : orthDerived R ≤ O := Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact O.mul_mem (O.mul_mem (O.mul_mem h₁ h₂) (O.inv_mem h₁)) (O.inv_mem h₂)
  refine .step (Subgroup.map_subtype_le N) ?_ (.step hΩO ?_ (.refl O))
  · show ((N.map (orthDerived R).subtype).comap (orthDerived R).subtype).Normal
    rwa [Subgroup.comap_map_eq_self_of_injective (orthDerived R).subtype_injective]
  · have h1 : (orthDerived R).subgroupOf O = _root_.commutator ↥O := by
      rw [orthDerived, ← Subgroup.map_subtype_commutator]
      exact Subgroup.comap_map_eq_self_of_injective O.subtype_injective _
    rw [h1]
    infer_instance

theorem orthDerived_quasisimple_normal_type {F : Type} [Field F] [Finite F] [CharP F 2]
    {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W] {R : QuadraticForm F W}
    (hR : (polarBilin R).Nondegenerate) {s f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hs : Module.finrank F W = 2 * s) (htype : 1 ≤ s → (IsPlusType R ↔ Even s))
    (N : Subgroup ↥(orthDerived R)) (hN : N.Normal) (hNq : CFSG.IsQuasisimple ↥N) :
    (∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = 2 ^ f ∧
        Nonempty (↥N ≃* Matrix.SpecialLinearGroup (Fin 2) E)) ∨
      (∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = (2 ^ f) ^ 2 ∧
        Nonempty (↥N ≃* ↥(StatedSU 4 (2 ^ f) E))) ∨
      (Subgroup.center ↥N = ⊥ ∧ ∃ s' : ℕ,
        StatedClassicalModel ↥N .POmegaPlus s' 2 f ∨
          StatedClassicalModel ↥N .POmegaMinus s' 2 f) := by
  classical
  set T : Subgroup (W ≃ₗ[F] W) := N.map (orthDerived R).subtype
  let eNT : ↥N ≃* ↥T := N.equivMapOfInjective _ (orthDerived R).subtype_injective
  have hTq : CFSG.IsQuasisimple ↥T := CFSG.LocalCores.isQuasisimple_of_mulEquiv eNT hNq
  obtain ⟨h4, ⟨hns, hTc⟩ | ⟨-, -, ψ, hψ, hψT⟩⟩ :=
    CFSG.StandardType.OmNonsplit.structure_of_isSubnormal hR hTq (isSubnormal_map_subtype N hN)
  · have hNtop : N = ⊤ := by
      rw [eq_top_iff]
      intro n _
      have hn : (n : W ≃ₗ[F] W) ∈ T := by
        rw [hTc]
        exact n.2
      obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.mp hn
      rwa [show m = n from Subtype.ext hmn] at hm
    let eN : ↥N ≃* ↥(orthDerived R) := (MulEquiv.subgroupCongr hNtop).trans Subgroup.topEquiv
    rcases (show s = 2 ∨ s = 3 ∨ 4 ≤ s by omega) with rfl | rfl | h4s
    · obtain ⟨S, hS, hSs⟩ := (htype (by norm_num)).2 (by decide)
      exact absurd ⟨by omega, S, by omega, hSs⟩ hns
    · obtain ⟨E, _, _, hE, ⟨e⟩⟩ := six_minus_equiv hR hF (by omega)
        (fun ⟨T', hT', hT's⟩ => absurd ((htype (by norm_num)).1 ⟨T', by omega, hT's⟩)
          (by decide))
      exact Or.inr (Or.inl ⟨E, inferInstance, inferInstance, hE, ⟨eN.trans e.symm⟩⟩)
    · obtain ⟨hZ, hM⟩ := large_model hR hF hs h4s (htype (by omega))
      refine Or.inr (Or.inr ⟨?_, s, ?_⟩)
      · rw [← Subgroup.map_center_eq eN.symm, hZ, Subgroup.map_bot]
      · rcases hM with hM | hM
        · exact Or.inl (StatedAPI.statedClassicalModel_of_mulEquiv eN.symm hM)
        · exact Or.inr (StatedAPI.statedClassicalModel_of_mulEquiv eN.symm hM)
  · exact Or.inl ⟨F, inferInstance, inferInstance, hF,
      ⟨eNT.trans ((MulEquiv.subgroupCongr hψT.symm).trans (MonoidHom.ofInjective hψ).symm)⟩⟩

open Polynomial CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary in
theorem specialBlock_selfDual_ennola {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) :
    (∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = Nat.card K ∧
        Nonempty (↥(specialBlock Q x h) ≃* Matrix.SpecialLinearGroup (Fin 2) E)) ∨
      (∃ (E : Type) (_ : Field E) (_ : Finite E), 3 ≤ primaryMultiplicity x.toLinearMap h ∧
        Nat.card E = Nat.card K ^ 2 ∧
        Nonempty (↥(specialBlock Q x h) ≃*
          ↥(StatedSU (primaryMultiplicity x.toLinearMap h) (Nat.card K) E))) := by
  classical
  have hm2 := CFSG.StandardType.SevOmSmall.two_le_primaryMultiplicity hx hh hq
  rcases (show primaryMultiplicity x.toLinearMap h = 2 ∨
      3 ≤ primaryMultiplicity x.toLinearMap h by omega) with hm | hm3
  · obtain ⟨E, _, _, hE, ⟨e⟩⟩ :=
      CFSG.StandardType.SevOmSmall.exists_specialBlock_equiv_SL2 hx hp hp2 hpq hh hne1 hm
    exact Or.inl ⟨E, inferInstance, inferInstance, hE, ⟨e⟩⟩
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hself : h = reciprocalPolynomial h :=
    (CFSG.RankThree.PartOne.K159.reciprocalPolynomial_eq_of_dvd_card_add_one hx hpq hh).symm
  have hdeg :=
    CFSG.RankThree.PartOne.K159.natDegree_eq_two_of_dvd_card_add_one hx hp hp2 hpq hh hne1
  obtain ⟨d, ℓ, f, hU, B, hd, -, hKℓ, hBs, hBl, hrange⟩ :=
    CFSG.StandardType.SevOmSmall.selfDual_unitary hx hp hp2 hh hne1 hself
  obtain rfl : d = 1 := by omega
  haveI := hU.finite
  haveI : Fact ℓ.Prime := ⟨hU.prime⟩
  haveI := hU.charP
  let e₁ : ↥(specialBlock Q x h) ≃*
      ↥(CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  have hE : Nat.card (AdjoinRoot h) = (ℓ ^ (f * 1)) ^ 2 := by
    rw [hU.card]
    ring
  obtain ⟨e₀, he₀⟩ := hU.exists_orthonormal_basis hBs hBl
  obtain ⟨e₂⟩ :=
    CFSG.RankThree.CentralLiftU.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid hU e₀ he₀
  have hS : CFSG.LieType.Universal.Unitary.SUid hU.barEquiv
      (primaryMultiplicity x.toLinearMap h) =
      StatedSU (primaryMultiplicity x.toLinearMap h) (ℓ ^ (f * 1)) (AdjoinRoot h) := by
    rw [CFSG.RankThree.CentralLiftU.barEquiv_eq_unitaryInvolution hU]
    exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hE _
  have hq' : ℓ ^ (f * 1) = Nat.card K := by rw [mul_one, hKℓ]
  refine Or.inr ⟨AdjoinRoot h, inferInstance, inferInstance, hm3, by rw [hE, hq'], ?_⟩
  rw [← hq']
  exact ⟨e₁.trans (e₂.trans (MulEquiv.subgroupCongr hS))⟩

end CFSG.StandardType.TCJ

end
