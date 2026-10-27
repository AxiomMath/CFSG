module

public import CFSG.LieType.ChevTwo.Main
public import CFSG.LieType.ChevTwo.OutCommInner
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
public import CFSG.LocalAnalysis.GLTheoremA.CatA.CentQChar2Index
public import CFSG.Adapters.StatedPSLTwoSeven
public import CFSG.Adapters.LinearCatalog
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.ChevFrontier
public import CFSG.GroupTheory.ConjNormalFaithful
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalModel
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4O2
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.FFC4Pair
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.Background.SmithB42L2L32
public import CFSG.Quasithin.Background.SmithB42L2Nat
public import CFSG.Quasithin.Background.SmithB51LnRealB
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremA
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo IsChevIndexTwo)
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531
  (isChevIndexTwo_of_characteristic isChevTwo_of_mulEquiv)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_statedScalars statedProjCongr glCongr_statedSU)

theorem isChevTwo_of_statedClassicalModel_psl_two_seven {S : Type} [Group S]
    (h : StatedClassicalModel S .PSL 2 7 1) : IsChevTwo S := by
  let q : TauCeti.PrimePower := ⟨7, 1, Nat.prime_seven, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.A 1 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [q, TauCeti.PrimePower.card_def]
  let _ : Fact q.p.Prime := ⟨Nat.prime_seven⟩
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  have hK7 : Nat.card K = 7 := by simpa using hK
  have eK := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 2 7 1
    (by norm_num) (by rw [hK7]; norm_num)
  have eC := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv
  refine Or.inr (Or.inr ⟨⟨.A 1 q, hv⟩, Or.inl ⟨q, ?_, rfl⟩,
    ⟨e.trans eK |>.trans eC.symm⟩⟩)
  simp [q, TauCeti.PrimePower.card_def]

theorem isChevTwo_of_statedClassicalModel_psu_three_three {S : Type} [Group S]
    (h : StatedClassicalModel S .PSU 3 3 1) : IsChevTwo S := by
  let q : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [q, TauCeti.PrimePower.card_def]
  let _ : Fact q.p.Prime := ⟨Nat.prime_three⟩
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  let ec := (TauCeti.LieTypeIndex.twistedA 2 q).characteristic
  let ef := (TauCeti.LieTypeIndex.twistedA 2 q).fieldExponent
  have hc : ec = 3 := TauCeti.LieTypeIndex.characteristic_twistedA 2 q
  have hf : ef = 1 := TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
  let _ : Fact ec.Prime := ⟨by rw [hc]; norm_num⟩
  let L := GaloisField ec (2 * ef)
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card K = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card ec (2 * ef) (by rw [hf]; norm_num)]
    rw [hc, hf]
    norm_num
  let φ : K ≃+* L := FiniteField.ringEquivOfCardEq hcard
  let e1 := statedProjCongr (glCongr (ι := Fin 3) φ) (glCongr_statedSU φ 3 (ec ^ ef))
    (glCongr_statedScalars φ)
  let P : ℕ → Type := fun m => StatedProj (StatedSU 3 m K)
  have hq : 3 ^ 1 = ec ^ ef := by rw [hc, hf]
  let eparam : P (3 ^ 1) ≃* P (ec ^ ef) := MulEquiv.cast (M := P) hq
  let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv
  refine Or.inr (Or.inr ⟨⟨.twistedA 2 q, hv⟩, Or.inr ⟨q, ?_, rfl⟩,
    ⟨(e.trans eparam).trans e1 |>.trans eT.symm⟩⟩)
  simp [q, TauCeti.PrimePower.card_def]

section MarkedModel


theorem isChevTwo_of_markedModel {lab : LargeEvenLabel} {R : Type} [Group R]
    (h : MarkedModel lab R) : IsChevTwo R := by
  obtain ⟨tag, rank, n⟩ := lab
  have hclass : ∀ {t' : StatedLieTag} {n' f' : ℕ}, LieModel R t' n' 2 f' →
      t' ∈ classicalTags → IsChevTwo R := by
    intro t' n' f' hm ht
    have hsc : StatedClassicalModel R t' n' 2 f' := hm.statedClassicalModel ht
    rcases classical_two_cases hsc with
      ⟨d, hd, ⟨e⟩⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Or.inl ⟨d, isChevIndexTwo_of_characteristic hd, ⟨e⟩⟩
    · obtain ⟨-, K, _, _, hK, ⟨eRK⟩⟩ := hsc
      obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
        (Or.inl (by rw [hK]; norm_num))
      exact Or.inr (Or.inl ⟨5, by norm_num, ⟨eRK.trans e5⟩⟩)
    · exact isChevTwo_of_statedClassicalModel_psl_two_seven
        (CFSG.Open.StatedAPI.statedClassicalModel_psl_two_seven_of_psl_three_two hsc)
    · exact Or.inr (Or.inl ⟨8, by norm_num,
        CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel
          (Or.inl ⟨ht, hsc⟩)⟩)
  have hchev : ∀ {t' : StatedLieTag} {n' f' : ℕ}, LieModel R t' n' 2 f' →
      t' ∈ chevalleyExceptionalTags → IsChevTwo R := by
    intro t' n' f' hm ht
    obtain ⟨d, hd, he⟩ := index_of_chevalleyExceptional ht (hm.chevalleyExceptionalModel ht)
    exact Or.inl ⟨d, isChevIndexTwo_of_characteristic hd, he⟩
  cases tag
  · exact hclass (t' := .PSL) h (by simp [classicalTags])
  · exact hclass (t' := .PSU) h (by simp [classicalTags])
  · exact hclass (t' := .PSp) h (by simp [classicalTags])
  · exact hclass (t' := .PSp) h (by simp [classicalTags])
  · by_cases hr : rank = 3
    · subst hr
      exact hclass (t' := .PSL) h (by simp [classicalTags])
    · have h' : LieModel R .POmegaPlus rank 2 n := by
        simpa [MarkedModel, markTag, markRank, markChar, markDeg, hr] using h
      exact hclass h' (by simp [classicalTags])
  · by_cases hr2 : rank = 2
    · subst hr2
      exact hclass (t' := .PSL) h (by simp [classicalTags])
    · by_cases hr3 : rank = 3
      · subst hr3
        exact hclass (t' := .PSU) h (by simp [classicalTags])
      · have h' : LieModel R .POmegaMinus rank 2 n := by
          simpa [MarkedModel, markTag, markRank, markChar, markDeg, hr2, hr3] using h
        exact hclass h' (by simp [classicalTags])
  · exact hchev (t' := .E6) h (by simp [chevalleyExceptionalTags])
  · exact hchev (t' := .E7) h (by simp [chevalleyExceptionalTags])
  · exact hchev (t' := .E8) h (by simp [chevalleyExceptionalTags])
  · exact hchev (t' := .F4) h (by simp [chevalleyExceptionalTags])
  · exact hchev (t' := .twistedE6) h (by simp [chevalleyExceptionalTags])
  · exact hchev (t' := .trialityD4) h (by simp [chevalleyExceptionalTags])
  · exact hchev (t' := .G2) h (by simp [chevalleyExceptionalTags])
  ·
    obtain ⟨-, -, hS⟩ : (0 = 0) ∧ (StatedLieTag.twistedB2 = .twistedB2) ∧ SuzukiModel R 2 n := by
      rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
      · exact absurd ht (by simp [classicalTags, markTag])
      · exact absurd ht (by simp [chevalleyExceptionalTags, markTag])
      · exact absurd ht (by simp [reeTitsTags, markTag])
      · exact ⟨rfl, rfl, hS⟩
    obtain ⟨d, hd, he⟩ := index_of_suzuki hS
    exact Or.inl ⟨d, isChevIndexTwo_of_characteristic hd, he⟩
  ·
    obtain ⟨-, hR⟩ := CFSG.Blueprint.LieModel.reeTitsModel (t := .twistedF4) h
      (by simp [reeTitsTags])
    obtain ⟨d, hd, he⟩ := index_of_reeTits_two (Or.inl rfl) hR
    exact Or.inl ⟨d, isChevIndexTwo_of_characteristic hd, he⟩
  ·
    exact Or.inr (Or.inl ⟨6, by norm_num,
      CFSG.Blueprint.LieModel.nonempty_mulEquiv_alternating_six h⟩)
  ·
    exact isChevTwo_of_statedClassicalModel_psu_three_three
      (CFSG.Blueprint.LieModel.statedClassicalModel (t := .PSU) h (by simp [classicalTags]))
  ·
    obtain ⟨-, hR⟩ := CFSG.Blueprint.LieModel.reeTitsModel (t := .Tits) h
      (by simp [reeTitsTags])
    obtain ⟨d, hd, he⟩ := index_of_reeTits_two (Or.inr rfl) hR
    exact Or.inl ⟨d, isChevIndexTwo_of_characteristic hd, he⟩

end MarkedModel

section Marking


theorem isChevTwo_of_largeEvenMarking {L : Type} [Group L]
    {P : LargeEvenMarkProp L} (h : LargeEvenMarking L P) :
    IsChevTwo (L ⧸ Subgroup.center L) := by
  obtain ⟨lab, -, hM⟩ := CFSG.StandardType.largeEvenMarking_markedModel_centerQuot h
  exact isChevTwo_of_markedModel hM

theorem isChevTwo_of_largeEvenMarking_of_center_eq_bot {L : Type} [Group L]
    {P : LargeEvenMarkProp L} (h : LargeEvenMarking L P)
    (hcenter : Subgroup.center L = ⊥) : IsChevTwo L := by
  have hq := isChevTwo_of_largeEvenMarking h
  let e : L ≃* L ⧸ Subgroup.center L :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
  exact isChevTwo_of_mulEquiv e.symm hq

end Marking

section K3


theorem ggOutTwoCommInner_holds : GGOutTwoCommInner := by
  intro W _ _ Kb hKbNormal hCent hSimple hMark δ hδ Y hY hδY y hy
  haveI : Kb.Normal := hKbNormal
  let φ : W →* MulAut Kb := MulAut.conjNormal
  have hnab : ∃ a b : Kb, a * b ≠ b * a := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hle : Kb ≤ Subgroup.centralizer (Kb : Set W) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      simpa using (h ⟨a, ha⟩ ⟨b, hb⟩).symm
    rw [hCent] at hle
    have hbot : Kb = ⊥ := le_bot_iff.mp hle
    haveI : Subsingleton Kb := by rw [hbot]; infer_instance
    obtain ⟨a, b, hab⟩ := hSimple.toNontrivial.exists_pair_ne
    exact hab (Subsingleton.elim a b)
  have hcenter : Subgroup.center Kb = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Kb) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hinj : Function.Injective φ := by
    change Function.Injective (MulAut.conjNormal : W →* MulAut Kb)
    exact Subgroup.conjNormal_injective_of_centralizer_le (N := Kb)
      (by rw [hCent]; exact bot_le) hcenter
  have hchev : IsChevTwo Kb :=
    isChevTwo_of_largeEvenMarking_of_center_eq_bot hMark hcenter
  have hOut : CFSG.LieType.ChevTwo.OutTwoNilpConcl Kb :=
    CFSG.LieType.ChevTwo.chev2OutTwoNilp_of_leaves Kb hSimple hnab hchev
  have hY' : IsPGroup 2 (Y.map φ) := hY.map φ
  have hδY' : φ δ ∈ Subgroup.normalizer ((Y.map φ) : Set (MulAut Kb)) :=
    Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ hδY)
  have hδ' : Odd (orderOf (φ δ)) := hδ.of_dvd_nat (orderOf_map_dvd φ δ)
  have hcomm : (φ y)⁻¹ * (φ δ)⁻¹ * (φ y) * (φ δ) ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner Kb :=
    CFSG.LieType.ChevTwo.OutTwoNilpConcl.commutator_mem_inner hOut hδ' hY' hδY'
      (Subgroup.mem_map_of_mem φ hy)
  obtain ⟨k, hk⟩ := hcomm
  have hkφ : φ (k : W) = φ (y⁻¹) * φ (δ⁻¹) * φ y * φ δ := by
    calc φ (k : W) = MulAut.conj k := by simp only [φ, MulAut.conjNormal_val]
      _ = (φ y)⁻¹ * (φ δ)⁻¹ * φ y * φ δ := hk
      _ = φ (y⁻¹) * φ (δ⁻¹) * φ y * φ δ := by simp only [map_inv]
  have hyδ : y⁻¹ * δ⁻¹ * y * δ = (k : W) := hinj (by
    calc φ (y⁻¹ * δ⁻¹ * y * δ)
        = φ (y⁻¹) * φ (δ⁻¹) * φ y * φ δ := by simp only [map_mul]
      _ = φ (k : W) := hkφ.symm)
  rw [hyδ]
  exact k.2

end K3

end CFSG.StandardType
