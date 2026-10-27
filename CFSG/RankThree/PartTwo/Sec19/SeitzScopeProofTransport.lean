module

public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofDefs
public import CFSG.Adapters.TauCetiExceptional.EvenD4
import CFSG.Assembly.OrderReductions.LinearOrders
import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverThreeAut
public import CFSG.RankThree.PartTwo.Sec19.Step1914TriSeitz434
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

namespace SeitzScopeProof

open TauCeti CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen
open CFSG.LieType.SeitzGeneration CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

theorem closure_fixSet_of_lThreePi (hS : SeitzThreeLThreePi) {X : Type} [Group X] {p f : ℕ}
    [Fact p.Prime] (hf : 1 ≤ f) (h2 : 2 < p ^ f) (hiso : Sec4.IsoLThreePi X p f)
    (h4 : ¬ (p = 2 ∧ f = 2)) (F : Subgroup (MulAut X)) (hF : CFSG.Open.IsElemAbelian 3 F)
    (hF9 : Nat.card F = 9) : Subgroup.closure (fixSet F) = ⊤ := by
  have hp : p.Prime := Fact.out
  have hp3 : p ≠ 3 := by
    rintro rfl
    rcases hiso with ⟨h, -⟩ | ⟨h, -⟩
    · have : (3 : ℕ) ^ f % 3 = 0 := by
        rw [Nat.pow_mod]
        simp [Nat.zero_pow (by omega : 0 < f)]
      omega
    · have : (3 : ℕ) ^ f % 3 = 0 := by
        rw [Nat.pow_mod]
        simp [Nat.zero_pow (by omega : 0 < f)]
      omega
  set q : PrimePower := ⟨p, f, hp, by omega⟩ with hqdef
  rcases hiso with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  ·
    have hv : (LieTypeIndex.A 2 q).Valid := by
      rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
        LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [hqdef, PrimePower.card_def]
      simp
      omega
    refine closure_fixSet_eq_top_of_seitzPlanes hS (d := ⟨.A 2 q, hv⟩) ?_ ?_
      (φ.trans ((Sec4.projSLEquivPSLn 3 _).trans
        (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).symm)) F hF hF9
      ⟨rfl, q, Or.inl rfl⟩
    · change 3 ≠ (LieTypeIndex.A 2 q).characteristic
      rw [LieTypeIndex.characteristic_A]
      exact hp3.symm
    · simp only [IsD2SeitzException, hqdef]
      simp
      intro h1 h2
      exact h4 ⟨h1, h2⟩
  ·
    have hv : (LieTypeIndex.twistedA 2 q).Valid := by
      rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
        LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [hqdef, PrimePower.card_def]
      simp
      omega
    refine closure_fixSet_eq_top_of_seitzPlanes hS (d := ⟨.twistedA 2 q, hv⟩) ?_ ?_
      (φ.trans ((Sec4.projSUEquivStatedProj 3 p f).trans
        (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv).symm)) F hF hF9
      ⟨rfl, q, Or.inr rfl⟩
    · change 3 ≠ (LieTypeIndex.twistedA 2 q).characteristic
      rw [LieTypeIndex.characteristic_twistedA]
      exact hp3.symm
    · simp [IsD2SeitzException]

theorem closure_fixSet_of_trialityD4_scope
    (hS : SeitzThreeTriality) {X : Type} [Group X] {p f : ℕ} (hp3 : p ≠ 3)
    (hmod : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 p f)
    (D : Subgroup (MulAut X)) (hD : CFSG.Open.IsElemAbelian 3 D) (hD9 : Nat.card D = 9) :
    Subgroup.closure (fixSet D) = ⊤ := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, σ, hσ, ⟨ι⟩⟩ := hmod
  set q : PrimePower := ⟨p, f, hp, by omega⟩ with hqdef
  have hv : (LieTypeIndex.trialityD4 q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    simp
  have hK' : Nat.card K = q.card ^ CFSG.Blueprint.Chevalley.TwistTag.D4.order := by
    rw [hK, PrimePower.card_def]
  have hσ' : ∀ x, σ x = x ^ q.card := fun x => by rw [hσ, PrimePower.card_def]
  obtain ⟨e⟩ : Nonempty (CFSG.Blueprint.DerivedCentralQuotient
      (CFSG.Blueprint.twistedFixedGroup .D4 K σ) ≃*
        ValidLieTypeIndex.Group ⟨LieTypeIndex.trialityD4 q, hv⟩) := by
    by_cases hp2 : p = 2
    · exact CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv hp2 K hK' σ hσ'
    · exact CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv hp2 K hK' σ hσ'
  refine closure_fixSet_eq_top_of_seitzPlanes hS (d := ⟨.trialityD4 q, hv⟩) ?_ ?_ (ι.trans e) D
    hD hD9 ⟨rfl, q, rfl⟩
  · change 3 ≠ (LieTypeIndex.trialityD4 q).characteristic
    rw [LieTypeIndex.characteristic_trialityD4]
    exact hp3.symm
  · simp [IsD2SeitzException]

theorem kGenTwoMod_and_card_center_sl_scope (hS : SeitzThreeLThreePi) {X : Type} [Group X]
    (hX : CFSG.IsQuasisimple X) {q : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = q)
    (hq : q % 3 = 1) (hq4 : q ≠ 4) (ι : X ≃* StatedSL 3 K) :
    CFSG.AGLEmbedding.KGenTwoMod 3 X ∧ Nat.card (Subgroup.center X) = 3 := by
  have := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' K
  rw [← Nat.card_eq_fintype_card, hK] at hcard
  have : Fact p.Prime := ⟨hp⟩
  have hn : 0 < (n : ℕ) := n.pos
  set qq : PrimePower := ⟨p, n, hp, hn⟩ with hqq
  set ψ : X ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
    ι.trans (specialLinearGroupEquivStatedSL 3 K).symm with hψ
  have hv : (LieTypeIndex.A 2 qq).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [hqq, PrimePower.card_def]
    simp
    omega
  have eZ : X ⧸ Subgroup.center X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K :=
    QuotientGroup.congr _ _ ψ (CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv ψ)
  have eT : X ⧸ Subgroup.center X ≃* (CFSGIndex.lie ⟨.A 2 qq, hv⟩).Group :=
    eZ.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).trans
      ((CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 3 p n hn
        (by rw [hK, hcard])).trans
        (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 qq hv).symm))
  have hp3 : p ≠ 3 := by
    rintro rfl
    rw [hcard] at hq
    obtain ⟨m, hm⟩ : ∃ m, (n : ℕ) = m + 1 := ⟨n - 1, by omega⟩
    rw [hm, pow_succ, Nat.mul_mod_left] at hq
    omega
  refine ⟨CFSG.AGLEmbedding.KFactProofs.CoverThree.kGenTwoMod_of_seitz hX.1 eT
    fun E' hE' hc => hS ⟨.A 2 qq, hv⟩ 3 Nat.prime_three (by norm_num) ?_ ?_ E' hE' hc
      ⟨rfl, qq, Or.inl rfl⟩, ?_⟩
  · change 3 ≠ (LieTypeIndex.A 2 qq).characteristic
    rw [LieTypeIndex.characteristic_A]
    exact hp3.symm
  · simp only [IsD2SeitzException, hqq]
    simp
    intro h1 h2
    apply hq4
    rw [hcard, h1, h2]
    norm_num
  · rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective,
      CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv ψ,
      CFSG.OrderReductions.LinearOrders.card_specialLinear_center K 3 (by norm_num), hK]
    have h3 : 3 ∣ q - 1 := by omega
    exact Nat.gcd_eq_left h3

theorem kGenTwoMod_and_card_center_su_scope (hS : SeitzThreeLThreePi) {X : Type} [Group X]
    (hX : CFSG.IsQuasisimple X) {p f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData p f K)
    (hq : p ^ f % 3 = 2) (hq2 : 2 < p ^ f)
    (ι : X ≃* CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3) :
    CFSG.AGLEmbedding.KGenTwoMod 3 X ∧ Nat.card (Subgroup.center X) = 3 := by
  have hp : p.Prime := hU.prime
  have : Fact p.Prime := ⟨hp⟩
  have := hU.finite
  have hf : 0 < f := by have := hU.one_le; omega
  set qq : PrimePower := ⟨p, f, hp, hf⟩ with hqq
  have hv : (LieTypeIndex.twistedA 2 qq).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [hqq, PrimePower.card_def]
    simp
    omega
  set L := GaloisField p (2 * f) with hL
  have := Fintype.ofFinite K
  have : Fintype L := Fintype.ofFinite L
  have hcardL : Fintype.card K = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hU.card,
      GaloisField.card p (2 * f) (by omega)]
  set φ : K ≃+* L := FiniteField.ringEquivOfCardEq hcardL with hφ
  have eZ : X ⧸ Subgroup.center X ≃* CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3 ⧸
      Subgroup.center (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3) :=
    QuotientGroup.congr _ _ ι (CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv ι)
  have e3 : StatedProj (StatedSU 3 (p ^ f) K) ≃* StatedProj (StatedSU 3 (p ^ f) L) :=
    CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ 3 (p ^ f))
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  have eT : X ⧸ Subgroup.center X ≃* (CFSGIndex.lie ⟨.twistedA 2 qq, hv⟩).Group :=
    eZ.trans ((KFacts.suCenterEquiv hU hq2).trans
      ((CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by norm_num)).trans
        (e3.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 qq hv).symm)))
  have hp3 : p ≠ 3 := by
    rintro rfl
    obtain ⟨m, hm⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    rw [hm, pow_succ, Nat.mul_mod_left] at hq
    omega
  refine ⟨CFSG.AGLEmbedding.KFactProofs.CoverThree.kGenTwoMod_of_seitz hX.1 eT
    fun E' hE' hc => hS ⟨.twistedA 2 qq, hv⟩ 3 Nat.prime_three (by norm_num) ?_
      (by simp [IsD2SeitzException]) E' hE' hc ⟨rfl, qq, Or.inr rfl⟩, ?_⟩
  · change 3 ≠ (LieTypeIndex.twistedA 2 qq).characteristic
    rw [LieTypeIndex.characteristic_twistedA]
    exact hp3.symm
  · rw [← Subgroup.card_map_of_injective (f := ι.toMonoidHom) ι.injective,
      CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv ι,
      KFacts.center_unitarySU_three (h := hU) hq2,
      CFSG.ClassicalGroups.UnitaryFlag.card_unitaryScalars hU (by norm_num)]
    have h3 : 3 ∣ p ^ f + 1 := by omega
    exact Nat.gcd_eq_left h3

end SeitzScopeProof

open SeitzScopeProof in
theorem seitzL3PiGap_of_seitzThree (hS : SeitzThreeLThreePi) : SeitzL3PiGap := by
  intro X _ _ p e _ he hiso hgap F hF hF9
  have hp : p.Prime := Fact.out
  have hpe8 : 8 ≤ p ^ e := by
    rcases hgap with ⟨h1, h2⟩ | ⟨rfl, rfl | rfl⟩
    · calc 8 ≤ 4 ^ 3 := by norm_num
        _ ≤ p ^ 3 := Nat.pow_le_pow_left h1 3
        _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos h2
    · norm_num
    · norm_num
  have h4 : ¬ (p = 2 ∧ e = 2) := by
    rintro ⟨rfl, rfl⟩
    rcases hgap with ⟨h, -⟩ | ⟨-, h | h⟩ <;> omega
  exact closure_fixSet_of_lThreePi hS he (by omega) hiso h4 F ⟨hF.1, hF.2⟩ hF9

end CFSG.RankThree.PartTwo.Sec19
