module

public import CFSG.LocalAnalysis.StandardType.GGLieLayerBridge
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.LocalAnalysis.StandardType.GGLayerCycMRestTwo
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.Adapters.TauCetiExceptional.ReeModel
public import CFSG.Adapters.ExceptionalCatalogReverse
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType

public section

namespace CFSG.StandardType.LieLayer

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.Yardstones.Md42047359a2a

set_option linter.unusedSectionVars false


theorem ggLayerLieTwo_recipe_untw (hres : ExcRationalLieTypes) (hout : TrialityOuterExport)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) {n : ℕ} (hn : 1 ≤ n)
    (hv : (c ⟨2, n, Nat.prime_two, hn⟩).Valid)
    (hc : lieIndexChar (c ⟨2, n, Nat.prime_two, hn⟩) = 2)
    (hF : lieFamily (c ⟨2, n, Nat.prime_two, hn⟩) = .exceptional) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ n)
    (φ : MulAut (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))) :
    LayerCycM.GGLayerLieTwo p φ := by
  obtain ⟨e₁⟩ := centerQuot_chevGroup_equiv K τ
  obtain ⟨e₂⟩ := hB ⟨2, n, Nat.prime_two, hn⟩ hv K (by rw [PrimePower.card_def]; exact hK)
  exact ggLayerLieTwo_of_catEquiv hres hout hp hp2 ⟨_, hv⟩ hc (Or.inl hF) (e₁.trans e₂) φ

theorem ggLayerLieTwo_recipe_tw (hres : ExcRationalLieTypes) (hout : TrialityOuterExport)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : TwistTag} {c : PrimePower → LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.TwistedBridgeAll t c) {n : ℕ} (hn : 1 ≤ n)
    (hv : (c ⟨2, n, Nat.prime_two, hn⟩).Valid)
    (hc : lieIndexChar (c ⟨2, n, Nat.prime_two, hn⟩) = 2)
    (hF : lieFamily (c ⟨2, n, Nat.prime_two, hn⟩) = .exceptional) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ t.order)
    (φ : MulAut (LargeEvenCenterQuot (LargeEvenTwistedH t.tag.cartan K t.perm n))) :
    LayerCycM.GGLayerLieTwo p φ := by
  haveI : CharP K 2 :=
    CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow (f := n * t.order) (by rw [hK, pow_mul])
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ : K →+* K := iterateFrobenius K 2 n
  have hσ : ∀ x : K, σ x = x ^ 2 ^ n := fun _ => rfl
  obtain ⟨e₁⟩ := centerQuot_twistedH_equiv K t n σ hσ
  obtain ⟨e₂⟩ := hB ⟨2, n, Nat.prime_two, hn⟩ hv K (by rw [PrimePower.card_def]; exact hK) σ
    (fun x => by rw [PrimePower.card_def]; exact hσ x)
  exact ggLayerLieTwo_of_catEquiv hres hout hp hp2 ⟨_, hv⟩ hc (Or.inl hF) (e₁.trans e₂) φ

theorem ggLayerLieTwo_recipe_twF4 (hres : ExcRationalLieTypes) (hout : TrialityOuterExport)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (φ : MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K))) :
    LayerCycM.GGLayerLieTwo p φ := by
  haveI : CharP K 2 := CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow hK
  have hv : (LieTypeIndex.reeF4 a).Valid := reeF4_valid ha
  obtain ⟨e₁⟩ := centerQuot_twF4H_equiv K a
  have hhalf : (ReeF4LieIndex.of a hv).toSuzukiReeIndex.halfExponent = a :=
    SuzukiReeIndex.halfExponent_reeF4 a hv
  have hcard :
      Nat.card K = 2 ^ (2 * (ReeF4LieIndex.of a hv).toSuzukiReeIndex.halfExponent + 1) := by
    rw [hhalf, hK]
  obtain ⟨e₂⟩ := CFSG.TauCetiBridge.reeF4_candidate_equiv_of_card (ReeF4LieIndex.of a hv) hcard
  rw [hhalf] at e₂
  exact ggLayerLieTwo_of_catEquiv hres hout hp hp2 ⟨.reeF4 a, hv⟩ rfl (Or.inr ⟨a, rfl⟩)
    (e₁.trans ((CFSG.TauCetiBridge.ReeF4.nativeModelEquiv a).trans e₂.symm)) φ

theorem ggLieLayerInput_holds : GGLieLayerInput := by
  intro p lab hp hp2 hlab _ hS Q hQ
  have hres : ExcRationalLieTypes :=
    excRationalLieTypes_of_residualsD excRationalLieTypesOuterD_proved
      excRationalLieTypesF4Two_holds
  have hout : TrialityOuterExport := trialityOuterExport_of (trialityOddA2Comps_of_toral
      TriA2.a2PlusComps_holds TriA2.a2MinusComps_holds)
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hrest⟩ := hlab
  simp only [GGLieLayerLabel] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    obtain ⟨-, hn2⟩ := hrest
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    refine ⟨K, i1, i2, hK, hq, fun φ _ => ?_⟩
    have h3 : 3 ≤ (⟨2, n, Nat.prime_two, hn⟩ : PrimePower).card := by
      rw [PrimePower.card_def]
      show 3 ≤ 2 ^ n
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have hv : (LieTypeIndex.G2 ⟨2, n, Nat.prime_two, hn⟩).Valid := by
      rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
        LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨h3, by simp⟩
    exact ggLayerLieTwo_recipe_untw hres hout hp hp2 (τ := .G2) (c := LieTypeIndex.G2)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 hn hv rfl rfl K hK φ
  ·
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    refine ⟨K, i1, i2, hK, hq, fun φ _ => ?_⟩
    exact ggLayerLieTwo_recipe_untw hres hout hp hp2 (τ := .F4) (c := LieTypeIndex.F4)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 hn (by simp) rfl rfl K hK φ
  ·
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    refine ⟨K, i1, i2, hK, hq, fun φ _ => ?_⟩
    exact ggLayerLieTwo_recipe_untw hres hout hp hp2 (τ := .E6) (c := LieTypeIndex.E6)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 hn (LieTypeIndex.valid_E6 _) rfl rfl K hK φ
  ·
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    refine ⟨K, i1, i2, hK, hq, fun φ _ => ?_⟩
    exact ggLayerLieTwo_recipe_untw hres hout hp hp2 (τ := .E7) (c := LieTypeIndex.E7)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 hn (LieTypeIndex.valid_E7 _) rfl rfl K hK φ
  ·
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    refine ⟨K, i1, i2, hK, hq, fun φ _ => ?_⟩
    exact ggLayerLieTwo_recipe_untw hres hout hp hp2 (τ := .E8) (c := LieTypeIndex.E8)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 hn (by simp) rfl rfl K hK φ
  ·
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    refine ⟨K, i1, i2, hK, hq, fun φ _ => ?_⟩
    exact ggLayerLieTwo_recipe_tw hres hout hp hp2 (t := .E6) (c := LieTypeIndex.twistedE6)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 hn (LieTypeIndex.valid_twistedE6 _)
      rfl rfl K hK φ
  ·
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    refine ⟨K, i1, i2, hK, hq, fun φ _ => ?_⟩
    exact ggLayerLieTwo_recipe_tw hres hout hp hp2 (t := .D4) (c := LieTypeIndex.trialityD4)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 hn
      (LieTypeIndex.valid_trialityD4 _) rfl rfl K hK φ
  ·
    obtain ⟨-, -, hn3⟩ := hrest
    have hn3' : 3 ≤ n := hn3
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    refine ⟨K, i1, i2, hK, hq, fun φ _ => ?_⟩
    exact ggLayerLieTwo_recipe_twF4 hres hout hp hp2 (a := (n - 1) / 2) (by omega) K hK φ

end CFSG.StandardType.LieLayer

end
