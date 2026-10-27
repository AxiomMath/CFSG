module

public import CFSG.Quasithin.Background.RonanE114C5Gen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuMain
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import CFSG.Goldschmidt.StatementsG2
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteCore
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTwist
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperCommutingImages
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallerRecognitionDischarge
public import CFSG.Quasithin.Background.RonanE114ClausesL52He
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParMain
public import CFSG.Quasithin.EmptyFaithful.SzN15Good
public import CFSG.Quasithin.H13.QRCBenderAmbient
public import CFSG.Quasithin.H13.QRCBenderPairModel
public import CFSG.Quasithin.SteinbergCCPrimeWitness
public import CFSG.Quasithin.Vol2.Ch3E213MP6BC
public import CFSG.Quasithin.Vol2.Ch3E213MP6BD

public section

namespace CFSG.Quasithin.RonanE114.C5.Ru

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.Ch1.SporLat.Ru CFSG.QuasithinUnique.Ch1.SporLat.RuCert
  CFSG.Quasithin.A312Ru CFSG.Sporadic.Ru.Native CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2

section Lattice


theorem member_or_top {Z : Subgroup (J ruData)} (hZ : ruCtx.S ≤ Z) :
    (∃ j < 5, Z = ruCtx.Y j) ∨ Z = ⊤ := by
  obtain ⟨j, hj, hZeq⟩ := ru_complete Z hZ
  by_cases h : j < 5
  · left
    exact ⟨j, h, by rw [hZeq]; simp [memberOrTop, h]⟩
  · right
    rw [hZeq]
    simp [memberOrTop, h]

theorem card_top : Nat.card (⊤ : Subgroup (J ruData)) = 2 ^ 14 * 8906625 := by
  rw [Subgroup.card_top]
  exact ru_card

def ruIdx (j : ℕ) : ℕ := #[1, 15, 21, 3, 3][j]!

theorem card_Y {j : ℕ} (hj : j < 5) : Nat.card (ruCtx.Y j) = ruIdx j * 2 ^ 14 :=
  ru_member_card j hj

theorem unique_Y1 : ∀ Z : Subgroup (J ruData), ruCtx.S ≤ Z →
    Nat.card Z = Nat.card (ruCtx.Y 1) → Z = ruCtx.Y 1 := by
  intro Z hZ hc
  rcases member_or_top hZ with ⟨j, hj, rfl⟩ | rfl
  · rw [card_Y hj, card_Y (by norm_num)] at hc
    have hidx : ruIdx j = ruIdx 1 := by omega
    have key : ∀ j < 5, ruIdx j = ruIdx 1 → j = 1 := by decide
    rw [key j hj hidx]
  · exfalso
    rw [card_top, card_Y (by norm_num)] at hc
    have : ruIdx 1 = 15 := rfl
    omega

theorem unique_Y2 : ∀ Z : Subgroup (J ruData), ruCtx.S ≤ Z →
    Nat.card Z = Nat.card (ruCtx.Y 2) → Z = ruCtx.Y 2 := by
  intro Z hZ hc
  rcases member_or_top hZ with ⟨j, hj, rfl⟩ | rfl
  · rw [card_Y hj, card_Y (by norm_num)] at hc
    have hidx : ruIdx j = ruIdx 2 := by omega
    have key : ∀ j < 5, ruIdx j = ruIdx 2 → j = 2 := by decide
    rw [key j hj hidx]
  · exfalso
    rw [card_top, card_Y (by norm_num)] at hc
    have : ruIdx 2 = 21 := rfl
    omega

theorem sup_Y1_Y2 : ruCtx.Y 1 ⊔ ruCtx.Y 2 = ⊤ := by
  have hS : ruCtx.S ≤ ruCtx.Y 1 ⊔ ruCtx.Y 2 := le_sup_of_le_left (ruCtx.S_le_Y 1)
  rcases member_or_top hS with ⟨j, hj, hjeq⟩ | htop
  · exfalso
    have h1 : ruCtx.Y 1 ≤ ruCtx.Y j := hjeq ▸ le_sup_left
    have h2 : ruCtx.Y 2 ≤ ruCtx.Y j := hjeq ▸ le_sup_right
    have key : ∀ j < 5, j ∈ ruIncl[1]! → j ∈ ruIncl[2]! → False := by decide
    exact key j hj ((ru_Y_le_iff (by norm_num) hj).mp h1) ((ru_Y_le_iff (by norm_num) hj).mp h2)
  · exact htop

theorem card_Y1 : Nat.card (ruCtx.Y 1) = 2 ^ 14 * 3 * 5 := by
  rw [card_Y (by norm_num)]
  rfl

theorem card_Y2 : Nat.card (ruCtx.Y 2) = 2 ^ 14 * 3 * 7 := by
  rw [card_Y (by norm_num)]
  rfl

theorem card_Y3 : Nat.card (ruCtx.Y 3) = 2 ^ 14 * 3 := by
  rw [card_Y (by norm_num)]
  rfl

theorem Y3_le_Y1 : ruCtx.Y 3 ≤ ruCtx.Y 1 :=
  (ru_Y_le_iff (by norm_num) (by norm_num)).mpr (by decide)

theorem Y3_le_Y2 : ruCtx.Y 3 ≤ ruCtx.Y 2 :=
  (ru_Y_le_iff (by norm_num) (by norm_num)).mpr (by decide)

theorem no_order {H : Subgroup (J ruData)} (hSH : ruCtx.S ≤ H) {p : ℕ} (hp : p = 5 ∨ p = 7)
    (hc : Nat.card H = 2 ^ 14 * p) : False := by
  rcases member_or_top hSH with ⟨j, hj, rfl⟩ | rfl
  · rw [card_Y hj] at hc
    have key : ∀ j < 5, ∀ p, (p = 5 ∨ p = 7) → ruIdx j * 2 ^ 14 ≠ 2 ^ 14 * p := by
      intro j hj p hp
      rcases hp with rfl | rfl <;> revert j <;> decide
    exact key j hj p hp hc
  · rw [card_top] at hc
    rcases hp with rfl | rfl <;> omega

theorem Y1_not_solvable : ¬ Group.IsSolvable ↥(ruCtx.Y 1) :=
  not_isSolvable_of_no_overgroup (ruCtx.S_le_Y 1) ruCtx.S_isPGroup (e := 14) (m := 3) (p := 5)
    (by norm_num) card_Y1 (by norm_num) (by norm_num) fun H hSH _ hc =>
    no_order hSH (p := 5) (Or.inl rfl) hc

theorem Y2_not_solvable : ¬ Group.IsSolvable ↥(ruCtx.Y 2) :=
  not_isSolvable_of_no_overgroup (ruCtx.S_le_Y 2) ruCtx.S_isPGroup (e := 14) (m := 3) (p := 7)
    (by norm_num) card_Y2 (by norm_num) (by norm_num) fun H hSH _ hc =>
    no_order hSH (p := 7) (Or.inr rfl) hc

theorem Y1_levi5 : ∃ ρ : ↥(ruCtx.Y 1) →* Equiv.Perm (Fin 5),
    IsPGroup 2 ρ.ker ∧ alternatingGroup (Fin 5) ≤ ρ.range := by
  have hcard' : Nat.card ((ruCtx.Y 3).subgroupOf (ruCtx.Y 1)) = 2 ^ 14 * 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Y3_le_Y1).toEquiv]
    exact card_Y3
  exact levi5_of_index_five Y1_not_solvable (e := 14) card_Y1 hcard'

end Lattice

section Rows


theorem Y2_levi3 : ∃ f : ↥(ruCtx.Y 2) →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
    Function.Surjective f ∧ IsPGroup 2 f.ker := by
  have hcard' : Nat.card ((ruCtx.Y 3).subgroupOf (ruCtx.Y 2)) = 2 ^ 14 * 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Y3_le_Y2).toEquiv]
    exact card_Y3
  refine levi3_of_index_seven Y2_not_solvable (e := 14) card_Y2 hcard' ?_
  rw [ru_row_two]
  norm_num

end Rows

section Main


theorem nParam_le_two_of_isRu
    {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hRu : IsSporadic .Ru (ASInputs.FStar G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : E1.nParam (⊤ : Subgroup G) ≤ ((2 : ℕ) : ℕ∞) := by
  have hTs : IsSylowTwoOf T ⊤ := ⟨le_top, hT.1, by
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hT.2⟩
  have hLn : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  obtain ⟨e₀⟩ := hRu
  exact nParam_le_two_of_goodPair (U := ruCtx.S) ru_S_sylow sup_Y1_Y2
    (fun 𝒜 h => ⟨goodGam_levi5_of_unique (ruCtx.S_le_Y 1) unique_Y1 Y1_levi5 𝒜 h,
      goodGam_levi3_of_unique (ruCtx.S_le_Y 2) unique_Y2 Y2_levi3 𝒜 h⟩) hLn
    (e₀.trans (seedEquiv ru_facts.toBaseFacts)) hTs hFT

end Main

end CFSG.Quasithin.RonanE114.C5.Ru
