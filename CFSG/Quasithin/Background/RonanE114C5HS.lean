module

public import CFSG.Quasithin.Background.RonanE114C5Gen
public import CFSG.Quasithin.Background.A312SporHS
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
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

namespace CFSG.Quasithin.RonanE114.C5.HS

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.Ch1.SporLat.HS CFSG.Quasithin.A312S CFSG.Sporadic.HS.Native
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2

section Lattice

theorem member_or_top {Z : Subgroup (J hsData)} (hZ : hsCtx.S ≤ Z) :
    (∃ j < 5, Z = hsCtx.Y j) ∨ Z = ⊤ := by
  obtain ⟨j, hj, hZeq⟩ := hs_complete Z hZ
  by_cases h : j < 5
  · left
    exact ⟨j, h, by rw [hZeq]; simp [memberOrTop, h]⟩
  · right
    rw [hZeq]
    simp [memberOrTop, h]

theorem card_top : Nat.card (⊤ : Subgroup (J hsData)) = 2 ^ 9 * 86625 := by
  rw [Subgroup.card_top]
  exact hs_card

def hsIdx (j : ℕ) : ℕ := #[1, 15, 21, 3, 3][j]!

theorem card_Y {j : ℕ} (hj : j < 5) : Nat.card (hsCtx.Y j) = hsIdx j * 2 ^ 9 := by
  rw [hs_member_card j hj]
  rfl

theorem unique_Y1 : ∀ Z : Subgroup (J hsData), hsCtx.S ≤ Z →
    Nat.card Z = Nat.card (hsCtx.Y 1) → Z = hsCtx.Y 1 := by
  intro Z hZ hc
  rcases member_or_top hZ with ⟨j, hj, rfl⟩ | rfl
  · rw [card_Y hj, card_Y (by norm_num)] at hc
    have hidx : hsIdx j = hsIdx 1 := by omega
    have key : ∀ j < 5, hsIdx j = hsIdx 1 → j = 1 := by decide
    rw [key j hj hidx]
  · exfalso
    rw [card_top, card_Y (by norm_num)] at hc
    have : hsIdx 1 = 15 := rfl
    omega

theorem unique_Y2 : ∀ Z : Subgroup (J hsData), hsCtx.S ≤ Z →
    Nat.card Z = Nat.card (hsCtx.Y 2) → Z = hsCtx.Y 2 := by
  intro Z hZ hc
  rcases member_or_top hZ with ⟨j, hj, rfl⟩ | rfl
  · rw [card_Y hj, card_Y (by norm_num)] at hc
    have hidx : hsIdx j = hsIdx 2 := by omega
    have key : ∀ j < 5, hsIdx j = hsIdx 2 → j = 2 := by decide
    rw [key j hj hidx]
  · exfalso
    rw [card_top, card_Y (by norm_num)] at hc
    have : hsIdx 2 = 21 := rfl
    omega

theorem sup_Y1_Y2 : hsCtx.Y 1 ⊔ hsCtx.Y 2 = ⊤ := by
  have hS : hsCtx.S ≤ hsCtx.Y 1 ⊔ hsCtx.Y 2 := le_sup_of_le_left (hsCtx.S_le_Y 1)
  rcases member_or_top hS with ⟨j, hj, hjeq⟩ | htop
  · exfalso
    have h1 : Nat.card (hsCtx.Y 1) ∣ Nat.card (hsCtx.Y j) :=
      Subgroup.card_dvd_of_le (hjeq ▸ le_sup_left)
    have h2 : Nat.card (hsCtx.Y 2) ∣ Nat.card (hsCtx.Y j) :=
      Subgroup.card_dvd_of_le (hjeq ▸ le_sup_right)
    rw [card_Y (by norm_num), card_Y hj] at h1 h2
    have hd1 : hsIdx 1 ∣ hsIdx j := Nat.dvd_of_mul_dvd_mul_right (by positivity) h1
    have hd2 : hsIdx 2 ∣ hsIdx j := Nat.dvd_of_mul_dvd_mul_right (by positivity) h2
    have key : ∀ j < 5, hsIdx 1 ∣ hsIdx j → hsIdx 2 ∣ hsIdx j → False := by decide
    exact key j hj hd1 hd2
  · exact htop

theorem card_Y1 : Nat.card (hsCtx.Y 1) = 2 ^ 9 * 3 * 5 := by
  rw [card_Y (by norm_num)]
  rfl

theorem card_Y4 : Nat.card (hsCtx.Y 4) = 2 ^ 9 * 3 := by
  rw [card_Y (by norm_num)]
  rfl

theorem no_order {H : Subgroup (J hsData)} (hSH : hsCtx.S ≤ H) {p : ℕ} (hp : p = 5 ∨ p = 7)
    (hc : Nat.card H = 2 ^ 9 * p) : False := by
  rcases member_or_top hSH with ⟨j, hj, rfl⟩ | rfl
  · rw [card_Y hj] at hc
    have key : ∀ j < 5, ∀ p, (p = 5 ∨ p = 7) → hsIdx j * 2 ^ 9 ≠ 2 ^ 9 * p := by
      intro j hj p hp
      rcases hp with rfl | rfl <;> revert j <;> decide
    exact key j hj p hp hc
  · rw [card_top] at hc
    rcases hp with rfl | rfl <;> omega

theorem Y1_not_solvable : ¬ Group.IsSolvable ↥(hsCtx.Y 1) :=
  not_isSolvable_of_no_overgroup (hsCtx.S_le_Y 1) hsCtx.S_isPGroup (e := 9) (m := 3) (p := 5)
    (by norm_num) card_Y1 (by norm_num) (by norm_num) fun H hSH _ hc =>
    no_order hSH (p := 5) (Or.inl rfl) hc

end Lattice

section Levi

theorem Y4_le_Y1 : hsCtx.Y 4 ≤ hsCtx.Y 1 :=
  (hs_incl (by norm_num) (by norm_num)).mpr (by decide)

theorem Y1_levi5 : ∃ ρ : ↥(hsCtx.Y 1) →* Equiv.Perm (Fin 5),
    IsPGroup 2 ρ.ker ∧ alternatingGroup (Fin 5) ≤ ρ.range := by
  have hcard' : Nat.card ((hsCtx.Y 4).subgroupOf (hsCtx.Y 1)) = 2 ^ 9 * 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Y4_le_Y1).toEquiv]
    exact card_Y4
  exact levi5_of_index_five Y1_not_solvable (e := 9) card_Y1 hcard'

theorem Y2_levi3 : ∃ f : ↥(hsCtx.Y 2) →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
    Function.Surjective f ∧ IsPGroup 2 f.ker := by
  refine ⟨hsPsi, hsPsi_surjective, ?_⟩
  exact IsPGroup.of_card (n := 6) hsPsi_ker_card

end Levi

section Main

theorem nParam_le_two_of_isHS
    {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hHS : IsSporadic .HS (ASInputs.FStar G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : E1.nParam (⊤ : Subgroup G) ≤ ((2 : ℕ) : ℕ∞) := by
  have hTs : IsSylowTwoOf T ⊤ := ⟨le_top, hT.1, by
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hT.2⟩
  have hLn : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  obtain ⟨e₀⟩ := hHS
  exact nParam_le_two_of_goodPair (U := hsCtx.S) hs_S_sylow sup_Y1_Y2
    (fun 𝒜 h => ⟨goodGam_levi5_of_unique (hsCtx.S_le_Y 1) unique_Y1 Y1_levi5 𝒜 h,
      goodGam_levi3_of_unique (hsCtx.S_le_Y 2) unique_Y2 Y2_levi3 𝒜 h⟩) hLn
    (e₀.trans (seedEquiv hs_facts.toBaseFacts)) hTs hFT

end Main

end CFSG.Quasithin.RonanE114.C5.HS
