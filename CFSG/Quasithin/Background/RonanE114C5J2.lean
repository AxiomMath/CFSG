module

public import CFSG.Quasithin.Background.RonanE114C5Gen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2Model
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
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTwist
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperCommutingImages
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

namespace CFSG.Quasithin.RonanE114.C5.J2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.Quasithin.A312J2 CFSG.Sporadic.J2

section Lattice


theorem member_or_top {Z : Subgroup ↥J} (hZ : j2CtxA.S ≤ Z) :
    (∃ j < 5, Z = j2CtxA.Y j) ∨ Z = ⊤ := by
  obtain ⟨j, hj, hZeq⟩ := j2CtxA.complete Z hZ
  rw [j2A_J] at hj hZeq
  by_cases h : j < 5
  · left
    exact ⟨j, h, by rw [hZeq]; simp [memberOrTop, h]⟩
  · right
    rw [hZeq]
    simp [memberOrTop, h]

theorem card_top : Nat.card (⊤ : Subgroup ↥J) = 2 ^ 7 * 4725 := by
  rw [Subgroup.card_top, card_J]
  norm_num

def j2Idx (j : ℕ) : ℕ := #[1, 3, 9, 15, 3][j]!

theorem card_Y {j : ℕ} (hj : j < 5) : Nat.card (j2CtxA.Y j) = j2Idx j * 2 ^ 7 :=
  j2A_card hj

theorem unique_Y2 : ∀ Z : Subgroup ↥J, j2CtxA.S ≤ Z →
    Nat.card Z = Nat.card (j2CtxA.Y 2) → Z = j2CtxA.Y 2 := by
  intro Z hZ hc
  rcases member_or_top hZ with ⟨j, hj, rfl⟩ | rfl
  · rw [card_Y hj, card_Y (by norm_num)] at hc
    have hidx : j2Idx j = j2Idx 2 := by omega
    have key : ∀ j < 5, j2Idx j = j2Idx 2 → j = 2 := by decide
    rw [key j hj hidx]
  · exfalso
    rw [card_top, card_Y (by norm_num)] at hc
    have : j2Idx 2 = 9 := rfl
    omega

theorem unique_Y3 : ∀ Z : Subgroup ↥J, j2CtxA.S ≤ Z →
    Nat.card Z = Nat.card (j2CtxA.Y 3) → Z = j2CtxA.Y 3 := by
  intro Z hZ hc
  rcases member_or_top hZ with ⟨j, hj, rfl⟩ | rfl
  · rw [card_Y hj, card_Y (by norm_num)] at hc
    have hidx : j2Idx j = j2Idx 3 := by omega
    have key : ∀ j < 5, j2Idx j = j2Idx 3 → j = 3 := by decide
    rw [key j hj hidx]
  · exfalso
    rw [card_top, card_Y (by norm_num)] at hc
    have : j2Idx 3 = 15 := rfl
    omega

theorem sup_Y2_Y3 : j2CtxA.Y 2 ⊔ j2CtxA.Y 3 = ⊤ := by
  have hS : j2CtxA.S ≤ j2CtxA.Y 2 ⊔ j2CtxA.Y 3 := le_sup_of_le_left (j2CtxA.S_le_Y 2)
  rcases member_or_top hS with ⟨j, hj, hjeq⟩ | htop
  · exfalso
    have h1 : Nat.card (j2CtxA.Y 2) ∣ Nat.card (j2CtxA.Y j) :=
      Subgroup.card_dvd_of_le (hjeq ▸ le_sup_left)
    have h2 : Nat.card (j2CtxA.Y 3) ∣ Nat.card (j2CtxA.Y j) :=
      Subgroup.card_dvd_of_le (hjeq ▸ le_sup_right)
    rw [card_Y (by norm_num), card_Y hj] at h1 h2
    have hd1 : j2Idx 2 ∣ j2Idx j := Nat.dvd_of_mul_dvd_mul_right (by positivity) h1
    have hd2 : j2Idx 3 ∣ j2Idx j := Nat.dvd_of_mul_dvd_mul_right (by positivity) h2
    have key : ∀ j < 5, j2Idx 2 ∣ j2Idx j → j2Idx 3 ∣ j2Idx j → False := by decide
    exact key j hj hd1 hd2
  · exact htop

theorem card_Y2 : Nat.card (j2CtxA.Y 2) = 2 ^ 7 * 3 ^ 2 := by
  rw [card_Y (by norm_num)]
  rfl

theorem Y2_solvable : Group.IsSolvable ↥(j2CtxA.Y 2) :=
  A312Ru.isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 7) (b := 2)
    card_Y2

end Lattice

section Levi


theorem Y3_levi5 : ∃ ρ : ↥(j2CtxA.Y 3) →* Equiv.Perm (Fin 5),
    IsPGroup 2 ρ.ker ∧ alternatingGroup (Fin 5) ≤ ρ.range := by
  obtain ⟨V, hV, ⟨-, hcardV⟩, ⟨e⟩⟩ := (j2_Y3_ext).1
  have hV2 : IsPGroup 2 ↥V := IsPGroup.of_card (n := 1 + 2 * 2) hcardV
  exact levi5_of_quotient hV2 e

end Levi

section Main


theorem nParam_le_two_of_isJ2
    {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hJ2 : IsSporadic .J2 (ASInputs.FStar G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : E1.nParam (⊤ : Subgroup G) ≤ ((2 : ℕ) : ℕ∞) := by
  have hTs : IsSylowTwoOf T ⊤ := ⟨le_top, hT.1, by
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hT.2⟩
  have hLn : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  obtain ⟨e₀⟩ := hJ2
  exact nParam_le_two_of_goodPair (U := j2CtxA.S) j2A_sylow sup_Y2_Y3
    (fun 𝒜 h => ⟨goodGam_solvable_of_unique (j2CtxA.S_le_Y 2) unique_Y2 Y2_solvable 𝒜 h,
      goodGam_levi5_of_unique (j2CtxA.S_le_Y 3) unique_Y3 Y3_levi5 𝒜 h⟩) hLn
    (e₀.trans nativeEquiv) hTs hFT

end Main

end CFSG.Quasithin.RonanE114.C5.J2
