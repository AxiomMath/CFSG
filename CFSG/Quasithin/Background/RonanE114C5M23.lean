module

public import CFSG.Quasithin.Background.RonanE114C5Gen
public import CFSG.Quasithin.Background.E2TwoProofSporM23
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

namespace CFSG.Quasithin.RonanE114.C5.M23

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.Quasithin.H.MathieuLat CFSG.Quasithin.E2P.SporB CFSG.Blueprint.NativeSporadic

def idx (j : ℕ) : ℕ := #[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9][j]!

section Lattice


private theorem hL : m23CtxB.D.Om.map (fun o => o.lbl.size) =
    #[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9] := m23_lat_cert.2.2

private theorem hJ : m23CtxB.J = 16 := lat_J_eq m23CtxB hL

private theorem hN : m23CtxB.D.O.lbl.size = 79695 := m23_lat_cert.2.1

theorem member_or_top {Z : Subgroup ↥M23} (hZ : m23CtxB.S ≤ Z) :
    (∃ j < 16, Z = m23CtxB.Y j) ∨ Z = ⊤ := by
  obtain ⟨j, hj, hZeq⟩ := m23CtxB.complete Z hZ
  rw [hJ] at hj hZeq
  by_cases h : j < 16
  · left
    exact ⟨j, h, by rw [hZeq]; simp [memberOrTop, h]⟩
  · right
    rw [hZeq]
    simp [memberOrTop, h]

theorem card_Y {j : ℕ} (hj : j < 16) : Nat.card (m23CtxB.Y j) = idx j * 2 ^ 7 := by
  have := lat_card m23CtxB hL j (by simpa using hj)
  exact this

theorem card_top : Nat.card (⊤ : Subgroup ↥M23) = 79695 * 2 ^ 7 := by
  rw [Subgroup.card_top, m23CtxB.hΓ, hN]
  rfl

theorem le_iff {j jj : ℕ} (hj : j < 16) (hjj : jj < 16) :
    m23CtxB.Y j ≤ m23CtxB.Y jj ↔ jj ∈ m23Incl[j]! :=
  m23_Y_le_iff hj hjj

theorem S_sylow : IsSylowTwoOf m23CtxB.S ⊤ := by
  refine K1.isSylowTwoOf_top_iff.mpr ⟨m23CtxB.S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index m23CtxB.S
  rw [m23CtxB.S_card, m23CtxB.hΓ, hN] at h1
  have h2 : m23CtxB.S.index = 79695 := by
    have : m23CtxB.k = 7 := rfl
    rw [this] at h1
    omega
  rw [h2]
  norm_num

end Lattice

section Abstract

structure Data {Γ : Type} [Group Γ] (U : Subgroup Γ) (Y : ℕ → Subgroup Γ) : Prop where
  S_le : ∀ j, U ≤ Y j
  complete : ∀ Z : Subgroup Γ, U ≤ Z → (∃ j < 16, Z = Y j) ∨ Z = ⊤
  card : ∀ j < 16, Nat.card (Y j) = idx j * 2 ^ 7
  card_top : Nat.card (⊤ : Subgroup Γ) = 79695 * 2 ^ 7
  le_iff : ∀ {j jj : ℕ}, j < 16 → jj < 16 → (Y j ≤ Y jj ↔ jj ∈ m23Incl[j]!)

variable {Γ : Type} [Group Γ] {U : Subgroup Γ} {Y : ℕ → Subgroup Γ}

theorem Data.card_eq (h : Data U Y) {j k : ℕ} (hj : j < 16) (hk : k < 16)
    (hc : Nat.card (Y j) = Nat.card (Y k)) : idx j = idx k := by
  rw [h.card j hj, h.card k hk] at hc
  exact Nat.eq_of_mul_eq_mul_right (by positivity) hc

theorem Data.unique_of_idx (h : Data U Y) {a : ℕ} (ha : a < 16)
    (hu : ∀ j < 16, idx j = idx a → j = a) (ht : idx a ≠ 79695) :
    ∀ Z : Subgroup Γ, U ≤ Z → Nat.card Z = Nat.card (Y a) → Z = Y a := by
  intro Z hZ hc
  rcases h.complete Z hZ with ⟨j, hj, rfl⟩ | rfl
  · rw [hu j hj (h.card_eq hj ha hc)]
  · exfalso
    rw [h.card_top, h.card a ha] at hc
    exact ht (Nat.eq_of_mul_eq_mul_right (by positivity) hc).symm

theorem Data.unique_below (h : Data U Y) {a q : ℕ} (ha : a < 16) (hq : q < 16)
    (hu : ∀ j < 16, q ∈ m23Incl[j]! → idx j = idx a → j = a)
    (hqt : Y q ≠ ⊤) :
    ∀ Z : Subgroup Γ, U ≤ Z → Z ≤ Y q → Nat.card Z = Nat.card (Y a) → Z = Y a := by
  intro Z hZ hZq hc
  rcases h.complete Z hZ with ⟨j, hj, rfl⟩ | rfl
  · rw [hu j hj ((h.le_iff hj hq).mp hZq) (h.card_eq hj ha hc)]
  · exact absurd (top_le_iff.mp hZq) hqt

theorem Data.ne_top (h : Data U Y) {q : ℕ} (hq : q < 16) (hne : idx q ≠ 79695) : Y q ≠ ⊤ := by
  intro ht
  have := h.card q hq
  rw [ht, h.card_top] at this
  exact hne (Nat.eq_of_mul_eq_mul_right (by positivity) this).symm

theorem Data.sup_eq (h : Data U Y) {a b c : ℕ} (ha : a < 16) (hb : b < 16) (hc : c < 16)
    (hac : c ∈ m23Incl[a]!) (hbc : c ∈ m23Incl[b]!)
    (hmin : ∀ j < 16, j ∈ m23Incl[a]! → j ∈ m23Incl[b]! → c ∈ m23Incl[j]! → j = c)
    (hct : Y c ≠ ⊤) : Y a ⊔ Y b = Y c := by
  have hle : Y a ⊔ Y b ≤ Y c := sup_le ((h.le_iff ha hc).mpr hac) ((h.le_iff hb hc).mpr hbc)
  rcases h.complete (Y a ⊔ Y b) (le_sup_of_le_left (h.S_le a)) with ⟨j, hj, hjeq⟩ | htop
  · have h1 : Y a ≤ Y j := hjeq ▸ le_sup_left
    have h2 : Y b ≤ Y j := hjeq ▸ le_sup_right
    have h3 : Y j ≤ Y c := hjeq ▸ hle
    rw [hjeq, hmin j hj ((h.le_iff ha hj).mp h1) ((h.le_iff hb hj).mp h2)
      ((h.le_iff hj hc).mp h3)]
  · exact absurd (top_le_iff.mp (htop ▸ hle)) hct

theorem Data.sup_eq_top (h : Data U Y) {a b : ℕ} (ha : a < 16) (hb : b < 16)
    (hmin : ∀ j < 16, j ∈ m23Incl[a]! → j ∈ m23Incl[b]! → False) : Y a ⊔ Y b = ⊤ := by
  rcases h.complete (Y a ⊔ Y b) (le_sup_of_le_left (h.S_le a)) with ⟨j, hj, hjeq⟩ | htop
  · exfalso
    have h1 : Y a ≤ Y j := hjeq ▸ le_sup_left
    have h2 : Y b ≤ Y j := hjeq ▸ le_sup_right
    exact hmin j hj ((h.le_iff ha hj).mp h1) ((h.le_iff hb hj).mp h2)
  · exact htop

theorem Data.inv1 (h : Data U Y) (α : MulAut Γ) (hα : U.map α.toMonoidHom = U) :
    (Y 1).map α.toMonoidHom = Y 1 :=
  map_eq_of_unique_card (h.S_le 1)
    (h.unique_of_idx (a := 1) (by norm_num) (by decide) (by decide)) α hα

theorem Data.inv15 (h : Data U Y) (α : MulAut Γ) (hα : U.map α.toMonoidHom = U) :
    (Y 15).map α.toMonoidHom = Y 15 :=
  map_eq_of_unique_card (h.S_le 15)
    (h.unique_of_idx (a := 15) (by norm_num) (by decide) (by decide)) α hα

theorem Data.inv3 (h : Data U Y) (α : MulAut Γ) (hα : U.map α.toMonoidHom = U) :
    (Y 3).map α.toMonoidHom = Y 3 := by
  have h1 := h.inv1 α hα
  refine map_eq_of_unique_pred α hα (fun Z => Z ≤ Y 1)
    ((h.le_iff (by norm_num) (by norm_num)).mpr (by decide)) (h.S_le 3)
    (fun Z hZ => map_le_of_inv α h1 hZ) ?_
  exact h.unique_below (a := 3) (q := 1) (by norm_num) (by norm_num) (by decide)
    (h.ne_top (by norm_num) (by decide))

theorem Data.inv7 (h : Data U Y) (α : MulAut Γ) (hα : U.map α.toMonoidHom = U) :
    (Y 7).map α.toMonoidHom = Y 7 := by
  have h1 := h.inv1 α hα
  refine map_eq_of_unique_pred α hα (fun Z => Z ≤ Y 1)
    ((h.le_iff (by norm_num) (by norm_num)).mpr (by decide)) (h.S_le 7)
    (fun Z hZ => map_le_of_inv α h1 hZ) ?_
  exact h.unique_below (a := 7) (q := 1) (by norm_num) (by norm_num) (by decide)
    (h.ne_top (by norm_num) (by decide))

theorem Data.inv10 (h : Data U Y) (α : MulAut Γ) (hα : U.map α.toMonoidHom = U) :
    (Y 10).map α.toMonoidHom = Y 10 := by
  have h7 := h.inv7 α hα
  refine map_eq_of_unique_pred α hα (fun Z => Z ≤ Y 7)
    ((h.le_iff (by norm_num) (by norm_num)).mpr (by decide)) (h.S_le 10)
    (fun Z hZ => map_le_of_inv α h7 hZ) ?_
  exact h.unique_below (a := 10) (q := 7) (by norm_num) (by norm_num) (by decide)
    (h.ne_top (by norm_num) (by decide))

theorem Data.inv11 (h : Data U Y) (α : MulAut Γ) (hα : U.map α.toMonoidHom = U) :
    (Y 11).map α.toMonoidHom = Y 11 := by
  have h3 := h.inv3 α hα
  have h7 := h.inv7 α hα
  refine map_eq_of_unique_pred α hα (fun Z => Z ≤ Y 3 ∧ ¬ Z ≤ Y 7)
    ⟨(h.le_iff (by norm_num) (by norm_num)).mpr (by decide), fun hle =>
      absurd ((h.le_iff (by norm_num) (by norm_num)).mp hle) (by decide)⟩ (h.S_le 11)
    (fun Z hZ => ⟨map_le_of_inv α h3 hZ.1, fun hle =>
      hZ.2 ((map_le_iff_of_eq α h7).mp hle)⟩) ?_
  intro Z hZ hZp hc
  rcases h.complete Z hZ with ⟨j, hj, rfl⟩ | rfl
  · have h1 : 3 ∈ m23Incl[j]! := (h.le_iff hj (by norm_num)).mp hZp.1
    have h2 : 7 ∉ m23Incl[j]! := fun h7' => hZp.2 ((h.le_iff hj (by norm_num)).mpr h7')
    have key : ∀ j < 16, 3 ∈ m23Incl[j]! → 7 ∉ m23Incl[j]! → idx j = idx 11 → j = 11 := by decide
    rw [key j hj h1 h2 (h.card_eq hj (by norm_num) hc)]
  · exact absurd (top_le_iff.mp hZp.1) (h.ne_top (by norm_num) (by decide))

theorem Data.sup_1_15 (h : Data U Y) : Y 1 ⊔ Y 15 = ⊤ :=
  h.sup_eq_top (by norm_num) (by norm_num) (by decide)

theorem Data.sup_3_7 (h : Data U Y) : Y 3 ⊔ Y 7 = Y 1 :=
  h.sup_eq (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
    (h.ne_top (by norm_num) (by decide))

theorem Data.sup_10_11 (h : Data U Y) : Y 10 ⊔ Y 11 = Y 3 :=
  h.sup_eq (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
    (h.ne_top (by norm_num) (by decide))

theorem Data.card_Y10 (h : Data U Y) : Nat.card (Y 10) = 2 ^ 7 * 3 := by
  rw [h.card 10 (by norm_num)]
  rfl

theorem Data.card_Y11 (h : Data U Y) : Nat.card (Y 11) = 2 ^ 7 * 3 := by
  rw [h.card 11 (by norm_num)]
  rfl

theorem Data.card_Y15 (h : Data U Y) : Nat.card (Y 15) = 2 ^ 7 * 3 ^ 2 := by
  rw [h.card 15 (by norm_num)]
  rfl

theorem Data.card_Y7 (h : Data U Y) : Nat.card (Y 7) = 2 ^ 7 * 3 * 5 := by
  rw [h.card 7 (by norm_num)]
  rfl

theorem Data.Y10_solvable [Finite Γ] (h : Data U Y) : Group.IsSolvable ↥(Y 10) :=
  A312Ru.isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 7) (b := 1)
    h.card_Y10

theorem Data.Y11_solvable [Finite Γ] (h : Data U Y) : Group.IsSolvable ↥(Y 11) :=
  A312Ru.isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 7) (b := 1)
    h.card_Y11

theorem Data.Y15_solvable [Finite Γ] (h : Data U Y) : Group.IsSolvable ↥(Y 15) :=
  A312Ru.isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := 7) (b := 2)
    h.card_Y15

theorem Data.Y7_not_solvable [Finite Γ] (h : Data U Y) (hU : IsPGroup 2 ↥U) :
    ¬ Group.IsSolvable ↥(Y 7) :=
  not_isSolvable_of_no_overgroup (h.S_le 7) hU (e := 7) (m := 3) (p := 5) (by norm_num)
    h.card_Y7 (by norm_num) (by norm_num) fun H hUH _ hc => by
      rcases h.complete H hUH with ⟨j, hj, rfl⟩ | rfl
      · rw [h.card j hj] at hc
        have key : ∀ j < 16, idx j * 2 ^ 7 ≠ 2 ^ 7 * 5 := by decide
        exact key j hj hc
      · rw [h.card_top] at hc
        omega

theorem Data.Y7_levi5 [Finite Γ] (h : Data U Y) (hU : IsPGroup 2 ↥U) :
    ∃ ρ : ↥(Y 7) →* Equiv.Perm (Fin 5), IsPGroup 2 ρ.ker ∧ alternatingGroup (Fin 5) ≤ ρ.range := by
  have hle : Y 10 ≤ Y 7 := (h.le_iff (by norm_num) (by norm_num)).mpr (by decide)
  have hcard' : Nat.card ((Y 10).subgroupOf (Y 7)) = 2 ^ 7 * 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact h.card_Y10
  exact levi5_of_index_five (h.Y7_not_solvable hU) (e := 7) h.card_Y7 hcard'

theorem Data.good_pair [Finite Γ] (h : Data U Y) (hU : IsPGroup 2 ↥U) (𝒜 : Set (MulAut Γ))
    (h𝒜 : ∀ α ∈ 𝒜, U.map α.toMonoidHom = U) : GoodGam 𝒜 (Y 1) ∧ GoodGam 𝒜 (Y 15) := by
  have g10 : GoodGam 𝒜 (Y 10) :=
    GoodGam.solvable (fun α hα => h.inv10 α (h𝒜 α hα)) h.Y10_solvable
  have g11 : GoodGam 𝒜 (Y 11) :=
    GoodGam.solvable (fun α hα => h.inv11 α (h𝒜 α hα)) h.Y11_solvable
  have g7 : GoodGam 𝒜 (Y 7) :=
    GoodGam.levi5 (fun α hα => h.inv7 α (h𝒜 α hα)) (h.Y7_levi5 hU)
  have g3 : GoodGam 𝒜 (Y 3) := by
    rw [← h.sup_10_11]
    exact GoodGam.join g10 g11
  have g1 : GoodGam 𝒜 (Y 1) := by
    rw [← h.sup_3_7]
    exact GoodGam.join g3 g7
  exact ⟨g1, GoodGam.solvable (fun α hα => h.inv15 α (h𝒜 α hα)) h.Y15_solvable⟩

end Abstract

section Main


theorem data : Data m23CtxB.S m23CtxB.Y where
  S_le := m23CtxB.S_le_Y
  complete := fun _ hZ => member_or_top hZ
  card := fun _ hj => card_Y hj
  card_top := card_top
  le_iff := le_iff

theorem nParam_le_two_of_isM23
    {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hM23 : IsSporadic .M23 (ASInputs.FStar G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : E1.nParam (⊤ : Subgroup G) ≤ ((2 : ℕ) : ℕ∞) := by
  have hTs : IsSylowTwoOf T ⊤ := ⟨le_top, hT.1, by
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hT.2⟩
  have hLn : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  obtain ⟨e₀⟩ := hM23
  exact nParam_le_two_of_goodPair (U := m23CtxB.S) S_sylow data.sup_1_15
    (fun 𝒜 h => data.good_pair m23CtxB.S_isPGroup 𝒜 h) hLn e₀ hTs hFT

end Main

end CFSG.Quasithin.RonanE114.C5.M23
