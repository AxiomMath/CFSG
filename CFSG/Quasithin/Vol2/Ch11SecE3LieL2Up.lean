module

public import CFSG.Quasithin.Vol2.Ch11SecE3LieSL2
public import CFSG.Quasithin.Vol2.Ch11SecE3LieL2Fix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b CFSG.CGT
open CFSG.RankThree.PartOne.KCRootAxis
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner congr_conj)
open scoped MatrixGroups

section Bound

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_le_of_isElemAbelian_sl2 {L : Subgroup G} {n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (h : AlmostSimple L) (e : ↥L ≃* SL(2, K)) (hK : Nat.card K = 2 ^ n)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) : Nat.card A ≤ 2 ^ n := by
  classical
  have hLn := h.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set χ : G →* MulAut SL(2, K) := (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal with hχ
  have hχapp : ∀ (g : G) (x : ↥L), χ g (e x) = e (MulAut.conjNormal g x) := by
    intro g x
    show e ((MulAut.conjNormal g) (e.symm (e x))) = _
    rw [MulEquiv.symm_apply_apply]
  have hin : ∀ (g : G) (M : SL(2, K)), MulAut.conj M = χ g → g ∈ L := by
    intro g M hgM
    set m : ↥L := e.symm M with hm
    have hc : (m : G)⁻¹ * g ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := congrArg (fun φ : MulAut SL(2, K) => φ (e ⟨x, hx⟩)) hgM
      simp only [MulAut.conj_apply] at h1
      rw [hχapp] at h1
      have h2 : (MulAut.conjNormal g ⟨x, hx⟩ : ↥L) = m * ⟨x, hx⟩ * m⁻¹ := by
        apply e.injective
        rw [← h1, map_mul, map_mul, map_inv, hm, MulEquiv.apply_symm_apply]
      have h3 := congrArg Subtype.val h2
      simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, InvMemClass.coe_inv] at h3
      calc x * ((m : G)⁻¹ * g) = (m : G)⁻¹ * (m * x * (m : G)⁻¹) * g := by group
        _ = (m : G)⁻¹ * (g * x * g⁻¹) * g := by rw [h3]
        _ = (m : G)⁻¹ * g * x := by group
    rw [h.centralizer_eq, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact hc ▸ m.2
  have hinner : ∀ (x : G) (hx : x ∈ L), χ x = MulAut.conj (e ⟨x, hx⟩) := by
    intro x hx
    ext y : 1
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [hχapp, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
    exact congrArg e (Subtype.ext (MulAut.conjNormal_apply x y'))
  have hmapB : ∀ B : Subgroup G, B ≤ L →
      Nat.card ((B.subgroupOf L).map e.toMonoidHom) = Nat.card B := by
    intro B hBL
    rw [Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  have hmap2 : ∀ B : Subgroup G, B ≤ L → IsPGroup 2 B →
      IsPGroup 2 ((B.subgroupOf L).map e.toMonoidHom) := fun B hBL hB2 =>
    hB2.of_equiv ((Subgroup.subgroupOfEquivOfLe hBL).symm.trans
      ((B.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective))
  have hLbound : ∀ B : Subgroup G, B ≤ L → IsPGroup 2 B → Nat.card B ≤ 2 ^ n := by
    intro B hBL hB2
    obtain ⟨Q, hQ⟩ := (hmap2 B hBL hB2).exists_le_sylow
    obtain ⟨h₀, hh₀⟩ := Timmesfeld75.exists_conjSubgroup_utri_eq_of_sylow Q
    have hQcard : Nat.card (Q : Subgroup SL(2, K)) = 2 ^ n := by
      rw [← hh₀, Timmesfeld75.card_conjSubgroup, Timmesfeld75.card_utri, hK]
    rw [← hmapB B hBL, ← hQcard]
    exact Subgroup.card_le_of_le hQ
  by_cases hAL : A ≤ L
  · exact hLbound A hAL (B2F.isPGroup_of_isElemAbelian hA)
  obtain ⟨a, haA, haL⟩ := Set.not_subset.mp hAL
  set B : Subgroup G := A ⊓ L with hBdef
  have h2 : Nat.card A ≤ 2 * Nat.card B := by
    set f : ↥A →* Outer SL(2, K) :=
      (QuotientGroup.mk' (inner SL(2, K))).comp (χ.comp A.subtype) with hf
    have hker : ∀ x : ↥A, f x = 1 ↔ (x : G) ∈ L := by
      intro x
      rw [hf, MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      constructor
      · rintro ⟨M, hM⟩
        exact hin x M hM
      · intro hx
        exact ⟨e ⟨x, hx⟩, (hinner x hx).symm⟩
    have hkercard : Nat.card f.ker = Nat.card B := by
      have hk : f.ker = B.subgroupOf A := by
        ext x
        rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
        exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
      rw [hk]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hrange : Nat.card f.range ≤ 2 := by
      have : Finite (MulAut SL(2, K)) := MulEquiv.finite_left
      have := Fintype.ofFinite (Outer SL(2, K))
      have hcyc : IsCyclic (Outer SL(2, K)) := out_sl2_isCyclic
      have hsq : ∀ y ∈ f.range, y ^ 2 = 1 := by
        rintro _ ⟨x, rfl⟩
        have hx2 : x ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hA.2 x x.2)
        rw [← map_pow, hx2, map_one]
      calc Nat.card f.range = Fintype.card f.range := Nat.card_eq_fintype_card
        _ ≤ Fintype.card {y : Outer SL(2, K) // y ^ 2 = 1} :=
          Fintype.card_le_of_injective (fun y => ⟨y.1, hsq y.1 y.2⟩) fun y y' h =>
            Subtype.ext (congrArg (fun z : {y : Outer SL(2, K) // y ^ 2 = 1} =>
              (z : Outer SL(2, K))) h)
        _ = (Finset.univ.filter fun y : Outer SL(2, K) => y ^ 2 = 1).card :=
          Fintype.card_subtype _
        _ ≤ 2 := IsCyclic.card_pow_eq_one_le (by norm_num)
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hkercard] at hcard
    rw [hcard]
    exact Nat.mul_le_mul_right _ hrange
  obtain ⟨M, σ, hMσ⟩ := exists_conj_mul_slFieldAut (χ a)
  have hσ : σ ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one] at hMσ
    exact haL (hin a M hMσ.symm)
  have hB : Nat.card B ≤ Nat.card (σ.toRingHom.eqLocusField (RingHom.id K)) := by
    have hfix : ∀ y ∈ (B.subgroupOf L).map e.toMonoidHom,
        (MulAut.conj M * slFieldAut K σ) y = y := by
      rintro _ ⟨b, hb, rfl⟩
      rw [← hMσ, MulEquiv.coe_toMonoidHom, hχapp]
      congr 1
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have hab : a * b = b * a :=
        B2F.isElemAbelian_comm hA haA (Subgroup.mem_subgroupOf.mp hb).1
      rw [hab, mul_inv_cancel_right]
    rw [← hmapB B inf_le_right]
    exact card_le_of_fixed_sl2 (hmap2 B inf_le_right
      ((B2F.isPGroup_of_isElemAbelian hA).to_inf_left)) hfix
  have hS2 := card_eqLocusField_sq_le hσ
  have hS1 := two_le_card_eqLocusField σ
  set s := Nat.card (σ.toRingHom.eqLocusField (RingHom.id K)) with hs
  calc Nat.card A ≤ 2 * Nat.card B := h2
    _ ≤ 2 * s := Nat.mul_le_mul_left 2 hB
    _ ≤ s * s := Nat.mul_le_mul_right s hS1
    _ = s ^ 2 := (sq s).symm
    _ ≤ Nat.card K := hS2
    _ = 2 ^ n := hK

theorem nParam_le_of_isPSL22 {T : Subgroup G} {n : ℕ}
    (hL : IsPSL 2 2 n ↥(CFSG.generalizedFitting G))
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : E1.nParam (⊤ : Subgroup G) ≤ n := by
  obtain ⟨hn, K, _, _, _, hK, ⟨e⟩⟩ := exists_sl2_of_isPSL22 hL
  have hnab : ∃ a b : ↥(CFSG.generalizedFitting G), a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := sl2_nonabelian (K := K)
    refine ⟨e.symm x, e.symm y, fun hc => hxy ?_⟩
    simpa using congrArg e hc
  have h := almostSimple_generalizedFitting hs hnab hT.1 hFT
  exact nParam_le_of_card_le hs hnab hT hFT (by omega) fun A hA =>
    card_le_of_isElemAbelian_sl2 h e hK hA

theorem nParam_eq_of_isPSL22 {T : Subgroup G} {n : ℕ}
    (hL : IsPSL 2 2 n ↥(CFSG.generalizedFitting G))
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : E1.nParam (⊤ : Subgroup G) = n :=
  le_antisymm (nParam_le_of_isPSL22 hL hs hT hFT) (le_nParam_of_isPSL22 hL hs hT hFT)

end Bound

end CFSG.Quasithin.Vol2.Ch11.SecE3
