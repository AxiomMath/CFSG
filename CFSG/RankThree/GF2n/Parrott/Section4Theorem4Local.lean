module

public import CFSG.RankThree.GF2n.Parrott.Section4FusionIntoN
public import CFSG.RankThree.GF2n.Parrott.Section4InvolutionCoset
public import CFSG.RankThree.GF2n.Parrott.Section4SylowCentralizer
public import CFSG.RankThree.GF2n.Parrott.Section4SylowFiveFusion
public import CFSG.RankThree.GF2n.Parrott.Section4SylowFiveStructure
public import CFSG.RankThree.GF2n.Parrott.Section4Theorem4

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

section Certified

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

theorem exists_sylow_centralizer_of_local_data (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hB2 : ∀ z₁ ∈ centerIn (J z), z₁ ∉ Subgroup.zpowers z → orderOf z₁ = 2 →
      (∃ g ∈ centralizer ({z₁} : Set G), g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
      ∃ U : Subgroup G, U ≤ centralizer ({z₁} : Set G) ∧
        U.relIndex (centralizer ({z₁} : Set G)) = 2 ∧ J z ≤ U ∧
        (∃ (_ : ((Subgroup.zpowers z₁).subgroupOf U).Normal) (X : Type) (_ : Group X),
          CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
            Nonempty (↥U ⧸ (Subgroup.zpowers z₁).subgroupOf U ≃* X)) ∧
        ∃ E : Subgroup G, IsParrottE z E ∧ E ≤ U ∧
          ((E.subgroupOf (normalizer (E : Set G) ⊓ U)).Normal ∧
             Nat.card (↥(normalizer (E : Set G) ⊓ U) ⧸
               E.subgroupOf (normalizer (E : Set G) ⊓ U)) = 20160 ∧
             ∀ L : Subgroup G, E ≤ L → L ≤ normalizer (E : Set G) ⊓ U →
               L.relIndex (normalizer (E : Set G) ⊓ U) ≠ 2) ∧
          (∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
            ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E) ∧
          (∀ y ∈ ⁅H z, H z⁆ ⊔ centerIn (J z), orderOf y = 2 → ∃ c ∈ H z, c * y * c⁻¹ ∈ E) ∧
          ∃ t' j₀ : G, t' ∈ E ∧ t' ∉ J z ∧ orderOf t' = 2 ∧ IsConj z t' ∧ j₀ ∈ J z ∧
            j₀ ∉ centerIn (J z) ∧ IsConj (t' * z) j₀)
    (hB3 : ∀ e ∈ centerIn (J z), e ≠ 1 → e ≠ z →
      (∃ g ∈ centralizer ({e} : Set G), g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
      ∀ j ∈ J z, orderOf j = 2 → j ∉ Subgroup.zpowers z →
        ∀ g ∈ centralizer ({e} : Set G), g * z * g⁻¹ ≠ j)
    (hB6 : ∀ E : Subgroup G, IsParrottE z E →
      (∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
        ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E) →
      (∀ j ∈ J z, j ∉ Subgroup.zpowers z → ¬ IsConj z j) →
      (∃ e ∈ E, e ≠ z ∧ ∃ n ∈ normalizer (E : Set G), n * z * n⁻¹ = e) →
      ∃ K : Subgroup G, E ≤ K ∧ K.relIndex (normalizer (E : Set G)) = 2 ∧
        ¬ (normalizer (E : Set G) ⊓ H z ≤ K) ∧
        (E.subgroupOf K).Normal ∧ Nat.card (↥K ⧸ E.subgroupOf K) = 20160 ∧
          ∀ L : Subgroup G, E ≤ L → L ≤ K → L.relIndex K ≠ 2)
    (hH' : (⁅H z, H z⁆ ⊔ centerIn (J z)).relIndex (H z) = 2)
    (hJN : J z ≤ ⁅H z, H z⁆ ⊔ centerIn (J z))
    (hV2 : ∀ y : ↥(H z), IsConj (qH D y) (uA * vA) → fixDimV h y = 4)
    (hV5 : ∀ y : ↥(H z), orderOf (qH D y) = 5 → fixDimV h y = 0)
    (hC5 : ∀ B : Subgroup A45, Nat.card B = 5 → Nat.card (centralizer (B : Set A45)) = 10 ∧
      ∃ w : A45, orderOf w = 2 ∧ IsConj w (uA * vA) ∧
        centralizer (B : Set A45) = B ⊔ zpowers w)
    (hlift : ∃ B : Subgroup G, IsSylowOf 5 B (H z) ∧ ∃ x₀ ∈ H z, x₀ * x₀ = 1 ∧
      x₀ ∉ ⁅H z, H z⁆ ⊔ centerIn (J z) ∧ ∀ b ∈ B, x₀ * b = b * x₀)
    (hZs : ∀ B : Subgroup G, IsSylowOf 5 B (H z) → ∀ x₀ ∈ H z, x₀ * x₀ = 1 →
      x₀ ∉ ⁅H z, H z⁆ ⊔ centerIn (J z) → (∀ b ∈ B, x₀ * b = b * x₀) →
      ∀ Y : Subgroup G, IsSylowOf 2 Y (H z ⊓ centralizer ({x₀} : Set G)) →
        ∀ w ∈ Y ⊓ centralizer (Y : Set G), w ∈ J z ∨ ∃ j ∈ J z, w = x₀ * j) :
    ∃ x ∈ H z, orderOf x = 2 ∧ x ∉ ⁅H z, H z⁆ ⊔ centerIn (J z) ∧
      ∃ Y : Subgroup G, IsSylowOf 2 Y (H z ⊓ centralizer ({x} : Set G)) ∧
        IsSylowOf 2 Y (centralizer ({x} : Set G)) := by
  obtain ⟨B, hB5, x₀, hx₀H, hx₀x₀, hx₀N, hx₀B⟩ := hlift
  have hA := fusion_into_commutator_sup_of_hB2_hB6 h hZ hB2 hB3 hB6 hH'
  obtain ⟨Y₀, hY₀, hY₀c, hZY, hx₀Y, hY₀N⟩ := exists_sylowTwo_inf_centralizer_five D h hZ hV5
    (fun B' hB' => (hC5 B' hB').1) hB5 hx₀H hx₀x₀ hx₀N hx₀B
  have hx₀J : x₀ ∉ J z := fun hx => hx₀N (hJN hx)
  have hconj := isConj_qH_of_involution_mem_centralizer_five D h (fun B' hB' => (hC5 B' hB').2)
    hB5 hx₀H hx₀x₀ hx₀J hx₀B
  have hVx := hV2 ⟨x₀, hx₀H⟩ hconj
  have hf := not_isConj_of_involution_coset_of_fixDim h hZ hJN hB5 hY₀ hY₀c hZY hY₀N hA hx₀H
    hx₀Y hx₀x₀ hx₀N hVx
  have hJ : ∀ j ∈ J z, j ∉ Subgroup.zpowers z → ¬ IsConj z j := fun j hj hjz =>
    not_isConj_of_mem_J_of_lemma32 h hZ hB3 hj hjz
  have hx₀2 : orderOf x₀ = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hx₀x₀) (fun h1 => hx₀N (by rw [h1]; exact one_mem _))
  exact ⟨x₀, hx₀H, hx₀2, hx₀N, exists_sylow_centralizer_of_fusion_free h hJ hx₀H
    (hZs B hB5 x₀ hx₀H hx₀x₀ hx₀N hx₀B) hf⟩

theorem parrott_theorem4_of_local_data (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hne : H z ⊔ pPrimeCore 2 G ≠ ⊤)
    (hNF : (∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
        g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) →
      ∀ y ∈ H z, y ∉ J z → orderOf y = 2 → ¬ IsConj z y)
    (hB2 : ∀ z₁ ∈ centerIn (J z), z₁ ∉ Subgroup.zpowers z → orderOf z₁ = 2 →
      (∃ g ∈ centralizer ({z₁} : Set G), g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
      ∃ U : Subgroup G, U ≤ centralizer ({z₁} : Set G) ∧
        U.relIndex (centralizer ({z₁} : Set G)) = 2 ∧ J z ≤ U ∧
        (∃ (_ : ((Subgroup.zpowers z₁).subgroupOf U).Normal) (X : Type) (_ : Group X),
          CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
            Nonempty (↥U ⧸ (Subgroup.zpowers z₁).subgroupOf U ≃* X)) ∧
        ∃ E : Subgroup G, IsParrottE z E ∧ E ≤ U ∧
          ((E.subgroupOf (normalizer (E : Set G) ⊓ U)).Normal ∧
             Nat.card (↥(normalizer (E : Set G) ⊓ U) ⧸
               E.subgroupOf (normalizer (E : Set G) ⊓ U)) = 20160 ∧
             ∀ L : Subgroup G, E ≤ L → L ≤ normalizer (E : Set G) ⊓ U →
               L.relIndex (normalizer (E : Set G) ⊓ U) ≠ 2) ∧
          (∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
            ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E) ∧
          (∀ y ∈ ⁅H z, H z⁆ ⊔ centerIn (J z), orderOf y = 2 → ∃ c ∈ H z, c * y * c⁻¹ ∈ E) ∧
          ∃ t' j₀ : G, t' ∈ E ∧ t' ∉ J z ∧ orderOf t' = 2 ∧ IsConj z t' ∧ j₀ ∈ J z ∧
            j₀ ∉ centerIn (J z) ∧ IsConj (t' * z) j₀)
    (hB3 : ∀ e ∈ centerIn (J z), e ≠ 1 → e ≠ z →
      (∃ g ∈ centralizer ({e} : Set G), g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
      ∀ j ∈ J z, orderOf j = 2 → j ∉ Subgroup.zpowers z →
        ∀ g ∈ centralizer ({e} : Set G), g * z * g⁻¹ ≠ j)
    (hB6 : ∀ E : Subgroup G, IsParrottE z E →
      (∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
        ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E) →
      (∀ j ∈ J z, j ∉ Subgroup.zpowers z → ¬ IsConj z j) →
      (∃ e ∈ E, e ≠ z ∧ ∃ n ∈ normalizer (E : Set G), n * z * n⁻¹ = e) →
      ∃ K : Subgroup G, E ≤ K ∧ K.relIndex (normalizer (E : Set G)) = 2 ∧
        ¬ (normalizer (E : Set G) ⊓ H z ≤ K) ∧
        (E.subgroupOf K).Normal ∧ Nat.card (↥K ⧸ E.subgroupOf K) = 20160 ∧
          ∀ L : Subgroup G, E ≤ L → L ≤ K → L.relIndex K ≠ 2)
    (hH' : (⁅H z, H z⁆ ⊔ centerIn (J z)).relIndex (H z) = 2)
    (hJN : J z ≤ ⁅H z, H z⁆ ⊔ centerIn (J z))
    (hV2 : ∀ y : ↥(H z), IsConj (qH D y) (uA * vA) → fixDimV h y = 4)
    (hV5 : ∀ y : ↥(H z), orderOf (qH D y) = 5 → fixDimV h y = 0)
    (hC5 : ∀ B : Subgroup A45, Nat.card B = 5 → Nat.card (centralizer (B : Set A45)) = 10 ∧
      ∃ w : A45, orderOf w = 2 ∧ IsConj w (uA * vA) ∧
        centralizer (B : Set A45) = B ⊔ zpowers w)
    (hlift : ∃ B : Subgroup G, IsSylowOf 5 B (H z) ∧ ∃ x₀ ∈ H z, x₀ * x₀ = 1 ∧
      x₀ ∉ ⁅H z, H z⁆ ⊔ centerIn (J z) ∧ ∀ b ∈ B, x₀ * b = b * x₀)
    (hZs : ∀ B : Subgroup G, IsSylowOf 5 B (H z) → ∀ x₀ ∈ H z, x₀ * x₀ = 1 →
      x₀ ∉ ⁅H z, H z⁆ ⊔ centerIn (J z) → (∀ b ∈ B, x₀ * b = b * x₀) →
      ∀ Y : Subgroup G, IsSylowOf 2 Y (H z ⊓ centralizer ({x₀} : Set G)) →
        ∀ w ∈ Y ⊓ centralizer (Y : Set G), w ∈ J z ∨ ∃ j ∈ J z, w = x₀ * j)
    (hB5 : ∀ z₁ ∈ centerIn (J z), z₁ ∉ Subgroup.zpowers z → orderOf z₁ = 2 →
      ∀ G₀ : Subgroup G, G₀.Normal → G₀.index = 2 → z ∈ G₀ → z₁ ∉ G₀ →
        (∃ g ∈ G₀, g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
        ∃ G₁ : Subgroup G, G₁ ≤ G₀ ∧ G₁.relIndex G₀ = 2 ∧
          (∀ c ∈ G₀, (∀ x ∈ G₁, c * x = x * c) → c = 1) ∧
          ∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
            Nonempty (↥G₁ ≃* X)) :
    Tim79a.ParrottCaseII z := by
  have hS := exists_sylow_centralizer_of_local_data D h hZ hB2 hB3 hB6 hH' hJN hV2 hV5 hC5 hlift hZs
  exact parrott_theorem4_of_sylow_centralizer h hZ hne hNF hB2 hB3 hB6 hH' hJN hS hB5

end Certified

end CFSG.RankThree.GF2n.Parrott
