module

public import CFSG.RankThree.GF2n.Parrott.Section4Theorem4Spin
public import CFSG.RankThree.GF2n.Parrott.Section4Hrest
public import CFSG.RankThree.GF2n.Parrott.QA45InvolutionClasses
public import CFSG.RankThree.GF2n.Parrott.QA45SylowFacts
public import CFSG.RankThree.GF2n.Parrott.SpinFixedCardUT
public import CFSG.RankThree.GF2n.Parrott.Section4NoFusionClasses

import CFSG.RankThree.GF2n.Parrott.QA45ElementaryAbelian
import CFSG.RankThree.GF2n.Parrott.SpinFixedCardMore

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {z : G}

section Certified

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

theorem parrott_theorem4_of_classes (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hne : H z ⊔ pPrimeCore 2 G ≠ ⊤)
    (hB2c : ∀ z₁ ∈ centerIn (J z), z₁ ∉ Subgroup.zpowers z → orderOf z₁ = 2 →
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
    (hB5 : ∀ z₁ ∈ centerIn (J z), z₁ ∉ Subgroup.zpowers z → orderOf z₁ = 2 →
      ∀ G₀ : Subgroup G, G₀.Normal → G₀.index = 2 → z ∈ G₀ → z₁ ∉ G₀ →
        (∃ g ∈ G₀, g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
        ∃ G₁ : Subgroup G, G₁ ≤ G₀ ∧ G₁.relIndex G₀ = 2 ∧
          (∀ c ∈ G₀, (∀ x ∈ G₁, c * x = x * c) → c = 1) ∧
          ∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
            Nonempty (↥G₁ ≃* X))
    (hH' : (⁅H z, H z⁆ ⊔ centerIn (J z)).relIndex (H z) = 2)
    (hJN : J z ≤ ⁅H z, H z⁆ ⊔ centerIn (J z))
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    (hlift : ∃ B : Subgroup G, IsSylowOf 5 B (H z) ∧ ∃ x₀ ∈ H z, x₀ * x₀ = 1 ∧
      x₀ ∉ ⁅H z, H z⁆ ⊔ centerIn (J z) ∧ ∀ b ∈ B, x₀ * b = b * x₀)
    (hrest_t : ∀ E : Subgroup G, IsParrottE z E →
      ∀ (y : G) (hy : y ∈ ⁅H z, H z⁆ ⊔ centerIn (J z)), orderOf y = 2 →
        IsConj (qH D ⟨y, commutator_sup_centerIn_le_H hy⟩) tA → ∃ c ∈ H z, c * y * c⁻¹ ∈ E)
    (hZs_t : ∀ (x : G) (hx : x ∈ H z), x * x = 1 → IsConj (qH D ⟨x, hx⟩) tA →
      ∀ X : Subgroup G, IsSylowOf 2 X (H z ⊓ centralizer ({x} : Set G)) →
        ∀ w ∈ X ⊓ centralizer (X : Set G), w ∈ J z ∨ ∃ j ∈ J z, w = x * j)
    (hNF_e : (∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
        g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) →
      ∀ (y : G) (hy : y ∈ H z), orderOf y = 2 → IsConj (qH D ⟨y, hy⟩) (uA * tA) →
        ¬ IsConj z y)
    (hNF_g : (∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
        g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) →
      ∀ (y : G) (hy : y ∈ H z), orderOf y = 2 → IsConj (qH D ⟨y, hy⟩) vA → ¬ IsConj z y) :
    Tim79a.ParrottCaseII z := by
  have hinv := qa45_involution_classes
  have hC5 : ∀ B : Subgroup A45, Nat.card B = 5 → Nat.card (centralizer (B : Set A45)) = 10 ∧
      ∃ w : A45, orderOf w = 2 ∧ IsConj w (uA * vA) ∧
        centralizer (B : Set A45) = B ⊔ zpowers w := fun B hB =>
    ⟨(qa45_sylowFive B hB).2.1, (qa45_sylowFive B hB).2.2⟩
  have hV1 := fixDimV_eq_four_of_conj_rep D h rhoA P hP (fun a ha => spinFixedCard_ut a ha)
  have hV2 : ∀ y : ↥(H z), IsConj (qH D y) (uA * vA) → fixDimV h y = 4 :=
    fixDimV_eq_of_conj_rep D h rhoA P hP (fun a => IsConj a (uA * vA)) 4
      (fun a ha => by simpa using spinFixedCard_uv a ha)
  have hV5 : ∀ y : ↥(H z), orderOf (qH D y) = 5 → fixDimV h y = 0 :=
    fixDimV_eq_of_conj_rep D h rhoA P hP (fun a => orderOf a = 5) 0
      (fun a ha => by simpa using spinFixedCard_five a ha)
  have hEweak := eweak_of_fixDim_four D h hV1 qa45_elemAbelian_card_le_sixteen
    qa45_elemAbelian_pair_inf
  have hrest := hrest_of_t_part D h hZ P hP hinv hrest_t
  have hEinv := eInv_of_rest D h hV1 qa45_elemAbelian_pair_inf hrest
  have hNF := hNF_of_cosets D h hZ hJN hinv hV2 hV5 hC5 hlift hZs_t hNF_e hNF_g
  refine parrott_theorem4_of_spin_data D h hZ hne hNF ?_ hB3 hB6 hH' hJN P hP spinFixedCard_uv
    spinFixedCard_five spinFaithful_uv hC5 hlift hB5
  intro z₁ hz₁ hz₁z hz₁2 hfuse
  obtain ⟨U, hUC, hUi, hJU, hUq, E, hE, hEU, hQ, t', j₀, ht'E, ht'J, ht'2, hzt', hj₀, hj₀c,
    hconj⟩ := hB2c z₁ hz₁ hz₁z hz₁2 hfuse
  exact ⟨U, hUC, hUi, hJU, hUq, E, hE, hEU, hQ, hEweak E hE, hEinv E hE, t', j₀, ht'E, ht'J,
    ht'2, hzt', hj₀, hj₀c, hconj⟩

end Certified

end CFSG.RankThree.GF2n.Parrott
