module

public import CFSG.RankThree.GF2n.Parrott.Section4Theorem4OutsideEquality
public import CFSG.RankThree.GF2n.Parrott.SquareRelation

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

theorem exists_isParrottE_of_noFusion (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (hne : H z ⊔ pPrimeCore 2 G ≠ ⊤)
    (hNF : (∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
        g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) →
      ∀ y ∈ H z, y ∉ J z → orderOf y = 2 → ¬ IsConj z y)
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
    : ∃ E : Subgroup G, IsParrottE z E := by
  obtain ⟨z₁₀, hZeq, hz₁₀z, hz₁₀2⟩ := exists_z1 h
  have hz₁₀ : z₁₀ ∈ centerIn (J z) := by
    rw [hZeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z₁₀)
  have hNF' : (∀ g : G, (g ∈ centralizer ({z₁₀} : Set G) ∨ g ∈ centralizer ({z * z₁₀} : Set G)) →
      g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) →
      ∀ y ∈ H z, y ∉ J z → orderOf y = 2 → ¬ IsConj z y := by
    intro hA
    apply hNF
    rintro g ⟨e, he, he1, hez, hge⟩ hgH
    rcases (mem_centerIn_J_iff h hz₁₀ hz₁₀z hz₁₀2).mp he with h1 | h1 | h1 | h1
    · exact absurd h1 he1
    · exact absurd h1 hez
    · rw [h1] at hge
      exact hA g (Or.inl hge) hgH
    · rw [h1] at hge
      exact hA g (Or.inr hge) hgH
  obtain ⟨g, hg, hgH, hgz⟩ := lemma42_of_noFusion h hZ hne hz₁₀ hz₁₀z hz₁₀2 hNF'
  have hgz' : g * z * g⁻¹ ≠ z := fun h1 => hgz (by rw [h1]; exact Subgroup.mem_zpowers z)
  obtain ⟨z₁, hz₁, hz₁z, hz₁2, hfuse⟩ : ∃ z₁ : G, z₁ ∈ centerIn (J z) ∧
      z₁ ∉ Subgroup.zpowers z ∧ orderOf z₁ = 2 ∧
      ∃ g ∈ centralizer ({z₁} : Set G), g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z := by
    rcases hg with hg | hg
    · exact ⟨z₁₀, hz₁₀, hz₁₀z, hz₁₀2, g, hg, hgH, hgz'⟩
    · obtain ⟨h1, h2, h3⟩ := exists_z1_mul h hz₁₀ hz₁₀z hz₁₀2
      exact ⟨z * z₁₀, h1, h2, h3, g, hg, hgH, hgz'⟩
  obtain ⟨U, hUC, hUi, hJU, hUq, E, hE, -⟩ := hB2c z₁ hz₁ hz₁z hz₁2 hfuse
  exact ⟨E, hE⟩

theorem parrott_theorem4_of_not_equalityBranch_noV (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hne : H z ⊔ pPrimeCore 2 G ≠ ⊤)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
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
  obtain ⟨P, -, hP⟩ := (generatorConjugacy_iff_actionQA45_eq_conj_rhoAct h D).mp
    (generatorConjugacy_of_not_equalityBranch h D hIII)
  have hP' : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹ := fun a => by
    simpa [rhoA, toQAct] using hP a
  have hH' := relIndex_commutator_sup_centerIn_of_not_equalityBranch h D hIII
  have hJN := J_le_commutator_sup_centerIn_of_not_equalityBranch h D hIII
  have hinv := qa45_involution_classes
  have hC5 : ∀ B : Subgroup A45, Nat.card B = 5 → Nat.card (centralizer (B : Set A45)) = 10 ∧
      ∃ w : A45, orderOf w = 2 ∧ IsConj w (uA * vA) ∧
        centralizer (B : Set A45) = B ⊔ zpowers w := fun B hB =>
    ⟨(qa45_sylowFive B hB).2.1, (qa45_sylowFive B hB).2.2⟩
  have hV2 : ∀ y : ↥(H z), IsConj (qH D y) (uA * vA) → fixDimV h y = 4 :=
    fixDimV_eq_of_conj_rep D h rhoA P hP' (fun a => IsConj a (uA * vA)) 4
      (fun a ha => by simpa using spinFixedCard_uv a ha)
  have hV5 : ∀ y : ↥(H z), orderOf (qH D y) = 5 → fixDimV h y = 0 :=
    fixDimV_eq_of_conj_rep D h rhoA P hP' (fun a => orderOf a = 5) 0
      (fun a ha => by simpa using spinFixedCard_five a ha)
  have hNF := hNF_of_cosets_of_involution D h hZ hJN hinv hV2 hV5 hC5 hZs_t hNF_e hNF_g
  refine parrott_theorem4_of_not_equalityBranch D h hZ hne hIII hB2c hB3 hB6 hB5 ?_ hrest_t hZs_t
    hNF_e hNF_g
  intro y hy hyy hyc
  obtain ⟨E, hE⟩ := exists_isParrottE_of_noFusion h hZ hne hNF hB2c
  exact hv_of_isParrottE D h hZ P hP' hE y hy hyy hyc

end Certified

end CFSG.RankThree.GF2n.Parrott
