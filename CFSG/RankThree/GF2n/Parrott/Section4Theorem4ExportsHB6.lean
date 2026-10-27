module

public import CFSG.RankThree.GF2n.Parrott.Section4Theorem4NoV
public import CFSG.RankThree.GF2n.Parrott.Section4QuotientB
public import CFSG.RankThree.GF2n.Parrott.Section4G0TheoremA
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42Centres
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42ClassUtSpin
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42ClassVFinal
public import CFSG.RankThree.GF2n.Parrott.ZsTReduction
public import CFSG.RankThree.GF2n.Parrott.RestTReduction

import CFSG.RankThree.GF2n.Parrott.SpinFixedCardMore

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem hA_of_T3
    (hT3 : ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA w →
      ¬ (Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤) →
      ∃ K₁ : Subgroup K, K₁.index = 2 ∧ (∀ c : K, (∀ x ∈ K₁, c * x = x * c) → c = 1) ∧
        (∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
          Nonempty (↥K₁ ≃* X)) ∧
        K₁ ⊓ H w ≤ ⁅H w, H w⁆) :
    ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA w →
      Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤ ∨
      ∃ K₁ : Subgroup K, K₁.index = 2 ∧ (∀ c : K, (∀ x ∈ K₁, c * x = x * c) → c = 1) ∧
        ∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
          Nonempty (↥K₁ ≃* X) := by
  intro K _ _ w hw
  by_cases hsup : Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤
  · exact Or.inl hsup
  · obtain ⟨K₁, hK₁i, hK₁c, hX, -⟩ := hT3 K w hw hsup
    exact Or.inr ⟨K₁, hK₁i, hK₁c, hX⟩

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

theorem parrott_theorem4_of_exports_hB6 (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hne : H z ⊔ pPrimeCore 2 G ≠ ⊤)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    (hL32 : ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA w →
      ¬ (Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤) →
      ∀ j ∈ J w, orderOf j = 2 → j ∉ Subgroup.zpowers w → ¬ IsConj w j)
    (hT3 : ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA w →
      ¬ (Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤) →
      ∃ K₁ : Subgroup K, K₁.index = 2 ∧ (∀ c : K, (∀ x ∈ K₁, c * x = x * c) → c = 1) ∧
        (∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
          Nonempty (↥K₁ ≃* X)) ∧
        K₁ ⊓ H w ≤ ⁅H w, H w⁆)
    (hL345 : ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA w →
      ¬ (Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤) →
      ∃ E K' : Subgroup K,
        E ≤ H w ∧ E ≤ ⁅H w, H w⁆ ⊔ J w ∧ w ∈ E ∧
        Nat.card E = 2 ^ 9 ∧ Nat.card ↥(E ⊓ J w) = 2 ^ 5 ∧
        E = H w ⊓ Subgroup.centralizer ((E ⊓ J w : Subgroup K) : Set K) ∧
        E.relIndex (normalizer (E : Set K) ⊓ H w) = 1920 ∧
        (∀ x ∈ E, x ∈ Subgroup.closure
          {y : K | ∃ n ∈ normalizer (E : Set K), y = n * w * n⁻¹}) ∧
        E ≤ K' ∧ K'.relIndex (normalizer (E : Set K)) = 2 ∧
        normalizer (E : Set K) ⊓ ⁅H w, H w⁆ ≤ K' ∧ ¬ (normalizer (E : Set K) ⊓ H w ≤ K') ∧
        ((E.subgroupOf K').Normal ∧ Nat.card (↥K' ⧸ E.subgroupOf K') = 20160 ∧
           ∀ L : Subgroup K, E ≤ L → L ≤ K' → L.relIndex K' ≠ 2) ∧
        ∃ t j₀ : K, t ∈ E ∧ t ∉ J w ∧ orderOf t = 2 ∧ IsConj w t ∧
          j₀ ∈ J w ∧ j₀ ∉ Subgroup.zpowers w ∧ IsConj (t * w) j₀)
    (hB6 : ∀ E : Subgroup G, IsParrottE z E →
      (∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
        ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E) →
      (∀ j ∈ J z, j ∉ Subgroup.zpowers z → ¬ IsConj z j) →
      (∃ e ∈ E, e ≠ z ∧ ∃ n ∈ normalizer (E : Set G), n * z * n⁻¹ = e) →
      ∃ K : Subgroup G, E ≤ K ∧ K.relIndex (normalizer (E : Set G)) = 2 ∧
        ¬ (normalizer (E : Set G) ⊓ H z ≤ K) ∧
        (E.subgroupOf K).Normal ∧ Nat.card (↥K ⧸ E.subgroupOf K) = 20160 ∧
          ∀ L : Subgroup G, E ≤ L → L ≤ K → L.relIndex K ≠ 2) :
    Tim79a.ParrottCaseII z := by
  have hB3 := hB3_of_lemma32 h hZ hL32
  have hJN := J_le_commutator_sup_centerIn_of_not_equalityBranch h D hIII
  have hB2c := hB2c_of_theorem3 h hZ hJN hT3 hL345
  have hB5 := hB5_of_theoremA (hA_of_T3 hT3) h hZ
  have hrest_t := hrest_t_of_not_equalityBranch D h hZ hIII
  have hZs_t := hZs_t_of_not_equalityBranch D h hZ hIII
  obtain ⟨P, -, hP⟩ := (generatorConjugacy_iff_actionQA45_eq_conj_rhoAct h D).mp
    (generatorConjugacy_of_not_equalityBranch h D hIII)
  have hP' : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹ := fun a => by
    simpa [rhoA, toQAct] using hP a
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
  have hNF_e : (∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
        g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) →
      ∀ (y : G) (hy : y ∈ H z), orderOf y = 2 → IsConj (qH D ⟨y, hy⟩) (uA * tA) →
        ¬ IsConj z y := fun A0 => not_isConj_of_class_ut_of_spin D h hZ hIII A0
  have hNF_t : (∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
        g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) →
      ∀ (y : G) (hy : y ∈ H z), orderOf y = 2 → IsConj (qH D ⟨y, hy⟩) tA → ¬ IsConj z y := by
    intro A0 y hyH hy2 hyt
    have hyy : y * y = 1 := by
      have h1 := pow_orderOf_eq_one y
      rwa [hy2, pow_two] at h1
    have hyJ : y ∉ J z := by
      intro hyJ
      have h1 : qH D ⟨y, hyH⟩ = 1 := (J_mem_iff D ⟨y, hyH⟩).mp hyJ
      rw [h1] at hyt
      exact t_ne_one (congrArg Subtype.val (isConj_one_right.mp hyt))
    obtain ⟨X, hX⟩ := exists_isSylowOf 2 (H z ⊓ centralizer ({y} : Set G))
    exact not_isConj_of_centre_in_J_union h hZ A0 hyH hyJ hyy hX (hZs_t y hyH hyy hyt X hX)
  have hNF_uv : (∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
        g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) →
      ∀ (y : G) (hy : y ∈ H z), orderOf y = 2 → IsConj (qH D ⟨y, hy⟩) (uA * vA) →
        ¬ IsConj z y := by
    intro A0 y hyH hy2 huv
    have hA : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
        g * z * g⁻¹ ∈ H z → g * z * g⁻¹ ∈ ⁅H z, H z⁆ ⊔ centerIn (J z) := fun g hg hgH => by
      rw [A0 g hg hgH]
      exact Subgroup.mem_sup_right (z_mem_centerIn_J h)
    exact not_isConj_of_uv_coset_of_involution D h hZ hJN hV2 hV5 hC5 hA y hyH hy2 huv
  exact parrott_theorem4_of_not_equalityBranch_noV D h hZ hne hIII hB2c hB3 hB6 hB5 hrest_t hZs_t
    hNF_e (fun A0 => not_isConj_of_class_v_of_fusion D h hZ hIII hNF_t hNF_uv A0)

end Certified

end CFSG.RankThree.GF2n.Parrott
