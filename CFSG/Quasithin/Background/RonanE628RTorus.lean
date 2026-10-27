module

public import CFSG.Quasithin.Background.RonanE628
public import CFSG.Quasithin.Background.RonanE628RCount

public section

namespace CFSG.Quasithin.RonanE628

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E6
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def UniqueMBorelTorus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V : Subgroup G), HypE61 T M V → IsUniqueM T M →
    ∃ P K : Subgroup G, IsElemAbelian 2 P ∧ P ≤ T ∧
      (∀ t ∈ T, t * t = 1 → t ∈ P) ∧ K ≤ M ∧ IsCyclic K ∧ Odd (Nat.card K) ∧
      K ≤ Subgroup.normalizer (T : Set G) ∧ K ≤ Subgroup.normalizer (P : Set G) ∧
      (∀ p ∈ P, ∀ q ∈ P, p ≠ 1 → q ≠ 1 → ∃ k ∈ K, k⁻¹ * p * k = q)

@[expose] def UniqueMBorelTorusR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V : Subgroup G), HypE61 T M V → 1 < E3.rParam V →
    IsUniqueM T M →
    ∃ P K : Subgroup G, IsElemAbelian 2 P ∧ P ≤ T ∧
      (∀ t ∈ T, t * t = 1 → t ∈ P) ∧ K ≤ M ∧ IsCyclic K ∧ Odd (Nat.card K) ∧
      K ≤ Subgroup.normalizer (T : Set G) ∧ K ≤ Subgroup.normalizer (P : Set G) ∧
      (∀ p ∈ P, ∀ q ∈ P, p ≠ 1 → q ≠ 1 → ∃ k ∈ K, k⁻¹ * p * k = q)

theorem uniqueMBorelTorusR_of (hBT : UniqueMBorelTorus) : UniqueMBorelTorusR :=
  fun G _ _ T M V h _ hu => hBT G T M V h hu

theorem alphaBetaNonempty_of_isUniqueM_R (hBT : UniqueMBorelTorusR) {T M V : Subgroup G}
    (h : HypE61 T M V) (hr : 1 < E3.rParam V) (hu : IsUniqueM T M) :
    AlphaBetaNonempty M V := by
  obtain ⟨P, K, hP, hPT, hinv, hKM, hKc, hKodd, hKT, hKP, htr⟩ := hBT G T M V h hr hu
  have hVP : V ≤ P := fun v hv => hinv v (h.le hv) (by
    have := h.isElemAbelian.2 v hv
    simpa [sq] using this)
  have hTI : ∀ g ∈ K, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conjSubgroup V g = ⊥ :=
    fun g hg hgN => h.tiSet.2 g (hKM hg) hgN
  obtain ⟨Y, hYKN, hYc, hYcard⟩ := ti_counting hP hVP h.ne_bot hKP hKc htr hTI
  have hYK : Y ≤ K := fun y hy => (hYKN hy).1
  have hYN : Y ≤ Subgroup.normalizer (V : Set G) := fun y hy => (hYKN hy).2
  have hV2 : Nat.card V = 2 ^ E3.mQuot V ⊥ := by
    have := E3.card_eq_two_pow_mul h.isPGroup_V (bot_le : (⊥ : Subgroup G) ≤ V)
    simpa using this
  have hc : 2 ≤ E3.mQuot V ⊥ := by
    have h1 : (1 : ℕ∞) < (E3.mQuot V ⊥ : ℕ∞) := lt_of_lt_of_le hr (rParam_le_mQuot_bot h)
    have h2 : 1 < E3.mQuot V ⊥ := by exact_mod_cast h1
    omega
  refine alphaBetaNonempty_of_torus h hc (Y := Y) (B := Y) le_rfl ?_ hYc (by rw [hYcard, hV2]) ?_ ?_ ?_
  · exact le_inf (hYK.trans hKM) hYN
  · intro a ha b hb
    letI : CommGroup ↥Y := IsCyclic.commGroup
    have := (mul_comm (⟨a, ha⟩ : Y) ⟨b, hb⟩)
    exact congrArg Subtype.val this
  · exact Odd.of_dvd_nat hKodd (Subgroup.card_dvd_of_le hYK)
  · ext x
    constructor
    · rintro ⟨y, hy, t, ht, rfl⟩
      refine ⟨y * t * y⁻¹, ?_, y, hy, by group⟩
      exact (Subgroup.mem_normalizer_iff.1 (hKT (hYK hy)) t).1 ht
    · rintro ⟨t, ht, y, hy, rfl⟩
      refine ⟨y, hy, y⁻¹ * t * y, ?_, by group⟩
      have := (Subgroup.mem_normalizer_iff.1 (hKT (hYK (Y.inv_mem hy))) t).1 ht
      simpa using this

@[expose] def ResidualUniqueness : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V : Subgroup G), HypE61 T M V → 1 < E3.rParam V →
    thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G) →
    (∀ U : Subgroup G, U ≤ V → U ≠ ⊥ →
      Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G)) →
    IsUniqueM T M

theorem hres_of_R (hBT : UniqueMBorelTorusR) (hRU : ResidualUniqueness) {T M V : Subgroup G}
    (h : HypE61 T M V) (hr : 1 < E3.rParam V)
    (hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G))
    (hC : ∀ U : Subgroup G, U ≤ V → U ≠ ⊥ →
      Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    AlphaBetaNonempty M V :=
  alphaBetaNonempty_of_isUniqueM_R hBT h hr (hRU G T M V h hr hJ hC)

end CFSG.Quasithin.RonanE628
