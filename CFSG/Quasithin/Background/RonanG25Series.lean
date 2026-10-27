module

public import CFSG.Quasithin.Background.RonanG25Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.RonanG25

section Series

variable {G : Type} [Group G] {F : Type} [Field F] {X : Subgroup G} {ord : Bool}

theorem FactorNatural.card [Finite G] {A B : Subgroup G} (hAB : A ≤ B)
    (h : FactorNatural F X A B) : Nat.card B = Nat.card F ^ 2 * Nat.card A := by
  obtain ⟨φ, β, hφs, hφk, -, -, -⟩ := h
  have hker : φ.ker = A.subgroupOf B := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφk]
  have hM : Nat.card (Multiplicative (Fin 2 → F)) = Nat.card F ^ 2 := by
    rw [← Nat.card_congr Multiplicative.ofAdd, Nat.card_fun, Nat.card_fin]
  have hrange : Nat.card φ.range = Nat.card F ^ 2 := by
    rw [MonoidHom.range_eq_top.mpr hφs, Subgroup.card_top, hM]
  have h1 := Subgroup.card_mul_index (H := φ.ker)
  rw [Subgroup.index_ker, hrange, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv] at h1
  rw [← h1]
  ring

theorem FactorNatural.factorTwo [Finite G] {A B : Subgroup G} (hAB : A ≤ B)
    (hF : ∃ m : ℕ, 0 < m ∧ Nat.card F = 2 ^ m) (h : FactorNatural F X A B) : FactorTwo A B := by
  obtain ⟨m, hm, hFm⟩ := hF
  refine ⟨2 * m, by omega, ?_⟩
  rw [FactorNatural.card hAB h, hFm]
  ring

private def consSeries (A : Subgroup G) (Ps : ℕ → Subgroup G) : ℕ → Subgroup G
  | 0 => A
  | j + 1 => Ps j

private theorem card_filter_fin_eq (k : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun i : Fin k => p i)).card =
      ∑ i ∈ Finset.range k, (if p i then 1 else 0) := by
  rw [Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if p i then 1 else 0) k

open Classical in
private theorem chain_series [Finite G] (hF : ∃ m : ℕ, 0 < m ∧ Nat.card F = 2 ^ m)
    {A C : Subgroup G} {a b : ℕ} (h : ChainCounts F X ord A C a b) :
    ∃ (k : ℕ) (Ps : ℕ → Subgroup G), Ps 0 = A ∧ Ps k = C ∧
      (∀ i < k, ChiefStep X (Ps i) (Ps (i + 1))) ∧ (∀ i ≤ k, Inv X (Ps i)) ∧
      (∑ i ∈ Finset.range k, (if FactorNatural F X (Ps i) (Ps (i + 1)) then 1 else 0)) = a ∧
      (∑ i ∈ Finset.range k, (if FactorTwo (Ps i) (Ps (i + 1)) ∧
          ¬ FactorCentral X (Ps i) (Ps (i + 1)) ∧ ¬ FactorNatural F X (Ps i) (Ps (i + 1))
        then 1 else 0)) = b ∧
      (∀ i < k, FactorTwo (Ps i) (Ps (i + 1)) → ¬ FactorCentral X (Ps i) (Ps (i + 1)) →
        ¬ FactorNatural F X (Ps i) (Ps (i + 1)) →
        Nat.card (Ps (i + 1)) = Nat.card F * Nat.card (Ps i)) ∧
      (∀ i < k, ¬ FactorCentral X (Ps i) (Ps (i + 1)) → ¬ FactorNatural F X (Ps i) (Ps (i + 1)) →
        FactorTwo (Ps i) (Ps (i + 1)) ∨ ord = true) := by
  obtain ⟨m, hm, hFm⟩ := hF
  have hF2 : 2 ≤ Nat.card F := by
    rw [hFm]
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hFm]; positivity)
  induction h with
  | refl A₀ hA =>
    refine ⟨0, fun _ => A₀, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i),
      fun i hi => ?_, by simp, by simp, fun i hi => absurd hi (Nat.not_lt_zero i),
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    exact hA
  | @natural A₁ B₁ C₁ a₁ b₁ hs hn rest ih =>
    obtain ⟨k, Ps, h0, hk, hsteps, hinv, ha, hb, hd, hT⟩ := ih
    have e0 : FactorNatural F X A₁ (Ps 0) := by
      rw [h0]
      exact hn
    have e0B : ¬ (FactorTwo A₁ (Ps 0) ∧ ¬ FactorCentral X A₁ (Ps 0) ∧
        ¬ FactorNatural F X A₁ (Ps 0)) := fun hh => hh.2.2 e0
    refine ⟨k + 1, consSeries A₁ Ps, rfl, hk, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        show ChiefStep X A₁ (Ps 0)
        rw [h0]
        exact hs
      | succ j => exact hsteps j (by omega)
    · intro i hi
      cases i with
      | zero => exact hs.invA
      | succ j => exact hinv j (by omega)
    · rw [Finset.sum_range_succ']
      show (∑ i ∈ Finset.range k, (if FactorNatural F X (Ps i) (Ps (i + 1)) then 1 else 0))
        + (if FactorNatural F X A₁ (Ps 0) then 1 else 0) = a₁ + 1
      rw [if_pos e0, ha]
    · rw [Finset.sum_range_succ']
      show (∑ i ∈ Finset.range k, (if FactorTwo (Ps i) (Ps (i + 1)) ∧
          ¬ FactorCentral X (Ps i) (Ps (i + 1)) ∧ ¬ FactorNatural F X (Ps i) (Ps (i + 1))
        then 1 else 0)) + (if FactorTwo A₁ (Ps 0) ∧ ¬ FactorCentral X A₁ (Ps 0) ∧
          ¬ FactorNatural F X A₁ (Ps 0) then 1 else 0) = b₁
      rw [if_neg e0B, add_zero]
      exact hb
    · intro i hi hT' hC' hN'
      cases i with
      | zero => exact absurd e0 hN'
      | succ j => exact hd j (by omega) hT' hC' hN'
    · intro i hi hC' hN'
      cases i with
      | zero => exact absurd e0 hN'
      | succ j => exact hT j (by omega) hC' hN'
  | @additional A₁ B₁ C₁ a₁ b₁ hs habel hc hcard rest ih =>
    obtain ⟨k, Ps, h0, hk, hsteps, hinv, ha, hb, hd, hT⟩ := ih
    have hAB : A₁ ≤ B₁ := hs.lt.le
    have hN0 : ¬ FactorNatural F X A₁ B₁ := by
      intro hN
      have e := FactorNatural.card hAB hN
      rw [hcard] at e
      have hA : 0 < Nat.card A₁ := Nat.card_pos
      have hsq : Nat.card F = Nat.card F ^ 2 := Nat.eq_of_mul_eq_mul_right hA e
      nlinarith
    have hT0 : FactorTwo A₁ B₁ := ⟨m, hm, by rw [hcard, hFm]⟩
    have e0N : ¬ FactorNatural F X A₁ (Ps 0) := by
      rw [h0]
      exact hN0
    have e0B : FactorTwo A₁ (Ps 0) ∧ ¬ FactorCentral X A₁ (Ps 0) ∧
        ¬ FactorNatural F X A₁ (Ps 0) := by
      rw [h0]
      exact ⟨hT0, hc, hN0⟩
    have e0card : Nat.card (Ps 0) = Nat.card F * Nat.card A₁ := by
      rw [h0]
      exact hcard
    refine ⟨k + 1, consSeries A₁ Ps, rfl, hk, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        show ChiefStep X A₁ (Ps 0)
        rw [h0]
        exact hs
      | succ j => exact hsteps j (by omega)
    · intro i hi
      cases i with
      | zero => exact hs.invA
      | succ j => exact hinv j (by omega)
    · rw [Finset.sum_range_succ']
      show (∑ i ∈ Finset.range k, (if FactorNatural F X (Ps i) (Ps (i + 1)) then 1 else 0))
        + (if FactorNatural F X A₁ (Ps 0) then 1 else 0) = a₁
      rw [if_neg e0N, add_zero]
      exact ha
    · rw [Finset.sum_range_succ']
      show (∑ i ∈ Finset.range k, (if FactorTwo (Ps i) (Ps (i + 1)) ∧
          ¬ FactorCentral X (Ps i) (Ps (i + 1)) ∧ ¬ FactorNatural F X (Ps i) (Ps (i + 1))
        then 1 else 0)) + (if FactorTwo A₁ (Ps 0) ∧ ¬ FactorCentral X A₁ (Ps 0) ∧
          ¬ FactorNatural F X A₁ (Ps 0) then 1 else 0) = b₁ + 1
      rw [if_pos e0B, hb]
    · intro i hi hT' hC' hN'
      cases i with
      | zero => exact e0card
      | succ j => exact hd j (by omega) hT' hC' hN'
    · intro i hi hC' hN'
      cases i with
      | zero => exact Or.inl e0B.1
      | succ j => exact hT j (by omega) hC' hN'
  | @central A₁ B₁ C₁ a₁ b₁ hs hc _p _hp _hcard _rest ih =>
    obtain ⟨k, Ps, h0, hk, hsteps, hinv, ha, hb, hd, hT⟩ := ih
    have hAB : A₁ ≤ B₁ := hs.lt.le
    have hN0 : ¬ FactorNatural F X A₁ B₁ := fun hN => FactorNatural.not_central hAB hN hc
    have e0N : ¬ FactorNatural F X A₁ (Ps 0) := by
      rw [h0]
      exact hN0
    have e0C : FactorCentral X A₁ (Ps 0) := by
      rw [h0]
      exact hc
    have e0B : ¬ (FactorTwo A₁ (Ps 0) ∧ ¬ FactorCentral X A₁ (Ps 0) ∧
        ¬ FactorNatural F X A₁ (Ps 0)) := fun hh => hh.2.1 e0C
    refine ⟨k + 1, consSeries A₁ Ps, rfl, hk, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        show ChiefStep X A₁ (Ps 0)
        rw [h0]
        exact hs
      | succ j => exact hsteps j (by omega)
    · intro i hi
      cases i with
      | zero => exact hs.invA
      | succ j => exact hinv j (by omega)
    · rw [Finset.sum_range_succ']
      show (∑ i ∈ Finset.range k, (if FactorNatural F X (Ps i) (Ps (i + 1)) then 1 else 0))
        + (if FactorNatural F X A₁ (Ps 0) then 1 else 0) = a₁
      rw [if_neg e0N, add_zero]
      exact ha
    · rw [Finset.sum_range_succ']
      show (∑ i ∈ Finset.range k, (if FactorTwo (Ps i) (Ps (i + 1)) ∧
          ¬ FactorCentral X (Ps i) (Ps (i + 1)) ∧ ¬ FactorNatural F X (Ps i) (Ps (i + 1))
        then 1 else 0)) + (if FactorTwo A₁ (Ps 0) ∧ ¬ FactorCentral X A₁ (Ps 0) ∧
          ¬ FactorNatural F X A₁ (Ps 0) then 1 else 0) = b₁
      rw [if_neg e0B, add_zero]
      exact hb
    · intro i hi hT' hC' hN'
      cases i with
      | zero => exact absurd e0C hC'
      | succ j => exact hd j (by omega) hT' hC' hN'
    · intro i hi hC' hN'
      cases i with
      | zero => exact absurd e0C hC'
      | succ j => exact hT j (by omega) hC' hN'
  | @other A₁ B₁ C₁ a₁ b₁ hord hs h2' rest ih =>
    obtain ⟨k, Ps, h0, hk, hsteps, hinv, ha, hb, hd, hT⟩ := ih
    have hAB : A₁ ≤ B₁ := hs.lt.le
    have hN0 : ¬ FactorNatural F X A₁ B₁ := fun hN =>
      h2' (FactorNatural.factorTwo hAB ⟨m, hm, hFm⟩ hN)
    have e0N : ¬ FactorNatural F X A₁ (Ps 0) := by
      rw [h0]
      exact hN0
    have e0T : ¬ FactorTwo A₁ (Ps 0) := by
      rw [h0]
      exact h2'
    have e0B : ¬ (FactorTwo A₁ (Ps 0) ∧ ¬ FactorCentral X A₁ (Ps 0) ∧
        ¬ FactorNatural F X A₁ (Ps 0)) := fun hh => e0T hh.1
    refine ⟨k + 1, consSeries A₁ Ps, rfl, hk, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        show ChiefStep X A₁ (Ps 0)
        rw [h0]
        exact hs
      | succ j => exact hsteps j (by omega)
    · intro i hi
      cases i with
      | zero => exact hs.invA
      | succ j => exact hinv j (by omega)
    · rw [Finset.sum_range_succ']
      show (∑ i ∈ Finset.range k, (if FactorNatural F X (Ps i) (Ps (i + 1)) then 1 else 0))
        + (if FactorNatural F X A₁ (Ps 0) then 1 else 0) = a₁
      rw [if_neg e0N, add_zero]
      exact ha
    · rw [Finset.sum_range_succ']
      show (∑ i ∈ Finset.range k, (if FactorTwo (Ps i) (Ps (i + 1)) ∧
          ¬ FactorCentral X (Ps i) (Ps (i + 1)) ∧ ¬ FactorNatural F X (Ps i) (Ps (i + 1))
        then 1 else 0)) + (if FactorTwo A₁ (Ps 0) ∧ ¬ FactorCentral X A₁ (Ps 0) ∧
          ¬ FactorNatural F X A₁ (Ps 0) then 1 else 0) = b₁
      rw [if_neg e0B, add_zero]
      exact hb
    · intro i hi hT' hC' hN'
      cases i with
      | zero => exact absurd hT' e0T
      | succ j => exact hd j (by omega) hT' hC' hN'
    · intro i hi hC' hN'
      cases i with
      | zero => exact Or.inr hord
      | succ j => exact hT j (by omega) hC' hN'

open Classical in
theorem ChainCounts.hasChiefCounts [Finite G] (hF : ∃ m : ℕ, 0 < m ∧ Nat.card F = 2 ^ m)
    {P : Subgroup G} {a b : ℕ} (h : ChainCounts F X false ⊥ P a b) :
    HasChiefCounts F X P a b := by
  obtain ⟨k, Ps, h0, hk, hsteps, hinv, ha, hb, hd, hT⟩ := chain_series hF h
  refine ⟨k, Ps, ⟨h0, hk, fun i hi => (hsteps i hi).lt.le, fun i hi => (hsteps i hi).lt,
    fun i hi => hinv i hi, fun i hi => (hsteps i hi).normal, fun i hi => (hsteps i hi).simple⟩,
    ?_, ?_, ?_⟩
  · exact (card_filter_fin_eq k (fun i => FactorNatural F X (Ps i) (Ps (i + 1)))).trans ha
  · refine (card_filter_fin_eq k (fun i => ¬ FactorCentral X (Ps i) (Ps (i + 1)) ∧
        ¬ FactorNatural F X (Ps i) (Ps (i + 1)))).trans ?_
    rw [← hb]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i < k := Finset.mem_range.mp hi
    by_cases hC : FactorCentral X (Ps i) (Ps (i + 1))
    · simp [hC]
    · by_cases hN : FactorNatural F X (Ps i) (Ps (i + 1))
      · simp [hN]
      · have hTi : FactorTwo (Ps i) (Ps (i + 1)) :=
          (hT i hi' hC hN).resolve_right (by simp)
        simp [hC, hN, hTi]
  · intro i hC hN
    exact hd i.1 i.2 ((hT i.1 i.2 hC hN).resolve_right (by simp)) hC hN

open Classical in
theorem ChainCounts.hasOrdinaryTwoChiefCounts [Finite G]
    (hF : ∃ m : ℕ, 0 < m ∧ Nat.card F = 2 ^ m) {a b : ℕ}
    (h : ChainCounts F X true ⊥ X a b) : HasOrdinaryTwoChiefCounts F X a b := by
  obtain ⟨k, Ps, h0, hk, hsteps, hinv, ha, hb, hd, -⟩ := chain_series hF h
  refine ⟨k, Ps, ⟨h0, hk, fun i hi => (hsteps i hi).lt.le, fun i hi => (hsteps i hi).lt,
    fun i hi => hinv i hi, fun i hi => (hsteps i hi).normal, fun i hi => (hsteps i hi).simple⟩,
    ?_, ?_, ?_⟩
  · refine Eq.trans ?_ ha
    refine (card_filter_fin_eq k (fun i => FactorTwo (Ps i) (Ps (i + 1)) ∧
        FactorNatural F X (Ps i) (Ps (i + 1)))).trans ?_
    refine Finset.sum_congr rfl (fun i hi => ?_)
    by_cases hN : FactorNatural F X (Ps i) (Ps (i + 1))
    · have hT' : FactorTwo (Ps i) (Ps (i + 1)) :=
        FactorNatural.factorTwo (hsteps i (Finset.mem_range.mp hi)).lt.le hF hN
      simp [hN, hT']
    · simp [hN]
  · exact (card_filter_fin_eq k (fun i => FactorTwo (Ps i) (Ps (i + 1)) ∧
        ¬ FactorCentral X (Ps i) (Ps (i + 1)) ∧ ¬ FactorNatural F X (Ps i) (Ps (i + 1)))).trans hb
  · intro i hT' hC hN
    exact hd i.1 i.2 hT' hC hN

end Series

end CFSG.Quasithin.RonanG25
