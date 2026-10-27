module

public import CFSG.Quasithin.Background.F1Basic

public section

namespace CFSG.Quasithin.Kleidman.F204

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_of_le_sup_commutator {Q M H : Subgroup G} (hQ : IsPGroup 2 Q) (hMQ : M ≤ Q)
    (hHQ : Q ≤ Subgroup.normalizer (H : Set G)) (h : M ≤ H ⊔ ⁅M, Q⁆) : M ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ k : ℕ, M ≤ H ⊔ Q.lowerCentralSeries k := by
    intro k
    induction k with
    | zero => exact le_sup_of_le_right (by rw [Subgroup.lowerCentralSeries_zero]; exact hMQ)
    | succ k ih =>
      have hcomm : ⁅M, Q⁆ ≤ H ⊔ Q.lowerCentralSeries (k + 1) := by
        rw [Subgroup.commutator_le]
        intro m hm q hq
        have hγQ : Q.lowerCentralSeries k ≤ Q := by
          clear ih hm hHQ h
          induction k with
          | zero => rw [Subgroup.lowerCentralSeries_zero]
          | succ k ihk =>
            rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_le]
            intro x hx y hy
            have hx' := ihk hx
            rw [commutatorElement_def]
            exact Q.mul_mem (Q.mul_mem (Q.mul_mem hx' hy) (Q.inv_mem hx')) (Q.inv_mem hy)
        obtain ⟨a, ha, c, hc, rfl⟩ :=
          (F1.mem_sup_iff_exists_mul_of_normalizes (hγQ.trans hHQ)).mp (ih hm)
        have e : ⁅a * c, q⁆ = a * ⁅c, q⁆ * a⁻¹ * ⁅a, q⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_)
          (Subgroup.inv_mem _ ?_)) ?_
        · exact Subgroup.mem_sup_left ha
        · refine Subgroup.mem_sup_right ?_
          rw [Subgroup.lowerCentralSeries_succ]
          exact Subgroup.commutator_mem_commutator hc hq
        · exact Subgroup.mem_sup_left ha
        · refine Subgroup.mem_sup_left ?_
          have e2 : ⁅a, q⁆ = a * (q * a⁻¹ * q⁻¹) := by
            simp only [commutatorElement_def]; group
          rw [e2]
          refine Subgroup.mul_mem _ ha ?_
          have := (Subgroup.mem_normalizer_iff.mp (hHQ hq) a⁻¹).mp (Subgroup.inv_mem _ ha)
          simpa using this
      exact h.trans (sup_le le_sup_left hcomm)
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries Q).mp hQ.isNilpotent
  have := key n
  rwa [hn, sup_bot_eq] at this

theorem conj_mem_commutator {A B : Subgroup G} {g : G} (hA : ∀ x ∈ A, g * x * g⁻¹ ∈ A)
    (hB : ∀ x ∈ B, g * x * g⁻¹ ∈ B) {x : G} (hx : x ∈ ⁅A, B⁆) : g * x * g⁻¹ ∈ ⁅A, B⁆ := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.commutator_mem_commutator (hA a ha) (hB b hb)
  | one => simp
  | mul y z _ _ ihy ihz =>
    have e : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
    rw [e]; exact Subgroup.mul_mem _ ihy ihz
  | inv y _ ihy =>
    have e : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [e]; exact Subgroup.inv_mem _ ihy

theorem const_of_erase_prod {A : Type*} [CommGroup A] (hA2 : ∀ a : A, a * a = 1) {Δ : Type*}
    [Fintype Δ] [DecidableEq Δ] (hΔ : Fintype.card Δ = 5) (f : Δ → A) (x : Δ)
    (h : ∀ γ, γ ≠ x → ∏ r ∈ Finset.univ.erase γ, f r = 1) : ∀ p, f p = f x := by
  set T := ∏ r, f r with hT
  have hγ : ∀ γ, γ ≠ x → f γ = T := by
    intro γ hγx
    have := Finset.mul_prod_erase Finset.univ f (Finset.mem_univ γ)
    rw [h γ hγx, mul_one] at this
    exact this
  have hT2 : T * T = 1 := hA2 T
  have hx : f x = T := by
    have h1 := Finset.mul_prod_erase Finset.univ f (Finset.mem_univ x)
    have h2 : ∏ r ∈ Finset.univ.erase x, f r = T ^ 4 := by
      rw [Finset.prod_congr rfl (fun r hr => hγ r (Finset.ne_of_mem_erase hr))]
      rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hΔ]
    rw [h2] at h1
    have h4 : T ^ 4 = 1 := by
      have : T ^ 4 = (T * T) * (T * T) := by
        have e1 : T * T = T ^ 2 := (sq T).symm
        rw [e1, ← pow_add]
      rw [this, hT2, one_mul]
    rw [h4, mul_one] at h1
    exact h1
  intro p
  by_cases hp : p = x
  · rw [hp]
  · rw [hγ p hp, hx]

theorem prod_erase_four {A : Type*} [CommGroup A] {Δ : Type*} [Fintype Δ] [DecidableEq Δ]
    (hΔ : Fintype.card Δ = 5) (f : Δ → A) {γ p0 p1 p2 p3 : Δ} (h01 : p0 ≠ p1) (h02 : p0 ≠ p2)
    (h03 : p0 ≠ p3) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) (hg0 : p0 ≠ γ) (hg1 : p1 ≠ γ)
    (hg2 : p2 ≠ γ) (hg3 : p3 ≠ γ) :
    ∏ r ∈ Finset.univ.erase γ, f r = f p0 * f p1 * f p2 * f p3 := by
  have hcard : ({p0, p1, p2, p3} : Finset Δ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h01, h02, h03]),
      Finset.card_insert_of_notMem (by simp [h12, h13]),
      Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
  have hsub : ({p0, p1, p2, p3} : Finset Δ) ⊆ Finset.univ.erase γ := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rw [Finset.mem_erase]
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨hg0, Finset.mem_univ _⟩
    · exact ⟨hg1, Finset.mem_univ _⟩
    · exact ⟨hg2, Finset.mem_univ _⟩
    · exact ⟨hg3, Finset.mem_univ _⟩
  have hcard' : (Finset.univ.erase γ).card = 4 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ γ), Finset.card_univ, hΔ]
  have heq : ({p0, p1, p2, p3} : Finset Δ) = Finset.univ.erase γ :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard'])
  rw [← heq, Finset.prod_insert (by simp [h01, h02, h03]),
    Finset.prod_insert (by simp [h12, h13]), Finset.prod_insert (by simp [h23]),
    Finset.prod_singleton]
  simp only [mul_assoc]

end CFSG.Quasithin.Kleidman.F204
