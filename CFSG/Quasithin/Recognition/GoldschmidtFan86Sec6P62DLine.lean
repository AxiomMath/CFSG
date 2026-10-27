module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P62

@[expose] def IsRay (Γ : SimpleGraph V) (r : ℕ → V) : Prop :=
  (∀ n, Γ.Adj (r n) (r (n + 1))) ∧ ∀ n, r n ≠ r (n + 2)

theorem exists_ray (F : FanTree Γ G) {u v : V} (huv : Γ.Adj u v) :
    ∃ r : ℕ → V, r 0 = u ∧ r 1 = v ∧ IsRay Γ r := by
  let S := {p : V × V // Γ.Adj p.1 p.2}
  let nxt : S → S := fun p => ⟨(p.1.2, Classical.choose (F.exists_adj_ne p.1.2 p.1.1)),
    (Classical.choose_spec (F.exists_adj_ne p.1.2 p.1.1)).1⟩
  let seq : ℕ → S := fun n => nxt^[n] ⟨(u, v), huv⟩
  have hs : ∀ n, seq (n + 1) = nxt (seq n) := fun n => Function.iterate_succ_apply' _ _ _
  refine ⟨fun n => (seq n).1.1, rfl, ?_, fun n => ?_, fun n => ?_⟩
  · show (seq 1).1.1 = v
    rw [hs]
    rfl
  · show Γ.Adj (seq n).1.1 (seq (n + 1)).1.1
    rw [hs]
    exact (seq n).2
  · show (seq n).1.1 ≠ (seq (n + 1 + 1)).1.1
    rw [hs (n + 1), hs n]
    exact (Classical.choose_spec (F.exists_adj_ne (seq n).1.2 (seq n).1.1)).2.symm

theorem IsRay.shift {r : ℕ → V} (h : IsRay Γ r) (m : ℕ) : IsRay Γ fun n => r (n + m) := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · have := h.1 (n + m)
    rwa [show n + m + 1 = n + 1 + m by omega] at this
  · have := h.2 (n + m)
    rwa [show n + m + 2 = n + 2 + m by omega] at this

theorem exists_ray_through (F : FanTree Γ G) {n : ℕ} (P : Arc Γ n) (hn : 1 ≤ n) :
    ∃ f : ℕ → V, (∀ k, k ≤ n → f k = P.vert k) ∧ IsRay Γ f := by
  have hlast : Γ.Adj (P.vert (n - 1)) (P.vert n) := by
    have := P.adj (n - 1) (by omega)
    rwa [Nat.sub_add_cancel hn] at this
  obtain ⟨r, hr0, hr1, hr⟩ := exists_ray F hlast
  let f : ℕ → V := fun k => if k < n then P.vert k else r (k + 1 - n)
  have hlt : ∀ k, k < n → f k = P.vert k := fun k hk => by simp [f, hk]
  have hge : ∀ k, n - 1 ≤ k → f k = r (k + 1 - n) := by
    intro k hk
    rcases Nat.lt_or_ge k n with h | h
    · have : k = n - 1 := by omega
      subst this
      rw [hlt _ h, show n - 1 + 1 - n = 0 by omega, hr0]
    · simp [f, not_lt.2 h]
  have hfP : ∀ k, k ≤ n → f k = P.vert k := by
    intro k hk
    rcases Nat.lt_or_ge k n with h | h
    · exact hlt k h
    · rw [show k = n by omega, hge n (by omega), show n + 1 - n = 1 by omega, hr1]
  refine ⟨f, hfP, fun k => ?_, fun k => ?_⟩
  · by_cases h : k + 1 < n
    · rw [hlt k (by omega), hlt (k + 1) h]
      exact P.adj k (by omega)
    · rw [hge k (by omega), hge (k + 1) (by omega), show k + 1 + 1 - n = k + 1 - n + 1 by omega]
      exact hr.1 _
  · by_cases h : k + 2 ≤ n
    · rw [hfP k (by omega), hfP (k + 2) h]
      exact P.nb k h
    · rw [hge k (by omega), hge (k + 2) (by omega), show k + 2 + 1 - n = k + 1 - n + 2 by omega]
      exact hr.2 _

@[expose] def raysVert (f q : ℕ → V) (i : ℤ) : V := if 0 ≤ i then f i.toNat else q (-i).toNat

theorem raysVert_nonneg (f q : ℕ → V) {i : ℤ} (hi : 0 ≤ i) : raysVert f q i = f i.toNat := by
  simp [raysVert, hi]

theorem raysVert_nonpos (f q : ℕ → V) (h0 : q 0 = f 0) {i : ℤ} (hi : i ≤ 0) :
    raysVert f q i = q (-i).toNat := by
  rcases hi.eq_or_lt with rfl | h
  · simp [raysVert, h0]
  · simp [raysVert, not_le.2 h]

@[expose] def lineOfRays (f q : ℕ → V) (hf : IsRay Γ f) (hq : IsRay Γ q) (h0 : q 0 = f 0)
    (h1 : q 1 ≠ f 1) : Line Γ where
  vert := raysVert f q
  adj i := by
    by_cases hi : 0 ≤ i
    · rw [raysVert_nonneg f q hi, raysVert_nonneg f q (i := i + 1) (by omega),
        show (i + 1).toNat = i.toNat + 1 by omega]
      exact hf.1 _
    · rw [raysVert_nonpos f q h0 (by omega), raysVert_nonpos f q h0 (i := i + 1) (by omega),
        show (-i).toNat = (-(i + 1)).toNat + 1 by omega]
      exact (hq.1 _).symm
  nb i := by
    by_cases hi : 0 ≤ i
    · rw [raysVert_nonneg f q hi, raysVert_nonneg f q (i := i + 2) (by omega),
        show (i + 2).toNat = i.toNat + 2 by omega]
      exact hf.2 _
    · by_cases hi2 : i = -1
      · subst hi2
        rw [raysVert_nonpos f q h0 (by omega), raysVert_nonneg f q (i := -1 + 2) (by omega)]
        simpa using h1
      · rw [raysVert_nonpos f q h0 (by omega), raysVert_nonpos f q h0 (i := i + 2) (by omega),
          show (-i).toNat = (-(i + 2)).toNat + 2 by omega]
        exact (hq.2 _).symm

theorem exists_line_of_arc (F : FanTree Γ G) {n : ℕ} (P : Arc Γ n) (hn : 1 ≤ n) :
    ∃ ℓ : Line Γ, ∀ k : ℕ, k ≤ n → ℓ.vert (k : ℤ) = P.vert k := by
  obtain ⟨f, hfP, hf⟩ := exists_ray_through F P hn
  obtain ⟨q', hq0, hq1, hq'⟩ := exists_ray F (P.adj 0 (by omega)).symm
  refine ⟨lineOfRays f (fun m => q' (m + 1)) hf (hq'.shift 1) ?_ ?_, fun k hk => ?_⟩
  · show q' 1 = f 0
    rw [hfP 0 (by omega), hq1]
  · show q' 2 ≠ f 1
    rw [hfP 1 hn, ← hq0]
    exact (hq'.2 0).symm
  · show raysVert f (fun m => q' (m + 1)) (k : ℤ) = P.vert k
    rw [raysVert_nonneg _ _ (by positivity), Int.toNat_natCast, hfP k hk]

end P62

end CFSG.Quasithin.Fan86
