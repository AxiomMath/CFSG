module

public import CFSG.Quasithin.Recognition.F4Paths
public import CFSG.Quasithin.Background.F3Geodesic

public section

namespace CFSG.Quasithin

universe u

namespace GPath

variable {V : Type u} {Γ : SimpleGraph V} {m : ℕ}

@[expose] def cycSeq (p q : GPath Γ m) (i : ℕ) : V :=
  if i % (2 * m) ≤ m then p (i % (2 * m)) else q (2 * m - i % (2 * m))

theorem cycSeq_per (p q : GPath Γ m) (i : ℕ) : cycSeq p q (i + 2 * m) = cycSeq p q i := by
  unfold cycSeq
  rw [Nat.add_mod_right]

theorem cycSeq_per' (p q : GPath Γ m) : ∀ i, cycSeq p q (i + 2 * m) = cycSeq p q i :=
  cycSeq_per p q

theorem cycSeq_of_le (p q : GPath Γ m) (hm : 1 ≤ m) {i : ℕ} (hi : i ≤ m) : cycSeq p q i = p i := by
  have h : i % (2 * m) = i := Nat.mod_eq_of_lt (by omega)
  unfold cycSeq
  rw [h]
  simp [hi]

theorem cycSeq_of_ge (p q : GPath Γ m) (hm : 1 ≤ m) (h0 : p 0 = q 0) (hmm : p m = q m) {i : ℕ}
    (hi : m ≤ i) (hi2 : i ≤ 2 * m) : cycSeq p q i = q (2 * m - i) := by
  by_cases h2 : i = 2 * m
  · subst h2
    have : cycSeq p q (0 + 2 * m) = cycSeq p q 0 := cycSeq_per p q 0
    rw [zero_add] at this
    rw [this, cycSeq_of_le p q hm (Nat.zero_le m), Nat.sub_self, h0]
  · have h : i % (2 * m) = i := Nat.mod_eq_of_lt (by omega)
    unfold cycSeq
    rw [h]
    by_cases hle : i ≤ m
    · have him : i = m := by omega
      simp only [hle, ↓reduceIte]
      rw [him, hmm, show 2 * m - m = m by omega]
    · simp only [hle, ↓reduceIte]

theorem cycSeq_adj (p q : GPath Γ m) (hm : 1 ≤ m) (h0 : p 0 = q 0) (hmm : p m = q m) (i : ℕ) :
    Γ.Adj (cycSeq p q i) (cycSeq p q (i + 1)) := by
  have key : ∀ r, r < 2 * m → Γ.Adj (cycSeq p q r) (cycSeq p q (r + 1)) := by
    intro r hr
    by_cases h1 : r + 1 ≤ m
    · rw [cycSeq_of_le p q hm (by omega), cycSeq_of_le p q hm h1]
      exact p.adj r (by omega)
    · rw [cycSeq_of_ge p q hm h0 hmm (by omega) (by omega),
        cycSeq_of_ge p q hm h0 hmm (by omega) (by omega)]
      have := (q.adj (2 * m - (r + 1)) (by omega)).symm
      rwa [show 2 * m - (r + 1) + 1 = 2 * m - r by omega] at this
  have hpos : 0 < 2 * m := by omega
  have hk : ∀ a k : ℕ, cycSeq p q (a + k * (2 * m)) = cycSeq p q a := fun a k =>
    Function.Periodic.nat_mul (fun x => cycSeq_per p q x) k a
  have hdecomp : i = i % (2 * m) + (i / (2 * m)) * (2 * m) := by
    have h := Nat.mod_add_div i (2 * m)
    rw [Nat.mul_comm (2 * m) (i / (2 * m))] at h
    exact h.symm
  have h1 : cycSeq p q i = cycSeq p q (i % (2 * m)) := by
    conv_lhs => rw [hdecomp]
    exact hk _ _
  have h2 : cycSeq p q (i + 1) = cycSeq p q (i % (2 * m) + 1) := by
    have : i + 1 = (i % (2 * m) + 1) + (i / (2 * m)) * (2 * m) := by omega
    rw [this]
    exact hk _ _
  rw [h1, h2]
  exact key _ (Nat.mod_lt _ hpos)

theorem cycSeq_nb (p q : GPath Γ m) (hm : 2 ≤ m) (hp : p.NoBack) (hq : q.NoBack) (h0 : p 0 = q 0)
    (hmm : p m = q m) (h1 : p 1 ≠ q 1) (hm1 : p (m - 1) ≠ q (m - 1)) (i : ℕ) :
    cycSeq p q i ≠ cycSeq p q (i + 2) := by
  have hm' : 1 ≤ m := by omega
  have hpos : 0 < 2 * m := by omega
  have key : ∀ r, r < 2 * m → cycSeq p q r ≠ cycSeq p q (r + 2) := by
    intro r hr
    by_cases ha : r + 2 ≤ m
    · rw [cycSeq_of_le p q hm' (by omega), cycSeq_of_le p q hm' ha]
      exact hp r ha
    · by_cases hb : r + 2 ≤ 2 * m
      · by_cases hc : r + 1 ≤ m
        ·
          have hrm : r = m - 1 := by omega
          rw [cycSeq_of_le p q hm' (by omega),
            cycSeq_of_ge p q hm' h0 hmm (by omega) (by omega)]
          have e : 2 * m - (r + 2) = m - 1 := by omega
          rw [e, hrm]
          exact hm1
        · by_cases hd : r = m
          · rw [hd, cycSeq_of_le p q hm' le_rfl,
              cycSeq_of_ge p q hm' h0 hmm (by omega) (by omega), hmm]
            have h' := hq (m - 2) (by omega)
            rw [show m - 2 + 2 = m by omega] at h'
            rw [show 2 * m - (m + 2) = m - 2 by omega]
            exact fun h => h' h.symm
          · rw [cycSeq_of_ge p q hm' h0 hmm (by omega) (by omega),
              cycSeq_of_ge p q hm' h0 hmm (by omega) (by omega)]
            have := hq (2 * m - (r + 2)) (by omega)
            rw [show 2 * m - (r + 2) + 2 = 2 * m - r by omega] at this
            exact fun h => this h.symm
      ·
        have hr' : r = 2 * m - 1 := by omega
        have e1 : cycSeq p q (r + 2) = p 1 := by
          have := cycSeq_per p q 1
          rw [show 1 + 2 * m = r + 2 by omega] at this
          rw [this, cycSeq_of_le p q hm' hm']
        rw [e1, cycSeq_of_ge p q hm' h0 hmm (by omega) (by omega)]
        have e : 2 * m - r = 1 := by omega
        rw [e]
        exact fun h => h1 h.symm
  have hk : ∀ a k : ℕ, cycSeq p q (a + k * (2 * m)) = cycSeq p q a := fun a k =>
    Function.Periodic.nat_mul (fun x => cycSeq_per p q x) k a
  have hdecomp : i = i % (2 * m) + (i / (2 * m)) * (2 * m) := by
    have h := Nat.mod_add_div i (2 * m)
    rw [Nat.mul_comm (2 * m) (i / (2 * m))] at h
    exact h.symm
  have h1 : cycSeq p q i = cycSeq p q (i % (2 * m)) := by
    conv_lhs => rw [hdecomp]
    exact hk _ _
  have h2 : cycSeq p q (i + 2) = cycSeq p q (i % (2 * m) + 2) := by
    have : i + 2 = (i % (2 * m) + 2) + (i / (2 * m)) * (2 * m) := by omega
    rw [this]
    exact hk _ _
  rw [h1, h2]
  exact key _ (Nat.mod_lt _ hpos)

theorem geod_first_last_ne (hΓ : Γ.Connected) (hU : UniqueGeod Γ m) (hm : 1 ≤ m) {p q : GPath Γ m}
    (hp : p.IsGeodesic) (hq : q.IsGeodesic) (h0 : p 0 = q 0) (hmm : p m = q m) (hne : p ≠ q) :
    p 1 ≠ q 1 ∧ p (m - 1) ≠ q (m - 1) := by
  constructor
  · intro h1
    have e := hU (m - 1) (p.drop 1 hm) (q.drop 1 hm) (hp.drop hΓ 1 hm) (hq.drop hΓ 1 hm)
      (by rw [drop_apply _ _ _ (Nat.zero_le _), drop_apply _ _ _ (Nat.zero_le _)]; simpa using h1)
      (by rw [drop_apply _ _ _ le_rfl, drop_apply _ _ _ le_rfl,
            show 1 + (m - 1) = m by omega]; exact hmm)
      (by omega)
    apply hne
    refine ext' fun i hi => ?_
    by_cases hi0 : i = 0
    · rw [hi0]; exact h0
    · have := congrArg (fun r : GPath Γ (m - 1) => r (i - 1)) e
      rw [drop_apply _ _ _ (by omega), drop_apply _ _ _ (by omega),
        show 1 + (i - 1) = i by omega] at this
      exact this
  · intro h1
    have e := hU (m - 1) (p.take (m - 1) (by omega)) (q.take (m - 1) (by omega))
      (hp.take hΓ _ _) (hq.take hΓ _ _)
      (by rw [take_apply_of_le _ _ _ (Nat.zero_le _), take_apply_of_le _ _ _ (Nat.zero_le _)]; exact h0)
      (by rw [take_apply_of_le _ _ _ le_rfl, take_apply_of_le _ _ _ le_rfl]; exact h1)
      (by omega)
    apply hne
    refine ext' fun i hi => ?_
    by_cases hi1 : i ≤ m - 1
    · have := congrArg (fun r : GPath Γ (m - 1) => r i) e
      rw [take_apply_of_le _ _ _ hi1, take_apply_of_le _ _ _ hi1] at this
      exact this
    · have : i = m := by omega
      rw [this]; exact hmm

theorem polygon_of_two_geods {c : V → Bool} (hΓ : Γ.Connected)
    (hc : ∀ a b, Γ.Adj a b → c a ≠ c b) (hU : UniqueGeod Γ m) (hm : 2 ≤ m) {p q : GPath Γ m}
    (hp : p.IsGeodesic) (hq : q.IsGeodesic) (h0 : p 0 = q 0) (hmm : p m = q m) (hne : p ≠ q) :
    IsPolygon Γ (Set.range (cycSeq p q)) (2 * m) := by
  obtain ⟨h1, h2⟩ := geod_first_last_ne hΓ hU (by omega) hp hq h0 hmm hne
  exact isPolygon_of_periodic hΓ hc hm hU (cycSeq p q) (cycSeq_adj p q (by omega) h0 hmm)
    (cycSeq_nb p q hm (noBack_of_dist_eq hΓ p hp) (noBack_of_dist_eq hΓ q hq) h0 hmm h1 h2)
    (cycSeq_per p q)

section Arcs

variable (z : ℕ → V) (hz : ∀ i, Γ.Adj (z i) (z (i + 1)))

@[expose] def arc₁ (m i : ℕ) : GPath Γ m := seqPath z hz i m

@[expose] def arc₂ (m i : ℕ) : GPath Γ m := seqPathRev z hz (i + 2 * m) m (by omega)

theorem arc₁_zero (m i : ℕ) : arc₁ z hz m i 0 = z i := by
  rw [arc₁, seqPath_apply _ _ _ _ (Nat.zero_le m), add_zero]

theorem arc₁_last (m i : ℕ) : arc₁ z hz m i m = z (i + m) := by
  rw [arc₁, seqPath_apply _ _ _ _ le_rfl]

theorem arc₁_one (m : ℕ) (hm : 1 ≤ m) (i : ℕ) : arc₁ z hz m i 1 = z (i + 1) := by
  rw [arc₁, seqPath_apply _ _ _ _ hm]

theorem arc₂_zero (m : ℕ) (hper : ∀ i, z (i + 2 * m) = z i) (i : ℕ) : arc₂ z hz m i 0 = z i := by
  rw [arc₂, seqPathRev_apply _ _ _ _ _ (Nat.zero_le m), Nat.sub_zero, hper]

theorem arc₂_last (m i : ℕ) : arc₂ z hz m i m = z (i + m) := by
  rw [arc₂, seqPathRev_apply _ _ _ _ _ le_rfl]
  congr 1
  omega

theorem arc₂_one (m : ℕ) (hm : 1 ≤ m) (i : ℕ) : arc₂ z hz m i 1 = z (i + 2 * m - 1) := by
  rw [arc₂, seqPathRev_apply _ _ _ _ _ hm]

theorem arc₁_noBack (hnb : ∀ i, z i ≠ z (i + 2)) (m i : ℕ) : (arc₁ z hz m i).NoBack := by
  intro j hj heq
  rw [arc₁, seqPath_apply _ _ _ _ (by omega), seqPath_apply _ _ _ _ hj] at heq
  apply hnb (i + j)
  rw [← add_assoc] at heq
  simpa [add_assoc] using heq

theorem arc₂_noBack (hnb : ∀ i, z i ≠ z (i + 2)) (m i : ℕ) : (arc₂ z hz m i).NoBack := by
  intro j hj heq
  rw [arc₂, seqPathRev_apply _ _ _ _ _ (by omega), seqPathRev_apply _ _ _ _ _ hj] at heq
  apply hnb (i + 2 * m - (j + 2))
  rw [show i + 2 * m - (j + 2) + 2 = i + 2 * m - j by omega]
  exact heq.symm

theorem arc_ne (hnb : ∀ i, z i ≠ z (i + 2)) (m : ℕ) (hper : ∀ i, z (i + 2 * m) = z i)
    (hm : 1 ≤ m) (i : ℕ) : arc₁ z hz m i ≠ arc₂ z hz m i := by
  intro h
  have h1 := congrArg (fun r : GPath Γ m => r 1) h
  rw [arc₁_one z hz m hm, arc₂_one z hz m hm] at h1
  have h2 := hnb (i + 2 * m - 1)
  rw [show i + 2 * m - 1 + 2 = (i + 1) + 2 * m by omega, hper] at h2
  exact h2 h1.symm

end Arcs

end GPath

end CFSG.Quasithin
