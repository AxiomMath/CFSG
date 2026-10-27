module

public import CFSG.Quasithin.Background.F3Lemma35
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin

universe u

namespace GPath

variable {V : Type u} {Γ : SimpleGraph V} {n : ℕ}

@[expose] def drop (p : GPath Γ n) (k : ℕ) (hk : k ≤ n) : GPath Γ (n - k) where
  toFun i := p (k + min i (n - k))
  adj i hi := by
    have h1 : min i (n - k) = i := min_eq_left hi.le
    have h2 : min (i + 1) (n - k) = i + 1 := min_eq_left hi
    simp only [h1, h2]
    have := p.adj (k + i) (by omega)
    rwa [show k + (i + 1) = k + i + 1 by omega]
  tail i hi := by
    have h1 : min i (n - k) = n - k := min_eq_right hi
    simp [h1]

@[simp] theorem drop_apply (p : GPath Γ n) (k : ℕ) (hk : k ≤ n) {i : ℕ} (hi : i ≤ n - k) :
    p.drop k hk i = p (k + i) := by
  show p (k + min i (n - k)) = p (k + i)
  rw [min_eq_left hi]

@[expose] def rev (p : GPath Γ n) : GPath Γ n where
  toFun i := p (n - min i n)
  adj i hi := by
    have h1 : min i n = i := min_eq_left hi.le
    have h2 : min (i + 1) n = i + 1 := min_eq_left hi
    simp only [h1, h2]
    have := (p.adj (n - (i + 1)) (by omega)).symm
    rwa [show n - (i + 1) + 1 = n - i by omega] at this
  tail i hi := by
    have h1 : min i n = n := min_eq_right hi
    simp [h1]

@[simp] theorem rev_apply (p : GPath Γ n) {i : ℕ} (hi : i ≤ n) : p.rev i = p (n - i) := by
  show p (n - min i n) = p (n - i)
  rw [min_eq_left hi]

theorem rev_rev (p : GPath Γ n) : p.rev.rev = p :=
  ext' fun i hi => by
    rw [rev_apply _ hi, rev_apply _ (by omega)]
    congr 1
    omega

theorem NoBack.rev {p : GPath Γ n} (h : p.NoBack) : p.rev.NoBack := by
  intro i hi heq
  rw [rev_apply _ (by omega), rev_apply _ hi] at heq
  have := h (n - (i + 2)) (by omega)
  apply this
  rw [show n - (i + 2) + 2 = n - i by omega]
  exact heq.symm

theorem NoBack.drop {p : GPath Γ n} (h : p.NoBack) (k : ℕ) (hk : k ≤ n) : (p.drop k hk).NoBack := by
  intro i hi heq
  rw [drop_apply _ _ _ (by omega), drop_apply _ _ _ hi] at heq
  have := h (k + i) (by omega)
  apply this
  rw [show k + (i + 2) = k + (i + 2) from rfl] at heq
  rw [show k + i + 2 = k + (i + 2) by omega]
  exact heq.symm.symm

theorem IsGeodesic.rev {p : GPath Γ n} (h : p.IsGeodesic) : p.rev.IsGeodesic := by
  show Γ.dist (p.rev 0) (p.rev n) = n
  rw [rev_apply _ (by omega), rev_apply _ le_rfl, Nat.sub_zero, Nat.sub_self,
    SimpleGraph.dist_comm]
  exact h

theorem IsGeodesic.drop (hΓ : Γ.Connected) {p : GPath Γ n} (h : p.IsGeodesic) (k : ℕ) (hk : k ≤ n) :
    (p.drop k hk).IsGeodesic := by
  show Γ.dist ((p.drop k hk) 0) ((p.drop k hk) (n - k)) = n - k
  rw [drop_apply _ _ _ (by omega), drop_apply _ _ _ le_rfl, add_zero, Nat.add_sub_cancel' hk]
  have h0 : Γ.dist (p 0) (p n) = n := h
  have h1 := dist_prefix hΓ p h hk
  have h2 : Γ.dist (p 0) (p n) ≤ Γ.dist (p 0) (p k) + Γ.dist (p k) (p n) := hΓ.dist_triangle
  have h3 := dist_le_sub hΓ p hk le_rfl
  omega

section Action

variable {H : Type*} [Group H] [MulAction H V] [GraphAction H Γ]

omit [GraphAction H Γ] in
theorem mem_stabPath_iff {p : GPath Γ n} {g : H} : g ∈ p.stabPath ↔ ∀ i, i ≤ n → g • p i = p i :=
  Iff.rfl

omit [GraphAction H Γ] in
theorem stabPath_rev (p : GPath Γ n) : (p.rev.stabPath : Subgroup H) = p.stabPath := by
  ext g
  rw [mem_stabPath_iff, mem_stabPath_iff]
  constructor
  · intro h i hi
    have := h (n - i) (by omega)
    rwa [rev_apply _ (by omega), show n - (n - i) = i by omega] at this
  · intro h i hi
    rw [rev_apply _ hi]
    exact h _ (by omega)

omit [GraphAction H Γ] in
theorem stabPath_le_drop (p : GPath Γ n) (k : ℕ) (hk : k ≤ n) :
    (p.stabPath : Subgroup H) ≤ (p.drop k hk).stabPath := by
  intro g hg i hi
  rw [drop_apply _ _ _ hi]
  exact hg _ (by omega)

theorem stabPath_smul (g : H) (p : GPath Γ n) :
    ((g • p).stabPath : Subgroup H) = conjSub g (p.stabPath : Subgroup H) := by
  ext h
  rw [mem_conjSub, mem_stabPath_iff, mem_stabPath_iff]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  rw [smul_apply, mul_smul, mul_smul, inv_smul_eq_iff]

omit [GraphAction H Γ] in
theorem stabPath_take_one (p : GPath Γ n) (hn : 1 ≤ n) :
    ((p.take 1 hn).stabPath : Subgroup H) = MulAction.stabilizer H (p 0) ⊓ MulAction.stabilizer H (p 1) := by
  ext g
  rw [mem_stabPath_iff, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact ⟨by simpa [take_apply_of_le _ _ _ (Nat.zero_le 1)] using h 0 (Nat.zero_le 1),
      by simpa [take_apply_of_le _ _ _ le_rfl] using h 1 le_rfl⟩
  · rintro ⟨h0, h1⟩ i hi
    rw [take_apply_of_le _ _ _ hi]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
    · exact h0
    · exact h1

omit [GraphAction H Γ] in
theorem stabPath_le_stabilizer (p : GPath Γ n) {a : V} (ha : p 0 = a) :
    (p.stabPath : Subgroup H) ≤ MulAction.stabilizer H a := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff, ← ha]
  exact hg 0 (Nat.zero_le n)

end Action

section ShiftSnoc

variable {m : ℕ}

@[expose] def shiftSnoc (r : GPath Γ m) (y : V) (h : Γ.Adj (r m) y) : GPath Γ m where
  toFun i := if i < m then r (i + 1) else y
  adj i hi := by
    by_cases h1 : i + 1 < m
    · simp only [hi, h1, ↓reduceIte]
      exact r.adj (i + 1) h1
    · have : i + 1 = m := by omega
      simp only [hi, h1, ↓reduceIte]
      rw [this]
      exact h
  tail i hi := by
    have h1 : ¬ i < m := by omega
    simp [h1]

@[simp] theorem shiftSnoc_apply_lt (r : GPath Γ m) (y : V) (h : Γ.Adj (r m) y) {i : ℕ} (hi : i < m) :
    shiftSnoc r y h i = r (i + 1) := by
  show (if i < m then r (i + 1) else y) = r (i + 1)
  simp [hi]

@[simp] theorem shiftSnoc_last (r : GPath Γ m) (y : V) (h : Γ.Adj (r m) y) :
    shiftSnoc r y h m = y := by
  show (if m < m then r (m + 1) else y) = y
  simp

theorem NoBack.shiftSnoc {r : GPath Γ m} (hr : r.NoBack) {y : V} (h : Γ.Adj (r m) y)
    (hy : y ≠ r (m - 1)) : (shiftSnoc r y h).NoBack := by
  intro i hi heq
  by_cases h1 : i + 2 < m
  · rw [shiftSnoc_apply_lt _ _ _ (by omega), shiftSnoc_apply_lt _ _ _ h1] at heq
    exact hr (i + 1) (by omega) heq
  · have h2 : i + 2 = m := by omega
    rw [shiftSnoc_apply_lt _ _ _ (by omega), h2, shiftSnoc_last] at heq
    apply hy
    rw [← heq, show i + 1 = m - 1 by omega]

end ShiftSnoc

@[expose] def triv (u : V) : GPath Γ 0 where
  toFun _ := u
  adj i hi := absurd hi (Nat.not_lt_zero i)
  tail _ _ := rfl

theorem exists_extend (hval : ∀ v a b : V, ∃ w, Γ.Adj v w ∧ w ≠ a ∧ w ≠ b) {u : V} {n : ℕ}
    {q : GPath Γ n} (hq : q ∈ nbPaths Γ u n) :
    ∀ k : ℕ, ∃ r : GPath Γ (n + k), r ∈ nbPaths Γ u (n + k) ∧ r.take n (Nat.le_add_right n k) = q
  | 0 => ⟨q, hq, ext' fun i hi => by simp [take_apply_of_le _ _ _ hi]⟩
  | k + 1 => by
    obtain ⟨r, hr, hrq⟩ := exists_extend hval hq k
    obtain ⟨w, h, hrw⟩ := (exists_extension hval hr : ∃ (w : V) (h : Γ.Adj (r (n + k)) w),
      r.snoc w h ∈ nbPaths Γ u (n + k + 1))
    refine ⟨r.snoc w h, hrw, ?_⟩
    refine ext' fun i hi => ?_
    rw [take_apply_of_le _ _ _ hi, snoc_of_le _ _ _ (by omega)]
    have := congrArg (fun s : GPath Γ n => s i) hrq
    simpa [take_apply_of_le _ _ _ hi] using this

theorem exists_extend_to (hval : ∀ v a b : V, ∃ w, Γ.Adj v w ∧ w ≠ a ∧ w ≠ b) {u : V} {n L : ℕ}
    (hn : n ≤ L) {q : GPath Γ n} (hq : q ∈ nbPaths Γ u n) :
    ∃ r : GPath Γ L, r ∈ nbPaths Γ u L ∧ r.take n hn = q := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact exists_extend hval hq k

theorem exists_nbPaths (hval : ∀ v a b : V, ∃ w, Γ.Adj v w ∧ w ≠ a ∧ w ≠ b) (u : V) :
    ∀ n : ℕ, ∃ p : GPath Γ n, p ∈ nbPaths Γ u n
  | 0 => ⟨triv u, rfl, fun i hi => absurd hi (by omega)⟩
  | n + 1 => by
    obtain ⟨p, hp⟩ := exists_nbPaths hval u n
    obtain ⟨w, h, hpw⟩ := exists_extension hval hp
    exact ⟨_, hpw⟩

end GPath

end CFSG.Quasithin
