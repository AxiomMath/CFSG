module

public import CFSG.Quasithin.Background.F3Paths

public section

namespace CFSG.Quasithin

universe u v

variable {V : Type u} {Γ : SimpleGraph V}

namespace GPath

variable {n : ℕ}

@[expose] def cons (y : V) {n : ℕ} (p : GPath Γ n) (h : Γ.Adj y (p 0)) : GPath Γ (n + 1) where
  toFun i := if i = 0 then y else p (i - 1)
  adj i hi := by
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · subst hi0
      show Γ.Adj (if (0 : ℕ) = 0 then y else p (0 - 1))
        (if 0 + 1 = 0 then y else p (0 + 1 - 1))
      simpa using h
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      show Γ.Adj (if j + 1 = 0 then y else p (j + 1 - 1))
        (if j + 1 + 1 = 0 then y else p (j + 1 + 1 - 1))
      rw [if_neg (by omega : ¬ (j + 1 = 0)), if_neg (by omega : ¬ (j + 1 + 1 = 0)),
        show j + 1 - 1 = j by omega, show j + 1 + 1 - 1 = j + 1 by omega]
      exact p.adj j (by omega)
  tail i hi := by
    have h1 : i ≠ 0 := by omega
    show (if i = 0 then y else p (i - 1)) = (if n + 1 = 0 then y else p (n + 1 - 1))
    rw [if_neg h1, if_neg (by omega : ¬ (n + 1 = 0)), show n + 1 - 1 = n by omega]
    exact p.tail (i - 1) (by omega)

@[simp] theorem cons_zero (y : V) {n : ℕ} (p : GPath Γ n) (h : Γ.Adj y (p 0)) :
    cons y p h 0 = y := rfl

@[simp] theorem cons_succ (y : V) {n : ℕ} (p : GPath Γ n) (h : Γ.Adj y (p 0)) (i : ℕ) :
    cons y p h (i + 1) = p i := by
  show (if i + 1 = 0 then y else p (i + 1 - 1)) = p i
  rw [if_neg (by omega : ¬ (i + 1 = 0)), show i + 1 - 1 = i by omega]

theorem noBack_cons (y : V) {n : ℕ} (p : GPath Γ n) (h : Γ.Adj y (p 0))
    (hp : p.NoBack) (hy : y ≠ p 1) : (cons y p h).NoBack := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    rw [cons_zero, show (2 : ℕ) = 1 + 1 from rfl, cons_succ]
    exact hy
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [cons_succ, show j + 1 + 2 = (j + 2) + 1 by omega, cons_succ]
    exact hp j (by omega)

@[expose] def ofAdj {y u : V} (h : Γ.Adj y u) : GPath Γ 1 where
  toFun i := if i = 0 then y else u
  adj i hi := by
    have hi0 : i = 0 := by omega
    subst hi0
    simpa using h
  tail i hi := by
    have hi0 : i ≠ 0 := by omega
    simp [hi0]

@[simp] theorem ofAdj_zero {y u : V} (h : Γ.Adj y u) : ofAdj h 0 = y := rfl

@[simp] theorem ofAdj_one {y u : V} (h : Γ.Adj y u) : ofAdj h 1 = u := by
  show (if (1 : ℕ) = 0 then y else u) = u
  simp

@[expose] def nil (v : V) : GPath Γ 0 where
  toFun _ := v
  adj i hi := by omega
  tail i _ := rfl

@[simp] theorem nil_apply (v : V) (i : ℕ) : nil (Γ := Γ) v i = v := rfl

theorem noBack_nil (v : V) : (nil (Γ := Γ) v).NoBack := by
  intro i hi
  omega

@[expose] def append {m : ℕ} (p : GPath Γ n) (q : GPath Γ m) (h : p n = q 0) :
    GPath Γ (n + m) where
  toFun i := if i ≤ n then p i else q (i - n)
  adj i hi := by
    by_cases hlt : i < n
    · have e1 : i ≤ n := by omega
      have e2 : i + 1 ≤ n := by omega
      simp only [e1, e2, if_true]
      exact p.adj i hlt
    · by_cases heq : i = n
      · subst i
        have hk : 0 < m := by omega
        change Γ.Adj (if n ≤ n then p n else q (n - n))
          (if n + 1 ≤ n then p (n + 1) else q (n + 1 - n))
        rw [if_pos le_rfl, h, if_neg (by omega)]
        have e : n + 1 - n = 1 := by omega
        rw [e]
        exact q.adj 0 hk
      · have h1 : ¬ i ≤ n := by omega
        have h2 : ¬ i + 1 ≤ n := by omega
        simp only [h1, h2, if_false]
        have e : i + 1 - n = (i - n) + 1 := by omega
        rw [e]
        exact q.adj (i - n) (by omega)
  tail i hi := by
    by_cases hle : i ≤ n
    · have hk : m = 0 := by omega
      subst m
      have hin : i = n := by omega
      subst i
      change (if n ≤ n then p n else q (n - n)) =
        (if n + 0 ≤ n then p (n + 0) else q (n + 0 - n))
      rw [if_pos le_rfl, if_pos (by omega)]
      simp
    · have h1 : ¬ i ≤ n := by omega
      by_cases hm0 : m = 0
      · subst m
        change (if i ≤ n then p i else q (i - n)) =
          (if n ≤ n then p n else q (n - n))
        rw [if_neg h1, if_pos le_rfl]
        have hq : q (i - n) = q 0 := q.tail (i - n) (by omega)
        rw [hq, ← h]
      · have hmpos : 0 < m := by omega
        change (if i ≤ n then p i else q (i - n)) =
          (if n + m ≤ n then p (n + m) else q (n + m - n))
        rw [if_neg h1, if_neg (by omega), Nat.add_sub_cancel_left]
        exact q.tail (i - n) (by omega)

@[simp] theorem append_apply_left {m : ℕ} (p : GPath Γ n) (q : GPath Γ m) (h : p n = q 0)
    {i : ℕ} (hi : i ≤ n) : append p q h i = p i := by
  show (if i ≤ n then p i else q (i - n)) = p i
  rw [if_pos hi]

theorem append_apply_right {m : ℕ} (p : GPath Γ n) (q : GPath Γ m) (h : p n = q 0)
    {i : ℕ} (hi : n ≤ i) : append p q h i = q (i - n) := by
  by_cases heq : i = n
  · subst i
    show (if n ≤ n then p n else q (n - n)) = q (n - n)
    rw [if_pos le_rfl, Nat.sub_self, h]
  · have hlt : ¬ i ≤ n := by omega
    show (if i ≤ n then p i else q (i - n)) = q (i - n)
    rw [if_neg hlt]

theorem noBack_append {m : ℕ} (p : GPath Γ n) (q : GPath Γ m) (h : p n = q 0)
    (hp : p.NoBack) (hq : q.NoBack) (hn : 0 < n) (hm : 0 < m)
    (hcross : p (n - 1) ≠ q 1) : (append p q h).NoBack := by
  intro i hi heq
  by_cases hlt : i + 2 ≤ n
  · apply hp i hlt
    have h1 : append p q h i = p i := append_apply_left p q h (by omega)
    have h2 : append p q h (i + 2) = p (i + 2) := append_apply_left p q h hlt
    rw [h1, h2] at heq
    exact heq
  · by_cases him : i < n
    · have hi1 : i = n - 1 := by omega
      subst hi1
      apply hcross
      have h1 : append p q h (n - 1) = p (n - 1) :=
        append_apply_left p q h (by omega)
      have h2 : append p q h (n - 1 + 2) = q ((n - 1 + 2) - n) :=
        append_apply_right p q h (by omega)
      rw [h1, h2] at heq
      have e : n - 1 + 2 - n = 1 := by omega
      rwa [e] at heq
    · have h1 : n ≤ i := by omega
      have h2 : n ≤ i + 2 := by omega
      apply hq (i - n) (by omega)
      have h3 : append p q h i = q (i - n) := append_apply_right p q h h1
      have h4 : append p q h (i + 2) = q ((i + 2) - n) :=
        append_apply_right p q h h2
      rw [h3, h4] at heq
      have e : i + 2 - n = (i - n) + 2 := by omega
      rwa [e] at heq

theorem NoBack.map_of_injective {W : Type v} {Δ : SimpleGraph W} {f : V → W}
    (hf : ∀ a b, Γ.Adj a b → Δ.Adj (f a) (f b)) (hinj : Function.Injective f)
    {p : GPath Γ n} (hp : p.NoBack) : (p.map f hf).NoBack := by
  intro i hi h
  rw [map_apply, map_apply] at h
  exact hp i hi (hinj h)

end GPath

end CFSG.Quasithin
