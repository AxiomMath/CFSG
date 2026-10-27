module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic

public section

namespace CFSG.Monster.B.E6.StdF4Radical

section Collect

variable {G : Type*} [Group G] (x : ℕ → G) (z : G) (C : ℕ → ℕ → Bool)

@[expose] def zb (b : Bool) : G := if b then z else 1

@[expose] def lprod (L : List ℕ) (u : ℕ → Bool) : G :=
  (L.map fun i => if u i then x i else 1).prod

@[expose] def par (L : List ℕ) (u : ℕ → Bool) (j : ℕ) : Bool :=
  L.foldr (fun i b => xor (u i && C i j) b) false

@[expose] def parAfter : List ℕ → (ℕ → Bool) → ℕ → Bool
  | [], _, _ => false
  | i :: L, u, j => if i = j then par C L u j else parAfter L u j

structure Rels (L : List ℕ) : Prop where
  sq : ∀ i ∈ L, x i * x i = 1
  zsq : z * z = 1
  zcomm : ∀ i ∈ L, z * x i = x i * z
  rel : ∀ i ∈ L, ∀ j ∈ L, x i * x j = x j * x i * zb z (C i j)

variable {x z C}

theorem zb_false : zb z false = 1 := rfl

theorem zb_true : zb z true = z := rfl

theorem zb_xor (hz : z * z = 1) (a b : Bool) : zb z (xor a b) = zb z a * zb z b := by
  cases a <;> cases b <;> simp [zb, hz]

theorem lprod_nil (u : ℕ → Bool) : lprod x [] u = 1 := rfl

theorem lprod_cons (i : ℕ) (L : List ℕ) (u : ℕ → Bool) :
    lprod x (i :: L) u = (if u i then x i else 1) * lprod x L u := rfl

theorem lprod_append (L L' : List ℕ) (u : ℕ → Bool) :
    lprod x (L ++ L') u = lprod x L u * lprod x L' u := by
  simp [lprod, List.map_append, List.prod_append]

theorem lprod_congr {L : List ℕ} {u u' : ℕ → Bool} (h : ∀ i ∈ L, u i = u' i) :
    lprod x L u = lprod x L u' := by
  unfold lprod
  congr 1
  exact List.map_congr_left fun i hi => by rw [h i hi]

theorem par_cons (i : ℕ) (L : List ℕ) (u : ℕ → Bool) (j : ℕ) :
    par C (i :: L) u j = xor (u i && C i j) (par C L u j) := rfl

theorem zb_comm_x {L₀ : List ℕ} (h : Rels x z C L₀) {i : ℕ} (hi : i ∈ L₀) (b : Bool) :
    zb z b * x i = x i * zb z b := by
  cases b
  · simp [zb]
  · exact h.zcomm i hi

theorem zb_comm_lprod {L₀ : List ℕ} (h : Rels x z C L₀) (b : Bool) (u : ℕ → Bool) :
    ∀ {L : List ℕ}, (∀ i ∈ L, i ∈ L₀) → zb z b * lprod x L u = lprod x L u * zb z b
  | [], _ => by simp [lprod]
  | i :: L, hL => by
    rw [lprod_cons, ← mul_assoc]
    have h1 : zb z b * (if u i then x i else 1) = (if u i then x i else 1) * zb z b := by
      split_ifs
      · exact zb_comm_x h (hL i (List.mem_cons_self ..)) b
      · simp
    rw [h1, mul_assoc, zb_comm_lprod h b u (fun k hk => hL k (List.mem_cons_of_mem _ hk)),
      mul_assoc]

theorem lprod_mul_x {L₀ : List ℕ} (h : Rels x z C L₀) {j : ℕ} (hj : j ∈ L₀) (u : ℕ → Bool) :
    ∀ {L : List ℕ}, (∀ i ∈ L, i ∈ L₀) →
      lprod x L u * x j = x j * lprod x L u * zb z (par C L u j)
  | [], _ => by simp [lprod, par, zb]
  | i :: L, hL => by
    have hi : i ∈ L₀ := hL i (List.mem_cons_self ..)
    have hL' : ∀ k ∈ L, k ∈ L₀ := fun k hk => hL k (List.mem_cons_of_mem _ hk)
    have h1 : (if u i then x i else 1) * x j =
        x j * (if u i then x i else 1) * zb z (u i && C i j) := by
      cases u i
      · simp [zb]
      · simpa using h.rel i hi j hj
    rw [lprod_cons, par_cons, zb_xor h.zsq, mul_assoc, lprod_mul_x h hj u hL', ← mul_assoc,
      ← mul_assoc, h1, mul_assoc (x j * _), zb_comm_lprod h _ u hL']
    simp only [mul_assoc]

theorem lprod_mul_x_of_mem {L₀ : List ℕ} (h : Rels x z C L₀) {j : ℕ} (hj : j ∈ L₀)
    (u : ℕ → Bool) :
    ∀ {L : List ℕ}, L.Nodup → j ∈ L → (∀ i ∈ L, i ∈ L₀) →
      lprod x L u * x j = lprod x L (Function.update u j (!u j)) * zb z (parAfter C L u j)
  | [], _, hjL, _ => absurd hjL (List.not_mem_nil)
  | i :: L, hnd, hjL, hL => by
    have hL' : ∀ k ∈ L, k ∈ L₀ := fun k hk => hL k (List.mem_cons_of_mem _ hk)
    rw [List.nodup_cons] at hnd
    by_cases hij : i = j
    · subst hij
      have hc : lprod x L u = lprod x L (Function.update u i (!u i)) :=
        lprod_congr fun k hk => by
          rw [Function.update_of_ne (fun e : k = i => hnd.1 (e ▸ hk))]
      rw [lprod_cons, lprod_cons, mul_assoc, lprod_mul_x h hj u hL', ← mul_assoc, ← mul_assoc,
        parAfter, ite_eq_left rfl, Function.update_self, hc]
      congr 2
      cases u i
      · simp
      · simp [h.sq i hj]
    · have hjL' : j ∈ L := by
        rcases List.mem_cons.1 hjL with e | e
        · exact absurd e.symm hij
        · exact e
      rw [lprod_cons, lprod_cons, mul_assoc, lprod_mul_x_of_mem h hj u hnd.2 hjL' hL',
        parAfter, ite_eq_right hij, Function.update_of_ne hij, mul_assoc]

end Collect

end CFSG.Monster.B.E6.StdF4Radical
