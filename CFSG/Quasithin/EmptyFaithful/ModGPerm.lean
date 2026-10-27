module

public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.ModG

@[expose] def enc : List ℕ → ℕ
  | [] => 0
  | d :: l => Nat.add d (Nat.mul 32 (enc l))

@[expose] def dg (k j : ℕ) : ℕ := Nat.mod (Nat.div k (Nat.pow 32 j)) 32

@[expose] def pk (f : Equiv.Perm (Fin 22)) : ℕ := enc (List.ofFn fun i : Fin 22 => (f i).val + 1)

theorem dg_eq (k j : ℕ) : dg k j = k / 32 ^ j % 32 := rfl

theorem enc_cons (d : ℕ) (l : List ℕ) : enc (d :: l) = d + 32 * enc l := rfl

theorem dg_enc (l : List ℕ) (hl : ∀ d ∈ l, d < 32) (j : ℕ) : dg (enc l) j = l.getD j 0 := by
  induction l generalizing j with
  | nil => simp [enc, dg_eq]
  | cons d l ih =>
    have hd : d < 32 := hl d (by simp)
    have hl' : ∀ e ∈ l, e < 32 := fun e he => hl e (by simp [he])
    cases j with
    | zero => simp [enc_cons, dg_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
    | succ j =>
      have h1 : (d + 32 * enc l) / 32 = enc l := by
        rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 32), Nat.div_eq_of_lt hd, zero_add]
      have h2 := ih hl' j
      rw [dg_eq] at h2 ⊢
      rw [enc_cons, pow_succ', ← Nat.div_div_eq_div_mul, h1, h2]
      simp

theorem digits_lt (f : Equiv.Perm (Fin 22)) :
    ∀ d ∈ List.ofFn (fun i : Fin 22 => (f i).val + 1), d < 32 := by
  intro d hd
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hd
  have := (f i).isLt
  omega

theorem dg_pk (f : Equiv.Perm (Fin 22)) (j : ℕ) (hj : j < 22) : dg (pk f) j = (f ⟨j, hj⟩).val + 1 := by
  rw [pk, dg_enc _ (digits_lt f), List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]

@[expose] def ci (a b i : ℕ) : ℕ := dg a (Nat.sub (dg b i) 1)

@[expose] def comp (a b : ℕ) : ℕ :=
  enc [ci a b 0, ci a b 1, ci a b 2, ci a b 3, ci a b 4, ci a b 5, ci a b 6, ci a b 7, ci a b 8, ci a b 9, ci a b 10, ci a b 11, ci a b 12, ci a b 13, ci a b 14, ci a b 15, ci a b 16, ci a b 17, ci a b 18, ci a b 19, ci a b 20, ci a b 21]

@[expose] def kId : ℕ := 919863205167070139185553590062145

theorem ci_pk (f g : Equiv.Perm (Fin 22)) (i : ℕ) (hi : i < 22) :
    ci (pk f) (pk g) i = ((f * g) ⟨i, hi⟩).val + 1 := by
  have h1 := dg_pk g i hi
  have h2 : Nat.sub (dg (pk g) i) 1 = (g ⟨i, hi⟩).val := by
    rw [h1]
    rfl
  rw [ci, h2, dg_pk f (g ⟨i, hi⟩).val (g ⟨i, hi⟩).isLt]
  rfl

theorem pk_mul (f g : Equiv.Perm (Fin 22)) : pk (f * g) = comp (pk f) (pk g) := by
  have h1 : List.ofFn (fun i : Fin 22 => ((f * g) i).val + 1) =
      List.ofFn (fun i : Fin 22 => ci (pk f) (pk g) i.val) := by
    congr 1
    funext i
    exact (ci_pk f g i.val i.isLt).symm
  have h2 : List.ofFn (fun i : Fin 22 => ci (pk f) (pk g) i.val) =
      [ci (pk f) (pk g) 0, ci (pk f) (pk g) 1, ci (pk f) (pk g) 2, ci (pk f) (pk g) 3,
        ci (pk f) (pk g) 4, ci (pk f) (pk g) 5, ci (pk f) (pk g) 6, ci (pk f) (pk g) 7,
        ci (pk f) (pk g) 8, ci (pk f) (pk g) 9, ci (pk f) (pk g) 10, ci (pk f) (pk g) 11,
        ci (pk f) (pk g) 12, ci (pk f) (pk g) 13, ci (pk f) (pk g) 14, ci (pk f) (pk g) 15,
        ci (pk f) (pk g) 16, ci (pk f) (pk g) 17, ci (pk f) (pk g) 18, ci (pk f) (pk g) 19,
        ci (pk f) (pk g) 20, ci (pk f) (pk g) 21] := rfl
  rw [pk, h1, h2]
  rfl

theorem pk_injective : Function.Injective pk := by
  intro f g h
  ext i
  have h1 := dg_pk f i.val i.isLt
  have h2 := dg_pk g i.val i.isLt
  rw [h] at h1
  have := h1.symm.trans h2
  simpa using this

theorem pk_one : pk 1 = kId := by decide +kernel

theorem val_apply_eq (f : Equiv.Perm (Fin 22)) (x : Fin 22) : (f x).val = dg (pk f) x.val - 1 := by
  have h := dg_pk f x.val x.isLt
  have : (⟨x.val, x.isLt⟩ : Fin 22) = x := rfl
  rw [this] at h
  omega

attribute [irreducible] pk enc dg ci comp kId

@[expose] def memB (x : ℕ) (L : List ℕ) : Bool :=
  List.rec false (fun y _ ih => Bool.or (Nat.beq y x) ih) L

@[expose] def nodupB (L : List ℕ) : Bool :=
  List.rec true (fun x xs ih => Bool.and (Bool.not (memB x xs)) ih) L

@[expose] def allL {α : Type} (p : α → Bool) (L : List α) : Bool :=
  List.rec true (fun x _ ih => Bool.and (p x) ih) L

@[expose] def anyL {α : Type} (p : α → Bool) (L : List α) : Bool :=
  List.rec false (fun x _ ih => Bool.or (p x) ih) L

theorem memB_cons (x y : ℕ) (L : List ℕ) : memB x (y :: L) = (Nat.beq y x || memB x L) := rfl

theorem memB_iff {x : ℕ} {L : List ℕ} : memB x L = true ↔ x ∈ L := by
  induction L with
  | nil => exact ⟨fun h => Bool.noConfusion h, fun h => (List.not_mem_nil h).elim⟩
  | cons y l ih =>
    rw [memB_cons, Bool.or_eq_true, ih, List.mem_cons]
    exact or_congr_left ⟨fun h => (Nat.eq_of_beq_eq_true h).symm, fun h => h ▸ Nat.beq_refl _⟩

theorem nodupB_cons (x : ℕ) (L : List ℕ) : nodupB (x :: L) = (!(memB x L) && nodupB L) := rfl

theorem nodupB_iff {L : List ℕ} : nodupB L = true ↔ L.Nodup := by
  induction L with
  | nil => exact ⟨fun _ => List.nodup_nil, fun _ => rfl⟩
  | cons x xs ih =>
    rw [nodupB_cons, Bool.and_eq_true, ih, List.nodup_cons, Bool.not_eq_true', ← Bool.not_eq_true,
      memB_iff]

theorem allL_cons {α : Type} (p : α → Bool) (x : α) (L : List α) :
    allL p (x :: L) = (p x && allL p L) := rfl

theorem allL_iff {α : Type} {p : α → Bool} {L : List α} :
    allL p L = true ↔ ∀ x ∈ L, p x = true := by
  induction L with
  | nil => exact ⟨fun _ x hx => (List.not_mem_nil hx).elim, fun _ => rfl⟩
  | cons x xs ih =>
    rw [allL_cons, Bool.and_eq_true, ih]
    exact ⟨fun h y hy => by
        rcases List.mem_cons.1 hy with rfl | hy
        · exact h.1
        · exact h.2 y hy,
      fun h => ⟨h x (List.mem_cons_self ..), fun y hy => h y (List.mem_cons_of_mem _ hy)⟩⟩

theorem anyL_cons {α : Type} (p : α → Bool) (x : α) (L : List α) :
    anyL p (x :: L) = (p x || anyL p L) := rfl

theorem anyL_iff {α : Type} {p : α → Bool} {L : List α} :
    anyL p L = true ↔ ∃ x ∈ L, p x = true := by
  induction L with
  | nil => exact ⟨fun h => Bool.noConfusion h, fun ⟨x, hx, _⟩ => (List.not_mem_nil hx).elim⟩
  | cons x xs ih =>
    rw [anyL_cons, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨y, hy, h⟩)
      · exact ⟨x, List.mem_cons_self .., h⟩
      · exact ⟨y, List.mem_cons_of_mem _ hy, h⟩
    · rintro ⟨y, hy, h⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact Or.inl h
      · exact Or.inr ⟨y, hy, h⟩

attribute [irreducible] memB nodupB allL anyL

end CFSG.Quasithin.ModG
