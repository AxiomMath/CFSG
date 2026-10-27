module

public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.ModE

@[expose] def enc : List ℕ → ℕ
  | [] => 0
  | d :: l => Nat.add d (Nat.mul 32 (enc l))

@[expose] def dg (k j : ℕ) : ℕ := Nat.mod (Nat.div k (Nat.pow 32 j)) 32

@[expose] def pk (f : Equiv.Perm (Fin 24)) : ℕ := enc (List.ofFn fun i : Fin 24 => (f i).val + 1)

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

theorem digits_lt (f : Equiv.Perm (Fin 24)) :
    ∀ d ∈ List.ofFn (fun i : Fin 24 => (f i).val + 1), d < 32 := by
  intro d hd
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hd
  have := (f i).isLt
  omega

theorem dg_pk (f : Equiv.Perm (Fin 24)) (j : ℕ) (hj : j < 24) : dg (pk f) j = (f ⟨j, hj⟩).val + 1 := by
  rw [pk, dg_enc _ (digits_lt f), List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]

@[expose] def ci (a b i : ℕ) : ℕ := dg a (Nat.sub (dg b i) 1)

@[expose] def comp (a b : ℕ) : ℕ :=
  enc [ci a b 0, ci a b 1, ci a b 2, ci a b 3, ci a b 4, ci a b 5, ci a b 6, ci a b 7, ci a b 8, ci a b 9, ci a b 10, ci a b 11, ci a b 12, ci a b 13, ci a b 14, ci a b 15, ci a b 16, ci a b 17, ci a b 18, ci a b 19, ci a b 20, ci a b 21, ci a b 22, ci a b 23]

@[expose] def kId : ℕ := 1027696566980429233681091202693336129

theorem ci_pk (f g : Equiv.Perm (Fin 24)) (i : ℕ) (hi : i < 24) :
    ci (pk f) (pk g) i = ((f * g) ⟨i, hi⟩).val + 1 := by
  have h1 := dg_pk g i hi
  have h2 : Nat.sub (dg (pk g) i) 1 = (g ⟨i, hi⟩).val := by
    rw [h1]
    rfl
  rw [ci, h2, dg_pk f (g ⟨i, hi⟩).val (g ⟨i, hi⟩).isLt]
  rfl

theorem pk_mul (f g : Equiv.Perm (Fin 24)) : pk (f * g) = comp (pk f) (pk g) := by
  have h1 : List.ofFn (fun i : Fin 24 => ((f * g) i).val + 1) =
      List.ofFn (fun i : Fin 24 => ci (pk f) (pk g) i.val) := by
    congr 1
    funext i
    exact (ci_pk f g i.val i.isLt).symm
  have h2 : List.ofFn (fun i : Fin 24 => ci (pk f) (pk g) i.val) =
      [ci (pk f) (pk g) 0, ci (pk f) (pk g) 1, ci (pk f) (pk g) 2, ci (pk f) (pk g) 3,
        ci (pk f) (pk g) 4, ci (pk f) (pk g) 5, ci (pk f) (pk g) 6, ci (pk f) (pk g) 7,
        ci (pk f) (pk g) 8, ci (pk f) (pk g) 9, ci (pk f) (pk g) 10, ci (pk f) (pk g) 11,
        ci (pk f) (pk g) 12, ci (pk f) (pk g) 13, ci (pk f) (pk g) 14, ci (pk f) (pk g) 15,
        ci (pk f) (pk g) 16, ci (pk f) (pk g) 17, ci (pk f) (pk g) 18, ci (pk f) (pk g) 19,
        ci (pk f) (pk g) 20, ci (pk f) (pk g) 21, ci (pk f) (pk g) 22, ci (pk f) (pk g) 23] := rfl
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

attribute [irreducible] pk enc dg ci comp kId

end CFSG.Quasithin.ModE
