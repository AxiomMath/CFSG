module

public import CFSG.Quasithin.Vol2.F134M22Data
public import CFSG.Quasithin.Vol2.F134PermCode
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin.F134

open Equiv

@[expose] def m22PermA : Perm (Fin 22) :=
  List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]

@[expose] def m22PermB : Perm (Fin 22) :=
  List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]

theorem m22_eq_closure :
    CFSG.Blueprint.NativeSporadic.M22 = Subgroup.closure {m22PermA, m22PermB} := rfl

@[expose] def m22Word : List ℕ → Perm (Fin 22)
  | [] => 1
  | c :: w => (if c = 0 then m22PermA else m22PermB) * m22Word w

@[expose] def m22WordC : List ℕ → ℕ
  | [] => m22oneC
  | c :: w => mul22 (if c = 0 then m22aC else m22bC) (m22WordC w)

@[expose] def m22TelB : ℕ := ofDigs (2 ^ 110) m22TelL

@[expose] def m22Tel (i : ℕ) : ℕ := digW 110 m22TelB i

@[expose] def m22TGB : ℕ := ofDigs (2 ^ 110) m22TGenL

@[expose] def m22TG (k : ℕ) : ℕ := digW 110 m22TGB k

@[expose] def m22NxtB : ℕ := ofDigs (2 ^ 7) m22NxtL

@[expose] def m22Nxt (i : ℕ) : ℕ := digW 7 m22NxtB i

@[expose] def m22ParB : ℕ := ofDigs (2 ^ 9) m22ParL

@[expose] def m22Par (i : ℕ) : ℕ := digW 9 m22ParB i

@[expose] def m22DB : ℕ := ofDigs (2 ^ 110) m22DL

@[expose] def m22D (j : ℕ) : ℕ := digW 110 m22DB j

@[expose] def m22DecB (j : ℕ) : ℕ := ofDigs (2 ^ 20) (m22DecRows.getD j [])

@[expose] def m22Dec (j i : ℕ) : ℕ := digW 20 (m22DecB j) i

@[expose] def m22BadB : ℕ := ofDigs (2 ^ 11) m22BadL

@[expose] def m22Bad (j : ℕ) : ℕ := digW 11 m22BadB j

@[expose] def m22Cos58B : ℕ := ofDigs (2 ^ 8) m22Cos58L

@[expose] def m22Cos59B : ℕ := ofDigs (2 ^ 8) m22Cos59L

theorem m22_code_a : permCode m22PermA = m22aC := by decide +kernel

theorem m22_code_b : permCode m22PermB = m22bC := by decide +kernel

theorem m22_code_one : permCode (1 : Perm (Fin 22)) = m22oneC := by decide +kernel

theorem m22_tel_zero : m22Tel 0 = m22oneC := by decide +kernel

theorem m22_dw_zero : m22DW.getD 0 [] = [] := by decide +kernel

theorem m22_tgen_check : ∀ k < 3, m22WordC (m22TGenW.getD k []) = m22TG k := by decide +kernel

theorem m22_nxt_check : ∀ i < 128, ∀ k < 3, m22Nxt (3 * i + k) < 128 ∧
    mul22 (m22Tel i) (m22TG k) = m22Tel (m22Nxt (3 * i + k)) := by
  decide +kernel

theorem m22_par_check : ∀ i < 128, 0 < i → m22Par i / 4 < i ∧ m22Par i % 4 < 3 ∧
    mul22 (m22Tel (m22Par i / 4)) (m22TG (m22Par i % 4)) = m22Tel i := by
  decide +kernel

theorem m22_pow_check : ∀ i < 128, sqC 7 (m22Tel i) = m22oneC := by decide +kernel

theorem m22_d_check : ∀ j < 60, m22WordC (m22DW.getD j []) = m22D j := by decide +kernel

@[expose] def m22DecOK (j i : ℕ) : Bool :=
  Nat.blt (m22Dec j i / 16384) 60 &&
    Nat.beq (mul22 (m22D j) (mul22 (m22Tel i) m22bC))
      (mul22 (mul22 (m22Tel (m22Dec j i / 128 % 128)) (m22D (m22Dec j i / 16384)))
        (m22Tel (m22Dec j i % 128)))

theorem m22_dec_check₀ : ∀ j < 15, ∀ i < 128, m22DecOK j i = true := by decide +kernel

theorem m22_dec_check₁ : ∀ j < 15, ∀ i < 128, m22DecOK (j + 15) i = true := by decide +kernel

theorem m22_dec_check₂ : ∀ j < 15, ∀ i < 128, m22DecOK (j + 30) i = true := by decide +kernel

theorem m22_dec_check₃ : ∀ j < 15, ∀ i < 128, m22DecOK (j + 45) i = true := by decide +kernel

theorem m22_dec_check : ∀ j < 60, ∀ i < 128, m22DecOK j i = true := by
  intro j hj
  rcases Nat.lt_or_ge j 15 with h | h
  · exact m22_dec_check₀ j h
  rcases Nat.lt_or_ge j 30 with h' | h'
  · have := m22_dec_check₁ (j - 15) (by omega)
    rwa [Nat.sub_add_cancel h] at this
  rcases Nat.lt_or_ge j 45 with h'' | h''
  · have := m22_dec_check₂ (j - 30) (by omega)
    rwa [Nat.sub_add_cancel h'] at this
  · have := m22_dec_check₃ (j - 45) (by omega)
    rwa [Nat.sub_add_cancel h''] at this

theorem m22_dec_spec {j i : ℕ} (hj : j < 60) (hi : i < 128) : m22Dec j i / 16384 < 60 ∧
    mul22 (m22D j) (mul22 (m22Tel i) m22bC) =
      mul22 (mul22 (m22Tel (m22Dec j i / 128 % 128)) (m22D (m22Dec j i / 16384)))
        (m22Tel (m22Dec j i % 128)) := by
  have h := m22_dec_check j hj i hi
  simp only [m22DecOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem m22_a_check : mul22 (mul22 (mul22 (m22Tel 7) m22bC) m22bC) (m22Tel 33) = m22aC := by
  decide +kernel

theorem m22_bad_check : ∀ j < 58, 0 < j →
    (m22Bad j % 16 = 5 ∨ m22Bad j % 16 = 7 ∨ m22Bad j % 16 = 11) ∧ m22Bad j / 16 < 128 ∧
      powC m22oneC (m22Bad j % 16) (mul22 (m22D j) (m22Tel (m22Bad j / 16))) = m22oneC ∧
      mul22 (m22D j) (m22Tel (m22Bad j / 16)) ≠ m22oneC := by
  decide +kernel

@[expose] def m22Cos58 (i : ℕ) : ℕ := digW 8 m22Cos58B i

@[expose] def m22Cos59 (i : ℕ) : ℕ := digW 8 m22Cos59B i

theorem m22_cos58_check : ∀ i < 128, m22Cos58 i / 128 < 2 ∧ mul22 (m22Tel i) (m22D 58) =
    mul22 (mul22 (m22Tel (if m22Cos58 i / 128 = 0 then 0 else 3)) (m22D 58))
      (m22Tel (m22Cos58 i % 128)) := by
  decide +kernel

theorem m22_cos59_check : ∀ i < 128, m22Cos59 i / 128 < 2 ∧ mul22 (m22Tel i) (m22D 59) =
    mul22 (mul22 (m22Tel (if m22Cos59 i / 128 = 0 then 0 else 1)) (m22D 59))
      (m22Tel (m22Cos59 i % 128)) := by
  decide +kernel

theorem m22_three_check :
    powC m22oneC 3 (m22WordC m22ThreeW) = m22oneC ∧ m22WordC m22ThreeW ≠ m22oneC := by
  decide +kernel

end CFSG.Quasithin.F134
