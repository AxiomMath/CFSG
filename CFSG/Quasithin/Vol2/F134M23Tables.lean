module

public import CFSG.Quasithin.Vol2.F134M23Data
public import CFSG.Quasithin.Vol2.F134M23Code
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin.F134

open Equiv

@[expose] def m23PermA : Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]

@[expose] def m23PermB : Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

theorem m23_eq_closure :
    CFSG.Blueprint.NativeSporadic.M23 = Subgroup.closure {m23PermA, m23PermB} := rfl

@[expose] def m23Word : List ℕ → Perm (Fin 23)
  | [] => 1
  | c :: w => (if c = 0 then m23PermA else m23PermB) * m23Word w

@[expose] def m23WordC : List ℕ → ℕ
  | [] => m23oneC
  | c :: w => mul23 (if c = 0 then m23aC else m23bC) (m23WordC w)

@[expose] def m23TelB : ℕ := ofDigs (2 ^ 115) m23TelL

@[expose] def m23Tel (i : ℕ) : ℕ := digW 115 m23TelB i

@[expose] def m23TGB : ℕ := ofDigs (2 ^ 115) m23TGenL

@[expose] def m23TG (k : ℕ) : ℕ := digW 115 m23TGB k

@[expose] def m23NxtB : ℕ := ofDigs (2 ^ 7) m23NxtL

@[expose] def m23Nxt (i : ℕ) : ℕ := digW 7 m23NxtB i

@[expose] def m23ParB : ℕ := ofDigs (2 ^ 9) m23ParL

@[expose] def m23Par (i : ℕ) : ℕ := digW 9 m23ParB i

@[expose] def m23DB : ℕ := ofDigs (2 ^ 115) m23DL

@[expose] def m23D (j : ℕ) : ℕ := digW 115 m23DB j

@[expose] def m23GB : ℕ := ofDigs (2 ^ 115) m23GL

@[expose] def m23G (c : ℕ) : ℕ := digW 115 m23GB c

@[expose] def m23Let (l : ℕ) : ℕ := if l < 128 then m23Tel l else m23G (l - 128)

@[expose] def m23LWordC : List ℕ → ℕ
  | [] => m23oneC
  | l :: w => mul23 (m23Let l) (m23LWordC w)

@[expose] def m23GEB (c : ℕ) : ℕ := ofDigs (2 ^ 7) (m23GEL.getD c [])

@[expose] def m23GEAt (c p : ℕ) : ℕ := digW 7 (m23GEB c) p

@[expose] def m23GPB (c : ℕ) : ℕ := ofDigs (2 ^ 8) (m23GPL.getD c [])

@[expose] def m23GPAt (c p : ℕ) : ℕ := digW 8 (m23GPB c) p

@[expose] def m23GQB (c : ℕ) : ℕ := ofDigs (2 ^ 9) (m23GQL.getD c [])

@[expose] def m23GQAt (c i : ℕ) : ℕ := digW 9 (m23GQB c) i

@[expose] def m23GDecB (c : ℕ) : ℕ := ofDigs (2 ^ 24) (m23GDecL.getD c [])

@[expose] def m23GDecAt (c e : ℕ) : ℕ := digW 24 (m23GDecB c) e

@[expose] def m23BadB : ℕ := ofDigs (2 ^ 15) m23BadL

@[expose] def m23Bad (j : ℕ) : ℕ := digW 15 m23BadB (j - 6)

@[expose] def m23CosB (j : ℕ) : ℕ := ofDigs (2 ^ 8) (m23CosRows.getD (j - 1) [])

@[expose] def m23Cos (j i : ℕ) : ℕ := digW 8 (m23CosB j) i

@[expose] def m23ExclB : ℕ := ofDigs (2 ^ 15) m23ExclL

@[expose] def m23Excl (k : ℕ) : ℕ := digW 15 m23ExclB (k - 1)

end CFSG.Quasithin.F134
