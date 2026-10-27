module

public import CFSG.Quasithin.Vol2.F134M24Data
public import CFSG.Quasithin.Vol2.F134M24Code
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin.F134

open Equiv

@[expose] def m24PermA : Perm (Fin 24) :=
  List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 16] * List.formPerm [4, 12] *
    List.formPerm [5, 8] * List.formPerm [7, 14] * List.formPerm [9, 18] *
    List.formPerm [10, 17] * List.formPerm [11, 20] * List.formPerm [13, 15] *
    List.formPerm [19, 23] * List.formPerm [21, 22]

@[expose] def m24PermB : Perm (Fin 24) :=
  List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] *
    List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22]

theorem m24_eq_closure :
    CFSG.Blueprint.NativeSporadic.M24 = Subgroup.closure {m24PermA, m24PermB} := rfl

@[expose] def m24Word : List ℕ → Perm (Fin 24)
  | [] => 1
  | c :: w => (if c = 0 then m24PermA else m24PermB) * m24Word w

@[expose] def m24WordC : List ℕ → ℕ
  | [] => m24oneC
  | c :: w => mul24 (if c = 0 then m24aC else m24bC) (m24WordC w)

@[expose] def m24TelB : ℕ := ofDigs (2 ^ 120) m24TelL

@[expose] def m24Tel (i : ℕ) : ℕ := digW 120 m24TelB i

@[expose] def m24TGB : ℕ := ofDigs (2 ^ 120) m24TGenL

@[expose] def m24TG (k : ℕ) : ℕ := digW 120 m24TGB k

@[expose] def m24NxtB : ℕ := ofDigs (2 ^ 10) m24NxtL

@[expose] def m24Nxt (i : ℕ) : ℕ := digW 10 m24NxtB i

@[expose] def m24ParB : ℕ := ofDigs (2 ^ 13) m24ParL

@[expose] def m24Par (i : ℕ) : ℕ := digW 13 m24ParB i

@[expose] def m24DB : ℕ := ofDigs (2 ^ 120) m24DL

@[expose] def m24D (j : ℕ) : ℕ := digW 120 m24DB j

@[expose] def m24GB : ℕ := ofDigs (2 ^ 120) m24GL

@[expose] def m24G (c : ℕ) : ℕ := digW 120 m24GB c

@[expose] def m24Let (l : ℕ) : ℕ := if l < 1024 then m24Tel l else m24G (l - 1024)

@[expose] def m24LWordC : List ℕ → ℕ
  | [] => m24oneC
  | l :: w => mul24 (m24Let l) (m24LWordC w)

@[expose] def m24GEB (c : ℕ) : ℕ := ofDigs (2 ^ 10) (m24GEL.getD c [])

@[expose] def m24GEAt (c p : ℕ) : ℕ := digW 10 (m24GEB c) p

@[expose] def m24GPB (c : ℕ) : ℕ := ofDigs (2 ^ 12) (m24GPL.getD c [])

@[expose] def m24GPAt (c p : ℕ) : ℕ := digW 12 (m24GPB c) p

@[expose] def m24GQB (c : ℕ) : ℕ := ofDigs (2 ^ 10) (m24GQL.getD c [])

@[expose] def m24GQAt (c i : ℕ) : ℕ := digW 10 (m24GQB c) i

@[expose] def m24GDecB (c : ℕ) : ℕ := ofDigs (2 ^ 29) (m24GDecL.getD c [])

@[expose] def m24GDecAt (c e : ℕ) : ℕ := digW 29 (m24GDecB c) e

@[expose] def m24BadB : ℕ := ofDigs (2 ^ 18) m24BadL

@[expose] def m24Bad (j : ℕ) : ℕ := digW 18 m24BadB (j - 8)

@[expose] def m24CR (j b : ℕ) : ℕ := (m24CosR.getD (j - 1) []).getD b 0

@[expose] def m24CN (j : ℕ) : ℕ := (m24CosR.getD (j - 1) []).length

@[expose] def m24CosB (j : ℕ) : ℕ := ofDigs (2 ^ 12) (m24CosRows.getD (j - 1) [])

@[expose] def m24Cos (j i : ℕ) : ℕ := digW 12 (m24CosB j) i

@[expose] def m24EP (e : ℕ) : ℕ := m24ExclP.getD e 0

@[expose] def m24Excl (e : ℕ) : ℕ := m24ExclL.getD e 0

@[expose] def m24HJ : List (List ℕ) := [[0, 2, 3, 5], [0, 1, 4, 6], [0, 1, 3, 7], [0, 1, 2, 3, 4]]

@[expose] def m24HC (X s : ℕ) : ℕ := (m24HCS.getD X []).getD s 0

@[expose] def m24CC (X s : ℕ) : ℕ := mul24 (m24Tel (m24HC X s % 1024)) (m24D (m24HC X s / 1024))

@[expose] def m24XC (X t : ℕ) : ℕ :=
  mul24 (m24CC X ((m24HX.getD X []).getD t 0 / 1024)) (m24Tel ((m24HX.getD X []).getD t 0 % 1024))

@[expose] def m24ZC (X a b : ℕ) : ℕ :=
  mul24 (powC24 m24oneC a (m24XC X 0)) (powC24 m24oneC b (m24XC X 1))

end CFSG.Quasithin.F134
