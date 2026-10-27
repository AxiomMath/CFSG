module

public import CFSG.LieType.Ree.Mirror
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree

@[expose] def d4bPos : List (List (Fin 8 × Fin 8)) :=
  [[(0, 1), (6, 7)],
  [(2, 3), (4, 5)],
  [(1, 2), (5, 6)],
  [(2, 4), (3, 5)],
  [(7, 6), (1, 0)],
  [(0, 2), (5, 7)],
  [(5, 4), (3, 2)],
  [(1, 3), (4, 6)],
  [(6, 5), (2, 1)],
  [(1, 4), (3, 6)],
  [(5, 3), (4, 2)],
  [(7, 5), (2, 0)],
  [(0, 3), (4, 7)],
  [(0, 4), (3, 7)],
  [(6, 4), (3, 1)],
  [(1, 5), (2, 6)],
  [(6, 3), (4, 1)],
  [(7, 4), (3, 0)],
  [(7, 3), (4, 0)],
  [(0, 5), (2, 7)],
  [(6, 2), (5, 1)],
  [(7, 2), (5, 0)],
  [(0, 6), (1, 7)],
  [(7, 1), (6, 0)]]

@[expose] def d4bE (m : ℕ) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun r c => if (r, c) ∈ d4bPos.getD m [] then 1 else 0

@[expose] def d4bSimple (i : Fin Tag.D4.rank) (s : Bool) : ℕ := if s then i.val else 4 + 2 * i.val

@[expose] def d4bEs (i : Fin Tag.D4.rank) (s : Bool) : Matrix (Fin 8) (Fin 8) (ZMod 2) := d4bE (d4bSimple i s)

@[expose] def d4bTh : Idx d4Certificate → Matrix (Fin 8) (Fin 8) (ZMod 2)
  | .inl j => d4bEs j true * d4bEs j false + d4bEs j false * d4bEs j true
  | .inr m => d4bE m.val

@[expose] def d4bCol : Col d4Certificate → Matrix (Fin 8) (Fin 8) (ZMod 2)
  | none => 0
  | some (a, z) => (z : ZMod 2) • d4bTh a

@[expose] def D4bXOK (i : Fin Tag.D4.rank) : Prop := ∀ a : Idx d4Certificate,
    d4bCol (xCol d4Certificate d4StringData i 0 a) = d4bTh a ∧
    d4bCol (xCol d4Certificate d4StringData i 1 a) =
      d4bEs i true * d4bTh a + d4bTh a * d4bEs i true ∧
    d4bCol (xCol d4Certificate d4StringData i 2 a) =
      d4bEs i true * d4bTh a * d4bEs i true ∧
    d4bCol (xCol d4Certificate d4StringData i 3 a) = 0

@[expose] def D4bYOK (i : Fin Tag.D4.rank) : Prop := ∀ a : Idx d4Certificate,
    d4bCol (yCol d4Certificate d4StringData i 0 a) = d4bTh a ∧
    d4bCol (yCol d4Certificate d4StringData i 1 a) =
      d4bEs i false * d4bTh a + d4bTh a * d4bEs i false ∧
    d4bCol (yCol d4Certificate d4StringData i 2 a) =
      d4bEs i false * d4bTh a * d4bEs i false ∧
    d4bCol (yCol d4Certificate d4StringData i 3 a) = 0

end CFSG.Quasithin
