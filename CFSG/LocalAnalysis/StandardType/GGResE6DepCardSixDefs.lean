module

public import CFSG.LocalAnalysis.StandardType.GGDepASmallNat
public import CFSG.LocalAnalysis.StandardType.GGResE6DepCardSixData

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev CS6E : Type := GGDepAE 3 6

@[expose] def cs6Root : Fin 6 → CS6E :=
  Fin.cases (![0, 1, 0, 2, 1, 0] : Fin 6 → ZMod 3) (fun j : Fin 5 => Pi.single j.castSucc 1)

@[expose] def cs6Alpha (i : Fin 6) : CS6E := fun j =>
  if h : j.val < 5 then (CartanMatrix.E 6 i ⟨j.val + 1, by omega⟩ : ZMod 3) else 0

@[expose] def cs6X : CS6E := Pi.single 5 1

@[expose] def cs6Refl (i : Fin 6) : Module.End (ZMod 3) CS6E :=
  ggDepARefl (cs6Root i) (cs6Alpha i)

@[expose] def CS6Gens (ha aa : CS6E) : Set (Module.End (ZMod 3) CS6E) :=
  Set.range cs6Refl ∪ {ggDepARefl ha aa}

@[expose] def CS6Outcome (d : Nat) (ha aa y : CS6E) : Prop :=
  (∃ g ∈ Submonoid.closure (CS6Gens ha aa), GGDepAIsTv g) ∨
  (∃ g ∈ Submonoid.closure (CS6Gens ha aa), g cs6X = y ∨ g cs6X = -y) ∨
  (d = 6 ∧ ∃ F : Finset CS6E, 122 ≤ F.card ∧
    ∀ v ∈ F, ∃ g ∈ Submonoid.closure (CS6Gens ha aa), g cs6X = v) ∨
  ggDepARefl ha aa ∈ Submonoid.closure (Set.range cs6Refl)

@[expose] def cs6J : Fin 5 → Fin 4 → Fin 6 :=
  ![![0, 1, 2, 3], ![0, 2, 3, 4], ![1, 2, 3, 4], ![1, 3, 4, 5], ![2, 3, 4, 5]]

@[expose] def cs6NumPat (jj : Fin 5) : Nat := (CS6Data.patterns.getD jj []).length

@[expose] def cs6PatPair (jj : Fin 5) (pi : Nat) (i : Fin 4) : ZMod 3 × ZMod 3 :=
  ((((CS6Data.patterns.getD jj []).getD pi []).getD i (0, 0)).1,
    (((CS6Data.patterns.getD jj []).getD pi []).getD i (0, 0)).2)

@[expose] def cs6PatDet (jj : Fin 5) (pi : Nat) : Nat := ((CS6Data.patDets.getD jj []).getD pi 0)

@[expose] def cs6Ys (jj : Fin 5) : List CS6E :=
  (CS6Data.yReps.getD jj []).map (ggDepANToZ 3 6)

@[expose] def CS6CellHyp (jj : Fin 5) (pi : Nat) (ha aa y : CS6E) : Prop :=
  pi < cs6NumPat jj ∧ (∃ r ∈ cs6Ys jj, y = r ∨ y = -r) ∧
  (∀ i : Fin 4, ggDepAdot (cs6Alpha (cs6J jj i)) ha = (cs6PatPair jj pi i).1) ∧
  (∀ i : Fin 4, ggDepAdot aa (cs6Root (cs6J jj i)) = (cs6PatPair jj pi i).2) ∧
  ggDepAdot aa y = 0 ∧ ggDepAdot aa ha = 2

end CFSG.StandardType
