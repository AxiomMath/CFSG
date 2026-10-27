module

public import CFSG.Quasithin.Recognition.M12AscHPres
public import CFSG.Certificates.CosetTablePresented
public meta import CFSG.Certificates.CosetTablePresented
public import CFSG.Certificates.SubgroupEnumeration
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import CFSG.Quasithin.Recognition.M12AscHModelInputs
public import Certificates.Certificate8084

public section

namespace CFSG.Quasithin

open CFSG.CosetTable

theorem ascH_card_le :
    Finite (PG 4 ascHRels) ∧ Nat.card (PG 4 ascHRels) ≤ 192 :=
  Certificates.certificate8084

@[expose] def ascHImg : Fin 4 → Equiv.Perm (Fin 12)
  | 0 => List.formPerm [0, 9, 4, 10] * List.formPerm [1, 11, 6, 8]
  | 1 => List.formPerm [0, 10, 4, 9] * List.formPerm [1, 11, 6, 8] * List.formPerm [2, 3] *
      List.formPerm [5, 7]
  | 2 => List.formPerm [1, 11, 9] * List.formPerm [2, 5, 7] * List.formPerm [6, 8, 10]
  | 3 => List.formPerm [1, 10] * List.formPerm [2, 5] * List.formPerm [6, 9] *
      List.formPerm [8, 11]

@[expose] def ascHLetter (l : Fin 4 × Bool) : Equiv.Perm (Fin 12) :=
  cond l.2 (ascHImg l.1) (ascHImg l.1)⁻¹

@[expose] def ascHEval (w : List (Fin 4 × Bool)) : Equiv.Perm (Fin 12) := (w.map ascHLetter).prod

theorem ascHImg_relators : ∀ w ∈ ascHRels, ascHEval w = 1 := by decide +kernel

@[expose] def ascHModel : Subgroup (Equiv.Perm (Fin 12)) :=
  Subgroup.closure (Set.range ascHImg)

@[expose] def tabOf (p : Equiv.Perm (Fin 12)) : List (Fin 12) := (List.finRange 12).map p

theorem tabOf_injective : Function.Injective tabOf := by
  intro p q h
  ext i
  exact congrArg Fin.val ((List.map_inj_left.1 h) i (List.mem_finRange i))

theorem tabOf_mul (p q : Equiv.Perm (Fin 12)) : tabOf (p * q) = (tabOf q).map p := by
  simp [tabOf, List.map_map, Function.comp_def]

@[expose] def ascHData : List (List (Fin 4 × Bool) × List (Fin 12)) :=
  [([], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]),
  ([(2, false)], [0, 9, 7, 3, 4, 2, 10, 5, 6, 11, 8, 1]),
  ([(3, true)], [0, 10, 5, 3, 4, 2, 9, 7, 11, 6, 1, 8]),
  ([(2, true)], [0, 11, 5, 3, 4, 7, 8, 2, 10, 1, 6, 9]),
  ([(1, false)], [9, 8, 3, 2, 10, 7, 11, 5, 6, 4, 0, 1]),
  ([(0, true)], [9, 11, 2, 3, 10, 5, 8, 7, 1, 4, 0, 6]),
  ([(0, false)], [10, 8, 2, 3, 9, 5, 11, 7, 6, 0, 4, 1]),
  ([(1, true)], [10, 11, 3, 2, 9, 7, 8, 5, 1, 0, 4, 6]),
  ([(1, true), (0, true)], [0, 6, 3, 2, 4, 7, 1, 5, 11, 9, 10, 8]),
  ([(3, true), (2, false)], [0, 6, 7, 3, 4, 5, 1, 2, 9, 8, 11, 10]),
  ([(3, true), (2, true)], [0, 8, 2, 3, 4, 7, 11, 5, 1, 10, 9, 6]),
  ([(3, true), (1, true)], [1, 8, 3, 5, 6, 7, 11, 2, 10, 0, 4, 9]),
  ([(2, true), (0, true)], [1, 9, 5, 3, 6, 7, 10, 2, 11, 4, 0, 8]),
  ([(2, true), (1, false)], [1, 10, 3, 5, 6, 2, 9, 7, 8, 4, 0, 11]),
  ([(3, true), (0, false)], [1, 11, 5, 3, 6, 2, 8, 7, 9, 0, 4, 10]),
  ([(1, false), (0, true)], [4, 1, 3, 2, 0, 7, 6, 5, 8, 10, 9, 11]),
  ([(0, true), (0, true)], [4, 6, 2, 3, 0, 5, 1, 7, 11, 10, 9, 8]),
  ([(3, true), (0, true)], [6, 8, 5, 3, 1, 2, 11, 7, 10, 4, 0, 9]),
  ([(2, true), (1, true)], [6, 9, 3, 5, 1, 2, 10, 7, 11, 0, 4, 8]),
  ([(2, true), (0, false)], [6, 10, 5, 3, 1, 7, 9, 2, 8, 0, 4, 11]),
  ([(3, true), (1, false)], [6, 11, 3, 5, 1, 7, 8, 2, 9, 4, 0, 10]),
  ([(2, false), (1, true)], [8, 1, 3, 7, 11, 5, 6, 2, 9, 0, 4, 10]),
  ([(2, false), (0, false)], [8, 6, 7, 3, 11, 2, 1, 5, 10, 0, 4, 9]),
  ([(0, true), (3, true)], [9, 0, 5, 3, 10, 2, 4, 7, 6, 8, 11, 1]),
  ([(1, false), (3, true)], [9, 0, 7, 2, 10, 3, 4, 5, 1, 11, 8, 6]),
  ([(1, false), (2, true)], [9, 1, 7, 2, 10, 5, 6, 3, 0, 8, 11, 4]),
  ([(1, false), (2, false)], [9, 4, 5, 2, 10, 3, 0, 7, 11, 1, 6, 8]),
  ([(0, true), (2, false)], [9, 4, 7, 3, 10, 2, 0, 5, 8, 6, 1, 11]),
  ([(0, true), (2, true)], [9, 6, 5, 3, 10, 7, 1, 2, 0, 11, 8, 4]),
  ([(1, true), (2, false)], [10, 0, 5, 2, 9, 3, 4, 7, 8, 6, 1, 11]),
  ([(0, false), (2, false)], [10, 0, 7, 3, 9, 2, 4, 5, 11, 1, 6, 8]),
  ([(0, false), (2, true)], [10, 1, 5, 3, 9, 7, 6, 2, 4, 8, 11, 0]),
  ([(0, false), (3, true)], [10, 4, 5, 3, 9, 2, 0, 7, 1, 11, 8, 6]),
  ([(1, true), (3, true)], [10, 4, 7, 2, 9, 3, 0, 5, 6, 8, 11, 1]),
  ([(1, true), (2, true)], [10, 6, 7, 2, 9, 5, 1, 3, 4, 11, 8, 0]),
  ([(2, false), (0, true)], [11, 1, 7, 3, 8, 2, 6, 5, 9, 4, 0, 10]),
  ([(2, false), (1, false)], [11, 6, 3, 7, 8, 5, 1, 2, 10, 4, 0, 9]),
  ([(2, true), (1, true), (0, true)], [0, 8, 3, 5, 4, 2, 11, 7, 9, 1, 6, 10]),
  ([(1, true), (0, true), (2, true)], [0, 8, 7, 2, 4, 5, 11, 3, 10, 6, 1, 9]),
  ([(3, true), (1, true), (0, true)], [0, 9, 3, 5, 4, 7, 10, 2, 8, 6, 1, 11]),
  ([(1, true), (0, true), (2, false)], [0, 9, 5, 2, 4, 3, 10, 7, 1, 8, 11, 6]),
  ([(2, false), (1, true), (0, true)], [0, 10, 3, 7, 4, 5, 9, 2, 1, 11, 8, 6]),
  ([(1, true), (0, true), (3, true)], [0, 10, 7, 2, 4, 3, 9, 5, 8, 1, 6, 11]),
  ([(3, true), (1, true), (2, false)], [1, 0, 2, 5, 6, 3, 4, 7, 11, 9, 10, 8]),
  ([(3, true), (0, false), (2, false)], [1, 0, 7, 3, 6, 5, 4, 2, 8, 10, 9, 11]),
  ([(2, true), (0, true), (2, false)], [1, 4, 2, 3, 6, 5, 0, 7, 10, 8, 11, 9]),
  ([(2, true), (1, false), (2, false)], [1, 4, 7, 5, 6, 3, 0, 2, 9, 11, 8, 10]),
  ([(1, false), (2, false), (0, true)], [1, 8, 5, 2, 6, 3, 11, 7, 4, 10, 9, 0]),
  ([(0, false), (2, false), (0, true)], [1, 8, 7, 3, 6, 2, 11, 5, 0, 9, 10, 4]),
  ([(3, true), (1, true), (2, true)], [1, 9, 7, 5, 6, 2, 10, 3, 4, 8, 11, 0]),
  ([(3, true), (0, false), (2, true)], [1, 10, 2, 3, 6, 7, 9, 5, 4, 11, 8, 0]),
  ([(1, true), (2, false), (1, true)], [1, 11, 2, 5, 6, 7, 8, 3, 0, 10, 9, 4]),
  ([(0, true), (2, false), (1, true)], [1, 11, 3, 7, 6, 5, 8, 2, 4, 9, 10, 0]),
  ([(2, true), (0, true), (0, true)], [4, 8, 5, 3, 0, 7, 11, 2, 9, 6, 1, 10]),
  ([(2, false), (1, false), (0, true)], [4, 9, 3, 7, 0, 5, 10, 2, 6, 8, 11, 1]),
  ([(3, true), (0, true), (0, true)], [4, 9, 5, 3, 0, 2, 10, 7, 8, 1, 6, 11]),
  ([(1, false), (0, true), (3, true)], [4, 9, 7, 2, 0, 3, 10, 5, 11, 6, 1, 8]),
  ([(3, true), (1, false), (0, true)], [4, 10, 3, 5, 0, 7, 9, 2, 11, 1, 6, 8]),
  ([(1, false), (0, true), (2, false)], [4, 10, 5, 2, 0, 3, 9, 7, 6, 11, 8, 1]),
  ([(2, false), (0, true), (0, true)], [4, 10, 7, 3, 0, 2, 9, 5, 1, 8, 11, 6]),
  ([(2, true), (1, false), (0, true)], [4, 11, 3, 5, 0, 2, 8, 7, 10, 6, 1, 9]),
  ([(1, false), (0, true), (2, true)], [4, 11, 7, 2, 0, 5, 8, 3, 9, 1, 6, 10]),
  ([(2, true), (0, false), (2, false)], [6, 0, 2, 3, 1, 5, 4, 7, 9, 11, 8, 10]),
  ([(2, true), (1, true), (2, false)], [6, 0, 7, 5, 1, 3, 4, 2, 10, 8, 11, 9]),
  ([(3, true), (1, false), (2, false)], [6, 4, 2, 5, 1, 3, 0, 7, 8, 10, 9, 11]),
  ([(3, true), (0, true), (2, false)], [6, 4, 7, 3, 1, 5, 0, 2, 11, 9, 10, 8]),
  ([(1, false), (2, false), (1, true)], [6, 8, 2, 5, 1, 7, 11, 3, 4, 9, 10, 0]),
  ([(0, false), (2, false), (1, true)], [6, 8, 3, 7, 1, 5, 11, 2, 0, 10, 9, 4]),
  ([(3, true), (0, true), (2, true)], [6, 9, 2, 3, 1, 7, 10, 5, 0, 8, 11, 4]),
  ([(3, true), (1, false), (2, true)], [6, 10, 7, 5, 1, 2, 9, 3, 0, 11, 8, 4]),
  ([(1, true), (2, false), (0, true)], [6, 11, 5, 2, 1, 3, 8, 7, 0, 9, 10, 4]),
  ([(0, true), (2, false), (0, true)], [6, 11, 7, 3, 1, 2, 8, 5, 4, 10, 9, 0]),
  ([(1, true), (2, true), (1, true)], [8, 0, 2, 7, 11, 3, 4, 5, 6, 10, 9, 1]),
  ([(0, false), (2, true), (0, true)], [8, 0, 5, 3, 11, 7, 4, 2, 1, 9, 10, 6]),
  ([(0, true), (3, true), (0, true)], [8, 1, 5, 3, 11, 2, 6, 7, 0, 10, 9, 4]),
  ([(1, true), (3, true), (0, true)], [8, 1, 7, 2, 11, 3, 6, 5, 4, 9, 10, 0]),
  ([(2, false), (0, false), (3, true)], [8, 4, 2, 3, 11, 7, 0, 5, 9, 1, 6, 10]),
  ([(0, true), (2, true), (1, true)], [8, 4, 3, 5, 11, 2, 0, 7, 6, 9, 10, 1]),
  ([(2, false), (1, true), (3, true)], [8, 4, 5, 7, 11, 3, 0, 2, 10, 6, 1, 9]),
  ([(1, false), (2, true), (0, true)], [8, 4, 7, 2, 11, 5, 0, 3, 1, 10, 9, 6]),
  ([(1, false), (3, true), (1, true)], [8, 6, 2, 7, 11, 5, 1, 3, 0, 9, 10, 4]),
  ([(0, false), (3, true), (1, true)], [8, 6, 3, 5, 11, 7, 1, 2, 4, 10, 9, 0]),
  ([(2, false), (0, false), (2, true)], [8, 9, 2, 3, 11, 5, 10, 7, 4, 6, 1, 0]),
  ([(3, true), (2, false), (1, false)], [8, 9, 3, 7, 11, 2, 10, 5, 1, 4, 0, 6]),
  ([(2, false), (1, true), (2, true)], [8, 10, 5, 7, 11, 2, 9, 3, 4, 1, 6, 0]),
  ([(3, true), (2, false), (0, true)], [8, 10, 7, 3, 11, 5, 9, 2, 6, 4, 0, 1]),
  ([(3, true), (2, true), (0, false)], [9, 1, 2, 3, 10, 7, 6, 5, 11, 0, 4, 8]),
  ([(3, true), (2, true), (1, true)], [9, 6, 3, 2, 10, 5, 1, 7, 8, 0, 4, 11]),
  ([(0, true), (3, true), (2, false)], [9, 8, 7, 3, 10, 5, 11, 2, 4, 1, 6, 0]),
  ([(1, false), (3, true), (2, false)], [9, 11, 5, 2, 10, 7, 8, 3, 4, 6, 1, 0]),
  ([(3, true), (2, true), (1, false)], [10, 1, 3, 2, 9, 5, 6, 7, 11, 4, 0, 8]),
  ([(3, true), (2, true), (0, true)], [10, 6, 2, 3, 9, 7, 1, 5, 8, 4, 0, 11]),
  ([(1, true), (3, true), (2, false)], [10, 8, 5, 2, 9, 7, 11, 3, 0, 1, 6, 4]),
  ([(0, false), (3, true), (2, false)], [10, 11, 7, 3, 9, 5, 8, 2, 0, 6, 1, 4]),
  ([(2, false), (0, true), (3, true)], [11, 0, 2, 3, 8, 7, 4, 5, 10, 6, 1, 9]),
  ([(0, false), (2, true), (1, true)], [11, 0, 3, 5, 8, 2, 4, 7, 1, 10, 9, 6]),
  ([(2, false), (1, false), (3, true)], [11, 0, 5, 7, 8, 3, 4, 2, 9, 1, 6, 10]),
  ([(1, true), (2, true), (0, true)], [11, 0, 7, 2, 8, 5, 4, 3, 6, 9, 10, 1]),
  ([(1, true), (3, true), (1, true)], [11, 1, 2, 7, 8, 5, 6, 3, 4, 10, 9, 0]),
  ([(0, true), (3, true), (1, true)], [11, 1, 3, 5, 8, 7, 6, 2, 0, 9, 10, 4]),
  ([(1, false), (2, true), (1, true)], [11, 4, 2, 7, 8, 3, 0, 5, 1, 9, 10, 6]),
  ([(0, true), (2, true), (0, true)], [11, 4, 5, 3, 8, 7, 0, 2, 6, 10, 9, 1]),
  ([(0, false), (3, true), (0, true)], [11, 6, 5, 3, 8, 2, 1, 7, 4, 9, 10, 0]),
  ([(1, false), (3, true), (0, true)], [11, 6, 7, 2, 8, 3, 1, 5, 0, 10, 9, 4]),
  ([(2, false), (1, false), (2, true)], [11, 9, 5, 7, 8, 2, 10, 3, 0, 6, 1, 4]),
  ([(3, true), (2, false), (0, false)], [11, 9, 7, 3, 8, 5, 10, 2, 1, 0, 4, 6]),
  ([(2, false), (0, true), (2, true)], [11, 10, 2, 3, 8, 5, 9, 7, 0, 1, 6, 4]),
  ([(3, true), (2, false), (1, true)], [11, 10, 3, 7, 8, 2, 9, 5, 6, 0, 4, 1]),
  ([(3, true), (2, false), (1, true), (0, true)], [0, 1, 3, 7, 4, 2, 6, 5, 10, 8, 11, 9]),
  ([(1, true), (0, true), (3, true), (2, false)], [0, 1, 5, 2, 4, 7, 6, 3, 9, 11, 8, 10]),
  ([(2, true), (1, true), (0, true), (2, false)], [0, 1, 7, 5, 4, 3, 6, 2, 11, 10, 9, 8]),
  ([(3, true), (1, true), (0, true), (2, false)], [0, 6, 2, 5, 4, 3, 1, 7, 10, 11, 8, 9]),
  ([(2, false), (1, true), (0, true), (2, true)], [0, 6, 5, 7, 4, 2, 1, 3, 8, 10, 9, 11]),
  ([(2, false), (1, true), (0, true), (3, true)], [0, 8, 5, 7, 4, 3, 11, 2, 6, 9, 10, 1]),
  ([(2, true), (1, true), (0, true), (2, true)], [0, 10, 2, 5, 4, 7, 9, 3, 6, 8, 11, 1]),
  ([(2, false), (1, true), (0, true), (2, false)], [0, 11, 2, 7, 4, 3, 8, 5, 9, 6, 1, 10]),
  ([(3, true), (2, true), (1, true), (0, true)], [0, 11, 3, 2, 4, 5, 8, 7, 6, 10, 9, 1]),
  ([(3, true), (1, true), (0, true), (2, true)], [0, 11, 7, 5, 4, 2, 8, 3, 1, 9, 10, 6]),
  ([(2, false), (0, false), (2, true), (1, true)], [1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10]),
  ([(2, false), (1, true), (2, true), (0, true)], [1, 0, 5, 7, 6, 2, 4, 3, 10, 11, 8, 9]),
  ([(0, false), (3, true), (2, false), (1, true)], [1, 4, 3, 7, 6, 2, 0, 5, 11, 10, 9, 8]),
  ([(1, true), (3, true), (2, false), (0, true)], [1, 4, 5, 2, 6, 7, 0, 3, 8, 9, 10, 11]),
  ([(1, false), (0, true), (3, true), (1, true)], [1, 8, 2, 7, 6, 5, 11, 3, 9, 4, 0, 10]),
  ([(1, true), (0, true), (2, true), (1, true)], [1, 9, 2, 7, 6, 3, 10, 5, 8, 0, 4, 11]),
  ([(2, false), (0, true), (3, true), (1, true)], [1, 9, 3, 2, 6, 5, 10, 7, 0, 11, 8, 4]),
  ([(2, false), (1, false), (3, true), (0, true)], [1, 10, 5, 7, 6, 3, 9, 2, 0, 8, 11, 4]),
  ([(1, false), (0, true), (2, true), (0, true)], [1, 10, 7, 2, 6, 5, 9, 3, 11, 0, 4, 8]),
  ([(1, true), (0, true), (3, true), (0, true)], [1, 11, 7, 2, 6, 3, 8, 5, 10, 4, 0, 9]),
  ([(3, true), (1, false), (0, true), (2, false)], [4, 1, 2, 5, 0, 3, 6, 7, 9, 8, 11, 10]),
  ([(2, false), (1, false), (0, true), (2, true)], [4, 1, 5, 7, 0, 2, 6, 3, 11, 9, 10, 8]),
  ([(3, true), (2, false), (0, true), (0, true)], [4, 1, 7, 3, 0, 5, 6, 2, 10, 11, 8, 9]),
  ([(3, true), (2, false), (1, false), (0, true)], [4, 6, 3, 7, 0, 2, 1, 5, 9, 11, 8, 10]),
  ([(1, false), (0, true), (3, true), (2, false)], [4, 6, 5, 2, 0, 7, 1, 3, 10, 8, 11, 9]),
  ([(2, true), (1, false), (0, true), (2, false)], [4, 6, 7, 5, 0, 3, 1, 2, 8, 9, 10, 11]),
  ([(2, false), (1, false), (0, true), (2, false)], [4, 8, 2, 7, 0, 3, 11, 5, 10, 1, 6, 9]),
  ([(3, true), (2, true), (1, false), (0, true)], [4, 8, 3, 2, 0, 5, 11, 7, 1, 9, 10, 6]),
  ([(3, true), (1, false), (0, true), (2, true)], [4, 8, 7, 5, 0, 2, 11, 3, 6, 10, 9, 1]),
  ([(2, true), (1, false), (0, true), (2, true)], [4, 9, 2, 5, 0, 7, 10, 3, 1, 11, 8, 6]),
  ([(3, true), (2, true), (0, true), (0, true)], [4, 11, 2, 3, 0, 7, 8, 5, 6, 9, 10, 1]),
  ([(2, false), (1, false), (0, true), (3, true)], [4, 11, 5, 7, 0, 3, 8, 2, 1, 10, 9, 6]),
  ([(0, true), (3, true), (2, false), (1, true)], [6, 0, 3, 7, 1, 2, 4, 5, 8, 9, 10, 11]),
  ([(1, false), (3, true), (2, false), (0, true)], [6, 0, 5, 2, 1, 7, 4, 3, 11, 10, 9, 8]),
  ([(2, false), (0, true), (2, true), (1, true)], [6, 4, 3, 2, 1, 7, 0, 5, 10, 11, 8, 9]),
  ([(2, false), (1, false), (2, true), (0, true)], [6, 4, 5, 7, 1, 2, 0, 3, 9, 8, 11, 10]),
  ([(1, false), (0, true), (3, true), (0, true)], [6, 8, 7, 2, 1, 3, 11, 5, 9, 0, 4, 10]),
  ([(2, false), (1, true), (3, true), (0, true)], [6, 9, 5, 7, 1, 3, 10, 2, 4, 11, 8, 0]),
  ([(1, true), (0, true), (2, true), (0, true)], [6, 9, 7, 2, 1, 5, 10, 3, 8, 4, 0, 11]),
  ([(1, false), (0, true), (2, true), (1, true)], [6, 10, 2, 7, 1, 3, 9, 5, 11, 4, 0, 8]),
  ([(2, false), (0, false), (3, true), (1, true)], [6, 10, 3, 2, 1, 5, 9, 7, 4, 8, 11, 0]),
  ([(1, true), (0, true), (3, true), (1, true)], [6, 11, 2, 7, 1, 5, 8, 3, 10, 0, 4, 9]),
  ([(3, true), (0, false), (2, true), (1, true)], [8, 0, 3, 2, 11, 5, 4, 7, 10, 1, 6, 9]),
  ([(3, true), (1, true), (2, true), (0, true)], [8, 0, 7, 5, 11, 2, 4, 3, 9, 6, 1, 10]),
  ([(1, false), (0, true), (2, false), (1, true)], [8, 1, 2, 5, 11, 7, 6, 3, 10, 4, 0, 9]),
  ([(1, true), (0, true), (2, false), (0, true)], [8, 6, 5, 2, 11, 3, 1, 7, 9, 4, 0, 10]),
  ([(1, true), (3, true), (0, true), (2, false)], [8, 9, 5, 2, 11, 7, 10, 3, 6, 0, 4, 1]),
  ([(2, true), (1, true), (2, false), (0, true)], [8, 9, 7, 5, 11, 3, 10, 2, 0, 1, 6, 4]),
  ([(0, false), (3, true), (1, true), (2, false)], [8, 10, 2, 5, 11, 3, 9, 7, 1, 0, 4, 6]),
  ([(2, true), (0, false), (2, false), (1, true)], [8, 10, 3, 2, 11, 7, 9, 5, 0, 6, 1, 4]),
  ([(1, false), (2, false), (1, true), (0, true)], [9, 0, 2, 5, 10, 7, 4, 3, 8, 1, 6, 11]),
  ([(0, true), (2, false), (1, true), (0, true)], [9, 0, 3, 7, 10, 5, 4, 2, 11, 6, 1, 8]),
  ([(0, true), (2, true), (1, true), (0, true)], [9, 1, 3, 5, 10, 2, 6, 7, 4, 11, 8, 0]),
  ([(1, false), (3, true), (1, true), (0, true)], [9, 4, 2, 7, 10, 5, 0, 3, 6, 11, 8, 1]),
  ([(0, true), (3, true), (1, true), (0, true)], [9, 4, 3, 5, 10, 7, 0, 2, 1, 8, 11, 6]),
  ([(1, false), (2, true), (1, true), (0, true)], [9, 6, 2, 7, 10, 3, 1, 5, 4, 8, 11, 0]),
  ([(3, true), (1, true), (2, false), (0, true)], [9, 8, 2, 5, 10, 3, 11, 7, 0, 6, 1, 4]),
  ([(3, true), (0, false), (2, false), (1, true)], [9, 11, 3, 7, 10, 2, 8, 5, 0, 1, 6, 4]),
  ([(1, true), (3, true), (1, true), (0, true)], [10, 0, 2, 7, 9, 5, 4, 3, 1, 8, 11, 6]),
  ([(0, false), (3, true), (1, true), (0, true)], [10, 0, 3, 5, 9, 7, 4, 2, 6, 11, 8, 1]),
  ([(1, true), (2, true), (1, true), (0, true)], [10, 1, 2, 7, 9, 3, 6, 5, 0, 11, 8, 4]),
  ([(1, true), (2, false), (1, true), (0, true)], [10, 4, 2, 5, 9, 7, 0, 3, 11, 6, 1, 8]),
  ([(0, false), (2, false), (1, true), (0, true)], [10, 4, 3, 7, 9, 5, 0, 2, 8, 1, 6, 11]),
  ([(0, false), (2, true), (1, true), (0, true)], [10, 6, 3, 5, 9, 2, 1, 7, 0, 8, 11, 4]),
  ([(3, true), (0, true), (2, false), (1, true)], [10, 8, 3, 7, 9, 2, 11, 5, 4, 6, 1, 0]),
  ([(3, true), (1, false), (2, false), (0, true)], [10, 11, 2, 5, 9, 3, 8, 7, 4, 1, 6, 0]),
  ([(1, false), (0, true), (2, false), (0, true)], [11, 1, 5, 2, 8, 3, 6, 7, 10, 0, 4, 9]),
  ([(3, true), (0, true), (2, true), (1, true)], [11, 4, 3, 2, 8, 5, 0, 7, 9, 6, 1, 10]),
  ([(3, true), (1, false), (2, true), (0, true)], [11, 4, 7, 5, 8, 2, 0, 3, 10, 1, 6, 9]),
  ([(1, true), (0, true), (2, false), (1, true)], [11, 6, 2, 5, 8, 7, 1, 3, 9, 0, 4, 10]),
  ([(0, true), (3, true), (1, true), (2, false)], [11, 9, 2, 5, 8, 3, 10, 7, 6, 4, 0, 1]),
  ([(2, true), (0, true), (2, false), (1, true)], [11, 9, 3, 2, 8, 7, 10, 5, 4, 1, 6, 0]),
  ([(1, false), (3, true), (0, true), (2, false)], [11, 10, 5, 2, 8, 7, 9, 3, 1, 4, 0, 6]),
  ([(2, true), (1, false), (2, false), (0, true)], [11, 10, 7, 5, 8, 3, 9, 2, 4, 6, 1, 0]),
  ([(1, true), (0, true), (3, true), (1, true), (0, true)], [0, 9, 2, 7, 4, 5, 10, 3, 11, 1, 6, 8]),
  ([(1, false), (0, true), (3, true), (1, true), (0, true)], [4, 10, 2, 7, 0, 5, 9, 3, 8, 6, 1, 11]),
  ([(2, false), (1, true), (0, true), (3, true), (0, true)], [9, 1, 5, 7, 10, 3, 6, 2, 8, 4, 0, 11]),
  ([(3, true), (1, true), (0, true), (2, true), (0, true)], [9, 6, 7, 5, 10, 2, 1, 3, 11, 4, 0, 8]),
  ([(2, false), (1, false), (0, true), (2, true), (0, true)], [9, 8, 5, 7, 10, 2, 11, 3, 1, 0, 4, 6]),
  ([(2, true), (1, false), (0, true), (2, false), (0, true)], [9, 11, 7, 5, 10, 3, 8, 2, 6, 0, 4, 1]),
  ([(3, true), (1, false), (0, true), (2, true), (0, true)], [10, 1, 7, 5, 9, 2, 6, 3, 8, 0, 4, 11]),
  ([(2, false), (1, false), (0, true), (3, true), (0, true)], [10, 6, 5, 7, 9, 3, 1, 2, 11, 0, 4, 8]),
  ([(2, true), (1, true), (0, true), (2, false), (0, true)], [10, 8, 7, 5, 9, 3, 11, 2, 1, 4, 0, 6]),
  ([(2, false), (1, true), (0, true), (2, true), (0, true)], [10, 11, 5, 7, 9, 2, 8, 3, 6, 4, 0, 1])]

@[expose] def ascHTabs : List (List (Fin 12)) := ascHData.map Prod.snd

theorem ascHData_ok : ∀ p ∈ ascHData, tabOf (ascHEval p.1) = p.2 := by decide +kernel

theorem ascHTabs_closed :
    ∀ l : Fin 4 × Bool, ∀ t ∈ ascHTabs, t.map (ascHLetter l) ∈ ascHTabs := by decide +kernel

theorem ascHTabs_nodup : ascHTabs.Nodup := by decide +kernel

theorem ascHTabs_length : ascHTabs.length = 192 := by decide +kernel

theorem tabOf_one : tabOf 1 ∈ ascHTabs := by decide +kernel

theorem ascHLetter_mem_signed (l : Fin 4 × Bool) :
    ascHLetter l ∈ CFSG.Certificates.SubgroupEnumeration.signedGenerators (Set.range ascHImg) := by
  obtain ⟨i, b⟩ := l
  cases b
  · exact Or.inr ⟨ascHImg i, ⟨i, rfl⟩, rfl⟩
  · exact Or.inl ⟨i, rfl⟩

theorem mem_ascHModel_iff (g : Equiv.Perm (Fin 12)) : g ∈ ascHModel ↔ tabOf g ∈ ascHTabs := by
  have h : {e : Equiv.Perm (Fin 12) | tabOf e ∈ ascHTabs} = (ascHModel : Set (Equiv.Perm (Fin 12))) := by
    refine CFSG.Certificates.subgroup_enumeration_completeness (Set.range ascHImg) _ tabOf_one ?_ ?_
    · intro e he
      obtain ⟨p, hp, hpe⟩ := List.mem_map.1 he
      have h1 := ascHData_ok p hp
      have h2 : ascHEval p.1 = e := tabOf_injective (h1.trans hpe)
      exact ⟨p.1.map ascHLetter, fun a ha => by
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 ha
        exact ascHLetter_mem_signed l, h2⟩
    · intro a ha e he
      have : ∃ l : Fin 4 × Bool, ascHLetter l = a := by
        rcases ha with ⟨i, rfl⟩ | ⟨_, ⟨i, rfl⟩, rfl⟩
        · exact ⟨(i, true), rfl⟩
        · exact ⟨(i, false), rfl⟩
      obtain ⟨l, rfl⟩ := this
      show tabOf (ascHLetter l * e) ∈ ascHTabs
      rw [tabOf_mul]
      exact ascHTabs_closed l _ he
  exact (Set.ext_iff.1 h g).symm

theorem ascHModel_card : Nat.card ascHModel = 192 := by
  have h1 : Nat.card ascHModel = Nat.card {t // t ∈ ascHTabs} := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun g : ascHModel => ⟨tabOf g, (mem_ascHModel_iff _).1 g.2⟩) ⟨?_, ?_⟩)
    · intro g h hgh
      exact Subtype.ext (tabOf_injective (congrArg Subtype.val hgh))
    · rintro ⟨t, ht⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
      refine ⟨⟨ascHEval p.1, ?_⟩, Subtype.ext (ascHData_ok p hp)⟩
      rw [mem_ascHModel_iff, ascHData_ok p hp]
      exact ht
  have h2 : Nat.card {t // t ∈ ascHTabs} = Nat.card ↥ascHTabs.toFinset :=
    Nat.card_congr (Equiv.subtypeEquivRight (by simp))
  rw [h1, h2, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup ascHTabs_nodup,
    ascHTabs_length]

noncomputable def ascHHom : PG 4 ascHRels →* Equiv.Perm (Fin 12) :=
  PresentedGroup.toGroup (f := ascHImg) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [FreeGroup.lift_mk]
    exact ascHImg_relators w hw)

theorem ascHHom_of (i : Fin 4) : ascHHom (PresentedGroup.of i) = ascHImg i := by
  rw [ascHHom, PresentedGroup.toGroup.of]

theorem range_ascHHom : ascHHom.range = ascHModel := by
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
      {r : FreeGroup (Fin 4) | r ∈ ascHRels.map FreeGroup.mk}, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [ascHHom_of]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, ascHHom_of i⟩

theorem ascHHom_mem (g : PG 4 ascHRels) : ascHHom g ∈ ascHModel := by
  rw [← range_ascHHom]; exact ⟨g, rfl⟩

noncomputable def ascHHom' : PG 4 ascHRels →* ascHModel := ascHHom.codRestrict _ ascHHom_mem

theorem ascHHom'_surjective : Function.Surjective ascHHom' := by
  intro y
  have hy : (y : Equiv.Perm (Fin 12)) ∈ ascHHom.range := by rw [range_ascHHom]; exact y.2
  obtain ⟨g, hg⟩ := hy
  exact ⟨g, Subtype.ext hg⟩

theorem ascHHom'_bijective : Function.Bijective ascHHom' := by
  obtain ⟨hfin, hle⟩ := ascH_card_le
  have := hfin
  exact ascHHom'_surjective.bijective_of_nat_card_le (by rw [ascHModel_card]; exact hle)

noncomputable def ascHEquiv : PG 4 ascHRels ≃* ascHModel :=
  MulEquiv.ofBijective ascHHom' ascHHom'_bijective

theorem ascHEquiv_of (i : Fin 4) :
    (ascHEquiv (PresentedGroup.of i) : Equiv.Perm (Fin 12)) = ascHImg i := ascHHom_of i

section Abstract

variable {K : Type*} [Group K] {a b x u : K}

theorem ascHRels_eval (h : HPres a b x u) :
    ∀ w ∈ ascHRels, (w.map fun l => cond l.2 (![a, b, x, u] l.1) (![a, b, x, u] l.1)⁻¹).prod = 1 := by
  intro w hw
  simp only [ascHRels, List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · simpa [pow_succ, mul_assoc] using h.r1
  · simpa [mul_assoc] using h.r2
  · simpa [mul_assoc] using h.r3
  · simpa [mul_assoc] using h.r4
  · simpa [mul_assoc] using h.r5
  · simpa [pow_succ, mul_assoc] using h.r6
  · simpa [mul_assoc] using h.r7
  · simpa [mul_assoc] using h.r8
  · simpa [mul_assoc] using h.r9
  · simpa [mul_assoc] using h.r10
  · simpa [mul_assoc] using h.r11
  · simpa [mul_assoc] using h.r12
  · simpa [mul_assoc] using h.r13
  · simpa [mul_assoc] using h.r14
  · simpa [mul_assoc] using h.r15
  · simpa [mul_assoc] using h.r16
  · simpa [mul_assoc] using h.r17

theorem exists_mulEquiv_ascHModel
    [Finite K] (hK : Nat.card K = 192) (h : HPres a b x u)
    (hgen : Subgroup.closure ({a, b, x, u} : Set K) = ⊤) :
    ∃ φ : K ≃* ascHModel, (φ a : Equiv.Perm (Fin 12)) = ascHImg 0 ∧
      (φ b : Equiv.Perm (Fin 12)) = ascHImg 1 ∧ (φ x : Equiv.Perm (Fin 12)) = ascHImg 2 ∧
      (φ u : Equiv.Perm (Fin 12)) = ascHImg 3 := by
  obtain ⟨hfin, hle⟩ := ascH_card_le
  let ψ : PG 4 ascHRels →* K := PresentedGroup.toGroup (f := ![a, b, x, u]) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [FreeGroup.lift_mk]
    exact ascHRels_eval h w hw)
  have hψ_of : ∀ i : Fin 4, ψ (PresentedGroup.of i) = ![a, b, x, u] i := fun i => by
    rw [PresentedGroup.toGroup.of]
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen]
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨PresentedGroup.of 0, hψ_of 0⟩
    · exact ⟨PresentedGroup.of 1, hψ_of 1⟩
    · exact ⟨PresentedGroup.of 2, hψ_of 2⟩
    · exact ⟨PresentedGroup.of 3, hψ_of 3⟩
  have hbij : Function.Bijective ψ := hsurj.bijective_of_nat_card_le (by rw [hK]; exact hle)
  let e₁ : PG 4 ascHRels ≃* K := MulEquiv.ofBijective ψ hbij
  have he₁ : ∀ i : Fin 4, e₁.symm (![a, b, x, u] i) = PresentedGroup.of i := fun i => by
    rw [← hψ_of i]
    exact e₁.symm_apply_apply (PresentedGroup.of i)
  have ha : e₁.symm a = PresentedGroup.of 0 := he₁ 0
  have hb : e₁.symm b = PresentedGroup.of 1 := he₁ 1
  have hx : e₁.symm x = PresentedGroup.of 2 := he₁ 2
  have hu : e₁.symm u = PresentedGroup.of 3 := he₁ 3
  refine ⟨e₁.symm.trans ascHEquiv, ?_, ?_, ?_, ?_⟩
  · show (ascHEquiv (e₁.symm a) : Equiv.Perm (Fin 12)) = _
    rw [ha]; exact ascHEquiv_of 0
  · show (ascHEquiv (e₁.symm b) : Equiv.Perm (Fin 12)) = _
    rw [hb]; exact ascHEquiv_of 1
  · show (ascHEquiv (e₁.symm x) : Equiv.Perm (Fin 12)) = _
    rw [hx]; exact ascHEquiv_of 2
  · show (ascHEquiv (e₁.symm u) : Equiv.Perm (Fin 12)) = _
    rw [hu]; exact ascHEquiv_of 3

end Abstract

end CFSG.Quasithin
