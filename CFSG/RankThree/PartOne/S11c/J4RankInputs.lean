module

public import CFSG.Assembly.Defs
public import CFSG.LinearAlgebra.ExtraspecialCyclotomicModule
public import CFSG.Sporadic.Schreier.J4SSylowBase

@[expose] public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LinearAlgebra CFSG.Sporadic.J4Schreier Matrix Module
open scoped Matrix
open CFSG.Sporadic.SmallF2 (rowsMatrix)

local instance (priority := high) cleanAddCommGroupFin (n : ℕ) : AddCommGroup (Fin n → ZMod 2) :=
  @Pi.addCommGroup (Fin n) (fun _ => ZMod 2) (fun _ => NonUnitalNonAssocRing.toAddCommGroup)

@[expose] def minorQ1 : List ℕ :=
  [1, 2, 3, 0, 5, 4, 7, 10, 9, 8, 14, 11, 6, 12, 13, 15, 17, 19, 18, 16, 23, 21, 22, 24, 20, 25]

@[expose] def minorB1 : List ℕ :=
  [54735585, 26183147, 7388452, 9055562, 17826433, 34089790, 14205083, 6730297, 48756935,
    5527611, 34714738, 44757205, 25184831, 18909855, 39547701, 60933955, 40926075, 49655312,
    30075283, 16183365, 62661840, 52814888, 8296138, 51870984, 49684949, 60984593]

@[expose] def minorQ14 : List ℕ :=
  [2, 5, 0, 1, 3, 4, 6, 7, 10, 8, 9, 13, 11, 12, 14, 16, 15, 17, 18, 19, 22, 20, 24, 21, 25, 23]

@[expose] def minorB14 : List ℕ :=
  [50501912, 24304203, 19771478, 23999583, 61295706, 36590740, 47891519, 15630608, 40174908,
    31114840, 19929938, 64597436, 8371102, 54907557, 62274299, 31985775, 7938364, 6381837,
    42966965, 56861827, 44370859, 63586080, 8016959, 66402897, 30748862, 57647712]

@[expose] def minorRow (a : Fin 26) : Fin 112 := Fin.castLE (by norm_num) a

@[expose] def minorCol (qs : List ℕ) (b : Fin 26) : Fin 112 :=
  ⟨qs[b.val]! % 112, Nat.mod_lt _ (by norm_num)⟩

@[expose] def minorInv (Bs : List ℕ) : Matrix (Fin 26) (Fin 26) (ZMod 2) :=
  Matrix.of fun b c => if (Bs[b.val]!).testBit c.val then 1 else 0

@[expose] def MinorCheck (X : Array ℕ) (qs Bs : List ℕ) : Prop :=
  ∀ a c : Fin 26, (∑ b : Fin 26, (rowsMatrix 112 X - 1) (minorRow a) (minorCol qs b) *
    minorInv Bs b c) = if a = c then (1 : ZMod 2) else 0

instance (X : Array ℕ) (qs Bs : List ℕ) : Decidable (MinorCheck X qs Bs) := by
  unfold MinorCheck
  infer_instance

end CFSG.RankThree.PartOne
