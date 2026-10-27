module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import CFSG.Dihedral.GorensteinWalter.FieldTransport
public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.Sporadic.Schreier.RuChainSpec
public import CFSG.Certificates.NativeSchreierEnum
public meta import CFSG.Sporadic.Schreier.RuChainSpec
public meta import CFSG.Sporadic.Schreier.RuCheckChains
public meta import CFSG.Certificates.NativeSchreierEnum
public meta import Certificates.Data.CFSGNative.Schreier.Enum3
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Schreier.RuCheckChainsBase
public import CFSG.Sporadic.Schreier.RuCheckLocalBase
public meta import CFSG.Sporadic.Schreier.RuCheckLocalBase
public meta import CFSG.Sporadic.Schreier.RuCheckOrbitsBase
public import CFSG.Sporadic.Schreier.RuCheckOrbitsBase
public import CFSG.Sporadic.Schreier.RuRestrictBase
public meta import CFSG.Sporadic.Schreier.RuRestrictBase

public section

namespace CFSG.Quasithin.RuRank3

open scoped MatrixGroups Matrix LinearAlgebra.Projectivization

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

open CFSG.Sporadic.RuSchreier

@[expose] def psl26X : Array ℕ :=
  #[9, 15, 6, 14, 11, 1, 25, 4, 2, 3, 24, 10, 21, 19, 16, 22, 5, 23, 13, 12, 7, 20, 8, 18, 17, 0]

@[expose] def psl26S : Array ℕ :=
  #[25, 1, 3, 2, 4, 15, 9, 11, 14, 6, 20, 7, 17, 18, 8, 5, 22, 12, 13, 23, 10, 24, 16, 19, 21, 0]

@[expose] def psl26T : Array ℕ :=
  #[25, 4, 2, 3, 1, 10, 21, 19, 16, 24, 5, 23, 13, 12, 22, 20, 8, 18, 17, 7, 15, 6, 14, 11, 9, 0]

@[expose] def powArr (n : ℕ) (g : Array ℕ) : ℕ → Array ℕ
  | 0 => idA n
  | k + 1 => compA n g (powArr n g k)

@[expose] def psl26Strong : Array (Array ℕ) :=
  #[#[9, 15, 6, 14, 11, 1, 25, 4, 2, 3, 24, 10, 21, 19, 16, 22, 5, 23, 13, 12, 7, 20, 8, 18, 17, 0],
    #[25, 1, 3, 2, 4, 15, 9, 11, 14, 6, 20, 7, 17, 18, 8, 5, 22, 12, 13, 23, 10, 24, 16, 19, 21, 0],
    #[25, 4, 2, 3, 1, 10, 21, 19, 16, 24, 5, 23, 13, 12, 22, 20, 8, 18, 17, 7, 15, 6, 14, 11, 9, 0],
    #[0, 4, 3, 2, 1, 20, 24, 23, 22, 21, 15, 19, 18, 17, 16, 10, 14, 13, 12, 11, 5, 9, 8, 7, 6, 25],
    #[0, 15, 14, 6, 11, 22, 3, 10, 16, 25, 7, 4, 23, 13, 2, 1, 8, 21, 19, 18, 24, 17, 5, 12, 20, 9],
    #[0, 9, 6, 15, 14, 12, 2, 24, 19, 1, 17, 25, 5, 23, 4, 3, 20, 10, 21, 8, 16, 18, 22, 13, 7, 11],
    #[0, 1, 4, 25, 2, 17, 19, 22, 13, 24, 11, 10, 20, 8, 21, 16, 15, 5, 23, 6, 12, 14, 7, 18, 9, 3],
    #[0, 1, 10, 18, 11, 24, 22, 21, 25, 20, 15, 16, 5, 3, 6, 2, 4, 9, 13, 7, 17, 19, 14, 8, 12, 23],
    #[0, 1, 25, 2, 3, 6, 17, 24, 16, 7, 23, 18, 14, 15, 20, 8, 13, 19, 10, 5, 21, 12, 9, 11, 22, 4]]

@[expose] def psl26Words : List (List ℤ) :=
  [[-2, 3], [-2, -1], [-1, -1, 3, 1, 1], [-6, -5, 6, 5, 4], [-5, -4, -5, -7, -1, -3, 7, 1],
      [-1, -3, 8, -1, 6, 1]]

@[expose] def psl26D : Array (Array ℕ) :=
  #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25],
    #[9, 15, 6, 14, 11, 1, 25, 4, 2, 3, 24, 10, 21, 19, 16, 22, 5, 23, 13, 12, 7, 20, 8, 18, 17, 0],
    #[25, 1, 3, 2, 4, 15, 9, 11, 14, 6, 20, 7, 17, 18, 8, 5, 22, 12, 13, 23, 10, 24, 16, 19, 21, 0],
    #[0, 15, 14, 6, 11, 22, 3, 10, 16, 25, 7, 4, 23, 13, 2, 1, 8, 21, 19, 18, 24, 17, 5, 12, 20, 9],
    #[9, 22, 16, 25, 10, 8, 14, 24, 5, 0, 4, 11, 18, 19, 6, 15, 2, 20, 12, 13, 17, 23, 1, 21, 7, 3],
    #[25, 5, 8, 9, 7, 16, 2, 20, 22, 0, 11, 4, 19, 18, 3, 1, 14, 24, 23, 13, 21, 12, 15, 17, 10, 6],
    #[3, 8, 5, 0, 24, 2, 16, 17, 1, 9, 11, 10, 13, 12, 25, 22, 6, 7, 21, 19, 23, 18, 15, 20, 4, 14],
    #[6, 16, 22, 0, 20, 14, 8, 21, 15, 25, 4, 7, 13, 23, 9, 5, 3, 10, 17, 18, 12, 19, 1, 24, 11, 2],
    #[14, 2, 1, 9, 17, 6, 5, 23, 15, 3, 10, 24, 19, 21, 0, 8, 25, 4, 20, 12, 18, 13, 22, 7, 11, 16],
    #[2, 14, 15, 25, 21, 3, 22, 12, 1, 6, 7, 20, 18, 17, 0, 16, 9, 11, 24, 23, 19, 13, 5, 10, 4, 8],
    #[16, 6, 15, 3, 23, 25, 1, 18, 22, 14, 24, 17, 12, 20, 9, 2, 0, 11, 7, 21, 13, 19, 8, 4, 10, 5],
    #[8, 3, 1, 6, 12, 9, 15, 19, 5, 2, 20, 21, 23, 24, 25, 14, 0, 4, 10, 17, 13, 18, 16, 11, 7, 22],
    #[5, 25, 22, 14, 18, 0, 15, 13, 8, 16, 17, 23, 21, 7, 3, 6, 9, 10, 4, 20, 19, 12, 2, 11, 24, 1],
    #[22, 9, 5, 2, 19, 0, 1, 13, 16, 8, 21, 12, 17, 10, 6, 3, 25, 7, 11, 24, 18, 23, 14, 4, 20, 15],
    #[1, 0, 8, 16, 13, 9, 22, 19, 2, 5, 23, 18, 20, 4, 14, 25, 3, 24, 11, 7, 12, 21, 6, 10, 17, 15],
    #[15, 0, 16, 8, 13, 25, 5, 18, 14, 22, 12, 19, 24, 11, 2, 9, 6, 20, 4, 10, 23, 17, 3, 7, 21, 1],
    #[15, 9, 2, 5, 19, 3, 8, 12, 6, 1, 18, 13, 7, 11, 16, 0, 14, 17, 10, 4, 21, 20, 25, 24, 23, 22],
    #[1, 25, 14, 22, 18, 6, 16, 23, 3, 15, 19, 13, 10, 4, 8, 0, 2, 21, 7, 11, 17, 24, 9, 20, 12, 5],
    #[22, 3, 6, 1, 12, 14, 2, 21, 25, 15, 13, 19, 4, 10, 5, 9, 16, 23, 24, 11, 20, 7, 0, 17, 18, 8],
    #[5, 6, 3, 15, 23, 2, 14, 17, 9, 1, 13, 18, 11, 7, 22, 25, 8, 12, 20, 4, 24, 10, 0, 21, 19, 16],
    #[8, 14, 25, 15, 21, 16, 6, 20, 0, 22, 19, 12, 11, 24, 1, 3, 5, 18, 17, 10, 7, 4, 9, 23, 13, 2],
    #[16, 2, 9, 1, 17, 8, 3, 24, 0, 5, 18, 23, 4, 20, 15, 6, 22, 19, 21, 7, 10, 11, 25, 12, 13, 14],
    #[2, 16, 0, 22, 20, 5, 25, 7, 9, 8, 12, 21, 10, 17, 15, 14, 1, 13, 23, 24, 4, 11, 3, 18, 19, 6],
    #[14, 8, 0, 5, 24, 22, 9, 10, 25, 16, 23, 17, 7, 21, 1, 2, 15, 13, 12, 20, 11, 4, 6, 19, 18, 3],
    #[6, 5, 9, 8, 7, 1, 0, 4, 3, 2, 21, 20, 24, 23, 22, 16, 15, 19, 18, 17, 11, 10, 14, 13, 12, 25],
    #[3, 22, 25, 16, 10, 15, 0, 11, 6, 14, 17, 24, 20, 12, 5, 8, 1, 18, 19, 21, 4, 7, 2, 13, 23, 9]]

@[expose] def psl26Levels : Array Level := rawLevels 26 psl26Strong (ruBaseArr 26 [0, 1, 2])

@[expose] def psl26OrdersOK (L : Array Level) : Bool :=
  allLt 26 fun a => allLt 25 fun b => allLt 12 fun c =>
    let g : Array ℕ := Array.ofFn (n := 26) fun p => tr3 L a b c p.val
    eqA 26 (powArr 26 g 12) (idA 26) || eqA 26 (powArr 26 g 13) (idA 26) ||
      eqA 26 (powArr 26 g 5) (idA 26)

@[expose] def psl26DClosed (a : Array ℕ) : Bool :=
  allLt 26 fun i => psl26D.any fun e => eqA 26 e (compA 26 a psl26D[i]!)

@[expose] def psl26RelOK : Bool :=
  eqA 26 (powArr 26 psl26X 13) (idA 26) && !eqA 26 psl26X (idA 26) &&
    eqA 26 (powArr 26 psl26S 2) (idA 26) && !eqA 26 psl26S (idA 26) &&
    eqA 26 (powArr 26 psl26T 2) (idA 26) && !eqA 26 psl26T (idA 26) &&
    eqA 26 (compA 26 (compA 26 (compA 26 psl26S psl26X) psl26S) psl26X) (idA 26) &&
    eqA 26 (compA 26 psl26T psl26S) (compA 26 psl26S psl26T) &&
    isInvA 26 psl26X (invCand 26 psl26X) && isInvA 26 psl26S (invCand 26 psl26S)

end CFSG.Quasithin.RuRank3
