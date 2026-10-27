module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThreeInputs
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.Native.ChainCentralizer
public import Certificates.Data.TabSuzFuse
public import Certificates.Data.K426Checks
public import CFSG.LieType.Multipliers.U43Data
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThreeInputs
public meta import CFSG.RankThree.PartOne.KS.PKit
public meta import CFSG.RankThree.Native.ChainCentralizer
public meta import Certificates.Data.TabSuzFuse
public meta import Certificates.Data.K426Checks
public meta import CFSG.LieType.Multipliers.U43Data
public import CFSG.Certificates.CosetTableShort
public meta import CFSG.Certificates.CosetTableShort
public meta import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.ProductKernel
public meta import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43Action

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabSuzA

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
  CFSG.RankThree.PartTwo.KFacts.K426 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.HardMathSupport.Dickson.I271.TabSuzFuse CFSG.LieType.Multipliers.U43

@[expose] def hex : String := include_str "TabSuzA.txt"

@[expose] def arr (k : ℕ) : Array ℕ := hexTable 3 1782 (1782 * k) hex

@[expose] def aStrong (_ : Unit := ()) : Array (Array ℕ) :=
  Array.ofFn fun j : Fin 11 => arr j.val

@[expose] def aWords : Array (List ℤ) :=
  #[[], [], [], [2, 2, 2], [-1, -2, -1, -2, 1, 4, 1, 2], [-5, -5], [-4, -5, 4, 5, 4], [-6, 7, 6],
   [-5, 7, 5], [-4, -6, -4, -1, -6, 9, 1], [-7, -9, -10, -6, -8, 10, 6, 10]]

@[expose] def aBase : Array ℕ := #[0, 1, 2, 3, 4, 8]

@[expose] def tTuple : Array ℕ := #[0, 213, 62, 617, 1598, 338]

@[expose] def uTuple : Array ℕ := #[735, 1457, 802, 1069, 189, 821]

@[expose] def vTuple : Array ℕ := #[983, 1515, 151, 835, 1119, 173]

@[expose] def levList (n : ℕ) (L : Array Level) (i : ℕ) : List (Fin n) :=
  (List.finRange n).filter fun q => decide ((L[i]!).pos[(q : ℕ)]! < (L[i]!).pts.size)

@[expose] def levCount (n : ℕ) (L : Array Level) (i : ℕ) : ℕ := (levList n L i).length

@[expose] def wordModX (a b xa : Array ℕ) (w : List (Fin 2 × Bool)) : Bool :=
  eqA 1782 (evalWA 1782 #[a, b] w) (idA 1782) || eqA 1782 (evalWA 1782 #[a, b] w) xa ||
    eqA 1782 (evalWA 1782 #[a, b] w) (compA 1782 xa xa)

@[expose] def caseACheck (_ : Unit := ()) : Bool :=
  let L := levels ()
  let S := aStrong ()
  let xa := xAArr L
  let a := S[0]!
  let b := S[1]!
  let t := rebuild L tTuple
  let u := rebuild L uTuple
  let v := rebuild L vTuple
  S.size == 11 && caseChainOK3 1782 S aBase aWords S[0]! S[1]! S[2]! && eqA 1782 S[2]! xa &&
    (rawOrbitSizes 1782 S aBase).prod == 9797760 &&
    validA 1782 a && validA 1782 b && inP L a && inP L b &&
    commA 1782 a xa && commA 1782 b xa &&
    rels.all (wordModX a b xa) &&
    validA 1782 u && validA 1782 v && siftA 1782 (rawLevels 1782 S aBase) aBase 0 u &&
    siftA 1782 (rawLevels 1782 S aBase) aBase 0 v &&
    eqA 1782 (commutatorA 1782 v u) xa &&
    validA 1782 t && inP L t && eqA 1782 (conjA 1782 t xa) (compA 1782 xa xa) &&
    allLt 5 (fun i => xa[aBase[i]!]! == aBase[i]!) &&
    fixLevCount 1782 L xa 0 == 162 && fixLevCount 1782 L xa 1 == 56 &&
    fixLevCount 1782 L xa 2 == 10 && fixLevCount 1782 L xa 3 == 9 &&
    fixLevCount 1782 L xa 4 == 8 && levCount 1782 L 5 == 3

end CFSG.HardMathSupport.Dickson.I271.TabSuzA
