module

public import CFSG.RankThree.PartTwo.Toolkit.M12LocalInputs
public import Certificates.Data.Item434SporGenKit

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporGen

open CFSG.GH74.M12.Hyp
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf)

@[expose] def a2T : List ℕ :=
  tmul CFSG.RankThree.PartTwo.Toolkit.M12.xT
    (tmul CFSG.RankThree.PartTwo.Toolkit.M12.yT CFSG.RankThree.PartTwo.Toolkit.M12.yT)

@[expose] def sigT (ws : List (List ℤ)) (i : ℕ) : List ℕ := wordT (ws.getD i [])

@[expose] def evalSigT (ws : List (List ℤ)) : List ℕ → List ℕ
  | [] => tid
  | i :: w => tmul (sigT ws i) (evalSigT ws w)

@[expose] def m12GenCheck (ws : List (List ℤ)) (ps : List (List ℕ)) (wa wb : List ℕ) : Bool :=
  (List.range ws.length).all (fun i => tpow (sigT ws i) 2 == tid &&
    tmul (sigT ws i) (ps.getD i tid) == tmul (ps.getD i tid) (sigT ws i) &&
    !(ps.getD i tid == tid)) && evalSigT ws wa == tA && evalSigT ws wb == tB

@[expose] def sigAW : List (List ℤ) :=
  [[2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1],
    [-2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2],
    [-2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1],
    [1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1]]

@[expose] def sigAP : List (List ℕ) :=
  [CFSG.RankThree.PartTwo.Toolkit.M12.aT, CFSG.RankThree.PartTwo.Toolkit.M12.zT,
    CFSG.RankThree.PartTwo.Toolkit.M12.zT, CFSG.RankThree.PartTwo.Toolkit.M12.zT]

@[expose] def sigA2W : List (List ℤ) :=
  [[-2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2],
    [-2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1],
    [1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1],
    [2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1]]

@[expose] def sigA2P : List (List ℕ) :=
  [CFSG.RankThree.PartTwo.Toolkit.M12.zT, CFSG.RankThree.PartTwo.Toolkit.M12.zT,
    CFSG.RankThree.PartTwo.Toolkit.M12.zT, a2T]

@[expose] def genAa : List ℕ := [3, 0, 1, 0, 2, 0, 1, 0, 3]

@[expose] def genAb : List ℕ := [3, 0, 2, 0, 1, 0, 1, 3, 2, 0, 1, 3, 0]

@[expose] def genA2a : List ℕ := [0, 1, 2, 3, 0, 3, 1, 0, 3, 1, 0, 3, 0, 1, 0, 2, 1, 0]

@[expose] def genA2b : List ℕ := [3, 2, 3, 1, 0, 2, 3, 1, 2, 0, 3, 1, 0, 3, 2, 0]

@[expose] def bpT : List ℕ := [5, 8, 1, 0, 7, 3, 10, 9, 2, 4, 11, 6]

@[expose] def letterTB (l : ℤ) : List ℕ :=
  if l = 1 then tA else if l = -1 then tinv tA else if l = 2 then bpT else tinv bpT

@[expose] def wordTB : List ℤ → List ℕ
  | [] => tid
  | l :: w => tmul (letterTB l) (wordTB w)

@[expose] def bxT : List ℕ := wordTB CFSG.RankThree.PartTwo.Toolkit.M12.wX

@[expose] def byT : List ℕ := wordTB CFSG.RankThree.PartTwo.Toolkit.M12.wY

@[expose] def bzT : List ℕ := CFSG.RankThree.PartTwo.Toolkit.M12.tcm bxT byT

@[expose] def m12FixCheck : Bool :=
  CFSG.RankThree.PartTwo.Toolkit.M12.zT.getD 0 0 == 0 &&
    CFSG.RankThree.PartTwo.Toolkit.M12.xT.getD 0 0 == 0 &&
    (List.range 12).all (fun i => !(bzT.getD i 0 == i) || !(bxT.getD i 0 == i)) &&
    bzT.getD 2 0 == 2 && byT.getD 2 0 == 2 &&
    (List.range 12).all (fun i => !(CFSG.RankThree.PartTwo.Toolkit.M12.zT.getD i 0 == i) ||
      !(CFSG.RankThree.PartTwo.Toolkit.M12.yT.getD i 0 == i))

@[expose] def centIdx (t : List ℕ) : List CFSG.RankThree.PartTwo.Toolkit.M12.Idx :=
  CFSG.RankThree.PartTwo.Toolkit.M12.allIdx.filter fun k =>
    tmul (CFSG.RankThree.PartTwo.Toolkit.M12.prodT k) t ==
      tmul t (CFSG.RankThree.PartTwo.Toolkit.M12.prodT k)

@[expose] def m12CentCheck : Bool :=
  (CFSG.RankThree.PartTwo.Toolkit.M12.ET ++ CFSG.RankThree.PartTwo.Toolkit.M12.FT).all fun t =>
    t == tid || ((centIdx t).length == 54 &&
      decide ((centIdx t).map CFSG.RankThree.PartTwo.Toolkit.M12.prodT).Nodup)

@[expose] def m22GenA : Array ℕ :=
  #[12, 7, 15, 11, 4, 21, 16, 1, 9, 8, 13, 3, 0, 10, 14, 2, 6, 17, 18, 19, 20, 5]

@[expose] def m22GenB : Array ℕ :=
  #[21, 17, 20, 12, 11, 10, 14, 13, 8, 7, 6, 4, 1, 19, 5, 15, 18, 3, 16, 9, 0, 2]

@[expose] def m22SigArrs : Array (Array ℕ) :=
  #[
    #[12, 10, 2, 3, 18, 21, 9, 13, 16, 6, 1, 11, 0, 7, 14, 15, 8, 17, 4, 20, 19, 5],
    #[15, 11, 6, 14, 21, 5, 2, 18, 8, 19, 10, 1, 12, 13, 3, 0, 16, 20, 7, 9, 17, 4],
    #[8, 18, 2, 3, 10, 6, 5, 20, 0, 21, 4, 11, 16, 19, 14, 15, 12, 17, 1, 13, 7, 9],
    #[2, 20, 0, 7, 9, 5, 15, 3, 8, 4, 10, 17, 12, 13, 18, 6, 16, 11, 14, 21, 1, 19]]

@[expose] def m22E1 : Array ℕ :=
  #[0, 7, 17, 14, 19, 10, 4, 21, 8, 18, 13, 2, 12, 5, 15, 3, 16, 11, 20, 6, 9, 1]

@[expose] def m22E2 : Array ℕ :=
  #[0, 9, 2, 14, 21, 13, 7, 18, 12, 19, 5, 11, 16, 10, 15, 3, 8, 17, 6, 1, 4, 20]

@[expose] def m22Ords : List ℕ := [2, 2, 2, 2]

@[expose] def m22PExps : List (ℕ × ℕ) := [(1, 0), (1, 2), (1, 0), (0, 1)]

@[expose] def m22Words : List (List ℤ) :=
  [[-1, 2, 1], [-1, 4, 1], [-2, 5, 1], [-5, -6, 7, 6], [-6, -4, 6, 1], [-5, -9, -7, -2, 3, 2],
    [10, -8, 9, -10], [-8, -10, 8, 10, 8], [11, 12, 11]]

@[expose] def m22GenS : Array (Array ℕ) := pushWords 22 m22SigArrs m22Words

@[expose] def m22Base : List (Fin 22) := [0, 2, 3, 1, 4]

@[expose] def m22Levels : Array Level := rawLevels 22 m22GenS (m22Base.map Fin.val).toArray

@[expose] def m22ChainCheck : Bool :=
  rawChainOK 22 (m22GenS.extract 0 4) m22GenS (m22Base.map Fin.val).toArray (wordsOf 4 m22Words)
      4 &&
    rawOrbitSizes 22 m22GenS (m22Base.map Fin.val).toArray == [22, 21, 20, 16, 3]

@[expose] def m22SiftCheck : Bool :=
  siftA 22 m22Levels (m22Base.map Fin.val).toArray 0 m22GenA &&
    siftA 22 m22Levels (m22Base.map Fin.val).toArray 0 m22GenB &&
    siftA 22 m22Levels (m22Base.map Fin.val).toArray 0 m22E1 &&
    siftA 22 m22Levels (m22Base.map Fin.val).toArray 0 m22E2

@[expose] def m22EltCheck : Bool :=
  e9Check 22 m22E1 m22E2 && sigCheck 22 m22SigArrs m22Ords m22PExps m22E1 m22E2

end CFSG.RankThree.PartTwo.Sec4.Item434SporGen
