module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.M12SigCheckInputs
public import Certificates.Data.Kernel.M12Cent

public section

namespace CFSG.KC.M12Sig

open CFSG.GH74.M12.Hyp CFSG.RankThree.PartTwo.Toolkit.M12 CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig
  CFSG.KC.M12Cent

@[expose] def g1W : List ℕ := [2, 0, 2, 0, 3, 0, 3, 0, 2, 0, 3, 0, 3, 0, 3, 0, 2]

@[expose] def invW : List ℕ := [2, 0, 3, 0, 2, 0, 2, 0, 3, 0, 2, 0, 2, 0, 2, 0, 2, 0, 3, 0]

@[expose] def outerB (g1 zb ab : List ℕ) (C : List (List ℕ)) : Bool :=
  conjN g1 zb == zT && C.all fun w => conjN w (conjN g1 ab) != aT

@[expose] def vvB (V : ℕ → List (List ℕ)) : Bool :=
  [(0, 1), (0, 2), (1, 2)].all fun p => (V p.1).all fun v => (V p.2).all fun w =>
    v == tid || w == tid || !isTwo (tmul v w)

@[expose] def twoC (V : ℕ → List (List ℕ)) : Bool :=
  (List.range 3).all fun i => (idxC i).all fun k => !isTwo (prodT k) || (V i).contains (prodT k)

@[expose] def xconjB (t : List ℕ) : Bool :=
  (List.range 3).all fun i => tconj (tpow t i) aT == aiT i

@[expose] def invB (w : List ℕ) : Bool := conjN w aT == tpow aT 2

@[expose] def centL : Bool :=
  (List.range 3).all fun i =>
    (idxC i).all (fun k => predC [aiT i] (prodT k)) && decide ((idxC i).map prodT).Nodup

end CFSG.KC.M12Sig

end
