
module

public import CFSG.YGroups.Y443.Native.Words
public import CFSG.Open.MonsterY443Defs

public section

namespace CFSG.YGroups.Y443
namespace EdgeNoncomm

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443Native CFSG.Open

@[expose] def gL : ℕ → List Native.Gen
  | 0 => []
  | k + 1 => L k

@[expose] def gI : ℕ → List Native.Gen
  | 0 => []
  | k + 1 => invW k

@[expose] def pw (p : ℕ × ℕ) : List Native.Gen := gL p.2 ++ gI p.1

@[expose] def pairsWord (ps : List (ℕ × ℕ)) : List Native.Gen := (ps.map pw).reverse.flatten

@[expose] def qP : List (ℕ × ℕ) := [(0, 1), (2, 3), (5, 6), (9, 0), (1, 2), (3, 5), (6, 9)]

@[expose] def rP : List (ℕ × ℕ) := [(0, 1), (2, 3), (5, 6), (9, 4)]

@[expose] def nP : List (ℕ × ℕ) := qP ++ qP ++ qP ++ qP ++ rP

@[expose] def edgeWord : List Native.Gen := powL 4 (pairsWord nP)

@[expose] def moveCheckAux (u v : Native.DVec) : Bool :=
  let pu : Int := 2 ^ u.e
  let pv : Int := 2 ^ v.e
  (List.range 196884).any fun k => u.D.getD k 0 * pv != v.D.getD k 0 * pu

@[expose] def moveCheck (w : List Native.Gen) (v : Native.DVec) : Bool :=
  w.all (fun g => g.validB) && moveCheckAux (Native.evalWord w v) v

end EdgeNoncomm
end CFSG.YGroups.Y443
