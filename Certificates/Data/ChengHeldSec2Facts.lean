module

public import Certificates.Data.ChengHeldPresProps

public section

namespace CFSG.OddStandard.ChengHeldData

open RegModel

@[expose] def autArr (M : RegModel) (α k : ℕ) : Array ℕ := M.autMap (M.tabImgs α k)

@[expose] def secV (M : RegModel) : Array Bool :=
  M.closure [M.pw (M.g 0) 2, M.g 1, M.m (M.g 0) (M.g 2)]

@[expose] def secZ (M : RegModel) : Array Bool := M.closure [M.g 0]

@[expose] def twM (M : RegModel) (α k : ℕ) : Bool :=
  let a := autArr M α k
  let Zt := secZ M
  (List.range M.N).all fun s0 =>
    !Zt[M.m s0 a[s0]!]! || (List.range M.N).any fun s => Zt[M.m (M.m M.inv[s]! s0) a[s]!]!

@[expose] def twOK (α k : ℕ) : Bool := twM (mkReg α) α k

@[expose] def sqVM (M : RegModel) : Bool :=
  let V := secV M
  let W := M.cent V
  (elems V).all fun v => (elems W).any fun w => M.m w w == v

@[expose] def sqVOK (α : ℕ) : Bool := sqVM (mkReg α)

@[expose] def notCentVM (M : RegModel) (α k : ℕ) : Bool :=
  let a := autArr M α k
  let V := secV M
  (List.range M.N).all fun s => (elems V).any fun v => a[M.cj v s]! != v

@[expose] def notCentVOK (α k : ℕ) : Bool := notCentVM (mkReg α) α k

@[expose] def secInvs (M : RegModel) : Array ℕ :=
  ((List.range M.N).filter fun a => a != 0 && M.m a a == 0).toArray

@[expose] def secEA3 (M : RegModel) : Array (Array ℕ) :=
  M.eaNext (secInvs M) (M.eaNext (secInvs M) ((secInvs M).map fun a => #[0, a]))

@[expose] def secBitmap (M : RegModel) (E : Array ℕ) : Array Bool :=
  (Array.range M.N).map fun i => E.contains i

@[expose] def eaCentM (M : RegModel) : Bool :=
  let V := secV M
  (secEA3 M).all fun E =>
    let B := secBitmap M E
    let C := M.cent B
    B == V || (card C ≤ 16 && (elems C).all fun s => M.pw s 4 == 0)

@[expose] def eaCentOK (α : ℕ) : Bool := eaCentM (mkReg α)

@[expose] def fixSet1 (M : RegModel) (a1 : Array ℕ) (s1 : ℕ) : List ℕ :=
  (List.range M.N).filter fun x => a1[M.cj x s1]! == x

@[expose] def pairSet (M : RegModel) (a2 : Array ℕ) (F1 : List ℕ) (s2 : ℕ) : List ℕ :=
  F1.filter fun x => a2[M.cj x s2]! == x

@[expose] def pairCase (M : RegModel) (a2 : Array ℕ) (F1 : List ℕ) (s2 : ℕ) : Bool :=
  let H := pairSet M a2 F1 s2
  H.length < 8 || (H.length == 8 && H.any fun x => M.m x x != 0)

@[expose] def pairFixM (M : RegModel) (α : ℕ) : Bool :=
  let a1 := autArr M α 0
  let a2 := autArr M α 1
  (List.range M.N).all fun s1 =>
    let F1 := fixSet1 M a1 s1
    (List.range M.N).all fun s2 => pairCase M a2 F1 s2

@[expose] def pairFixOK (α : ℕ) : Bool := pairFixM (mkReg α) α

@[expose] def inV1 (V : Array Bool) (x : ℕ) : Bool := V[x]! && x != 0

@[expose] def graphSet (M : RegModel) (a : Array ℕ) (V W : Array Bool) (e s : ℕ) : List ℕ :=
  (elems W).filter fun x => inV1 V (M.m (M.m e a[M.cj x s]!) x)

@[expose] def graphCase (M : RegModel) (a : Array ℕ) (V W : Array Bool) (s c : ℕ) : Bool :=
  let e := M.m c (M.m s a[s]!)
  !inV1 V e ||
    (let G := graphSet M a V W e s
     G.length < 32 || (G.length == 32 && G.any fun x => G.any fun y => !(G.contains (M.m x y))))

@[expose] def graphM (M : RegModel) (α : ℕ) : Bool :=
  α == 0 ||
  (let a := autArr M α 1
   let V := secV M
   let W := M.cent V
   (elems W).all fun s =>
     (List.range 4).all fun n => graphCase M a V W s (M.pw (M.g 0) n))

@[expose] def graphOK (α : ℕ) : Bool := graphM (mkReg α) α

@[expose] def unitFixM (M : RegModel) (α : ℕ) : Bool :=
  let a := autArr M α 2
  let q := M.pw (M.g 0) 2
  let m := M.m (M.m (M.m (M.g 3) (M.g 4)) (M.g 6)) (M.g 2)
  M.fixedPts a == M.closure [q, m] || M.fixedPts a == M.closure [q, M.m m (M.g 0)]

@[expose] def unitFixOK (α : ℕ) : Bool := unitFixM (mkReg α) α

@[noinline, expose] def chSec2OK : Bool :=
  [0, 1].all fun α =>
    let M := mkReg α
    twM M α 0 && twM M α 1 && twM M α 2 && sqVM M && eaCentM M && pairFixM M α && graphM M α &&
      notCentVM M α 0 && notCentVM M α 2 && unitFixM M α

end CFSG.OddStandard.ChengHeldData
