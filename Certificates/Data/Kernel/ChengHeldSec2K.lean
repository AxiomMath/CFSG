module

public import Certificates.Data.ChengHeldSec2Facts
public import Certificates.Data.Kernel.L34K
public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KC.ChengHeldS2

open CFSG.OddStandard.ChengHeldData
open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw

variable (N : ℕ) (m : ℕ → ℕ → ℕ) (inv : ℕ → ℕ)

@[expose] def pwK (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => m (pwK a n) a

@[expose] def cjK (a b : ℕ) : ℕ := m (m (inv b) a) b

@[expose] def elemsK (B : ℕ → Bool) : List ℕ := (List.range N).filter B

@[expose] def centK (B : ℕ → Bool) (a : ℕ) : Bool := (elemsK N B).all fun b => m a b == m b a

@[expose] def evalK (g : ℕ → ℕ) : Tm → ℕ
  | .var i => g i
  | .one => 0
  | .mul a b => m (evalK g a) (evalK g b)
  | .inv a => inv (evalK g a)

@[expose] def imgK (g : ℕ → ℕ) (α k : ℕ) (j : ℕ) : ℕ :=
  match (actRels α k).find? (fun e => e.1 == j) with
  | some e => evalK m inv g e.2
  | none => 0

@[expose] def autK (order parent label img : ℕ → ℕ) : Array ℕ :=
  (List.range' 1 (N - 1)).foldl (fun a i => a.set! (order i) (m (img (label i)) a[parent i]!))
    (Array.replicate N 0)

@[expose] def twK (a : ℕ → ℕ) (Zt : ℕ → Bool) : Bool :=
  (List.range N).all fun s0 =>
    !Zt (m s0 (a s0)) || (List.range N).any fun s => Zt (m (m (inv s) s0) (a s))

@[expose] def sqVK (V : ℕ → Bool) : Bool :=
  (elemsK N V).all fun v => (elemsK N (centK N m V)).any fun w => m w w == v

@[expose] def notCentK (a : ℕ → ℕ) (V : ℕ → Bool) : Bool :=
  (List.range N).all fun s => (elemsK N V).any fun v => a (cjK m inv v s) != v

@[expose] def fixSet1K (a1 : ℕ → ℕ) (s1 : ℕ) : List ℕ :=
  (List.range N).filter fun x => a1 (cjK m inv x s1) == x

@[expose] def pairCaseK (a2 : ℕ → ℕ) (F1 : List ℕ) (s2 : ℕ) : Bool :=
  let H := F1.filter fun x => a2 (cjK m inv x s2) == x
  H.length < 8 || (H.length == 8 && H.any fun x => m x x != 0)

@[expose] def pairFixK (a1 a2 : ℕ → ℕ) : Bool :=
  (List.range N).all fun s1 =>
    let F1 := fixSet1K N m inv a1 s1
    (List.range N).all fun s2 => pairCaseK m inv a2 F1 s2

@[expose] def inV1K (V : ℕ → Bool) (x : ℕ) : Bool := V x && x != 0

@[expose] def graphCaseK (a : ℕ → ℕ) (V W : ℕ → Bool) (s c : ℕ) : Bool :=
  let e := m c (m s (a s))
  !inV1K V e ||
    (let G := (elemsK N W).filter fun x => inV1K V (m (m e (a (cjK m inv x s))) x)
     G.length < 32 || (G.length == 32 && G.any fun x => G.any fun y => !(G.contains (m x y))))

@[expose] def graphK (a : ℕ → ℕ) (V : ℕ → Bool) (t : ℕ) : Bool :=
  (elemsK N (centK N m V)).all fun s =>
    (List.range 4).all fun n => graphCaseK N m inv a V (centK N m V) s (pwK m t n)

@[expose] def unitFixK (a : ℕ → ℕ) (C1 C2 : ℕ → Bool) : Bool :=
  (List.range N).all (fun x => (a x == x) == C1 x) || (List.range N).all (fun x => (a x == x) == C2 x)

@[expose] def maskL (E : List ℕ) : ℕ := E.foldl (fun m i => m ||| (1 <<< i)) 0

@[expose] def eaStepK (E : List ℕ) (st : List ℕ × List (List ℕ)) (a : ℕ) :
    List ℕ × List (List ℕ) :=
  if !((maskL E).testBit a) && E.all (fun e => m a e == m e a) then
    if !(st.1.contains (maskL (E ++ E.map fun e => m a e))) then
      (maskL (E ++ E.map fun e => m a e) :: st.1, st.2 ++ [E ++ E.map fun e => m a e])
    else st
  else st

@[expose] def eaNextK (invs : List ℕ) (L : List (List ℕ)) : List (List ℕ) :=
  (L.foldl (fun st E => invs.foldl (eaStepK m E) st) ([], [])).2

@[expose] def invsK : List ℕ := (List.range N).filter fun a => a != 0 && m a a == 0

@[expose] def ea3K : List (List ℕ) :=
  eaNextK m (invsK N m) (eaNextK m (invsK N m) ((invsK N m).map fun a => [0, a]))

@[expose] def eaCentK (V : ℕ → Bool) : Bool :=
  (ea3K N m).all fun E =>
    (List.range N).all (fun x => (decide (x < N) && E.contains x) == V x) ||
      (decide ((elemsK N (centK N m fun i => decide (i < N) && E.contains i)).length ≤ 16) &&
        (elemsK N (centK N m fun i => decide (i < N) && E.contains i)).all fun s =>
          pwK m s 4 == 0)

@[expose] def clStepK (gs : List ℕ) (B : ℕ) : ℕ :=
  (List.range N).foldl (fun acc x =>
    if B.testBit x then gs.foldl (fun acc g => acc ||| (1 <<< m x g)) acc else acc) B

@[expose] def clIterK (gs : List ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => clStepK N m gs (clIterK gs k)

@[expose] noncomputable def mR (T : ℕ → ℕ) (IXP a b : ℕ) : ℕ :=
  if a * 256 + b < 256 * 256 then
    pg 9 (mask 9) (T (pg 9 (mask 9) IXP ((a * 256 + b) / 256))) ((a * 256 + b) % 256)
  else 0

@[expose] noncomputable def iR (IVP a : ℕ) : ℕ := if a < 256 then pg 9 (mask 9) IVP a else 0

@[expose] noncomputable def gR (G : ℕ → ℕ) (j : ℕ) : ℕ := if j < 7 then pg 9 (mask 9) (G j) 0 else 0

@[expose] noncomputable def aR (P x : ℕ) : ℕ := if x < 256 then pg 9 (mask 9) P x else 0

@[expose] noncomputable def oR (T : ℕ → ℕ) (i : ℕ) : ℕ := if i < 256 then pg 9 (mask 9) (T i) 0 else 0

@[expose] noncomputable def pR (T PL : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < 256 then pg 9 (mask 9) (T (CFSG.KS.PEnum.parOf PL i)) 0 else 0

@[expose] noncomputable def lR (PL : ℕ → ℕ) (i : ℕ) : ℕ := if i < 256 then CFSG.KS.PEnum.labOf PL i else 0

@[expose] noncomputable def bR (m : ℕ → ℕ → ℕ) (gs : List ℕ) (x : ℕ) : Bool :=
  decide (x < 256) && (clIterK 256 m gs 16).testBit x

@[expose] noncomputable def zGs (g : ℕ → ℕ) : List ℕ := [g 0]
@[expose] noncomputable def vGs (m : ℕ → ℕ → ℕ) (g : ℕ → ℕ) : List ℕ :=
  [pwK m (g 0) 2, g 1, m (g 0) (g 2)]
@[expose] noncomputable def u1Gs (m : ℕ → ℕ → ℕ) (g : ℕ → ℕ) : List ℕ :=
  [pwK m (g 0) 2, m (m (m (g 3) (g 4)) (g 6)) (g 2)]
@[expose] noncomputable def u2Gs (m : ℕ → ℕ → ℕ) (g : ℕ → ℕ) : List ℕ :=
  [pwK m (g 0) 2, m (m (m (m (g 3) (g 4)) (g 6)) (g 2)) (g 0)]

@[expose] noncomputable def bindK (T PL : ℕ → ℕ) (IXP IVP : ℕ) : Bool :=
  allN 256 fun a => bAnd(Nat.blt (pg 9 (mask 9) IXP a) 256,
    bAnd(Nat.beq (pg 9 (mask 9) (T (pg 9 (mask 9) IXP a)) 0) a,
    bAnd(Nat.blt (iR IVP a) 256, bAnd(Nat.beq (mR T IXP a (iR IVP a)) 0,
      Nat.blt (CFSG.KS.PEnum.parOf PL a) 256))))

@[expose] noncomputable def autRecK (m : ℕ → ℕ → ℕ) (inv g : ℕ → ℕ) (T PL : ℕ → ℕ) (α k P : ℕ) :
    Bool :=
  bAnd(Nat.beq (aR P 0) 0, allN 255 fun j =>
    Nat.beq (aR P (oR T (Nat.succ j)))
      (m (imgK m inv g α k (lR PL (Nat.succ j))) (aR P (pR T PL (Nat.succ j)))))

@[expose] noncomputable def clK (m : ℕ → ℕ → ℕ) (gs : List ℕ) : Bool :=
  gs.all (fun g => Nat.blt g 256) &&
    Nat.beq (clStepK 256 m gs (clIterK 256 m gs 16)) (clIterK 256 m gs 16)

end CFSG.KC.ChengHeldS2

end
