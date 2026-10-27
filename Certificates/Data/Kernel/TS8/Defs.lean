module

public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8EA16Check
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.TS8

open CFSG.KC.Enum

@[expose] noncomputable def sortDK (P S : Nat → Nat) (N : Nat) : Bool :=
  allN N fun k => bAnd(Nat.blt (S k) N,
    bIf(Nat.beq (Nat.succ k) N, true, Nat.blt (P (S k)) (P (S (Nat.succ k)))))

@[expose] noncomputable def mtK (MT : Nat → Nat → Nat) (W Pa La : Nat → Nat) (ng : Nat) : Bool :=
  allN 256 fun a => bAnd(Nat.beq (MT a 0) a, allN 255 fun b =>
    Nat.beq (MT a (Nat.succ b)) (W (Nat.add (Nat.mul ng (MT a (Pa (Nat.succ b)))) (La (Nat.succ b)))))

@[expose] noncomputable def letP (n w PA PB PU l : Nat) : Nat :=
  if l = 0 then PA else if l = 1 then PB else if l = 2 then CFSG.KS.pinvS n w (CFSG.KS.mask w) PA
    else if l = 3 then CFSG.KS.pinvS n w (CFSG.KS.mask w) PB else PU

@[expose] noncomputable def wordP (n w PA PB PU : Nat) (ws : List Nat) : Nat :=
  ws.foldl (fun acc l => pcomp n w (CFSG.KS.mask w) acc (letP n w PA PB PU l)) (pidn n w)

@[expose] noncomputable def mF (MT : Nat → Nat → Nat) (a b : Nat) : Nat :=
  if a < 256 ∧ b < 256 then MT a b else 0

@[expose] noncomputable def iF (IT : Nat → Nat) (a : Nat) : Nat := if a < 256 then IT a else 0

@[expose] noncomputable def ord4F (m : Nat → Nat → Nat) (a : Nat) : Bool :=
  m (m a a) (m a a) == 0 && m a a != 0

@[expose] noncomputable def involF (m : Nat → Nat → Nat) (iv : Nat → Nat) (b a : Nat) : Bool :=
  m b b == 0 && m (m b a) (iv b) == iv a

@[expose] noncomputable def commF (m : Nat → Nat → Nat) (a c : Nat) : Bool := m a c == m c a

@[expose] noncomputable def searchF (m : Nat → Nat → Nat) (iv : Nat → Nat) : Bool :=
  allN 256 fun a => !ord4F m a ||
    allN 256 fun b => !involF m iv b a ||
      allN 256 fun c => !(ord4F m c && commF m a c && commF m b c && (m a a != m c c)) ||
        allN 256 fun d => !(involF m iv d c && commF m a d && commF m b d)

@[expose] noncomputable def invsF (m : Nat → Nat → Nat) : List Nat :=
  (List.range 256).filter fun a => a != 0 && m a a == 0

@[expose] noncomputable def spanF (m : Nat → Nat → Nat) (S : List Nat) (X : Nat) : List Nat :=
  S ++ S.map fun Y => m Y X

@[expose] noncomputable def hasChainF (m : Nat → Nat → Nat) : Nat → List Nat → List Nat → Bool
  | 0, _, _ => true
  | k + 1, S, C => C.tails.any fun T => match T with
    | [] => false
    | X :: T' => !decide (X ∈ S) && hasChainF m k (spanF m S X) (T'.filter fun Y => commF m X Y)

end CFSG.KC.TS8

end
