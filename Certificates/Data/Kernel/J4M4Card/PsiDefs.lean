module

public import Certificates.Data.J4M4Card.Native
public import Certificates.Data.Kernel.J4M4Card.Defs
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KD.J4M4Card

open CFSG.KC.Enum CFSG.KS CFSG.Quasithin.J4M4Card

@[expose] def psiOP : Nat :=
  503858914849923688362966063066413842918072097753790800564648079457144017882645055290668280985413619830462002708713079257465060633525372580412672263087477557143561902337658129989657007691710158860611891649579106451537724401484158300389603825778939467724151058331495144717806420997591355029922066907773200758046552769326531709177614153051951501473298030858823492395566998412814282172537010622869219811033174356594948129639393216899058882692385939505422664281325572

@[expose] def psiMP : Nat :=
  12037633752130155034291146073496026533810890926883186419177092505480359654245088006619048168514650904856000151697124483431309199716597194840505061376

@[expose] def psiD : List (List Int) := psiW.toList.drop 62

@[expose] def psiD128 : List (List Int) :=
  [[-2, 16, 1], [-18, -2, 3, 2], [-1, 19, 1], [-11, -18, -11, 20, 11, 18, 11]]

@[expose] def psiSpan : List (List Nat) :=
  [[1, 3, 6, 7, 9, 10], [1, 3, 5, 8], [0], [0, 3, 10], [0, 2, 5, 8], [2, 3, 5, 6, 7, 8, 10],
    [0, 1, 3, 4, 7, 8, 10], [1, 2, 3, 4, 6, 10], [2, 3, 4, 9], [0, 3, 6, 8, 9], [0, 2, 6, 8, 9, 10]]

@[expose] noncomputable def psiOv (k : Nat) : Nat := pg 12 (mask 12) psiOP k

@[expose] noncomputable def psiRx (i : Nat) : Nat := pg 8 (mask 8) psiMP i

@[expose] noncomputable def dblK (p : Nat) : Bool :=
  allN 11 fun k => allN (Nat.shiftLeft 1 k) fun c =>
    Nat.beq (pg 12 (mask 12) p (Nat.add (Nat.shiftLeft 1 k) c))
      (Nat.xor (pg 12 (mask 12) p c) (pg 12 (mask 12) p (Nat.shiftLeft 1 k)))

@[expose] noncomputable def laneK (P : Nat → Nat) (lo n : Nat) : Bool :=
  allN n fun d => strictB (P (Nat.add lo d)) fun p => bAnd(dblK p,
    bAnd(Nat.beq (pg 12 (mask 12) p 0) (xorMasks (maskTab.getD (Nat.add lo d) []) 0),
      allN 11 fun k => Nat.beq (pg 12 (mask 12) p (Nat.shiftLeft 1 k))
        (xorMasks (maskTab.getD (Nat.add lo d) []) (Nat.shiftLeft 1 k))))

@[expose] noncomputable def pairK (PS PR : Nat → Nat) : Bool :=
  allN 62 fun i => allN 128 fun k =>
    Nat.beq (pg 12 (mask 12) (PS i) (psiOv k)) (psiOv (pg 8 (mask 8) (PR (psiRx i)) k))

@[expose] noncomputable def rxK : Bool := allN 62 fun i => Nat.blt (psiRx i) 17

@[expose] noncomputable def ovK : Bool := allN 128 fun k => Nat.blt (psiOv k) 2048

@[expose] noncomputable def xorL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun p _ ih => Nat.xor (psiOv p) ih) l

@[expose] noncomputable def ltL (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun p _ ih => bAnd(Nat.blt p 128, ih)) l

@[expose] noncomputable def spanK : Bool :=
  allN 11 fun j => bAnd(ltL (getLL psiSpan j), Nat.beq (xorL (getLL psiSpan j)) (Nat.shiftLeft 1 j))

end CFSG.KD.J4M4Card

end
