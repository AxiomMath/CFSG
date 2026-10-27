module

public import Certificates.Data.Kernel.TwoF4LieK
public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.TwoF4LieCheck
public import CFSG.Certificates.Kernel.SchreierFam.EvalWord

public section

namespace CFSG.KC.TwoF4LocK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.TwoF4LieK

@[expose] def wdOf (s : String) : List Int :=
  (CFSG.RuF45.decodeWord s).map CFSG.RuF45.signedLetter

@[expose] noncomputable def wv (F FI : Nat → Nat) (wd : List Int) : Nat :=
  wordK (nat_lit 1755) (nat_lit 11) (mask (nat_lit 11)) (pidn (nat_lit 1755) (nat_lit 11)) F FI wd

@[expose] noncomputable def cn (P : Nat) : Bool :=
  canonK (nat_lit 1755) (nat_lit 11) (mask (nat_lit 11)) (nat_lit 19305) P

@[expose] noncomputable def invP (P Q : Nat) : Bool :=
  permOK (nat_lit 1755) (nat_lit 11) (mask (nat_lit 11)) (nat_lit 19305) P Q

@[expose] noncomputable def conj (C X CI : Nat) : Nat := mul (mul C X) CI

@[expose] def onLineR (lp : Nat → Nat) (p v : Nat) : Bool :=
  lp (3 * v) == p || lp (3 * v + 1) == p || lp (3 * v + 2) == p

@[expose] noncomputable def fixHK (P : Nat) : Bool := gp P 0 == 0

@[expose] noncomputable def fixNK (lp : Nat → Nat) (P : Nat) : Bool :=
  (List.range 3).all fun k => onLineR lp (gp P (lp (3 * 0 + k))) 0

@[expose] noncomputable def fixSK (lp : Nat → Nat) (P : Nat) : Bool := fixHK P && fixNK lp P

@[expose] def colK (lp : Nat → Nat) : List Nat :=
  ((List.range 2925).filter fun w => onLineR lp 0 w).flatMap fun w =>
    [lp (3 * w), lp (3 * w + 1), lp (3 * w + 2)]

@[expose] noncomputable def collK (lp : Nat → Nat) (P : Nat) : Bool :=
  (colK lp).all fun q => gp P q == q

@[expose] noncomputable def fixL (T : Nat) : List Nat := (List.range 1755).filter fun p => gp T p == p

@[expose] noncomputable def lineK (lp : Nat → Nat) (C : Nat) : Bool :=
  onLineR lp 0 0 && onLineR lp (gp C 0) 0 && onLineR lp (gp C (gp C 0)) 0 &&
    (List.range 3).all fun k => lp k == 0 || lp k == gp C 0 || lp k == gp C (gp C 0)

@[expose] noncomputable def vK (Z Z1 Z2 : Nat) : Bool :=
  Nat.beq (mul Z Z1) Z2 && Nat.beq (mul Z Z1) (mul Z1 Z) && !Nat.beq Z Z1

@[expose] noncomputable def qK (T Z Z1 Q : Nat) : Bool :=
  Nat.beq (mul Q Q) Z && Nat.beq (mul Q T) (mul T Q) && Nat.beq (mul Q Z1) (mul Z1 Q)

@[expose] noncomputable def wordIs (F FI : Nat → Nat) (s : String) (X : Nat) : Bool :=
  CFSG.TwoF4Lie.wordOK s && lettersK 4 (wdOf s) && Nat.beq (wv F FI (wdOf s)) X && cn X

@[expose] noncomputable def wordsK (F FI W WI : Nat → Nat) (ws : List String) : Bool :=
  (List.range ws.length).all fun j =>
    wordIs F FI (ws.getD j "") (W j) && cn (WI j) && invP (W j) (WI j)

@[expose] noncomputable def chainK (lp : Nat → Nat) (cl : List Nat) (Z : Nat) (W WI : Nat → Nat) :
    List (Nat × Nat) → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool)
    (fun A B => Nat.beq A Z && !(cl.all fun q => gp B q == q))
    (fun st _ ih A B =>
      strictB (conj (W st.2) A (WI st.2)) fun A' => strictB (conj (W st.2) B (WI st.2)) fun B' =>
        (if st.1 == 0 then fixHK (W st.2) else fixNK lp (W st.2)) && fixSK lp A' && fixSK lp B' &&
          ih A' B')

@[expose] noncomputable def rowK (F FI lp W WI : Nat → Nat) (cl : List Nat) (Z T Z1 Z2 M MI p : Nat)
    (w : String) (ch : List (Nat × Nat)) : Bool :=
  strictB (conj M Z MI) fun U =>
    wordIs F FI w M && cn MI && invP M MI && gp M 0 == p &&
      (Nat.beq U Z || Nat.beq U Z1 || Nat.beq U Z2 ||
        (fixSK lp U && fixSK lp T && chainK lp cl Z W WI ch U T))

end CFSG.KC.TwoF4LocK

end
