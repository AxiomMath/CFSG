module

public import Certificates.Data.Kernel.J4Q.VOrb

public section

namespace CFSG.KC.J4Q

open CFSG.KC.Loop CFSG.KC.LQT.Syl

@[expose] noncomputable def packK (rm : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor (Nat.land x rm) (Nat.shiftLeft ih (nat_lit 128))) l

@[expose] noncomputable def rowsL (rm Q : Nat) (l : List Nat) (k : Nat) (tl : List Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => tl)
    (fun _ _ ih k => List.cons (rowJ rm Q k) (ih (Nat.succ k))) l k

@[expose] noncomputable def clGo (rm c a : Nat) (pc SP : List Nat) (Ms : List Nat) :
    List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun acc => inSK acc SP)
    (fun M _ ih acc => strictB (mulJ c rm a M) fun q => ih (rowsL rm q pc (nat_lit 0) acc)) Ms

@[expose] noncomputable def clB (rm c : Nat) (Ms pc SP : List Nat) : Bool :=
  strictB c fun c => strictB (packK rm pc) fun a => clGo rm c a pc SP Ms List.nil

@[expose] noncomputable def ordGo (nl : Nat) (ch : List Nat) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun e _ ih ci k => andB (Nat.ble ci (Nat.shiftRight e (nat_lit 114)))
      (andB (Nat.blt (Nat.shiftRight e (nat_lit 114)) k)
        (andB (Nat.blt (Nat.land (Nat.shiftRight e (nat_lit 112)) (nat_lit 3)) nl)
          (ih (Nat.shiftRight e (nat_lit 114)) (Nat.succ k))))) ch

@[expose] noncomputable def ppGo (ch : List Nat) : List Nat → Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → Nat → List Nat) (fun _ _ => List.nil)
    (fun e _ ih cur ci => (fun cur' => List.cons (headK cur') (ih cur' (Nat.shiftRight e (nat_lit 114))))
      (dropK (Nat.sub (Nat.shiftRight e (nat_lit 114)) ci) cur)) ch

@[expose] noncomputable def rowChk (rm Q g : Nat) (ch : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih j => Bool.rec (motive := fun _ => Bool) (ih (Nat.succ j))
      (andB (Nat.beq (rowJ rm Q j) (Nat.land e rm)) (ih (Nat.succ j)))
      (Nat.beq (Nat.land (Nat.shiftRight e (nat_lit 112)) (nat_lit 3)) g)) ch

@[expose] noncomputable def trGo (rm c a : Nat) (ch : List Nat) (Ms : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun M _ ih g => andB (strictB (mulJ c rm a M) fun q => rowChk rm q g ch (nat_lit 0))
      (ih (Nat.succ g))) Ms

@[expose] noncomputable def vtB (rm c : Nat) (Ms : List Nat) (P ch : List Nat) (p₀ k₀ : Nat) : Bool :=
  andB (ordGo (List.length Ms) ch p₀ k₀)
    (strictB c fun c => strictB (packK rm (ppGo ch (dropK p₀ P) p₀)) fun a =>
      trGo rm c a ch Ms (nat_lit 0))

@[expose] noncomputable def diffAll (sc : List Nat) (SQ : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun s _ ih acc => ih (diffS acc s)) SQ sc

end CFSG.KC.J4Q

end
