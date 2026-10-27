module

public import Certificates.Data.Kernel.SporSch.Co1Orb

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.SporSch.Orb

@[expose] noncomputable def lettersIK (k : Nat) (w : List Int) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun z _ ih => strictB (icode z) (fun c => bAnd(Nat.ble (nat_lit 2) c,
      bAnd(Nat.blt (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)) k, ih)))) w

@[expose] noncomputable def wordIK (M MI : Nat → Nat) (w : List Int) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun z _ ih acc => strictN (mulK acc (letterK M MI (icode z))) ih) w idM

@[expose] noncomputable def lenWI (ws : List (List Int)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) ws

@[expose] noncomputable def dagIK (M MI : Nat → Nat) (nb N : Nat) (ws : List (List Int)) : Bool :=
  bAnd(Nat.beq (Nat.add nb (lenWI ws)) N,
  bAnd(allN N (fun k => invOKK (M k) (MI k)),
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun w _ ih k => bAnd(lettersIK k w, bAnd(Nat.beq (wordIK M MI w) (M k), ih (Nat.succ k))))
      ws nb))

@[expose] noncomputable def ngetW (l : List (List (List Int))) : Nat → List (List Int) :=
  List.rec (motive := fun _ => Nat → List (List Int)) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List (List Int)) x (fun j _ => ih j) i) l

@[expose] noncomputable def witK (M MI : Nat → Nat) (W : List (List (List Int))) (sv : List Nat) :
    Bool :=
  strictB (nget sv (nat_lit 0)) (fun z => allN (nat_lit 3) (fun m =>
    strictB (nget sv (Nat.succ m)) (fun v =>
      List.rec (motive := fun _ => Bool) true (fun w _ ih => bAnd(lettersIK (nat_lit 2) w,
        strictB (wordIK M MI w) (fun R => bAnd(Nat.beq (actK R z) z,
          bAnd(Nat.beq (actK R v) v, ih))))) (ngetW W m))))

@[expose] noncomputable def valsK (M MI : Nat → Nat) (ws : List (List Int)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun w _ ih => wordIK M MI w :: ih) ws

@[expose] noncomputable def wsRow (Wl : List Nat) (c : Nat) : Nat :=
  strictN (Nat.div c (nat_lit 24)) (fun q => strictN (Nat.mod c (nat_lit 24)) (fun r =>
    nIf(Nat.blt q (lenN Wl), rowK (nget Wl q) r, Nat.shiftLeft (nat_lit 1) r)))

@[expose] noncomputable def coefK (Wl : List Nat) (c u : Nat) : Bool :=
  Nat.beq (fld(Nat.xor (wsRow Wl c) (Nat.shiftLeft (nat_lit 1) (Nat.mod c (nat_lit 24))), u,
    nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def combK (Wl : List Nat) (cs : List Nat) (v : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun c _ ih => Bool.rec (motive := fun _ => Bool) ih (bIf(ih, false, true)) (coefK Wl c v)) cs

@[expose] noncomputable def pairFst (l : List (Nat × Nat)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) (Prod.rec (motive := fun _ => Nat)
      (fun a _ => a) x) (fun j _ => ih j) i) l

@[expose] noncomputable def pairSnd (l : List (Nat × Nat)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) (Prod.rec (motive := fun _ => Nat)
      (fun _ b => b) x) (fun j _ => ih j) i) l

@[expose] noncomputable def bitK (x i : Nat) : Bool := Nat.beq (fld(x, i, nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def fixOneK (Wl : List Nat) (FF : List (Nat × Nat))
    (FS : List (List (List Nat))) (sv : List Nat) (m : Nat) : Bool :=
  strictB (pairFst FF m) (fun a => strictB (pairSnd FF m) (fun b =>
  strictB (nget sv (nat_lit 0)) (fun z => strictB (nget sv (Nat.succ m)) (fun v =>
  bAnd(Nat.blt a (nat_lit 24), bAnd(Nat.blt b (nat_lit 24),
  bAnd(Bool.rec (motive := fun _ => Bool) (bAnd(bitK z b, bitK v a))
      (bIf(bAnd(bitK z b, bitK v a), false, true)) (bAnd(bitK z a, bitK v b)),
    allN (nat_lit 24) (fun u => bIf(bIf(Nat.beq u a, false, bIf(Nat.beq u b, false, true)),
      strictB (lenN Wl) (fun len => bAnd(combK Wl (ngetL (ngetLL FS m) u) u,
      bAnd(allN (nat_lit 24) (fun w => bIf(Nat.beq w u, true,
          bIf(bIf(Nat.beq w a, false, bIf(Nat.beq w b, false, true)),
            bIf(combK Wl (ngetL (ngetLL FS m) u) w, false, true), true))),
        List.rec (motive := fun _ => Bool) true
          (fun c _ ih => bAnd(Nat.blt (Nat.div c (nat_lit 24)) len, ih))
          (ngetL (ngetLL FS m) u)))), true)))))))))

@[expose] noncomputable def fixK (M MI : Nat → Nat) (W : List (List (List Int)))
    (FF : List (Nat × Nat)) (FS : List (List (List Nat))) (sv : List Nat) : Bool :=
  allN (nat_lit 3) (fun m => fixOneK (valsK M MI (ngetW W m)) FF FS sv m)

end CFSG.KS.SporSch.M24

end
