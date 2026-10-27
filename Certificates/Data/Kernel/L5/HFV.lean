module

public import Certificates.Data.Kernel.L5.HFP

public section

namespace CFSG.Certificates.Kernel.L5H

open Equiv Perm CFSG.Certificates.Kernel.PkCV CFSG.KC.Enum CFSG.Certificates.Kernel.L5S
  CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.HF CFSG.GH74.GLS.C3.Layer2.Model

@[expose] noncomputable def memV (a : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun b _ r => Bool.rec (motive := fun _ => Bool) r true (Nat.beq a b)) l

@[expose] noncomputable def dedupV (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun a t r => Bool.rec (motive := fun _ => List Nat) (a :: r) r (memV a t)) l

@[expose] noncomputable def imgV (g M : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.mul (Nat.land (Nat.shiftRight M i) (nat_lit 1))
      (Nat.shiftLeft (nat_lit 1) (pg (nat_lit 5) (nat_lit 31) g i)))) (nat_lit 16)

@[expose] noncomputable def orbStepV (gs : List Nat) (l : List Nat) : List Nat :=
  (dedupV (l ++ l.flatMap fun M => gs.map fun g => imgV g M)).take 5

@[expose] noncomputable def orbListV (gs : List Nat) (k : Nat) : List Nat :=
  (orbStepV gs)^[k] [nat_lit 15]

@[expose] noncomputable def n24PreV (x : Nat) : Bool :=
  let A := imgV x (nat_lit 15)
  !(Nat.beq A (nat_lit 15)) && Nat.beq (Nat.land A (nat_lit 15)) (nat_lit 1) &&
    Nat.beq (Nat.land A (nat_lit 4369)) (nat_lit 1)

@[expose] noncomputable def n24TailV (GN : List Nat) (MP : Nat) (x : CV 16) (o : List Nat) : Bool :=
  Nat.beq (imgV x.1 (nat_lit 4369)) (nat_lit 4369) &&
    ((memV (nat_lit 18465) o && memV (nat_lit 9345) o && memV (nat_lit 15) o &&
        memV (nat_lit 33345) o && covN GN MP x) ||
      (memV (nat_lit 10305) o && memV (nat_lit 17025) o && memV (nat_lit 33825) o &&
        memV (nat_lit 15) o && covN GN MP (twC⁻¹ * x * twC)))

@[expose] noncomputable def n24ChkV (GN : List Nat) (MP : Nat) (x : CV 16) : Bool :=
  Nat.beq (orbListV [yC.1, wC.1, x.1] 3).length (nat_lit 5) ||
    (let o := orbListV [yC.1, wC.1, x.1] 6
     Nat.ble (nat_lit 5) (dedupV o).length || n24TailV GN MP x o)

@[expose] noncomputable def n24EntryV (GN : List Nat) (MP : Nat) (x : CV 16) : Bool :=
  !(n24PreV x.1) || n24ChkV GN MP x

@[expose] noncomputable def fam1ChkN (c : CV 16) : Bool :=
  fam1L.all fun V => decide (imgN c (pN V) ∈ fam1L.map pN)

end CFSG.Certificates.Kernel.L5H

end
