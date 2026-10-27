module

public import Certificates.Data.Kernel.Fi23Nt.FixDefs
public import Certificates.Data.Kernel.Fi23R.Defs

public section

namespace CFSG.KC.Fi23Nt

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R

@[expose] noncomputable def newK (l : List Nat) (x : Nat) : Nat :=
  nIf(memK l x, nat_lit 0, nat_lit 1)

@[expose] noncomputable def cnt5K (v a b c e : Nat) : Nat :=
  Nat.add (Nat.add (Nat.add (Nat.add (nat_lit 1) (newK [v] a)) (newK [v, a] b))
    (newK [v, a, b] c)) (newK [v, a, b, c] e)

@[expose] noncomputable def dd4K (G : Nat → Nat) (W : List (List Nat)) (v : Nat) : Bool :=
  strictB (wv G (List.getD W (nat_lit 0) []) v) fun a =>
    strictB (wv G (List.getD W (nat_lit 1) []) v) fun b =>
      strictB (wv G (List.getD W (nat_lit 2) []) v) fun c =>
        strictB (wv G (List.getD W (nat_lit 3) []) v) fun e =>
          Nat.ble (nat_lit 4) (cnt5K v a b c e)

@[expose] noncomputable def ddSlK (G : Nat → Nat) (W : List (List Nat)) (lo len : Nat) : Bool :=
  allBlk lo (fun v => bIf(Nat.ble v (nat_lit 1), true,
    bIf(Nat.beq (tA G (nat_lit 0) v) v,
      bIf(Nat.beq (tA G (nat_lit 1) v) v, dd4K G W v, true), true))) len

end CFSG.KC.Fi23Nt

end
