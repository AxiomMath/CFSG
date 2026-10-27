module

public import CFSG.Sporadic.Schreier.Co1ChainCheck
public import Certificates.Data.CFSGNative.Co1.TwoB
public import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs

public section

namespace CFSG.Sporadic.Co1Block.Native

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.TwoBNative

@[expose] def brayRows (tR : Rows) (d₁ : List (List Int)) : List Rows × List Rows × Bool :=
  dag [aR, bR, tR] d₁

@[expose] def brayElts (D : List Rows × List Rows × Bool) (bidx : List Nat) : List Rows :=
  bidx.map fun j => D.1.getD (j - 1) one

@[noinline, expose] def centCheckOf (tR : Rows) (d₁ : List (List Int)) (bidx : List Nat)
    (d₂ : List (List Int)) (base : List Nat) (gens : List (List Nat)) (sizes : List Nat) : Bool :=
  let D₁ := brayRows tR d₁
  let B := brayElts D₁ bidx
  let D₂ := dag B d₂
  D₁.2.2 && D₂.2.2 && bidx.all (fun j => decide (3 < j) && decide (j ≤ D₁.1.length)) &&
    B.all (fun g => mul g tR == mul tR g) &&
    vTowerOK (D₂.1.toArray.map (transposeRows 24)) base gens sizes

@[expose] def conjAtLeast (G Gi : Array (Array Nat)) (root : Array Nat) (n : Nat) : Bool :=
  let c := conjBFS G Gi root n
  ctOK G Gi root c && decide (n ≤ c.pts.size)

@[expose] def conjLevelOK (S : List Rows) (roots : List Rows) (gens : List (List Nat))
    (sizes : List Nat) (i : Nat) : Bool :=
  let js := gens.getD i []
  let G := (js.map fun j => S.getD j one).toArray
  let Gi := G.map inv
  js.all (fun j => decide (j < S.length) && (List.range i).all fun l =>
      mul (S.getD j one) (roots.getD l one) == mul (roots.getD l one) (S.getD j one)) &&
    (List.range G.size).all (fun l => mul G[l]! Gi[l]! == one) &&
    conjAtLeast G Gi (roots.getD i one) (sizes.getD i 0)

@[noinline, expose] def qCheckOf (tR : Rows) (d₁ : List (List Int)) (bidx : List Nat)
    (d₂ : List (List Int)) (Qg : List Rows) (cap : Nat) (roots : List Rows)
    (gens : List (List Nat)) (sizes : List Nat) : Bool :=
  let D₁ := brayRows tR d₁
  let B := brayElts D₁ bidx
  let D₂ := dag B d₂
  let T := gtBFS Qg.toArray cap
  gtOK Qg.toArray T && roots.all (fun r => T.pts.contains r) &&
    (List.range roots.length).all (conjLevelOK D₂.1 roots gens sizes) &&
    B.all fun g => mul g (inv g) == one && Qg.all fun q => T.pts.contains (conjRows g (inv g) q)

end CFSG.Sporadic.Co1Block.Native
