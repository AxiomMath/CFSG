module

public import Certificates.Data.Kernel.F4Rank
public import Certificates.Data.Kernel.F4Salt
public import Certificates.Data.Kernel.F4Syl3PhiInv

public section

namespace CFSG.KC.F4Gamma

open CFSG.KC.F4Rank CFSG.KC.F4Syl3 CFSG.KC.F4Salt

@[expose] noncomputable def dotAux (r v : Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun p ih => (r &&& v) >>> p % 2 ^^^ ih) n

@[expose] noncomputable def dotR (r v : Nat) : Nat :=
  dotAux r v 52

@[expose] noncomputable def basisChk (B : Nat) : Bool :=
  echelon ((List.range 52).map (colR B))

@[expose] noncomputable def flagChk (B G C : Nat) : Bool :=
  allN 52 fun i => vapp G (colR B i) ^^^ colR B i == vapp B (colR C i) && colR C i >>> i == 0

@[expose] noncomputable def coordChk (r B j₀ : Nat) : Bool :=
  allN 52 fun j => dotR r (colR B j) == (j == j₀).toNat

@[expose] def fldW (X w i : Nat) : Nat :=
  X >>> (w * i) % 2 ^ w

@[expose] noncomputable def orbRow (gs : List Nat) (w₀ P R i : Nat) : Bool :=
  (fldW R 32 i / 16384 == 0 && fldW P 64 i == w₀ ||
    Nat.blt (fldW R 32 (fldW R 32 i % 4096) / 16384) (fldW R 32 i / 16384) &&
      Nat.blt (fldW R 32 i / 4096 % 4) gs.length && vapp (gs.getD (fldW R 32 i / 4096 % 4) 0) (fldW P 64 (fldW R 32 i % 4096)) ==
        fldW P 64 i) &&
  (i == 0 || Nat.blt (fldW P 64 (i - 1)) (fldW P 64 i)) && Nat.blt (fldW P 64 i) (2 ^ 52)

@[expose] noncomputable def orbChk (gs : List Nat) (w₀ P R n : Nat) : Bool :=
  allN n fun i => orbRow gs w₀ P R i && Nat.blt (fldW R 32 i % 4096) n

@[expose] noncomputable def prodS (gs : List Nat) (w : List Nat) : Nat :=
  w.foldr (fun k acc => CFSG.KC.Loop.strictN acc fun A => mulS (saltOf (gs.getD k 0)) A) oneS

@[expose] noncomputable def stabRow (gs hs : List Nat) (hw : List (List Nat)) (w₁ j : Nat) :
    Bool :=
  (hw.getD j []).all (fun k => Nat.blt k gs.length) &&
    eqS (prodS gs (hw.getD j [])) (saltOf (hs.getD j 0)) && vapp (hs.getD j 0) w₁ == w₁

end CFSG.KC.F4Gamma

end
