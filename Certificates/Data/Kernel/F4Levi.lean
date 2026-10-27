module

public import Certificates.Data.Kernel.F4Gamma

public section

namespace CFSG.KC.F4Levi

open CFSG.LieType.Simplicity.TitsBits CFSG.KC.F4Salt CFSG.KC.Loop CFSG.KC.F4Syl3
  CFSG.KC.F4Gamma

@[expose] def lvC (l : Nat) : Nat := if l < 3 then l + 1 else l + 2

@[expose] noncomputable def lvOK (W L : Nat) : Bool :=
  allN L fun m => digit W m != 0 && digit W m != 4

@[expose] noncomputable def genN (l : Nat) : Nat :=
  strictN (letS (lvC l)) fun X => strictN (saltOf (sBits 3)) fun R =>
    (eqS (mulS X X) oneS && eqS (mulS X R) (mulS R X)).toNat

@[expose] noncomputable def d3Row (dw dl gs : List Nat) (k : Nat) : Bool :=
  lvOK (dw.getD k 0) (dl.getD k 0) &&
    eqS (wordS (dw.getD k 0) (dl.getD k 0)) (saltOf (gs.getD k 0))

@[expose] noncomputable def elN (gs es : List Nat) (ew : List (List Nat)) (nx : List Nat)
    (n i : Nat) : Nat :=
  ((ew.getD i []).all (fun k => Nat.blt k 4)).toNat *
    strictN (saltOf (es.getD i 0)) fun E =>
      (eqS (prodS gs (ew.getD i [])) E &&
        allN 4 fun k => Nat.blt (nx.getD (4 * i + k) 0) n &&
          eqS (mulS E (saltOf (gs.getD k 0))) (saltOf (es.getD (nx.getD (4 * i + k) 0) 0))).toNat

@[expose] def incB : List Nat → Bool
  | a :: b :: l => Nat.blt a b && incB (b :: l)
  | _ => true

@[expose] noncomputable def cvN (es cw cl ri ra : List Nat) (i : Nat) : Nat :=
  strictN (saltOf (es.getD i 0)) fun X =>
    if eqS X oneS || !eqS (mulS (mulS X X) X) oneS then 1 else
      (Nat.blt (ri.getD i 0) 3 && lvOK (cw.getD i 0) (cl.getD i 0)).toNat *
        strictN (wordS (cw.getD i 0) (cl.getD i 0)) fun C =>
          (eqS (mulS C X) (mulS (saltOf (es.getD (ra.getD (ri.getD i 0) 0) 0)) C)).toNat

end CFSG.KC.F4Levi

end
