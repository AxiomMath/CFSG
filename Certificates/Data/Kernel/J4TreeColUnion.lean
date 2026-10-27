module

public import Certificates.Data.Kernel.J4TreeCol

public section

namespace CFSG.KC.J4TreeCol

open CFSG.KC.J4TreeN CFSG.KC.J4Tree CFSG.KC.J4Q CFSG.KC.Loop CFSG.J4Tree.Native

@[expose] noncomputable def colUnionOK (T : Tabs) (D : CRec) : Bool :=
  let wv := treeWv D.k
  let B := wv.map (ccT T)
  let n := 2 ^ wv.length
  Nat.ble wv.length 9 && wv.all coordOK && B.all (fun b => sqOneK b && B.all fun b' => commK b b') &&
    Nat.ble D.mode 1 && labsOK T.sx D (codesOf B) && unionOK D n (bitsOf D.om n)

end CFSG.KC.J4TreeCol

end
