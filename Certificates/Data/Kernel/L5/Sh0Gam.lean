module

public import Certificates.Data.Kernel.L5.Sh0T

public section

namespace CFSG.Certificates.Kernel.L5S

@[expose] noncomputable def gamL (m : Nat) : List Nat :=
  (List.range 128).map fun j => evFromT tF (xsK.getD m []) 0 (wdK.getD j [])

@[expose] def invTabL (t : List Nat) : List Nat :=
  (List.range 128).map fun i => ((List.range 128).find? fun j => t.getD j 0 == i).getD 0

@[expose] def gamChkT (mt iv : Nat → Nat) (t ti : List Nat) (s : Nat) : Bool :=
  decide (s < 128) &&
  (List.range 128).all (fun a => decide (t.getD a 0 < 128) && decide (ti.getD a 0 < 128) &&
      decide (ti.getD (t.getD a 0) 0 = a) && decide (t.getD (ti.getD a 0) 0 = a)) &&
  (List.range 128).all (fun a => (List.range 128).all fun b =>
      decide (t.getD (mt (a * 128 + b)) 0 = mt (t.getD a 0 * 128 + t.getD b 0))) &&
  decide (t.getD s 0 = s) &&
  (List.range 128).all (fun a => decide (t.getD (t.getD a 0) 0 = conjIT mt iv s a))

@[expose] noncomputable def gamK (m : Nat) : Bool :=
  gamChkT tF iT (gamL m) (invTabL (gamL m)) (ssK.getD m 0)

@[expose] noncomputable def wdChkK : Bool :=
  gsK.all (fun n => decide (n < 128)) &&
    (List.range 128).all fun i =>
      decide (evFromT tF gsK 0 (wdK.getD i []) = i) && (wdK.getD i []).all fun k => decide (k < 3)

@[expose] noncomputable def relsChkK : Bool :=
  (relK :: relsK).all fun r => decide (evFromT tF gsK 0 r.1 = evFromT tF gsK 0 r.2)

end CFSG.Certificates.Kernel.L5S

end
