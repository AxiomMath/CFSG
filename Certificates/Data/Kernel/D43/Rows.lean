module

public import CFSG.Milestones.ASVolI.F48.D43.Inputs
public import Certificates.Data.Kernel.D43.Twin

public section

namespace CFSG.KC.D43

open CFSG.ASVolI CFSG.KS.ON CFSG.Sporadic.Fi23.Native

@[expose] noncomputable def rowsOK (L : List Nat) (k : Nat) : Bool :=
  let M := burnsideF48d_rows (burnsideF48d_colTab ()) k
  M.size == 154 && L.length == 84 && (List.range 84).all fun j =>
    decide (M[j]! = ofV ⟨vP (L.getD j 0), vM (L.getD j 0)⟩) && canon (L.getD j 0)

end CFSG.KC.D43

end
