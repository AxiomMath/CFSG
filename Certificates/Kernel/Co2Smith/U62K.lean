module

public import Certificates.Kernel.Co2Smith.RootDefs
public import CFSG.Sporadic.Co2Smith.GlU62Inputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native

@[expose] noncomputable def qnfK (c : Nat × Nat × Nat × Nat × Nat) : Nat :=
  mulV (mulV (mulV (mulV (if c.1 == 1 then zK else IDP) (rootK 0 c.2.1)) (rootK 1 c.2.2.1))
    (rootK 2 c.2.2.2.1)) (rootK 3 c.2.2.2.2)

@[expose] noncomputable def wrK (G : List Nat) (w : List Nat) : Nat :=
  w.foldl (fun a j => mulV a (G.getD j IDP)) IDP

@[expose] def distL : List Nat → Bool
  | [] => true
  | a :: l => l.all (fun b => !Nat.beq a b) && distL l

@[expose] noncomputable def invK (ws : List (List Nat)) : Bool :=
  ws.all fun w => w.all (· < 22) && eqK (mulV (wK LP w) (wK LP w)) IDP && mapsK (wK LP w) 80 80

@[expose] noncomputable def g1K : List Nat := u62G1Words.map (wK LP)

@[expose] noncomputable def orbK (w : List Nat) : Nat :=
  mulV (mulV (wrK g1K w) zK) (wrK g1K w.reverse)

@[expose] noncomputable def c1K : List Nat := u62C1Words.map (wK LP)

theorem q_k : ((List.range 8).all fun j =>
    eqK (LP (j + 1)) (qnfK (u62QNF.getD j (0, 0, 0, 0, 0)))) = true := by
  decide +kernel

theorem comm_k : (!commK zK x61K) = true := by
  decide +kernel

theorem l1w_k : (u62L1Words.all (fun w => w.all (· < 22) && mapsK (wK LP w) 80 80 &&
      commK (wK LP w) zK) &&
    u62L1Words.length == 22 && u62L1Words.getD 21 [] == glD0hWord &&
    (List.range 21).all fun i => eqK (wK LP (u62L1Words.getD i []))
      (rootK (u62L1Ids.getD i (0, 0)).1 (u62L1Ids.getD i (0, 0)).2)) = true := by
  decide +kernel

theorem orb_k : (invK u62G1Words && u62Orb.size == 693 &&
    distL (u62Orb.toList.map fun w => cK (orbK w))) = true := by
  decide +kernel

theorem c1_k : (invK u62C1Words && u62C1Words.all (fun w => w.all (glC0Let.contains ·)) &&
    u62C1.size == 1296 && distL (u62C1.toList.map fun w => cK (wrK c1K w)) &&
    u62C1Words.length == 8 && u62C1Words.getD 6 [] == glD0hWord &&
    u62C1Words.getD 7 [] == glD1hWord &&
    (List.range 6).all fun j => eqK (wK LP (u62C1Words.getD j [])) (longK (u62C1Frame.getD j 0))) =
    true := by
  decide +kernel

end CertificateChecks.KernelCo2Smith
