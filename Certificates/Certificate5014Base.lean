
module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.QuaternionCoordinateHom
public import CFSG.GH74.E2.Basic

@[expose] public section

open CFSG
open CFSG.GH74
open CFSG.GH74.E2
open Subgroup

namespace CertificateChecks.Batch5014

set_option maxHeartbeats 0 in
private theorem card_mulAut_q8_0 : Nat.card (MulAut (QuaternionGroup 2)) = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

end CertificateChecks.Batch5014

