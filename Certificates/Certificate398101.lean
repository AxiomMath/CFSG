module

public import Certificates.Data.TwinPerpV3A6iCurtis
import Certificates.Kernel.CosPres.F398101
import CFSG.Certificates.Kernel.Misc.Coset.TableFactSub

public section

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6

namespace Certificates

open CFSG.CosetTable CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6 in
theorem certificate398101 : Finite (PG 8 curtisPG) ∧ Nat.card (PG 8 curtisPG) ≤ 8640 * (560 * 36) :=
  card_PG_le_chain₃_tf (ws := curtisPG) (L₃ := curtisPG) (L₂ := curtisSub) (L₁ := curtisSubSub)
    (S₁ := [2, 3, 4, 5, 6, 7]) (S₂ := [2, 3, 4, 5]) (by norm_num) (by decide) (by decide)
    (fun _ h => h) (fun _ h => h) (fun _ h => h)
    CFSG.KBFact.F398101a CFSG.KBFact.F398101b CFSG.KBFact.F398101c

end Certificates
