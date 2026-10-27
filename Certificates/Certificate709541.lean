module

public import CFSG.LocalAnalysis.StandardType.GGZSHallSoicherInputs
public import CFSG.Certificates.CosetTablePresented
import Certificates.Kernel.CosPres.F709541
import CFSG.Certificates.Kernel.Misc.Coset.TableFactSub

public section

public section

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.StandardType.ZS

namespace Certificates

open CFSG.CosetTable CFSG.StandardType.ZS in
theorem certificate709541 :
    (Finite (PG 5 hsFiveRels) ∧ Nat.card (PG 5 hsFiveRels) ≤ 51840) ∧
      (Finite (PG 6 hsSixRels) ∧ Nat.card (PG 6 hsSixRels) ≤ 39191040) :=
  ⟨TableFact.card_restrict hsFiveRels (by norm_num) (subsetOf 5 [0, 1, 2, 3]) (by decide)
    CFSG.KBFact.F709541a CFSG.KBFact.F709541b,
   card_PG_le_chain₃_tf (ws := hsSixRels) (L₃ := hsSixRels)
    (L₂ := restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) hsSixRels)
    (L₁ := restrictWords (subsetOf 5 [0, 1, 2, 3])
      (restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) hsSixRels))
    (S₁ := [0, 1, 2, 3, 4]) (S₂ := [0, 1, 2, 3]) (by norm_num) (by decide) (by decide)
    (fun _ h => h) (fun _ h => h) (fun _ h => h)
    CFSG.KBFact.F709541c CFSG.KBFact.F709541d CFSG.KBFact.F709541e⟩

end Certificates

end
