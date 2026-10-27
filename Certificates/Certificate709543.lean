module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.LocalAnalysis.StandardType.GGZSNFourInputs
import Certificates.Kernel.CosPres.F709543
import CFSG.Certificates.Kernel.Misc.Coset.TableFactSub

public section

public section

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.StandardType.ZS

namespace Certificates

open CFSG.CosetTable CFSG.StandardType.ZS in
theorem certificate709543 :
    (Finite (PG 4 n4Rels) ∧ Nat.card (PG 4 n4Rels) ≤ 7680) ∧
      (Finite (PG 5 en4Rels) ∧ Nat.card (PG 5 en4Rels) ≤ 46080) :=
  ⟨TableFact.card_restrict n4Rels (by norm_num) (subsetOf 4 [0, 1, 2]) (by decide)
    CFSG.KBFact.F709543a CFSG.KBFact.F709543b,
   card_PG_le_chain₃_tf (ws := en4Rels) (L₃ := en4Rels)
    (L₂ := restrictWords (subsetOf 5 [0, 1, 2, 3]) en4Rels)
    (L₁ := restrictWords (subsetOf 4 [0, 1, 2])
      (restrictWords (subsetOf 5 [0, 1, 2, 3]) en4Rels))
    (S₁ := [0, 1, 2, 3]) (S₂ := [0, 1, 2]) (by norm_num) (by decide) (by decide)
    (fun _ h => h) (fun _ h => h) (fun _ h => h)
    CFSG.KBFact.F709543c CFSG.KBFact.F709543d CFSG.KBFact.F709543e⟩

end Certificates

end
