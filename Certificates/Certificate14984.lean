module

public import CFSG.CGT.T75JM.N6Class
public import CFSG.CGT.T75JM.N6A6
public import CFSG.CGT.T75JM.N6Rels
import Certificates.Kernel.Census.N6.Class
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Census.N6.A6
import Certificates.Kernel.Census.N6.F14984
import CFSG.Certificates.Kernel.N6ModClassSound
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import CFSG.CGT.T75JM.M22PresInputs
public import Mathlib

public section

open CFSG.CosetTable CFSG.CGT.T75JM CFSG.KC.MiscCoset

namespace Certificates

open CFSG.CGT.T75JM CFSG.CosetTable in
theorem certificate14984 : ModClass ∧ A6Nodup ∧ (Finite (PG 6 rels6) ∧ Nat.card (PG 6 rels6) ≤ 5760) ∧
    (Finite (PG (subsetOf 6 [0, 1]).length rels6K) ∧
      Nat.card (PG (subsetOf 6 [0, 1]).length rels6K) ≤ 360) :=
  ⟨CFSG.KernelN6.modClass_of_checks CFSG.KernelN6.invAll_ok CFSG.KernelN6.relAll0_ok
      CFSG.KernelN6.relAll1_ok,
    CFSG.KernelN6.a6Nodup_ok,
    TableFact.card_restrict rels6 (by norm_num) (subsetOf 6 [0, 1]) (by decide)
      CFSG.KBFact.F14984a CFSG.KBFact.F14984b,
    TableFact.card rels6K (by decide) CFSG.KBFact.F14984b⟩

end Certificates
