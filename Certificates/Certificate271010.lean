module

public import CFSG.CGT.T75M23.N7Class
public import CFSG.CGT.T75M23.N7Rels
import Certificates.Kernel.CosPres.N7Class
import Certificates.Kernel.CosPres.N7A7
import Certificates.Kernel.CosPres.F271010
import CFSG.Certificates.Kernel.N7ModClassSound
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.CosetTable CFSG.CGT.T75M23 CFSG.KC.MiscCoset

namespace Certificates

open CFSG.CosetTable CFSG.CGT.T75M23 in
theorem certificate271010 : ModClass7 ∧ A7Nodup ∧ (Finite (PG 6 rels7) ∧ Nat.card (PG 6 rels7) ≤ 40320) := by
  obtain ⟨f, c⟩ := TableFact.card_restrict rels7 (by norm_num) (subsetOf 6 [0, 1]) (by decide)
    CFSG.KBFact.F271010a CFSG.KBFact.F271010b
  exact ⟨CFSG.KernelN7.modClass7_of_checks CFSG.KernelN7.invAll7_ok CFSG.KernelN7.relAll70_ok
    CFSG.KernelN7.relAll71_ok, CFSG.KernelN7.a7Nodup_ok, f, c.trans (by norm_num)⟩

end Certificates
