module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3DataCo1
import Certificates.Kernel.Local3.Co1
import Certificates.Kernel.CosetCC.C291362A
import CFSG.Certificates.Kernel.Local3KSound
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Misc.Coset.PGFilter

public section

open CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator CFSG.KC.MiscCoset
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.LieType.Multipliers CertificateChecks.KernelLocal3

namespace Certificates

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
private theorem certificate291362_rels :
    (coverWords co1Local3.rels (fun i => [(i, true)]) ++ cubeWords co1Local3.rels ++
      powWords (fun i => co1Local3.ords.getD i 0)).map encW = CFSG.KBRoute.F291362.rels := by
  decide +kernel

set_option maxRecDepth 200000 in
open CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator in
theorem certificate291362 : (∃ x : Fin 3 → CFSG.Blueprint.NativeSporadic.Co1,
      (∀ r ∈ co1Local3.rels, FreeGroup.lift x (FreeGroup.mk r) = 1) ∧
      (∀ i : Fin 3, x i ^ co1Local3.ords.getD i 0 = 1) ∧
      157464 ≤ Nat.card (Subgroup.closure (Set.range x))) ∧
    (Finite (PG 3 co1Cover) ∧ Nat.card (PG 3 co1Cover) ≤ 157464) := by
  have h := CFSG.KBFact.F291362
  rw [← certificate291362_rels] at h
  have hc := TableFact.card _ (by norm_num) h
  have e : PG 3 co1Cover = PG 3 (coverWords co1Local3.rels (fun i => [(i, true)]) ++
      cubeWords co1Local3.rels ++ powWords (fun i => co1Local3.ords.getD i 0)) :=
    PG_congr_mem fun w => by
      rw [co1Cover, mem_cover₃Words, List.mem_append, List.mem_append, or_assoc]
  rw [← e] at hc
  obtain ⟨x, hR, hpow, hn⟩ := CFSG.KC.Local3K.exists_local3_of_K Co1.SA.bind Co1.SB.bind Co1.SA.eq
    Co1.SB.eq Co1.MS.eq Co1.local3_K
  exact ⟨⟨x, hR, hpow, hn⟩, hc⟩

end Certificates
