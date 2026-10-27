module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3DataCo2
import Certificates.Kernel.Local3.Co2
import Certificates.Kernel.CosetCC.C291361A
import CFSG.Certificates.Kernel.Local3KSound
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Misc.Coset.PGFilter

public section

open CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator CFSG.KC.MiscCoset
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.LieType.Multipliers CertificateChecks.KernelLocal3

namespace Certificates

private theorem certificate291361_rels :
    (coverWords co2Local3.rels (fun i => [(i, true)]) ++ cubeWords co2Local3.rels ++
      powWords (fun i => co2Local3.ords.getD i 0)).map encW = CFSG.KBRoute.F291361.rels := by
  decide +kernel

open CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator in
theorem certificate291361 : (∃ x : Fin 3 → CFSG.Blueprint.NativeSporadic.Co2,
      (∀ r ∈ co2Local3.rels, FreeGroup.lift x (FreeGroup.mk r) = 1) ∧
      (∀ i : Fin 3, x i ^ co2Local3.ords.getD i 0 = 1) ∧
      23328 ≤ Nat.card (Subgroup.closure (Set.range x))) ∧
    (Finite (PG 3 co2Cover) ∧ Nat.card (PG 3 co2Cover) ≤ 23328) := by
  have h := CFSG.KBFact.F291361
  rw [← certificate291361_rels] at h
  have hc := TableFact.card _ (by norm_num) h
  have e : PG 3 co2Cover = PG 3 (coverWords co2Local3.rels (fun i => [(i, true)]) ++
      cubeWords co2Local3.rels ++ powWords (fun i => co2Local3.ords.getD i 0)) :=
    PG_congr_mem fun w => by
      rw [co2Cover, mem_cover₃Words, List.mem_append, List.mem_append, or_assoc]
  rw [← e] at hc
  obtain ⟨x, hR, hpow, hn⟩ := CFSG.KC.Local3K.exists_local3_of_K Co2.SA.bind Co2.SB.bind Co2.SA.eq
    Co2.SB.eq Co2.MS.eq Co2.local3_K
  exact ⟨⟨x, hR, hpow, hn⟩, hc⟩

end Certificates
