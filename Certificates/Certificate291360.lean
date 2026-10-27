module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3DataCo3
import Certificates.Kernel.Local3.Co3
import Certificates.Kernel.CosetCC.C291360A
import CFSG.Certificates.Kernel.Local3KSound
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Misc.Coset.PGFilter

public section

open CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator CFSG.KC.MiscCoset
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.LieType.Multipliers CertificateChecks.KernelLocal3

namespace Certificates

set_option maxRecDepth 200000

private theorem certificate291360_rels_a :
    (coverWords co3Local3.rels (fun i => [(i, true)]) ++ cubeWords co3Local3.rels ++
      powWords (fun i => co3Local3.ords.getD i 0)).map encW = CFSG.KBRoute.F291360a.rels := by
  decide +kernel

private theorem certificate291360_rels_b :
    (restrictWords (subsetOf 3 [2]) (coverWords co3Local3.rels (fun i => [(i, true)]) ++
      cubeWords co3Local3.rels ++ powWords (fun i => co3Local3.ords.getD i 0))).map encW =
      CFSG.KBRoute.F291360b.rels := by
  decide +kernel

open CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator in
theorem certificate291360 : (∃ x : Fin 3 → CFSG.Blueprint.NativeSporadic.Co3,
      (∀ r ∈ co3Local3.rels, FreeGroup.lift x (FreeGroup.mk r) = 1) ∧
      (∀ i : Fin 3, x i ^ co3Local3.ords.getD i 0 = 1) ∧
      69984 ≤ Nat.card (Subgroup.closure (Set.range x))) ∧
    (Finite (PG 3 co3Cover) ∧ Nat.card (PG 3 co3Cover) ≤ 69984) := by
  have ha := CFSG.KBFact.F291360a
  have hb := CFSG.KBFact.F291360b
  rw [← certificate291360_rels_a] at ha
  rw [← certificate291360_rels_b] at hb
  have hc := TableFact.card_restrict _ (by norm_num) (subsetOf 3 [2]) (by decide) ha hb
  have e : PG 3 co3Cover = PG 3 (coverWords co3Local3.rels (fun i => [(i, true)]) ++
      cubeWords co3Local3.rels ++ powWords (fun i => co3Local3.ords.getD i 0)) :=
    PG_congr_mem fun w => by
      rw [co3Cover, mem_cover₃Words, List.mem_append, List.mem_append, or_assoc]
  rw [← e] at hc
  obtain ⟨x, hR, hpow, hn⟩ := CFSG.KC.Local3K.exists_local3_of_K Co3.SA.bind Co3.SB.bind Co3.SA.eq
    Co3.SB.eq Co3.MS.eq Co3.local3_K
  exact ⟨⟨x, hR, hpow, hn⟩, hc⟩

end Certificates
