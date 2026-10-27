module

public import CFSG.Sporadic.SuzI301.RowBasic
public import CFSG.Sporadic.SuzOddCore.ExtModel
import CFSG.Sporadic.SuzI301.RowMaxAux

public noncomputable section

namespace CFSG.Sporadic.SuzI301

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore
  CFSG.ComponentClassification.AS81.SuzB0 CFSG.HardMathSupport.Dickson.I271 CFSG.Open
  CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8
  CFSG.LocalAnalysis.GLTheoremA.H301


theorem row_hMax : ∀ (A : Type) [Group A] [Finite A] (ι : ↥suzM →* A), Function.Injective ι →
    ι.range.Normal → Subgroup.centralizer (ι.range : Set A) = ⊥ →
    ∀ R' : Subgroup A, IsPGroup 2 R' →
      (B1.subgroupOf suzM).map ι ≤ Subgroup.normalizer (R' : Set A) →
      (Q1.subgroupOf suzM).map ι ≤ R' → R' = (Q1.subgroupOf suzM).map ι := by
  intro A _ _ ι hι hN hC R' hR' hBR hQR
  obtain ⟨f, hf, hfT, hfι⟩ := exists_embedding_suzT ι hι hN hC
  have hEM : invE 1 ≤ suzM := fun _ hg => (invE_le_centM (by norm_num) hg).2
  have hBM : B1 ≤ suzM := (Subgroup.closure_le suzM).2 (by
    rintro _ (rfl | rfl | rfl)
    exacts [hEM gens_mem.1, hEM gens_mem.2.1, hEM gens_mem.2.2.1])
  have hQM : Q1 ≤ suzM := fun _ hq => hEM (Q_le_invE hq)
  have hS := eq_Q1_of_invariant (R'.map f) (by rintro _ ⟨r, -, rfl⟩; exact hfT r) (hR'.map f)
    (fun b hb => by
      have h1 := Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f
        (hBR ⟨⟨b, hBM hb⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩))
      rwa [hfι] at h1)
    (fun q hq => by
      have h1 := Subgroup.mem_map_of_mem f (hQR ⟨⟨q, hQM hq⟩, Subgroup.mem_subgroupOf.2 hq, rfl⟩)
      rwa [hfι] at h1)
  refine le_antisymm (fun r hr => ?_) hQR
  have hr1 : f r ∈ Q1 := by
    rw [show Q1 = coord_qVec.Q from rfl, ← hS]
    exact Subgroup.mem_map_of_mem f hr
  exact ⟨⟨f r, hQM hr1⟩, Subgroup.mem_subgroupOf.2 hr1, hf (by rw [hfι])⟩

end CFSG.Sporadic.SuzI301
