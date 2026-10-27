module

public import CFSG.Sporadic.ThI301.RowMaxAux
public import CFSG.Sporadic.ThSchreier.NodeFullAutomorphism

public noncomputable section

namespace CFSG.Sporadic.ThI301

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Recog CFSG.Open
  CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8
  CFSG.LocalAnalysis.GLTheoremA.H301


theorem row_hMax : ∀ (A : Type) [Group A] [Finite A] (ι : J →* A), Function.Injective ι →
    ι.range.Normal → Subgroup.centralizer (ι.range : Set A) = ⊥ →
    ∀ R' : Subgroup A, IsPGroup 2 R' →
      (rowKOf Row.th.prime (hswJ 6) Max3.Q ⊔ B1).map ι ≤ Subgroup.normalizer (R' : Set A) →
      Max3.Q.map ι ≤ R' → R' = Max3.Q.map ι := by
  intro A _ _ ι hι hN hC R' hR' hKB hQR'
  have htop := range_eq_top_of_forall_inner (K := ↥J) (A := A) (fun α => by
    have h : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner J := by
      rw [CFSG.Sporadic.ThSchreier.inner_J]
      exact Subgroup.mem_top _
    obtain ⟨g, hg⟩ := h
    exact ⟨g, hg.symm⟩) ι hι hN hC
  have hR'eq : R' = (R'.comap ι).map ι := by
    rw [Subgroup.map_comap_eq, htop, top_inf_eq]
  rw [row_K, bot_sup_eq] at hKB
  rw [hR'eq, eq_Q_of_invariant (R'.comap ι) (hR'.comap_of_injective ι hι)
    ((Subgroup.map_le_iff_le_comap.1 hKB).trans (Subgroup.le_normalizer_comap ι))
    (Subgroup.map_le_iff_le_comap.1 hQR')]

end CFSG.Sporadic.ThI301
