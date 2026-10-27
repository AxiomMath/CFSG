module

public import Certificates.Certificate1037301
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFi22Pack

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.QuasithinUnique.Setup.X1
  CFSG.Certificates

theorem fi22_outerGen_t4 :
    ∃ cs : List (Equiv.Perm (Fin 3510)), cs.length = 4 ∧ (∀ c ∈ cs, c ∈ fi22P) ∧
      fi22P ≤ Subgroup.closure {x | ∃ c ∈ cs, x = c * fi22ExtRep 4 * c⁻¹} := by
  have hc : fi22OuterGenCheck () = true := Certificates.certificate1037301
  simp only [fi22OuterGenCheck] at hc
  have ht : PRep 3510 (fi22RepP 4) (fi22ExtRep 4) := pRep_fi22RepP (by norm_num)
  obtain ⟨gs, hlen, hgs, hmem⟩ := threeConj_sound regIn_fi22P ht hc
  have h0 := hmem (fi22ChainGen 0) (by simp) (fi22GenPerm 0) (rep_fi22Gen (by norm_num))
  have h1 := hmem (fi22ChainGen 1) (by simp) (fi22GenPerm 1) (rep_fi22Gen (by norm_num))
  refine ⟨gs, ?_, hgs, ?_⟩
  · rw [hlen]; rfl
  · have hle : fi22P ≤ Subgroup.closure (conjSet gs {fi22ExtRep 4}) := by
      rw [fi22P]
      refine (Subgroup.closure_le _).2 ?_
      intro y hy
      simp only [Set.mem_setOf_eq] at hy
      obtain ⟨j, hj⟩ := (schreier_vector_mem_toList_iff_get fi22Chain.original y).1 hy
      rw [fi22Chain_original_get j] at hj
      rw [← hj]
      fin_cases j
      · exact h0
      · exact h1
    have hsub : conjSet gs {fi22ExtRep 4} ⊆
        {x | ∃ c ∈ gs, x = c * fi22ExtRep 4 * c⁻¹} := by
      rintro x hx
      simp only [conjSet, Set.mem_setOf_eq, Set.mem_singleton_iff] at hx ⊢
      obtain ⟨c, hc, t, ht', rfl⟩ := hx
      exact ⟨c, hc, by rw [ht']⟩
    exact hle.trans (Subgroup.closure_mono hsub)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
