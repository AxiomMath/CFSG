module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}

private theorem s16t3_fixV_map_mk_eq_bot :
    (fixV L).map (QuotientGroup.mk' (modFix L (⊤ : Subgroup W))) = ⊥ := by
  have hZ : modFix L (⊤ : Subgroup W) = fixV L := by
    rw [modFix, fixed_eq_inf_fixV, top_inf_eq]
  rw [← hZ, QuotientGroup.map_mk'_self]

private theorem s16t3_tilde_sup_fixV (J : Subgroup W) :
    tilde L (⊤ : Subgroup W) (J ⊔ fixV L) = tilde L (⊤ : Subgroup W) J := by
  unfold tilde
  rw [Subgroup.map_sup, s16t3_fixV_map_mk_eq_bot, sup_bot_eq]

private theorem s16t3_tilde_iSup {ι : Sort*} (J : ι → Subgroup W) :
    (⨆ i, tilde L (⊤ : Subgroup W) (J i)) = tilde L (⊤ : Subgroup W) (⨆ i, J i) := by
  unfold tilde
  rw [Subgroup.map_iSup]

theorem s16t3_quot_summands (hq : CFSG.Open.IsQuasisimple ↥L)
    (hsum : SumOfNatShape L (⊤ : Subgroup W) (fixV L) 3) :
    ∃ I : Fin 3 → Subgroup W, (∀ i, SumOfNatShape L (I i) (fixV L) 1) ∧
      (∀ i, XMod.IsIrr ↥L (tilde L (⊤ : Subgroup W) (I i))) ∧
      iSupIndep (fun i => tilde L (⊤ : Subgroup W) (I i)) ∧
      (⨆ i, tilde L (⊤ : Subgroup W) (I i)) = ⊤ := by
  obtain ⟨I, hZI, hind, hsup, hnat⟩ := s16t3_summands (L := L) hsum
  refine ⟨I, hnat, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨hJ, -, hJZ⟩ := s16t3_commSub_mem_irrSet_of_natural (L := L) hq (hZI i) (hnat i)
    have hIi : tilde L (⊤ : Subgroup W) (I i) =
        tilde L (⊤ : Subgroup W) (commSub (I i) L) := by
      conv_lhs => rw [← hJZ]
      exact s16t3_tilde_sup_fixV (commSub (I i) L)
    rw [hIi]
    exact s16t3_isIrr_tilde_of_mem_irrSet (L := L) hq hJ
  · rw [iSupIndep_def]
    intro i
    rw [disjoint_iff]
    rw [Subgroup.eq_bot_iff_forall]
    intro q hqmem
    obtain ⟨hqi, hqj⟩ := Subgroup.mem_inf.1 hqmem
    obtain ⟨a, ha, haq⟩ :=
      (mem_tilde_iff (X := L) (W := (⊤ : Subgroup W)) (I := I i)).1 hqi
    have h2 : (⨆ (j : Fin 3) (_ : j ≠ i), tilde L (⊤ : Subgroup W) (I j)) =
        tilde L (⊤ : Subgroup W) (⨆ (j : Fin 3) (_ : j ≠ i), I j) := by
      simp_rw [s16t3_tilde_iSup]
    rw [h2] at hqj
    obtain ⟨b, hb, hbq⟩ :=
      (mem_tilde_iff (X := L) (W := (⊤ : Subgroup W))
        (I := ⨆ (j : Fin 3) (_ : j ≠ i), I j)).1 hqj
    have hab : (QuotientGroup.mk a : W ⧸ modFix L (⊤ : Subgroup W)) =
        QuotientGroup.mk b := by
      rw [haq, hbq]
    have hZ : modFix L (⊤ : Subgroup W) = fixV L := by
      rw [modFix, fixed_eq_inf_fixV, top_inf_eq]
    have hz : a⁻¹ * b ∈ modFix L (⊤ : Subgroup W) := QuotientGroup.eq.1 hab
    have hzfix : a⁻¹ * b ∈ fixV L := by
      rwa [hZ] at hz
    have hain : a ∈ I i ⊓ (fixV L ⊔ ⨆ (j : Fin 3) (_ : j ≠ i), I j) := by
      refine Subgroup.mem_inf.2 ⟨ha, ?_⟩
      rw [sup_comm]
      refine Subgroup.mem_sup.2 ⟨b, hb, (a⁻¹ * b)⁻¹, inv_mem hzfix, ?_⟩
      rw [mul_inv_rev, inv_inv]
      exact mul_inv_cancel_left b a
    have hfix : a ∈ fixV L := hind i hain
    rw [← haq]
    exact (QuotientGroup.eq_one_iff a).2 (by rwa [hZ])
  · have hgen : (⨆ i, tilde L (⊤ : Subgroup W) (I i)) =
        tilde L (⊤ : Subgroup W) (⨆ i, I i) := by
      simp_rw [s16t3_tilde_iSup]
    rw [hgen]
    calc tilde L (⊤ : Subgroup W) (⨆ i, I i)
        = tilde L (⊤ : Subgroup W) (fixV L ⊔ ⨆ i, I i) := by
          rw [sup_comm, s16t3_tilde_sup_fixV]
      _ = tilde L (⊤ : Subgroup W) (⊤ : Subgroup W) := by rw [hsup]
      _ = ⊤ := Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
