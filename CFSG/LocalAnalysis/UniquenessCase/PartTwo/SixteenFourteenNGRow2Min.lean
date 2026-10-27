module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

private lemma s1614_rm_conj_apply {W : Type} [CommGroup W] (x l : MulAut W) (w : W) :
    (x * l * x⁻¹) (x w) = x (l w) := by
  simp [MulAut.mul_apply]

theorem s1614_exists_irr_le {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)}
    (hfix : fixV A = ⊥) {U : Subgroup W} (hU : StableUnder A U) (hne : U ≠ ⊥) :
    ∃ I : Subgroup W, I ∈ irrSet A ∧ I ≤ U := by
  obtain ⟨I, hIU, hIirr⟩ := s15_Three_exists_irr_le hU hne
  have hIirr' : IsIrrOn A I (I ⊓ fixV A) := by simpa [hfix] using hIirr
  have hJI : commSub I A ≤ I := commSub_le_of_invariant hIirr.2.1
  have hJstab : StableUnder A (commSub I A) := by
    intro x hx u hu
    have hmap : (commSub I A).map x.toMonoidHom ≤ commSub I A := by
      rw [commSub, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨c, ⟨l, hl, w, hw, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨x * l * x⁻¹, ?_, x w, hIirr.2.1 x hx w hw, ?_⟩
      · exact A.mul_mem (A.mul_mem hx hl) (A.inv_mem hx)
      · show (x * l * x⁻¹) (x w) * (x w)⁻¹ = x (l w * w⁻¹)
        rw [map_mul, map_inv, s1614_rm_conj_apply]
    exact hmap (Subgroup.mem_map.2 ⟨u, hu, rfl⟩)
  have hJne : commSub I A ≠ ⊥ := by
    intro hbot
    have hle : I ≤ fixV A := commSub_eq_bot_iff.1 hbot
    rw [hfix] at hle
    exact absurd (le_bot_iff.1 hle) (ne_of_gt hIirr.1)
  rcases hIirr.2.2.2 (commSub I A) hJstab bot_le hJI with hbot | htop
  · exact absurd hbot hJne
  · exact ⟨I, ⟨htop, hIirr'⟩, hIU⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
