module

public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FoundA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FoundB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem s134_clause_two (hW : ∀ w : W, w * w = 1) {Y K : Subgroup (MulAut W)}
    (hK : IsComponentOf K Y) {g : MulAut W} (hg : g ∈ Y)
    (hgK : g ∉ normalizer (K : Set (MulAut W))) (hI : commSub ⊤ K ∈ irrSet K) :
    commSub (commSub ⊤ K) (K.map (MulAut.conj g).toMonoidHom) = ⊥ := by
  set K' : Subgroup (MulAut W) := K.map (MulAut.conj g).toMonoidHom with hK'def
  have hK' : IsComponentOf K' Y := by
    rw [hK'def]
    exact CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK hg
  have hne : K' ≠ K := by
    intro h
    apply hgK
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hK'def.trans h
  have hcomm : ⁅K, K'⁆ = ⊥ :=
    CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hK hK' (Ne.symm hne)
  have hRK : ⁅K, K⁆ = K := by
    have hq := hK.2.2.1
    have hmap := Subgroup.map_subtype_commutator K
    rw [hq, Subgroup.map_top, Subgroup.range_subtype] at hmap
    exact hmap.symm
  have hRK' : ⁅K', K'⁆ = K' := by
    have hq := hK'.2.2.1
    have hmap := Subgroup.map_subtype_commutator K'
    rw [hq, Subgroup.map_top, Subgroup.range_subtype] at hmap
    exact hmap.symm
  have hcomm_el : ∀ x ∈ K, ∀ k' ∈ K', k' * x = x * k' := by
    intro x hx k' hk'
    exact (Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hx)) k' hk'
  have hstab : StableUnder K' (commSub ⊤ K) := by
    intro k' hk' w hw
    rw [commSub] at hw
    refine Subgroup.closure_induction (p := fun c _ => k' c ∈ commSub ⊤ K) ?_ ?_ ?_ ?_ hw
    · rintro c ⟨x, hx, v, -, rfl⟩
      have hkx : k' * x = x * k' := hcomm_el x hx k' hk'
      have h1 : k' (x v) = x (k' v) := by
        have := congrArg (fun f : MulAut W => f v) hkx
        simpa [MulAut.mul_apply] using this
      have hmem : x (k' v) * (k' v)⁻¹ ∈ commSub ⊤ K :=
        Subgroup.subset_closure ⟨x, hx, k' v, Subgroup.mem_top _, rfl⟩
      simpa only [map_mul, map_inv, h1] using hmem
    · simp
    · intro a b ha hb iha ihb
      rw [map_mul]
      exact (commSub ⊤ K).mul_mem iha ihb
    · intro a ha iha
      rw [map_inv]
      exact (commSub ⊤ K).inv_mem iha
  have hschur := s13_schur_perfect hW K K' hcomm hRK' (commSub ⊤ K) hI.2.2.1 hstab hI.2
  have hC := s13_commSub_comm K K' hcomm ⊤
  have hle : commSub (commSub ⊤ K') K ≤ fixV K := by
    rw [← hC]
    exact hschur.trans inf_le_right
  have hbot : commSub (commSub (commSub ⊤ K') K) K = ⊥ :=
    commSub_eq_bot_iff.mpr hle
  have hchain := s13_perfect_chain K hRK ⊥ (commSub (commSub ⊤ K') K) (commSub ⊤ K')
    hbot.le le_rfl
  have hU : commSub (commSub ⊤ K') K = ⊥ := le_bot_iff.mp hchain
  rw [hC]
  exact hU

end CFSG.LocalAnalysis.WeakClosure81
