module

public import CFSG.Quasithin.Background.F918J1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def D3A38 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
      Mp = L ⊔ conjAutSub t L → A38Types ↥L

theorem d3L38_of_a38 (h : D3A38) : D3L38 := by
  intro W _ _ M Mp T L V std t ht htn hMp
  have hA := h W M Mp T L V std t ht htn hMp
  have hcomm := insp5a_commute std.hyp ht htn hA
  refine ⟨hA, hcomm, ?_, insp5a_conj_cases std.hyp ht hMp hA⟩
  have hLs : IsSimpleGroup ↥L :=
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hA
  have hcent : conjAutSub t L ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rw [Subgroup.commutator_comm]
    exact hcomm
  have hZ : Subgroup.center ↥L = ⊥ := by
    rcases hLs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h0 | h0
    · exact h0
    · exfalso
      refine not_isSolvable_of_mem_cComp std.hyp.comp (Group.isSolvable_of_comm fun a b => ?_)
      exact Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top b) a
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hxZ : (⟨x, hx.1⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_centralizer_iff.mp (hcent hx.2) (g : MulAut W) g.2
    exact Subtype.ext this
  rw [hZ, Subgroup.mem_bot] at hxZ
  exact congrArg Subtype.val hxZ

end CFSG.Quasithin
