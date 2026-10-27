module

public import CFSG.LocalAnalysis.WeakClosure81.FourFiveComp
public import CFSG.Quasithin.EmptyFaithful.E111RComp
public import CFSG.Quasithin.EmptyFaithful.E22NParam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N
open CFSG.Quasithin.Vol2.Ch11.SecB Subgroup

private theorem fourFive_isQuasisimple_of_simple_nonabelian {A : Type*} [Group A]
    [IsSimpleGroup A] (h : ¬ IsMulCommutative A) : CFSG.Open.IsQuasisimple A := by
  have hZ : Subgroup.center A = ⊥ :=
    (Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center A)).resolve_right fun ht =>
      h (Subgroup.center_eq_top_iff.mp ht)
  refine ⟨Group.isPerfect_def.mp ?_, ?_⟩
  · refine ⟨(Subgroup.Normal.eq_bot_or_eq_top (commutator A)).resolve_left fun hb => ?_⟩
    rw [commutator_def, commutator_top_right_eq_bot_iff_le_center, top_le_iff] at hb
    exact h (Subgroup.center_eq_top_iff.mp hb)
  · exact MulEquiv.isSimpleGroup ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot)

theorem fourFive_nmn_of_reduced {G : Type} [Group G] {X T : Subgroup G}
    (hR : E111Reduced G X T) : FourFiveNMN X := by
  obtain ⟨hn, hne, hmin, ⟨a, b, hab⟩, -, -, -⟩ := hR
  exact ⟨hn, hne, hmin, fun h => hab (h.is_comm.comm a b)⟩

theorem fourFive_isComponentOf_of_isComp {G : Type} [Group G] {X J : Subgroup G}
    (hJ : E111R.IsComp X J) : IsComponentOf J X := by
  haveI : IsSimpleGroup ↥J := hJ.2.2.1
  refine ⟨hJ.1, CFSG.Open.IsSubnormal.step hJ.1 hJ.2.1 (CFSG.Open.IsSubnormal.refl X), ?_⟩
  exact fourFive_isQuasisimple_of_simple_nonabelian fun h => by
    obtain ⟨a, b, hab⟩ := hJ.2.2.2
    exact hab (h.is_comm.comm a b)

end CFSG.LocalAnalysis.WeakClosure81
