module

public import CFSG.LocalAnalysis.WeakClosure81.EightTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem inf_centralizer_eSub_eq_bot_of_not_mem {V H T U : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : CFSG.CGT.Timmesfeld75.IsTI V) (hVne : V ≠ ⊥)
    (hH : IsCalH V H) (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)))
    (hUconj : ∃ g : G, U = conjSubgroup V g) (hUH : U ≤ H)
    (hUV : ∀ h ∈ H, U ≠ conjSubgroup V h)
    (hUC : ¬ ∀ h ∈ H, ∀ u ∈ U, ∀ v ∈ conjSubgroup V h, u * v = v * u) :
    U ⊓ Subgroup.centralizer (eSub V H T : Set G) = ⊥ ∧
      ∀ u ∈ U, u ≠ 1 →
        eSub V H T ⊓ Subgroup.centralizer (U : Set G) =
          eSub V H T ⊓ Subgroup.centralizer ({u} : Set G) := by
  have hbot : U ⊓ Subgroup.centralizer (eSub V H T : Set G) = ⊥ := by
    by_contra hne
    rcases eight_two hV hTI hVne hH hT hUconj hUH hne with hcomm | ⟨-, hconj'⟩
    · exact hUC hcomm
    · obtain ⟨h, hh, heq⟩ := hconj'
      exact hUV h hh heq
  refine ⟨hbot, ?_⟩
  intro u hu hu1
  obtain ⟨g, rfl⟩ := hUconj
  have hUn : conjSubgroup V g ≤ Subgroup.normalizer (eSub V H T : Set G) := by
    rw [eSub]
    exact hUH.trans
      (le_normalizer_conjClosure (V ⊓ Subgroup.centralizer (T : Set G)) H)
  have hEW : eSub V H T ⊓ conjSubgroup V g = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxU⟩ := Subgroup.mem_inf.mp hx
    have hxU' : x ∈ conjSubgroup V g ⊓
        Subgroup.centralizer (eSub V H T : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hxU, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy
      exact (congrArg Subtype.val
        ((eSub_isElemAbelian hV hH hT).1.is_comm.comm ⟨x, hxE⟩ ⟨y, hy⟩)).symm
    rw [hbot] at hxU'
    exact hxU'
  exact eight_one (V := conjSubgroup V g) (U := conjSubgroup V g) (E := eSub V H T)
    (isTI_conjSubgroup_quasithin hTI g) le_rfl hUn hEW hu hu1

end CFSG.LocalAnalysis.WeakClosure81

end
