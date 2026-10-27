module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubBar2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem nonempty_bar2_mulEquiv_barSub_of_isSimpleGroup {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) {L : Subgroup G} (hLS : L ≤ stabTil V₀ V)
    (h2 : barSub V₀ V hV (pCoreOf 2 L) = ⊥) (hL1 : barSub V₀ V hV L ≠ ⊥)
    (hsimple : IsSimpleGroup (Bar2 L)) :
    Nonempty (Bar2 L ≃* ↥(barSub V₀ V hV L)) := by
  let φ := barSubBar2Hom hV hLS h2
  have hφ : Function.Surjective φ := barSubBar2Hom_surjective hV hLS h2
  have hker : φ.ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top φ.ker with h | h
    · exact h
    · refine absurd ?_ hL1
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨y, hy⟩ := hφ ⟨x, hx⟩
      have hy1 : φ y = 1 := (MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top y)
      have hval : ((φ y : ↥(barSub V₀ V hV L)) : MulAut (Vtil V₀ V hV)) = x :=
        congrArg Subtype.val hy
      rw [hy1] at hval
      simpa using hval.symm
  exact ⟨MulEquiv.ofBijective φ ⟨(MonoidHom.ker_eq_bot_iff φ).1 hker, hφ⟩⟩

theorem barSubBar2Equiv_of_isSimpleGroup {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥)
    (hsimple : IsSimpleGroup (Bar2 L)) :
    Nonempty (Bar2 L ≃* ↥(barSub V₀ V hV.isElemAbelian L)) :=
  nonempty_bar2_mulEquiv_barSub_of_isSimpleGroup hV.isElemAbelian
    (hL.1.le.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀))
    (TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV.isElemAbelian hL.1
      (barSub_pCoreOf_eq_bot_of_hyp125 hV)) hL1 hsimple

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
