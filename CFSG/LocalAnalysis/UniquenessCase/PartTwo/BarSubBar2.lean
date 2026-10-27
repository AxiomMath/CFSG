module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubComponent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

noncomputable def barSubBar2Hom {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {L : Subgroup G}
    (hLS : L ≤ stabTil V₀ V) (h2 : barSub V₀ V hV (pCoreOf 2 L) = ⊥) :
    Bar2 L →* ↥(barSub V₀ V hV L) := by
  classical
  let φ : ↥L →* ↥(barSub V₀ V hV L) :=
    ((actTil V₀ V hV).comp (Subgroup.inclusion hLS)).codRestrict
      (barSub V₀ V hV L) (fun x => actTil_mem_barSub V₀ V hV x.2 (hLS x.2))
  have hker : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxP : (x : G) ∈ pCoreOf 2 L := ⟨x, hx, rfl⟩
    have h1 : actTil V₀ V hV ⟨(x : G), hLS x.2⟩ ∈ barSub V₀ V hV (pCoreOf 2 L) :=
      actTil_mem_barSub V₀ V hV hxP (hLS x.2)
    rw [h2, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  exact QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hker

theorem barSubBar2Hom_surjective {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {L : Subgroup G}
    (hLS : L ≤ stabTil V₀ V) (h2 : barSub V₀ V hV (pCoreOf 2 L) = ⊥) :
    Function.Surjective (barSubBar2Hom hV hLS h2) := by
  classical
  intro y
  obtain ⟨a, haL, hay⟩ :=
    (mem_barSub V₀ V hV L (y : MulAut (Vtil V₀ V hV))).1 y.2
  refine ⟨QuotientGroup.mk ⟨a, haL⟩, ?_⟩
  apply Subtype.ext
  change actTil V₀ V hV a = (y : MulAut (Vtil V₀ V hV))
  rw [hay]

noncomputable def barSubBar2HomOfHyp125 {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    {L : Subgroup G} (hL : L ∈ calC D.M) : Bar2 L →* ↥(barSub V₀ V hV.isElemAbelian L) :=
  barSubBar2Hom hV.isElemAbelian
    (hL.1.le.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀))
    (TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV.isElemAbelian hL.1
      (barSub_pCoreOf_eq_bot_of_hyp125 hV))

theorem barSubBar2HomOfHyp125_surjective {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) {L : Subgroup G} (hL : L ∈ calC D.M) :
    Function.Surjective (barSubBar2HomOfHyp125 hV hL) :=
  barSubBar2Hom_surjective hV.isElemAbelian _ _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
