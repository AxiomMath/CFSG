module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubComponent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_pCoreOf_of_actTil_eq_one {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    {X : Subgroup G} (hXsub : CFSG.Open.IsSubnormal X D.M)
    (hsimple : IsSimpleGroup (Bar2 X))
    (hX1 : barSub V₀ V hV.isElemAbelian X ≠ ⊥) {x : G} (hxX : x ∈ X)
    (hxs : x ∈ stabTil V₀ V)
    (hact : actTil V₀ V hV.isElemAbelian ⟨x, hxs⟩ = 1) :
    x ∈ pCoreOf 2 X := by
  have hLS : X ≤ stabTil V₀ V := hXsub.le.trans
    (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀)
  have h2 : barSub V₀ V hV.isElemAbelian (pCoreOf 2 X) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV.isElemAbelian hXsub
      (barSub_pCoreOf_eq_bot_of_hyp125 hV)
  let φ0 : ↥X →* ↥(barSub V₀ V hV.isElemAbelian X) :=
    ((actTil V₀ V hV.isElemAbelian).comp (Subgroup.inclusion hLS)).codRestrict
      (barSub V₀ V hV.isElemAbelian X)
      (fun y => actTil_mem_barSub V₀ V hV.isElemAbelian y.2 (hLS y.2))
  have hker0 : CFSG.pCore 2 ↥X ≤ φ0.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    have hyP : (y : G) ∈ pCoreOf 2 X := ⟨y, hy, rfl⟩
    have hmem := actTil_mem_barSub V₀ V hV.isElemAbelian hyP (hLS y.2)
    rw [h2, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  let ψ : Bar2 X →* ↥(barSub V₀ V hV.isElemAbelian X) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥X) φ0 hker0
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨a, haX, hay⟩ := (mem_barSub V₀ V hV.isElemAbelian X y).1 hy
    refine ⟨QuotientGroup.mk ⟨a, haX⟩, ?_⟩
    apply Subtype.ext
    change actTil V₀ V hV.isElemAbelian a = y
    exact hay
  have hψker : ψ.ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top ψ.ker with hbot | htop
    · exact hbot
    · exfalso
      haveI : Nontrivial ↥(barSub V₀ V hV.isElemAbelian X) :=
        (Subgroup.nontrivial_iff_ne_bot _).2 hX1
      obtain ⟨y, hy1⟩ := exists_ne (1 : ↥(barSub V₀ V hV.isElemAbelian X))
      obtain ⟨a, ha⟩ := hψ y
      have hmem : a ∈ ψ.ker := by rw [htop]; exact Subgroup.mem_top a
      rw [MonoidHom.mem_ker] at hmem
      exact hy1 (ha.symm.trans hmem)
  have hxbar : (QuotientGroup.mk ⟨x, hxX⟩ : Bar2 X) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    have hval : ψ (QuotientGroup.mk ⟨x, hxX⟩) =
        (⟨actTil V₀ V hV.isElemAbelian ⟨x, hLS hxX⟩,
          actTil_mem_barSub V₀ V hV.isElemAbelian hxX (hLS hxX)⟩ :
          ↥(barSub V₀ V hV.isElemAbelian X)) := rfl
    rw [hval]
    refine Subtype.ext ?_
    have h1 : actTil V₀ V hV.isElemAbelian ⟨x, hLS hxX⟩ = 1 := by
      rwa [show (⟨x, hLS hxX⟩ : stabTil V₀ V) = ⟨x, hxs⟩ from rfl]
    simpa using h1
  rw [hψker, Subgroup.mem_bot] at hxbar
  exact Subgroup.mem_map.2 ⟨⟨x, hxX⟩, (QuotientGroup.eq_one_iff _).1 hxbar, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
