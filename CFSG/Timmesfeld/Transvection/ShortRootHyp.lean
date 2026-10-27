module

public import CFSG.Timmesfeld.Transvection.ShortRootReg

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

namespace PairFrame

variable {A E D E' : Subgroup G}

theorem shortRootFieldHyp_of_meetsLines [Finite G] (P : PairFrame Δ A E D E')
    (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ) (hlines : MeetsLines Δ)
    (hq : 4 ≤ Nat.card A) : ShortRootFieldHyp Δ A E D E' :=
  P.shortRootFieldHyp hΔ (hΔ.noIsolated hpts ⟨A, P.memA, D, P.memD, P.ne_AD, P.commuting_AD⟩)
    hpts hq hlines

theorem shortRootFieldHyp_swap [Finite G] (P : PairFrame Δ A E D E')
    (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ) (hlines : MeetsLines Δ)
    (hq : 4 ≤ Nat.card A) : ShortRootFieldHyp Δ D E' A E :=
  P.swap.shortRootFieldHyp_of_meetsLines hΔ hpts hlines (by
    rwa [hΔ.root.card_eq P.memD P.memA])

theorem exists_conjSub_eq_of_meetsLines [Finite G] (P : PairFrame Δ A E D E')
    (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ) (hlines : MeetsLines Δ)
    (hq : 4 ≤ Nat.card A) :
    ∀ C ∈ lineOf Δ A D, C ≠ D → ∃ x ∈ shortRootGroup Δ E A D E', conjSub A x = C :=
  fun _ hC hCD => P.exists_conjSub_eq hΔ
    (hΔ.noIsolated hpts ⟨A, P.memA, D, P.memD, P.ne_AD, P.commuting_AD⟩) hpts hlines hq hC hCD

theorem exists_conjSub_eq_swap [Finite G] (P : PairFrame Δ A E D E')
    (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ) (hlines : MeetsLines Δ)
    (hq : 4 ≤ Nat.card A) :
    ∀ C ∈ lineOf Δ D A, C ≠ A → ∃ y ∈ shortRootGroup Δ E' D A E, conjSub D y = C :=
  P.swap.exists_conjSub_eq_of_meetsLines hΔ hpts hlines (by
    rwa [hΔ.root.card_eq P.memD P.memA])

theorem exists_ne_one_of_thickLines [Finite G] (P : PairFrame Δ A E D E')
    (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ) (hlines : MeetsLines Δ)
    (hq : 4 ≤ Nat.card A) (hthick : ThickLines Δ) :
    ∃ x ∈ shortRootGroup Δ E A D E', x ≠ 1 := by
  obtain ⟨C, hC, hCA, hCD, hCl⟩ := hthick A P.memA D P.memD P.ne_AD P.commuting_AD
  obtain ⟨x, hx, hxC⟩ := P.exists_conjSub_eq_of_meetsLines hΔ hpts hlines hq C ⟨hC, hCl⟩ hCD
  refine ⟨x, hx, ?_⟩
  rintro rfl
  rw [conjSub_one] at hxC
  exact hCA hxC.symm

end PairFrame

end CFSG.Timmesfeld.Transvection
