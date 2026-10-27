module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Adapters.WholeGroupLayer
public import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem fstar_eq_of_isSimpleGroup_of_centralizer_eq_bot {H X : Subgroup G} (hXH : X ≤ H)
    (hX : (X.subgroupOf H).Normal) (hsimple : IsSimpleGroup ↥X)
    (hnab : ¬ ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hC : H ⊓ Subgroup.centralizer (X : Set G) = ⊥) : Fstar H = X := by
  let N : Subgroup ↥H := X.subgroupOf H
  haveI : N.Normal := hX
  haveI : IsSimpleGroup ↥X := hsimple
  haveI : IsSimpleGroup ↥N := (Subgroup.subgroupOfEquivOfLe hXH).isSimpleGroup
  have hnc : ∃ x y : ↥N, x * y ≠ y * x := by
    by_contra h
    apply hnab
    intro x hx y hy
    let xN : ↥N := ⟨⟨x, hXH hx⟩, by rw [Subgroup.mem_subgroupOf]; exact hx⟩
    let yN : ↥N := ⟨⟨y, hXH hy⟩, by rw [Subgroup.mem_subgroupOf]; exact hy⟩
    by_contra hxy
    refine h ⟨xN, yN, ?_⟩
    intro hcomm
    apply hxy
    have hval := congrArg (fun z : ↥N => (z : G)) hcomm
    simpa [xN, yN] using hval
  have hC' : Subgroup.centralizer (N : Set ↥H) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro γ hγ
    have hfun : ∀ h ∈ (N : Set ↥H), h * γ = γ * h := hγ
    have hγ' : (γ : G) ∈ H ⊓ Subgroup.centralizer (X : Set G) := by
      refine ⟨γ.2, ?_⟩
      intro x hx
      have hxN : (⟨x, hXH hx⟩ : ↥H) ∈ N := by
        rw [Subgroup.mem_subgroupOf]; exact hx
      have hcomm := hfun (⟨x, hXH hx⟩ : ↥H) hxN
      have hval := congrArg (fun z : ↥H => (z : G)) hcomm
      simpa using hval
    have hmem : (γ : G) ∈ (⊥ : Subgroup G) := by
      rw [← hC]
      exact hγ'
    have hγbot : (γ : G) = 1 := Subgroup.mem_bot.mp hmem
    exact Subtype.ext (by simpa using hγbot)
  have hgf : CFSG.generalizedFitting ↥H = N :=
    CFSG.Adapters.generalizedFitting_eq_of_normal_simple_of_centralizer_eq_bot N hnc hC'
  unfold CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar
  rw [CFSG.Adapters.genFittingFStar_eq_foundations, hgf]
  exact Subgroup.map_subgroupOf_eq_of_le hXH

end CFSG.LocalAnalysis.WeakClosure81
