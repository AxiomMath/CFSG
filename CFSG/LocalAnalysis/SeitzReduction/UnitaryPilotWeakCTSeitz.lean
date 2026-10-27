module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotNeighbourParamRoot

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open scoped MatrixGroups

section SwapRow

variable {G : Type} [Group G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ}

@[expose] def UnitaryRootTorusSwapRow (e : L ≃* unitaryPSU h n) (t : G) {a b : Fin n}
    (hab : a ≠ b) : Prop :=
  ∃ htX : t ∈ centralizer (modelToG e (unitaryRootTorus h hab) : Set G),
    ∃ Kc : Subgroup (centralizer (modelToG e (unitaryRootTorus h hab) : Set G) ⧸
        oddCore (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))),
      IsComponent Kc ∧
      ((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) :
            Set G)))) ≤
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (unitaryRootTorus h hab) : Set G))) ⟨t, htX⟩)).toMonoidHom ∧
      Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
        (modelToG e (unitaryRootTorus h hab) : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc ∧
      ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
        (modelToG e (unitaryRootTorus h hab) : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥ ∧
      center Kc = ⊥ ∧
      Nonempty (Kc ≃* ((modelToG e (blockSU h ({a, b}ᶜ : Finset (Fin n)))).subgroupOf
        (centralizer (modelToG e (unitaryRootTorus h hab) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (unitaryRootTorus h hab) :
            Set G)))))

end SwapRow

section Seitz

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  (h : UnitaryFieldData 2 f K)

theorem nonempty_graphFieldNeighbourParam_or_swapRow_unitaryRootTorus {n : ℕ}
    (hset : SeitzSetting G L) (hcat : SUmCatalogueClausesAt (n - 2)) (e : L ≃* unitaryPSU h n)
    (hn : 6 ≤ n) (hnf : (n, f) ≠ (6, 1)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b) :
    Nonempty (GraphFieldNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
        ({a, b}ᶜ : Finset (Fin n))) ∨
      UnitaryRootTorusSwapRow e t hab := by
  have htX : t ∈ centralizer (modelToG e (unitaryRootTorus h hab) : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 (modelToG_le e _)) htC
  rcases nonempty_graphFieldNeighbourParam_or_swap_unitaryRootTorus h hset hcat e hn hnf htC ht
    hab htX with hP | hswap
  · exact Or.inl hP
  · exact Or.inr ⟨htX, hswap⟩

end Seitz

end CFSG.SeitzReduction.UnitaryPilot
