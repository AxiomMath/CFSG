module

public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace CfgLemmaQ

variable {M V₀ V C : Subgroup G} {h : G}

theorem isElemAbelian_map_subgroupOf (q : CfgLemmaQ M V₀ V h C) {K : Type} [Group K]
    (ψ : ↥(V₀ ⊔ conjSubgroup V₀ h) →* K) :
    IsElemAbelian 2 ((V₀.subgroupOf (V₀ ⊔ conjSubgroup V₀ h)).map ψ) :=
  CFSG.RankThree.GF2n.Tim77.isElemAbelian_map'
    (CFSG.RankThree.GF2n.Tim77.isElemAbelian_subgroupOf q.hyp.elemAbelian₀ _) ψ

theorem card_map_subgroupOf_eq_relIndex (q : CfgLemmaQ M V₀ V h C) {K : Type} [Group K]
    (ψ : ↥(V₀ ⊔ conjSubgroup V₀ h) →* K)
    (hψk : ψ.ker = (nVSub V₀ h ⊔ bSub V₀ h).subgroupOf (V₀ ⊔ conjSubgroup V₀ h)) :
    Nat.card ((V₀.subgroupOf (V₀ ⊔ conjSubgroup V₀ h)).map ψ) = (nVSub V₀ h).relIndex V₀ := by
  let X : Subgroup G := V₀ ⊔ conjSubgroup V₀ h
  let N : Subgroup ↥X := (nVSub V₀ h ⊔ bSub V₀ h).subgroupOf X
  haveI : N.Normal := q.prop24Setup.normal_subgroupOf
  have hrel : (nVSub V₀ h).relIndex V₀ =
      Nat.card ((V₀.subgroupOf X).map (QuotientGroup.mk' N)) :=
    q.prop24Setup.relIndex_eq_card_image
  rw [hrel]
  have hle : N ≤ ψ.ker := le_of_eq hψk.symm
  let φ : (↥X ⧸ N) →* K := QuotientGroup.lift N ψ hle
  have hφ : Function.Injective φ := (QuotientGroup.injective_lift_iff N ψ hle).mpr hψk.symm
  have hcomp : ψ = φ.comp (QuotientGroup.mk' N) :=
    (QuotientGroup.lift_comp_mk' N ψ hle).symm
  have hmain : Nat.card ((V₀.subgroupOf X).map ψ) =
      Nat.card ((V₀.subgroupOf X).map (QuotientGroup.mk' N)) := by
    rw [hcomp, ← Subgroup.map_map, Subgroup.card_map_of_injective hφ]
  exact hmain

end CfgLemmaQ

end CFSG.LocalAnalysis.WeakClosure81

end
