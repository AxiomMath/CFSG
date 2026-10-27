module

public import CFSG.LocalAnalysis.StandardType.GGQ2ActualFrame
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneConj
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType.GGQ2Frame.SpPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin Matrix
open CFSG.Open (StatedSp IsElemAbelian)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {G : Type} [Group G] [Finite G] {H E : Subgroup G} {m : ℕ}
  {K : Type} [Field K] [Finite K] [CharP K 2] [NeZero m]

@[expose] def piMat (θ : ↥H ⧸ Subgroup.center ↥H ≃* LargeEvenProj (LargeEvenSpGroup K m)) :
    ↥H →* ↥(StatedSp m K) :=
  (TableBSymp.spProjEquivSp (K := K) (m := m)).toMonoidHom.comp (ggQuotHom θ)

structure SpFrame (H E : Subgroup G) (hEN : E ≤ Subgroup.normalizer (H : Set G)) (K : Type) [Field K]
    (m : ℕ) (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) : Type where
  π : ↥H →* ↥(StatedSp m K)
  surj : Function.Surjective π
  ker_le : π.ker ≤ Subgroup.center ↥H
  τ : (Fin m → Multiplicative (ZMod 3)) ≃* ↥E
  intertwine : ∀ (u : Fin m → Multiplicative (ZMod 3)) (h : ↥H),
    π (H.normalizerMonoidHom ⟨((τ u : ↥E) : G), hEN (τ u).2⟩ h) =
      spPlaneTorus m ζ u * π h * (spPlaneTorus m ζ u)⁻¹

end

end CFSG.StandardType.GGQ2Frame.SpPlacement
