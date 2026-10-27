module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure GGB2derModelProp {G : Type} [Group G] (B L : Subgroup G)
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) {K : Type} [Field K] [Finite K] {r : ℕ} [NeZero r]
    (ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup K r))
    (β : ↥B →* LargeEvenProj (LargeEvenSpGroup K r)) : Prop where
  surj : Function.Surjective ψ
  ker_eq : ψ.ker = Subgroup.center ↥L
  conj : ∀ (b : ↥B) (l : ↥L),
    ψ ((L.normalizerMonoidHom (Subgroup.inclusion hBL b)) l) = β b * ψ l * (β b)⁻¹

end CFSG.StandardType
