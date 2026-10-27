module

public import CFSG.LocalAnalysis.StandardType.GGFinModelInput

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.HardMathSupport.Timmesfeld.LangTorus

section Iso

private lemma intCast_eq_one_of_sign {k : Type} [Ring k] [CharP k 2] {s : ℤ}
    (hs : s = 1 ∨ s = -1) : (s : k) = 1 := by
  rcases hs with rfl | rfl
  · exact Int.cast_one
  · rw [Int.cast_neg, Int.cast_one, CharTwo.neg_eq]

private lemma pinnedFamilySign_cast_eq_one {τ : Tag}
    (F : RootOperatorFamily τ) {k : Type} [Ring k] [CharP k 2]
    (α : Fin τ.rank → ℤ) : (F.pinnedFamilySign α : k) = 1 :=
  intCast_eq_one_of_sign (F.pinnedFamilySign_eq α)

private lemma relSignOr_cast_eq_one
    {τ : Tag}
    (F : RootOperatorFamily τ) {D : AdjData τ} (hD : D.Valid) {k : Type} [Ring k] [CharP k 2]
    (α : Fin τ.rank → ℤ) : (relSignOr F hD α : k) = 1 := by
  by_cases h : IsRoot τ α
  · rw [relSignOr_of_isRoot h]
    exact intCast_eq_one_of_sign (RootOperatorFamily'.relSign_eq F hD ⟨α, h⟩)
  · classical
    rw [relSignOr, dif_neg h, Int.cast_one]

theorem ggE6_isogeny_xm_pinned
    (k : Type) [Field k] [Finite k] [CharP k 2]
    {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (c : k) :
    ((e6Isogeny k (e6Data_valid.xm k α c) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) =
      pinnedX .E6 k α c := by
  rw [e6Isogeny_xm k hα c, yPar, xPar_of_isRoot hα, RootOperatorFamily.coe_eltElement,
    (rootOperatorFamily .E6).pinnedX_eq_eltUnit k hα]
  congr 1
  rw [relSignOr_cast_eq_one (rootOperatorFamily .E6) e6AdjData_valid α,
    pinnedFamilySign_cast_eq_one (rootOperatorFamily .E6) α]

theorem ggE7_isogeny_xm_pinned
    (k : Type) [Field k] [Finite k] [CharP k 2]
    {α : Fin (Tag.rank .E7) → ℤ} (hα : IsRoot .E7 α) (c : k) :
    ((e7Isogeny k (e7Data_valid.xm k α c) : ↥(adjointGroup .E7 k)) : ModGL .E7 k) =
      pinnedX .E7 k α c := by
  rw [e7Isogeny_xm k α c, xPar_of_isRoot hα, RootOperatorFamily.coe_eltElement,
    (rootOperatorFamily .E7).pinnedX_eq_eltUnit k hα]
  congr 1
  rw [intCast_eq_one_of_sign (e7Eps_eq_one_or α),
    pinnedFamilySign_cast_eq_one (rootOperatorFamily .E7) α]

end Iso

end CFSG.StandardType.GGFinModel
