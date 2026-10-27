module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Lift

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.Glauberman

namespace CFSG.SignalizerFunctorTheorem.Quadratic

variable {G : Type*} [Group G] [Finite G]

theorem thompson_generation {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    {U A T : Subgroup G} (hU : Group.IsSolvable U) (hA : IsElemAbelian r A)
    (hcop : Nat.Coprime r (Nat.card U)) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hT : IsSylowOf q T U) (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    primeCoreIn ({q}ᶜ : Set ℕ) U ⊔ (U ⊓ Subgroup.normalizer (thompsonJ q T : Set G)) ⊔
      (U ⊓ Subgroup.centralizer (omegaCenter q T : Set G)) ⊔
      (U ⊓ Subgroup.centralizer (A : Set G)) = U :=
  lift_generation hq hr hU hA hcop hAU hT hAT

theorem not_thompsonFactorizable_two {r : ℕ} (hr : r.Prime)
    {U A T : Subgroup G} (hU : Group.IsSolvable U) (hA : IsElemAbelian r A)
    (hcop : Nat.Coprime r (Nat.card U)) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hT : IsSylowOf 2 T U) (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hnot : ¬ ThompsonFactorizable 2 U T) :
    ∃ W : Subgroup G, W ≤ U ⊓ Subgroup.centralizer (A : Set G) ∧ IsElemAbelian 2 W ∧
      Nat.card W = 4 ∧ ∃ d ∈ U ⊓ Subgroup.centralizer (A : Set G),
        IsPGroup 3 (Subgroup.zpowers d) ∧ d ∈ Subgroup.normalizer (W : Set G) ∧
        ∀ w ∈ W, d * w * d⁻¹ = w → w = 1 :=
  lift_two hr hU hA hcop hAU hT hAT hnot

theorem not_thompsonFactorizable_three {r : ℕ} (hr : r.Prime)
    {U A T : Subgroup G} (hU : Group.IsSolvable U) (hA : IsElemAbelian r A)
    (hcop : Nat.Coprime r (Nat.card U)) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hT : IsSylowOf 3 T U) (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hnot : ¬ ThompsonFactorizable 3 U T) :
    (∃ W : Subgroup G, W ≤ U ⊓ Subgroup.centralizer (A : Set G) ∧ IsElemAbelian 3 W ∧
      Nat.card W = 9) ∧
    ∃ D : Subgroup G, D ≤ U ⊓ Subgroup.centralizer (A : Set G) ∧
      ∃ φ : D →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), Function.Surjective φ :=
  lift_three hr hU hA hcop hAU hT hAT hnot

end CFSG.SignalizerFunctorTheorem.Quadratic
