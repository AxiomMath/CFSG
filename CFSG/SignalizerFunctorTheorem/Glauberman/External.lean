module

public import CFSG.SignalizerFunctorTheorem.MinimalAction.Main
public import CFSG.SignalizerFunctorTheorem.Quadratic.Main

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.Glauberman

variable {G : Type*} [Group G] [Finite G]

theorem thompson_generation {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    {U A T : Subgroup G} (hU : Group.IsSolvable U) (hA : IsElemAbelian r A)
    (hcop : Nat.Coprime r (Nat.card U)) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hT : IsSylowOf q T U) (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    primeCoreIn ({q}ᶜ : Set ℕ) U ⊔ (U ⊓ Subgroup.normalizer (thompsonJ q T : Set G)) ⊔
      (U ⊓ Subgroup.centralizer (omegaCenter q T : Set G)) ⊔
      (U ⊓ Subgroup.centralizer (A : Set G)) = U :=
  Quadratic.thompson_generation hq hr hU hA hcop hAU hT hAT

theorem not_thompsonFactorizable_two {r : ℕ} (hr : r.Prime)
    {U A T : Subgroup G} (hU : Group.IsSolvable U) (hA : IsElemAbelian r A)
    (hcop : Nat.Coprime r (Nat.card U)) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hT : IsSylowOf 2 T U) (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hnot : ¬ ThompsonFactorizable 2 U T) :
    ∃ W : Subgroup G, W ≤ U ⊓ Subgroup.centralizer (A : Set G) ∧ IsElemAbelian 2 W ∧
      Nat.card W = 4 ∧ ∃ d ∈ U ⊓ Subgroup.centralizer (A : Set G),
        IsPGroup 3 (Subgroup.zpowers d) ∧ d ∈ Subgroup.normalizer (W : Set G) ∧
        ∀ w ∈ W, d * w * d⁻¹ = w → w = 1 :=
  Quadratic.not_thompsonFactorizable_two hr hU hA hcop hAU hT hAT hnot

theorem not_thompsonFactorizable_three {r : ℕ} (hr : r.Prime)
    {U A T : Subgroup G} (hU : Group.IsSolvable U) (hA : IsElemAbelian r A)
    (hcop : Nat.Coprime r (Nat.card U)) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hT : IsSylowOf 3 T U) (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hnot : ¬ ThompsonFactorizable 3 U T) :
    (∃ W : Subgroup G, W ≤ U ⊓ Subgroup.centralizer (A : Set G) ∧ IsElemAbelian 3 W ∧
      Nat.card W = 9) ∧
    ∃ D : Subgroup G, D ≤ U ⊓ Subgroup.centralizer (A : Set G) ∧
      ∃ φ : D →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), Function.Surjective φ :=
  Quadratic.not_thompsonFactorizable_three hr hU hA hcop hAU hT hAT hnot

theorem thompson_semidirect_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P Q X : Subgroup G} (hP : IsPGroup p P) (hQ : Nat.Coprime p (Nat.card Q))
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (hX : IsPGroup p X)
    (hPX : P ≤ Subgroup.normalizer (X : Set G)) (hQX : Q ≤ Subgroup.normalizer (X : Set G))
    (hC : X ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (Q : Set G)) :
    X ≤ Subgroup.centralizer (Q : Set G) :=
  MinimalAction.thompson_semidirect_centralizer hp hp2 hP hQ hPQ hX hPX hQX hC

theorem exists_elemAbelian_eight [Group.IsSolvable G]
    (hcore : CFSG.SignalizerFunctor.Helpers.primeSetCore (GroupType := G) ({2}ᶜ : Set ℕ) = ⊥)
    (hsix : ∃ x : G, orderOf x = 6) {d : G} (hd : IsPGroup 3 (Subgroup.zpowers d)) (hd1 : d ≠ 1)
    {W : Subgroup G} (hW : W ≠ ⊥) (hWe : IsElemAbelian 2 W)
    (hdW : d ∈ Subgroup.normalizer (W : Set G)) (hfree : ∀ w ∈ W, d * w * d⁻¹ = w → w = 1) :
    ∃ E : Subgroup G, IsElemAbelian 2 E ∧ Nat.card E = 8 :=
  MinimalAction.exists_elemAbelian_eight hcore hsix hd hd1 hW hWe hdW hfree

end CFSG.SignalizerFunctorTheorem.Glauberman
