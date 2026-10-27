module

public import CFSG.RankThree.PartOne.KC.UnitaryInnerPlaneCentralizationCore

public section

namespace CFSG.RankThree.PartOne

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCPrimary
open scoped commutatorElement

theorem unitary_nonsplit_all_dimension_inner_plane_local_core_centralization
    {ℓ f n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp3 : 3 < p)
    (hpℓ : p ≠ ℓ) (hpq : ¬p ∣ ℓ ^ f + 1) (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (B : Subgroup (MulAut (primeFormP h (idGram K n))))
    (hB : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ B)
    (A : Subgroup (MulAut (primeFormP h (idGram K n))))
    (Ahat : Subgroup (gramSU h (idGram K n))) (hAhat : IsPlaneLift h n p A Ahat)
    (a : MulAut (primeFormP h (idGram K n))) (haA : a ∈ A)
    (x : gramSU h (idGram K n)) (hxA : x ∈ Ahat) (hxa : innerLift h n x = a)
    (hxp : orderOf x = p) :
    (∀ i : GoodBlockIdx h x,
      (idSpecialBlock h x (i.1 : K[X]) ≤
          (gramSU h (idGram K n)).subgroupOf (primeFormUnitary h (idGram K n)) ∧
        Group.IsPerfect (idSpecialBlock h x (i.1 : K[X])) ∧
        ∀ y ∈ Subgroup.centralizer ({liftUnitary x} : Set (primeFormUnitary h (idGram K n))) ⊓
            (gramSU h (idGram K n)).subgroupOf (primeFormUnitary h (idGram K n)),
          ∀ g ∈ idSpecialBlock h x (i.1 : K[X]), y * g * y⁻¹ ∈ idSpecialBlock h x (i.1 : K[X])) ∧
      (idBlockImage h x (i.1 : K[X]) ≤ (MulAut.conj : primeFormP h (idGram K n) →*
            MulAut (primeFormP h (idGram K n))).range ∧
        CFSG.IsComponent ((idBlockImage h x (i.1 : K[X])).subgroupOf
          (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (primeFormP h (idGram K n)))))) ∧
        ((idBlockImage h x (i.1 : K[X])).subgroupOf (idInnCentralizer h n a)).Normal ∧
        ∀ s ∈ idLocalCore h n p B a, ∀ j ∈ idBlockImage h x (i.1 : K[X]), s * j = j * s)) ∧
    ((idGoodProduct h x).subgroupOf (idInnCentralizer h n a)).Normal ∧
    ⁅idLocalCore h n p B a, A⁆ = ⊥ ∧
    (∀ Y ∈ Subgroup.centralizer ({liftUnitary x} : Set (primeFormUnitary h (idGram K n))) ⊓
        (gramSU h (idGram K n)).subgroupOf (primeFormUnitary h (idGram K n)),
      (primeFormConjHom h (idGram K n) Y ∈
          Subgroup.centralizer
            ((idGoodProduct h x : Subgroup (MulAut (primeFormP h (idGram K n)))) :
              Set (MulAut (primeFormP h (idGram K n)))) ↔
        ∀ i : GoodBlockIdx h x, ∃ c : AdjoinRoot (i.1 : K[X]),
          ∀ v : primaryComponent ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K
              (Fin n → K)) : Module.End K (Fin n → K)) (i.1 : K[X]),
            ((toLinU h n Y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
              Module.End K (Fin n → K)) (v : Fin n → K) =
              ((c • v : primaryComponent ((toLinU h n (liftUnitary x) :
                LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))
                  (i.1 : K[X])) : Fin n → K))) ∧
    (∀ y ∈ idInnCentralizer h n a, (∀ j ∈ idGoodProduct h x, y * j = j * y) →
      ∀ b ∈ A, b * y = y * b) ∧
    (∀ i : primaryFactors ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K
        (Fin n → K)) : Module.End K (Fin n → K)),
      dualPoly h.bar (i : K[X]) = i →
      (primaryMultiplicity ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K
          (Fin n → K)) : Module.End K (Fin n → K)) (i : K[X]) = 2 →
        ℓ ^ (f * (i : K[X]).natDegree) = 2 →
        Nat.card (supportedUnitary (idForm h n) (toLinU h n (liftUnitary x)) {(i : K[X])}) = 18) ∧
      (primaryMultiplicity ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K
          (Fin n → K)) : Module.End K (Fin n → K)) (i : K[X]) = 2 →
        ℓ ^ (f * (i : K[X]).natDegree) = 3 →
        Nat.card (supportedUnitary (idForm h n) (toLinU h n (liftUnitary x)) {(i : K[X])}) = 96) ∧
      (primaryMultiplicity ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K
          (Fin n → K)) : Module.End K (Fin n → K)) (i : K[X]) = 3 →
        ℓ ^ (f * (i : K[X]).natDegree) = 2 →
        Nat.card (supportedUnitary (idForm h n) (toLinU h n (liftUnitary x)) {(i : K[X])}) =
          648)) := by
  have hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1 := by
    intro c hc _ hcp
    have h1 : c ^ (ℓ ^ f + 1) = 1 := (pow_succ_eq_one_iff_norm h c).mpr hc
    have h2 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
    rcases (Nat.dvd_prime hp).mp h2 with h3 | h3
    · exact orderOf_eq_one_iff.mp h3
    · exact absurd (h3 ▸ orderOf_dvd_of_pow_eq_one h1) hpq
  exact unitary_inner_plane_local_core_centralization h hn hne hp hp3 hpℓ hZp B hB A Ahat hAhat a
    haA x hxA hxa hxp

end CFSG.RankThree.PartOne
