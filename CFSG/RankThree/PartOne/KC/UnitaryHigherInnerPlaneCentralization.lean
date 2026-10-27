module

public import CFSG.RankThree.PartOne.KC.UnitaryInnerPlaneCentralizationCore

public section

namespace CFSG.RankThree.PartOne

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCPrimary
open scoped commutatorElement

theorem higher_unitary_inner_plane_all_parameter_local_core_centralization
    {ℓ f n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (hn3 : 3 ≤ n) (hnp : n < p)
    (hp : p.Prime) (hpℓ : p ≠ ℓ) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
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
    intro c _ hcn hcp
    have hcop : Nat.Coprime n p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt (by omega) hnp)).symm
    have : c ^ Nat.gcd n p = 1 := pow_gcd_eq_one.mpr ⟨hcn, hcp⟩
    rwa [hcop, pow_one] at this
  exact unitary_inner_plane_local_core_centralization h hn3 hne hp (by have := hp.two_le; omega)
    hpℓ hZp B hB A Ahat hAhat a haA x hxA hxa hxp

end CFSG.RankThree.PartOne
