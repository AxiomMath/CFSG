module

public import CFSG.RankThree.PartOne.KE.NativeCyclicAbstract
public import CFSG.RankThree.PartOne.KE.NativeCyclicLocalCore
public import CFSG.RankThree.PartOne.KE.OrdinaryEOuter

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.LocalRank
open CFSG.LieType.Chevalley

theorem native_plane_of_cyclic_centralizers (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hcyc : ∀ Q : Subgroup (adjointGroup τ K), IsPGroup p Q → IsCyclic Q)
    (hcent : ∀ x : adjointGroup τ K, orderOf x = p → IsCyclic (Subgroup.centralizer {x})) :
    ∀ B : Subgroup (MulAut (adjointGroup τ K)),
      (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range ≤ B →
      ∀ A : Subgroup (MulAut (adjointGroup τ K)), A ≤ B → IsElementaryAbelian p A →
        Nat.card A = p ^ 2 →
        ¬ A ≤ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range ∧
        autThetaT p B A = ⊥ ∧
        ∀ t ∈ A, t ≠ 1 → ¬ 2 ∣ Nat.card (autPlaneProduct p B A t) ∧
          (t ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range →
            inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {t}) = ⊥ ∧
              autPlaneProduct p B A t = ⊥) := by
  exact native_plane_of_cyclic_centralizers_abstract hp hp3 center_adjointGroup_eq_bot hcyc hcent
    (ordinary_E_outer_derived_subgroup_odd τ hτ K).1 (localCoreTrivialOn_noninner_E τ hτ K hp hp3)

theorem planeLocalCoreOdd_of_cyclic_centralizers (τ : Tag)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hcyc : ∀ Q : Subgroup (adjointGroup τ K), IsPGroup p Q → IsCyclic Q)
    (hcent : ∀ x : adjointGroup τ K, orderOf x = p → IsCyclic (Subgroup.centralizer {x})) :
    PlaneLocalCoreOdd p (adjointGroup τ K) := fun B hB A hAB hA hcard t htA ht1 =>
  ((native_plane_of_cyclic_centralizers τ hτ K hp hp3 hcyc hcent B hB A hAB hA hcard).2.2 t htA
    ht1).1

end CFSG.RankThree.PartOne.KE
