module

public import CFSG.RankThree.GF2n.Parrott.ParrottFi22CitedA1
public import CFSG.RankThree.GF2n.Parrott.ParrottHL345HypA

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

section Certified


theorem parrottFi22Statement_of_theorem1_theorem5_cited
    (hThm1 : ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      ParrottEqualityBranch (z := z) (D := D) h → H z ⊔ pPrimeCore 2 G = ⊤)
    (hJ14 : ∀ (X : Type) [Group X], CFSG.Blueprint.LieModel X .PSp 2 3 1 → ∀ x : X,
      orderOf x = 2 →
      (∃ S : Sylow 2 X, x ∈ (S : Subgroup X) ∧ ∀ s ∈ (S : Subgroup X), x * s = s * x) →
      ∀ (G : Type) [Group G] [Finite G], (∀ N : Subgroup G, N.index ≠ 2) →
        ∀ j : G, orderOf j = 2 →
          Nonempty (Subgroup.centralizer ({j} : Set G) ≃* Subgroup.centralizer ({x} : Set X)) →
            CFSG.Blueprint.LieModel G .PSp 2 3 1)
    (h5 : ∀ (G : Type) [Group G] [Finite G] (z : G), Tim79a.ParrottHyp z →
      centerIn (inSubgroup (pCore 2) (Subgroup.centralizer ({z} : Set G))) ≠
        centerIn (Subgroup.centralizer ({z} : Set G)) →
      Subgroup.centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤ →
        CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22) :
    Tim79a.ParrottFi22Statement :=
  parrottFi22Statement_of_theorem1_cited hThm1 hJ14
    (fun _ _ _ _ h hne =>
      parrott_hL345_hypA hThm1 h hne
        (parrott_theorem3_export (parrott_theoremA_one_cited hJ14) hThm1 _ _ h hne))
    h5

end Certified

end CFSG.RankThree.GF2n.Parrott
