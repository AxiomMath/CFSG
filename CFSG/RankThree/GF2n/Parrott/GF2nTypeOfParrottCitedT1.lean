module

public import CFSG.RankThree.GF2n.Tim81.GF2nTypeNoSqE1Parrott
public import CFSG.RankThree.GF2n.Parrott.ParrottFi22CitedS
public import CFSG.RankThree.GF2n.Parrott.Section2Theorem1EqualityBranchHolds

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

theorem gf2nType_of_noSqE1_parrott_h5_janko_gh (h2 : Tim79a.OddTranspNoSqE1Dich)
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
    GF2nTypeStatement :=
  Tim81.gf2nType_of_noSqE1_parrott h2 (parrottFi22Statement_of_theorem1_theorem5_janko_gh
      parrott_theorem1_equalityBranch_holds hJ14 h5)

end CFSG.RankThree.GF2n.Parrott
