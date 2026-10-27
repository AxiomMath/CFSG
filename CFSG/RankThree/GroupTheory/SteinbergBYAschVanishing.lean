module

public import CFSG.RankThree.GroupTheory.SteinbergCETwoCoreAlpha
public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank

@[expose] def AschVanishing (G : Type*) [Group G] (p : ℕ) : Prop :=
  ∀ A : Subgroup G, IsElementaryAbelian p A → Nat.card A = p ^ 3 →
    ∀ B : Subgroup G, B ≤ A → Nat.card B = p ^ 2 → ∀ c ∈ A, c ≠ 1 →
      twoCoreAlpha B = ⊥ ∧
        (∃ T : Sylow 2
            (inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({c} : Set G))),
          ⁅(T : Subgroup _).map
              (inSubgroup (aschbacherSolvableCore p)
                (Subgroup.centralizer ({c} : Set G))).subtype, A⁆ = ⊥) ∧
        Odd (Nat.card (thetaT p B))

end CFSG.RankThree.GroupTheory.SteinbergBY
