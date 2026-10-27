module

public import CFSG.RankThree.PartTwo.Sec8.Item87Res2Proof88

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo


@[expose] def KF88LinkOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G), Sec8Pair G A c L a b X 1 →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, (x = c ∨ x = b) →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      ∀ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x →
        IsQuasisimple (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
          aschbacherSolvableCore 3
            (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) →
        (∃ m : ℕ, 1 ≤ m ∧
          IsType418 (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
            aschbacherSolvableCore 3
              (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) m) →
        KFacts.InducesStdKind
          (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) x .field →
        ¬ ⁅inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)),
            inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G))⁆ ≤
          inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({d} : Set G))

theorem kF88StepOne_of (hD : KF88StepD) (hL : KF88LinkOne) : KF88StepOne := by
  intro G _ _ A c L a b X h Y hY hIJ x hx hxY
  obtain ⟨d, hdS, hdx, hUq, htypeU, hUx⟩ := hD G A c L a b X 1 h Y hY hIJ x hx hxY
  exact ⟨d, hdS, hdx, hUq, htypeU, hUx,
    hL G A c L a b X h Y hY hIJ x hx hxY d hdS hdx hUq htypeU hUx⟩

theorem kF88Step_of_link (hD : KF88StepD) (hL : KF88LinkOne) (hF : KF84Field) : KF88Step :=
  kF88Step_of hD (kF88StepOne_of hD hL) hF

end CFSG.RankThree.PartTwo.Sec8
