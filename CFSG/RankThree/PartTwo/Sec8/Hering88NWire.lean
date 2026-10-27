module

public import CFSG.RankThree.PartTwo.Sec8.Hering88FCovered
public import CFSG.RankThree.PartTwo.Sec8.Hering88NThm1

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def KF88Case1ClassBOneUnitary : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G), Sec8Pair G A c L a b X 1 →
    IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, x = c →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      ∀ (A₀ : Subgroup G) (d' : G) (m : ℕ), Odd m → Case83One Y x A₀ d' m →
      ∀ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x → d ∈ A → d ^ 3 = 1 →
        ∀ hdN : d ∈ Subgroup.normalizer (Y : Set G),
          KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)) →
          Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1 →
          (∃ E : Subgroup G, E ≤ A ∧ d ∈ E ∧ InvTwoBarNontrivial E Y) →
          Nonempty (imageModTheta Y
            (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃*
              projSL 2 (GaloisField 2 (3 * m)))

namespace Hering88N

theorem kF88Case1ClassBOne_of_unitary (h45 : Sec4.Item4_5) (h47 : Sec4.Inputs47ClassesD4)
    (hU : KF88Case1ClassBOneUnitary) : KF88Case1ClassBOne := by
  intro G _ _ A c L a b X h Y hY hIJ x hxc hxY A₀ d' m hodd hc1 d hdcl hdx hdA hd3 hdN hin hne hE
  by_cases hUn : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3
  · exact hU G A c L a b X h hUn Y hY hIJ x hxc hxY A₀ d' m hodd hc1 d hdcl hdx hdA hd3 hdN hin
      hne hE
  · subst hxc
    exact classBOne_of_not_unitary h45 h47 h hUn hY hIJ hxY hodd hc1 hdcl hdx hdA hd3 hdN hin hne

end Hering88N

end CFSG.RankThree.PartTwo.Sec8

end
