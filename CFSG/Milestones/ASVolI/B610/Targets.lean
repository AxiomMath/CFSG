module

public import CFSG.Milestones.ASVolI.B610.FamDef

public section

namespace CFSG.Quasithin.B610T

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def burnsideB610_TwoFamTarget : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V L : Subgroup G),
    MinParabolic H T M → ∀ hred : IsTwoReducedIn H V,
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) → IsSubnormal L H →
    IsNaturalL2Prime 1 L V →
    ∃ (ι : Type) (S : Finset ι) (X : ι → Subgroup G) (D : ∀ i, NatData (X i) V (ZMod 2)),
      burnsideB610_Fam H T V hred.2.2.1 (ZMod 2) S X D ∧
      ∃ i₀ ∈ S, L ≤ X i₀ ∧ ⁅V, X i₀⁆ = ⁅V, L⁆ ∧
        ∀ (g : G) (hg : g ∈ Subgroup.normalizer (V : Set G)),
          g ∈ Subgroup.normalizer ((X i₀ : Subgroup G) : Set G) →
          convI hred.2.2.1 ⟨g, hg⟩ ∈
            Subgroup.normalizer ((autI hred.2.2.1 L : Subgroup (MulAut (IntMod V hred.2.2.1))) :
              Set (MulAut (IntMod V hred.2.2.1)))

@[expose] def burnsideB610_CompFamTarget : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (n : ℕ), MinParabolic H T M → ∀ hred : IsTwoReducedIn H V,
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) → IsSubnormal L H → 2 ≤ n →
    Fintype.card F = 2 ^ n → NatData L V F →
    ∃ (ι : Type) (S : Finset ι) (X : ι → Subgroup G) (D : ∀ i, NatData (X i) V F),
      burnsideB610_Fam H T V hred.2.2.1 F S X D ∧
      ∃ i₀ ∈ S, X i₀ = L ⊔ (H ⊓ Subgroup.centralizer (V : Set G))

end CFSG.Quasithin.B610T
