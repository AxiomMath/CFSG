module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGF4ThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .F4 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1

@[expose] def GGF4ThreeNbrRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGNoTransvection p Bs → p = 3 → ∀ (y : G) (K : Subgroup G),
      GGNbr p B x D J y K →
      LargeEvenMarking ↥K (fun lab _ _ I _ θ => GGF4ThreeLabel p lab ∧
        Bs ≤ Subgroup.normalizer (K : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
        ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
          GGTorusSelfCent 3 (ggGamma K hN).range → 3 ^ 4 ≤ Nat.card (ggGamma K hN).range

end CFSG.StandardType

end
