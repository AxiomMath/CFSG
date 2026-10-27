module

public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarFam

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace Item1119NU

@[expose] def NumFam (F : ∀ (Z : Type) [Group Z], Prop) : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z], F Z →
    ∀ (α σ : MulAut Z) (J : Subgroup Z) (ξ γ : Z),
      α ^ 3 = 1 → J ∈ thetaComponentsIn (Sec4.Item426.fixSub α) →
      IsType424 (J ⧸ aschbacherSolvableCore 3 J) →
      ξ ∈ J → IsSylowOf 3 (Subgroup.zpowers ξ) J → 9 ≤ orderOf ξ →
      (∃ k : ℕ, σ ^ 3 ^ k = 1) → σ * α = α * σ →
      (∀ j ∈ J, j⁻¹ * σ j ∈ inSubgroup (aschbacherSolvableCore 3) J) →
      σ * MulAut.conj ξ = MulAut.conj ξ * σ →
      γ ^ 3 = 1 →
      IsPGroup 3 (Subgroup.closure ({σ, MulAut.conj ξ, MulAut.conj γ} : Set (MulAut Z))) →
      (∀ ζ : Z, (∃ k : ℕ, ζ ^ 3 ^ k = 1) → α ζ = ζ → (∀ j ∈ J, ζ * j * ζ⁻¹ = j) →
        orderOf (MulAut.conj ζ) ≤ orderOf σ) →
      orderOf ξ ≤ 3 * orderOf σ

@[expose] def NumFamG2 : Prop :=
  NumFam fun Z _ => ∃ q : TauCeti.PrimePower, Sec4.IsoGTwo Z q

@[expose] def NumFamD4 : Prop :=
  NumFam fun Z _ => ∃ n : ℕ, Sec8.IsoTrialityD4 Z n

@[expose] def NumFamL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y K : Subgroup G) (c s : G)
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hsN : s ∈ Subgroup.normalizer (Y : Set G))
    (J : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)) (ξ γ : Y ⧸ aschbacherSolvableCore 3 Y),
    Sec13.IsLThreePi (Y ⧸ aschbacherSolvableCore 3 Y) →
      V0Data Y K c s hcN hsN J ξ γ →
        orderOf ξ ≤ 3 * orderOf (Sec4.Item426.thetaAut Y hsN)

end Item1119NU

end CFSG.RankThree.PartTwo.Sec11

end
