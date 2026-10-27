module

public import CFSG.RankThree.PartTwo.Sec11.Item119
public import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def V0Concl {Z : Type} [Group Z] (σ : MulAut Z) (ξ γ : Z) : Prop :=
  MulAut.conj γ * σ * (MulAut.conj γ)⁻¹ ∈
      Subgroup.closure ({σ, MulAut.conj ξ} : Set (MulAut Z)) ∧
    MulAut.conj γ * MulAut.conj ξ * (MulAut.conj γ)⁻¹ ∈
      Subgroup.closure ({σ, MulAut.conj ξ} : Set (MulAut Z))

@[expose] def V0Fam (F : ∀ (Z : Type) [Group Z], Prop) : Prop :=
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
      V0Concl σ ξ γ

@[expose] def V0FamG2 : Prop :=
  V0Fam fun Z _ => ∃ q : TauCeti.PrimePower, Sec4.IsoGTwo Z q

@[expose] def V0FamD4 : Prop :=
  V0Fam fun Z _ => ∃ n : ℕ, Sec8.IsoTrialityD4 Z n

structure V0Data {G : Type} [Group G] [Finite G] (Y K : Subgroup G) (c s : G)
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hsN : s ∈ Subgroup.normalizer (Y : Set G))
    (J : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)) (ξ γ : Y ⧸ aschbacherSolvableCore 3 Y) :
    Prop where
  c_cube : c ^ 3 = 1
  K_comp : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G))
  K_type : IsType424 (K ⧸ aschbacherSolvableCore 3 K)
  s_three : ∃ k : ℕ, s ^ 3 ^ k = 1
  s_comm_c : s * c = c * s
  s_comm_K : ∀ k ∈ K, s * k * s⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K
  J_eq : J = (K.subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))
  alpha_cube : Sec4.Item426.thetaAut Y hcN ^ 3 = 1
  J_comp : J ∈ thetaComponentsIn (Sec4.Item426.fixSub (Sec4.Item426.thetaAut Y hcN))
  J_type : IsType424 (J ⧸ aschbacherSolvableCore 3 J)
  xi_mem : ξ ∈ J
  xi_sylow : IsSylowOf 3 (Subgroup.zpowers ξ) J
  xi_nine : 9 ≤ orderOf ξ
  sigma_three : ∃ k : ℕ, Sec4.Item426.thetaAut Y hsN ^ 3 ^ k = 1
  sigma_alpha : Sec4.Item426.thetaAut Y hsN * Sec4.Item426.thetaAut Y hcN =
    Sec4.Item426.thetaAut Y hcN * Sec4.Item426.thetaAut Y hsN
  sigma_J : ∀ j ∈ J, j⁻¹ * Sec4.Item426.thetaAut Y hsN j ∈
    inSubgroup (aschbacherSolvableCore 3) J
  sigma_xi : Sec4.Item426.thetaAut Y hsN * MulAut.conj ξ =
    MulAut.conj ξ * Sec4.Item426.thetaAut Y hsN
  gamma_cube : γ ^ 3 = 1
  P_three : IsPGroup 3 (Subgroup.closure ({Sec4.Item426.thetaAut Y hsN, MulAut.conj ξ,
    MulAut.conj γ} : Set (MulAut (Y ⧸ aschbacherSolvableCore 3 Y))))
  lower_bound : ∀ ζ : Y ⧸ aschbacherSolvableCore 3 Y, (∃ k : ℕ, ζ ^ 3 ^ k = 1) →
    Sec4.Item426.thetaAut Y hcN ζ = ζ → (∀ j ∈ J, ζ * j * ζ⁻¹ = j) →
      orderOf (MulAut.conj ζ) ≤ orderOf (Sec4.Item426.thetaAut Y hsN)

@[expose] def V0FamL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y K : Subgroup G) (c s : G)
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hsN : s ∈ Subgroup.normalizer (Y : Set G))
    (J : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)) (ξ γ : Y ⧸ aschbacherSolvableCore 3 Y),
    Sec13.IsLThreePi (Y ⧸ aschbacherSolvableCore 3 Y) → V0Data Y K c s hcN hsN J ξ γ →
      V0Concl (Sec4.Item426.thetaAut Y hsN) ξ γ

end CFSG.RankThree.PartTwo.Sec11

end
