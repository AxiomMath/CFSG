module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

/-!
# The Brauer--Suzuki--Wall theorem: source-faithful interfaces

This module separates the local hypotheses used by Bender's 1974 proof from
its structural conclusion.  The recognition of the resulting Zassenhaus
group is a downstream step.
-/

namespace CFSG.GorensteinWalter

universe u

/-- The hypotheses of the Brauer--Suzuki--Wall theorem in the form stated by
Bender.  Here `H = C_G(t)`, `K` is the abelian index-two subgroup of `H`, and
`s` acts on `K` by inversion with fixed subgroup `⟨t⟩`. -/
public structure BrauerSuzukiWallHypotheses
    (G : Type u) [Group G] [Finite G] where
  t : G
  K : Subgroup G
  H : Subgroup G
  s : G
  t_involution : IsInvolution t
  t_mem_K : t ∈ K
  H_eq_centralizer : H = Subgroup.centralizer ({t} : Set G)
  K_commutative : IsMulCommutative K
  s_involution : IsInvolution s
  s_not_mem_K : s ∉ K
  H_eq_join : H = K ⊔ Subgroup.zpowers s
  fixed_subgroup_eq :
    K ⊓ Subgroup.centralizer ({s} : Set G) = Subgroup.zpowers t
  s_inverts_K :
    ∀ x : G, x ∈ K → s * x * s⁻¹ = x⁻¹
  conjugate_disjoint :
    ∀ g : G, g ∉ H → Disjoint K (K.conjBy g)
  involutions_conjugate :
    ∀ u : G, IsInvolution u → ∃ g : G, g * u * g⁻¹ = t

/-- The structural conclusion of the Brauer--Suzuki--Wall theorem before the
final Zassenhaus recognition step.  It is the numbered conclusion in
`refs/bender-bsw.tex`. -/
public structure BrauerSuzukiWallConclusion
    (G : Type u) [Group G] [Finite G] where
  q : ℕ
  Q : Subgroup G
  D : Subgroup G
  q_odd : Odd q
  Q_card : Nat.card Q = q
  group_card : Nat.card G = q * (q + 1) * (q - 1) / 2
  centralizer_eq_Q :
    ∀ x : G, x ∈ Q → x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) = Q
  D_commutative : IsMulCommutative D
  Q_disjoint_D : Disjoint Q D
  normalizer_Q_eq :
    Subgroup.normalizer (Q : Set G) = Q ⊔ D
  D_card : Nat.card D = (q - 1) / 2
  normalizer_subgroup_data :
    ∀ X : Subgroup G, X ≠ ⊥ → X ≤ D →
      ∃ u : G,
        Subgroup.normalizer (X : Set G) =
            Subgroup.normalizer (D : Set G) ∧
          Subgroup.normalizer (D : Set G) =
            D ⊔ Subgroup.zpowers u ∧
          IsInvolution u ∧
          u ∉ D ∧
          ∀ d : G, d ∈ D → u * d * u⁻¹ = d⁻¹

end CFSG.GorensteinWalter
