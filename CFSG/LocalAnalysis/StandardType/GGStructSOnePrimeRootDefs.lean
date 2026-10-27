module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVStruct

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGIsRootInvolution {X : Type} [Group X] (G₀ : Subgroup X) (r : X) : Prop :=
  ∃ (t : CFSG.Open.StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X), ψ.range = G₀ ∧
    CFSG.Open.StatedLieAdmissible t n 2 f ∧ 2 ≤ (ggU t n f).D.rank ∧
    ψ.ker ≤ Subgroup.center (ggU t n f).K ∧ GGRootInvolution (ggU t n f).D t ψ r

@[expose] def GGStructSOnePrimeRoot : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (G₀ : Subgroup X) (r e : X),
    p.Prime → p ≠ 2 → IsSimpleGroup ↥G₀ →
    e ∈ Subgroup.normalizer (G₀ : Set X) →
    LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = e⁻¹ * l * e) φ) →
    r ∈ G₀ → orderOf r = 2 → orderOf e = p → Commute r e → GGIsRootInvolution G₀ r →
    ∀ S : Subgroup X,
      S ≤ Subgroup.centralizer ({r, e} : Set X) ⊓ G₀ →
      IsSubnormal S (Subgroup.centralizer ({r, e} : Set X) ⊓ G₀) →
      commutator ↥S = ⊤ →
      ∀ (N : Subgroup ↥S) [N.Normal],
        ((CFSG.pCore 2 ↥(Subgroup.centralizer ({r, e} : Set X) ⊓ G₀)).map
            (Subgroup.centralizer ({r, e} : Set X) ⊓ G₀).subtype).subgroupOf S ≤ N →
        IsSimpleGroup (↥S ⧸ N) → (∃ a b : ↥S ⧸ N, a * b ≠ b * a) →
        LargeEvenMarking (↥S ⧸ N) (fun _ _ _ _ _ _ => True)

end CFSG.StandardType
