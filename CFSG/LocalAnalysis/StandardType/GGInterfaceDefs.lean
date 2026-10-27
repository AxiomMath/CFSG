module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGPresentation
public import CFSG.LieType.Universal.Catalog
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Abstract

variable {U : Type*} [Group U] (Δ : UniversalRootDatum U)

@[expose] def ggTorus : Subgroup U :=
  ⨅ γ ∈ Δ.roots, Subgroup.normalizer (Δ.rootGroup γ : Set U)

variable {G : Type*} [Group G]

@[expose] def GGPsiInnerDiag (ψ : U →* G) (c : G) : Prop :=
  ∃ g ∈ ψ.range, ∀ γ ∈ Δ.roots, ∃ h ∈ ggTorus Δ, ∀ z ∈ Δ.rootGroup γ,
    (c * g)⁻¹ * ψ z * (c * g) = ψ (h * z * h⁻¹)

@[expose] def GGLongRoot (γ : Fin Δ.rank → ℤ) : Prop :=
  ∃ (w : GGWeyl Δ) (γ₀ : Fin Δ.rank → ℤ), γ₀ ∈ Δ.roots ∧
    (∀ δ ∈ Δ.roots, ∑ i, δ i ≤ ∑ i, γ₀ i) ∧ γ = weylAction Δ.isFiniteType w γ₀

@[expose] def GGTwistedTag (t : StatedLieTag) : Prop :=
  t = .PSU ∨ t = .POmegaMinus ∨ t = .twistedE6

@[expose] def GGRootClass (t : StatedLieTag) (γ : Fin Δ.rank → ℤ) : Prop :=
  γ ∈ Δ.roots ∧ (GGTwistedTag t → GGLongRoot Δ γ)

@[expose] def ggRootSub (ψ : U →* G) (γ : Fin Δ.rank → ℤ) (u : U) : Subgroup G :=
  ((Δ.rootGroup γ).map (MulAut.conj u).toMonoidHom).map ψ

@[expose] def GGRootInvolution (t : StatedLieTag) (ψ : U →* G) (r : G) : Prop :=
  orderOf r = 2 ∧ ∃ γ, GGRootClass Δ t γ ∧ ∃ u : U, r ∈ ggRootSub Δ ψ γ u

end Abstract

section Core

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U]

@[expose] def GGSixHypV2Core (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (Δ : UniversalRootDatum U) (t : StatedLieTag) (n f : ℕ) (ψ : U →* G) : Prop :=
  GGBstar p B Bs ∧ LargeEvenStdSub p B x L D J ∧
    (StatedLieAdmissible t n 2 f ∧ 2 ≤ Δ.rank) ∧
    (ψ.range = ggG0 p B x L D J ∧ ψ.ker ≤ Subgroup.center U) ∧
    (commutator ↥(ggG0 p B x L D J) = ⊤ ∧
      LieModel (↥(ggG0 p B x L D J) ⧸ Subgroup.center ↥(ggG0 p B x L D J)) t n 2 f) ∧
    (Bs ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) ∧ ∀ b ∈ Bs, GGPsiInnerDiag Δ ψ b) ∧
    Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) ∧
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

end Core

section Genuine

noncomputable abbrev ggU (t : StatedLieTag) (n f : ℕ) : LieUniversal :=
  lieUniversal t n 2 f Nat.prime_two

variable {G : Type} [Group G] [Finite G]

@[expose] def GGSixHypV2 (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixHypV2Core p B Bs x L D J (ggU t n f).D t n f ψ

end Genuine

end CFSG.StandardType
