module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
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

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

@[expose] def GGKGPosStdPos {U : Type*} [Group U] (Δ : UniversalRootDatum U) {G : Type*}
    [Group G] (ψ : U →* G) (Bs : Subgroup G) : Prop :=
  ∀ b ∈ Bs, ∀ γ ∈ Δ.roots, ∃ h ∈ ggTorus Δ, ∀ z ∈ Δ.rootGroup γ,
    b * ψ z * b⁻¹ = ψ (h * z * h⁻¹)

@[expose] def GGKGPosNoTrivRoot {U : Type*} [Group U] (Δ : UniversalRootDatum U) {G : Type*}
    [Group G] (ψ : U →* G) (Bs : Subgroup G) : Prop :=
  ∀ γ ∈ Δ.roots, ∃ b ∈ Bs, ∃ z ∈ Δ.rootGroup γ, b * ψ z * b⁻¹ ≠ ψ z

@[expose] def GGKGPosTorsion (p : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  (t = .PSL ∧ p ∣ n) ∨ (t = .E6 ∧ p = 3)

@[expose] def GGKGPosLocalHyp
    (p : ℕ) {G : Type} [Group G] (Bs X : Subgroup G) (t : StatedLieTag) (n f : ℕ)
    (ψ : (ggU t n f).K →* G) : Prop :=
  (p.Prime ∧ p ≠ 2 ∧ StatedLieAdmissible t n 2 f ∧ 3 ≤ bnRank t n) ∧
    (ψ.ker ≤ Subgroup.center (ggU t n f).K ∧ ψ.range = X ∧
      (t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) ∧ p ∣ 2 ^ f - 1) ∧
    (IsElemAbelian p Bs ∧ Bs ≤ Subgroup.normalizer (X : Set G) ∧
      ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) ∧
    (∀ b ∈ Bs, GGPsiInnerDiag (ggU t n f).D ψ b) ∧
    ((¬ GGKGPosTorsion p t n →
        p ^ bnRank t n * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥Bs) ∧
      p ^ (bnRank t n - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥Bs)

@[expose] def GGKGPosStdPosCase
    (t : StatedLieTag) (c : ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs X : Subgroup G) (n f : ℕ)
    (ψ : (ggU t n f).K →* G), GGKGPosLocalHyp p Bs X t n f ψ → c p n →
      ∃ k : (ggU t n f).K,
        GGKGPosStdPos (ggU t n f).D (ψ.comp (MulAut.conj k).toMonoidHom) Bs

@[expose] def GGKGPosStep
    (P : ∀ (G : Type) [Group G] [Finite G], ℕ → Subgroup G → Subgroup G →
      ∀ (t : StatedLieTag) (n f : ℕ), ((ggU t n f).K →* G) → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs X : Subgroup G) (t : StatedLieTag) (n f : ℕ)
    (ψ : (ggU t n f).K →* G), GGKGPosLocalHyp p Bs X t n f ψ →
      GGKGPosStdPos (ggU t n f).D ψ Bs → P G p Bs X t n f ψ

@[expose] def GGKGPosInduced
    {G : Type} [Group G] (Bs X : Subgroup G) (t : StatedLieTag) (n f : ℕ)
    (ψ : (ggU t n f).K →* G) (ν : GGWeyl (ggU t n f).D →* (ggU t n f).K)
    (ε : GGWeyl (ggU t n f).D ≃* ↥(ggAutomizer X Bs)) : Prop :=
  ∀ (w : GGWeyl (ggU t n f).D) (b : ↥Bs),
    ((ε w : MulAut ↥Bs) b : G) = ψ (ν w) * b * (ψ (ν w))⁻¹

end CFSG.StandardType

end
