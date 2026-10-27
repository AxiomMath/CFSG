module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerCenter
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary Matrix

structure QTwoDivInnerFrame {G : Type} [Group G] (m : ℕ) (Bs L : Subgroup G)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (F0 : Type) [Field F0] [Finite F0] [CharP F0 2]
    (L0 : Type) [Group L0] (c : ↥L →* L0) (π : Su F0 2 1 m →* L0) (ρ : ↥Bs →* MulAut L0) :
    Prop where
  card : Nat.card F0 = 4
  c_surj : Function.Surjective c
  c_ker : c.ker ≤ Subgroup.center ↥L
  c_two : IsPGroup 2 c.ker
  π_surj : Function.Surjective π
  π_ker : π.ker ≤ Subgroup.center (Su F0 2 1 m)
  diag : ∀ b : ↥Bs, ∃ g : GL (Fin m) F0, ggIsDiagMat g ∧
    ∀ u : Su F0 2 1 m, ∃ u' : Su F0 2 1 m,
      (u' : GL (Fin m) F0) = g * (u : GL (Fin m) F0) * g⁻¹ ∧ ρ b (π u) = π u'
  induced : ∀ (b : ↥Bs) (l : ↥L),
    c ⟨(b : G) * l * (b : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hN b.2) l).mp l.2⟩ = ρ b (c l)

structure QTwoDivTorus {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {m : ℕ} (h3 : 3 ∣ m)
    (δ : ↥(sumZero m 3) →* Su F0 2 1 m) : Prop where
  inj : Function.Injective δ
  diag : ∀ f, ggIsDiagMat (δ f : GL (Fin m) F0)
  surj_diag : ∀ s : Su F0 2 1 m, ggIsDiagMat (s : GL (Fin m) F0) → ∃ f, δ f = s
  perm : ∀ (σ : Equiv.Perm (Fin m)) f,
    ggPermSU σ⁻¹ * δ f * (ggPermSU σ⁻¹)⁻¹ = δ (permAutV σ f)
  scalar : ∀ f, (∃ c : F0, ((δ f : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal fun _ => c) ↔ f ∈ Subgroup.zpowers (qTwoOneVec m h3)
  mono : ∀ u : GL (Fin m) F0, (∀ f, ∃ f', ∃ z : F0, z ≠ 0 ∧
      (u : Matrix (Fin m) (Fin m) F0) * ((δ f : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
        z • ((δ f' : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
          (u : Matrix (Fin m) (Fin m) F0)) →
    ∃ ρ : Equiv.Perm (Fin m), ∀ f,
      u * (δ f : GL (Fin m) F0) = (δ (permAutV ρ f) : GL (Fin m) F0) * u

structure QTwoDivLift {G : Type} [Group G] {m : ℕ} (Bs L : Subgroup G) {F0 : Type} [Field F0]
    [Finite F0] [CharP F0 2] {L0 : Type} [Group L0] (c : ↥L →* L0) (π : Su F0 2 1 m →* L0)
    (δ : ↥(sumZero m 3) →* Su F0 2 1 m) (τ : ↥(sumZero m 3) →* ↥L) : Prop where
  comm : ∀ f, c (τ f) = π (δ f)
  mem : ∀ f, ((τ f : ↥L) : G) ∈ Bs
  cube : ∀ f, τ f ^ 3 = 1

end CFSG.StandardType.QTwo

end
