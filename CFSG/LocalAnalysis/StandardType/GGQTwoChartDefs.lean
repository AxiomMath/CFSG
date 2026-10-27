module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBlockHubDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLocalDefs
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix

variable {G : Type} [Group G] [Finite G]

abbrev QTwoH (L : Subgroup G) (𝒦 : Finset (Subgroup G)) : Subgroup G := L ⊔ ⨆ k ∈ 𝒦, k

structure QTwoChartSetting (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (m n : ℕ) where
  hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦
  hm : 5 ≤ m
  hN : n = m ∨ (n = m + 1 ∧ 3 ∣ n + 1)
  hLocal : QTwoLocalModel m Bs L x
  hRMGen : QTwoRMGenAt 3 B Bs x L D J 𝒦
  ρA : Equiv.Perm (Fin (n + 1)) ≃* ↥(ggAutomizerJoin L Bs 𝒦)
  hrefl : ∀ a b : Fin (n + 1), a ≠ b →
    GGIsReflection 3 ((ρA (Equiv.swap a b) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)

variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m n : ℕ}

@[expose] def QTwoLiftsPerm (Bs H : Subgroup G)
    (ρA : Equiv.Perm (Fin (n + 1)) ≃* ↥(ggAutomizerJoin L Bs 𝒦)) (g : G)
    (π : Equiv.Perm (Fin (n + 1))) : Prop :=
  g ∈ H ∧ g ∈ Subgroup.normalizer (Bs : Set G) ∧
    ∀ b : ↥Bs,
      ((((ρA π : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b : ↥Bs) : G) = g * (b : G) * g⁻¹

@[expose] def qTwoFrameSet (ε0 : Fin m ↪ Fin (n + 1)) (π : Equiv.Perm (Fin (n + 1)))
    (J : Finset (Fin m)) : Finset (Fin (n + 1)) :=
  (J.map ε0).map π.toEmbedding

@[expose] noncomputable def qTwoSymI
    (ρA : Equiv.Perm (Fin (n + 1)) ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (I : Finset (Fin (n + 1))) : Subgroup (MulAut ↥Bs) :=
  (Subgroup.closure {σ : Equiv.Perm (Fin (n + 1)) | ∀ y, y ∉ I → σ y = y}).map
    ((Subgroup.subtype (ggAutomizerJoin L Bs 𝒦)).comp ρA.toMonoidHom)

@[expose] noncomputable def qTwoFixI
    (ρA : Equiv.Perm (Fin (n + 1)) ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (I : Finset (Fin (n + 1))) : Subgroup G :=
  (⨅ s : qTwoSymI ρA I,
    MonoidHom.eqLocus (s : MulAut ↥Bs).toMonoidHom (MonoidHom.id ↥Bs)).map Bs.subtype

@[expose] def qTwoOTwoPrime (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {y | y ∈ X ∧ ∃ k : ℕ, y ^ (2 ^ k) = 1}

section Model

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]

@[expose] noncomputable def qTwoBlockOf (ψ : Su F0 2 1 m →* G) (g : G) (J : Finset (Fin m)) :
    Subgroup G :=
  (coordBlockSU F0 2 1 J).map ((MulAut.conj g).toMonoidHom.comp ψ)

@[expose] def QTwoOrdModel (Bs L : Subgroup G) (ψ : Su F0 2 1 m →* G) : Prop :=
  ψ.range = L ∧ ψ.ker ≤ Subgroup.center (Su F0 2 1 m) ∧
    ∀ b : ↥Bs, ∃ g : GL (Fin m) F0, ggIsDiagMat g ∧
      ∀ u : Su F0 2 1 m, ∃ u' : Su F0 2 1 m,
        (u' : GL (Fin m) F0) = g * (u : GL (Fin m) F0) * g⁻¹ ∧
          ψ u' = (b : G) * ψ u * (b : G)⁻¹

open Classical in
@[expose] def QTwoFrameMatch (S : QTwoChartSetting B Bs x L D J 𝒦 m n) (ψ : Su F0 2 1 m →* G)
    (ε0 : Fin m ↪ Fin (n + 1)) : Prop :=
  ∀ σ : Equiv.Perm (Fin m), ∃ u : Su F0 2 1 m,
    (∀ i : Fin m, ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 =
      Pi.single (σ i) 1) ∧
    QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA (ψ u)
      (σ.extendDomain (Equiv.ofInjective ε0 ε0.injective))

end Model

end CFSG.StandardType.QTwo

end
