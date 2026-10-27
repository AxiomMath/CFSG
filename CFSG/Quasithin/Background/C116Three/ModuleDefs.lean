module

public import CFSG.Quasithin.EmptyFaithful.R3c23Def
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank

section Defs

variable {V : Type} [CommGroup V]

structure PairHyp (X L₁ L₂ : Subgroup (MulAut V)) (τ : MulAut V) : Prop where
  τ_mem : τ ∈ X
  le₁ : L₁ ≤ X
  le₂ : L₂ ≤ X
  conj : L₂ = L₁.map (MulAut.conj τ).toMonoidHom
  q₁ : CFSG.IsQuasisimple ↥L₁
  q₂ : CFSG.IsQuasisimple ↥L₂
  comm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a
  norm : ∀ x ∈ X, ∀ l ∈ L₁ ⊔ L₂, x * l * x⁻¹ ∈ L₁ ⊔ L₂

structure JPair (X L₁ L₂ : Subgroup (MulAut V)) (τ : MulAut V) [Finite V] : Prop extends PairHyp X L₁ L₂ τ where
  b53 : B53Hyp (ffJ X)
  L₁J : L₁ ≤ ffJ X
  Jn : ∀ x ∈ ffJ X, x ∈ Subgroup.normalizer (L₁ : Set (MulAut V))

@[expose] def NoBigSL3 (L₁ : Subgroup (MulAut V)) : Prop :=
  ¬ ∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 3 ≤ m ∧ Odd m ∧ Nat.card K = 2 ^ m ∧
    Nonempty (↥L₁ ≃* ↥(StatedSL 3 K))

@[expose] def IsL32 (L₁ : Subgroup (MulAut V)) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧ Nonempty (↥L₁ ≃* ↥(StatedSL 3 K))

@[expose] def Case5Out (X L₁ L₂ : Subgroup (MulAut V)) : Prop :=
  ∃ G₁ G₂ : Subgroup (MulAut V), ffJ X = G₁ ⊔ G₂ ∧ G₁ ⊓ G₂ = ⊥ ∧ (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) ∧
    L₁ = G₁ ∧ L₂ = G₂ ∧ IsL32 L₁ ∧ commV G₁ ⊓ commV G₂ = ⊥ ∧
    (∀ b ∈ G₂, ∀ w ∈ commV G₁, b w = w) ∧ Nat.card ↥(commV G₁) = 2 ^ 3 ∧
    (∀ w ∈ commV G₁, (∀ g ∈ G₁, g w = w) → w = 1)

@[expose] def TypeTwo (X L₁ L₂ : Subgroup (MulAut V)) : Prop :=
  TwoB56Gen X L₁ L₂ ∧ Lin2Cover ↥L₁

@[expose] def TwoB56GenInv (X L₁ L₂ : Subgroup (MulAut V)) : Prop :=
  ∃ (G₁ G₂ : Subgroup (MulAut V)) (W₁ W₂ : Subgroup V),
    ffJ X = G₁ ⊔ G₂ ∧ G₁ ⊓ G₂ = ⊥ ∧ (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) ∧ L₁ ≤ G₁ ∧ L₂ ≤ G₂ ∧
      (G₁ = L₁ ∨ (Nonempty (↥G₁ ≃* Equiv.Perm (Fin 5)) ∧ Nat.card ↥L₁ = 60)) ∧
      (G₂ = L₂ ∨ (Nonempty (↥G₂ ≃* Equiv.Perm (Fin 5)) ∧ Nat.card ↥L₂ = 60)) ∧
      fixV (G₁ ⊔ G₂) ≤ W₁ ∧ fixV (G₁ ⊔ G₂) ≤ W₂ ∧ W₁ ⊔ W₂ = ⊤ ∧ W₁ ⊓ W₂ = fixV (G₁ ⊔ G₂) ∧
      B56Piece G₁ W₁ (fixV (G₁ ⊔ G₂)) ∧ B56Piece G₂ W₂ (fixV (G₁ ⊔ G₂)) ∧
      XMod.IsInv ↥(G₁ ⊔ G₂) W₁ ∧ XMod.IsInv ↥(G₁ ⊔ G₂) W₂

@[expose] def TypeThree (X L₁ L₂ : Subgroup (MulAut V)) : Prop :=
  TwoB56GenInv X L₁ L₂ ∧
    ∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 1 ≤ m ∧ Odd m ∧ Nat.card K = 2 ^ m ∧
      Nonempty (↥L₁ ≃* ↥(StatedSL 3 K))

@[expose] def TypeFive (X L₁ L₂ : Subgroup (MulAut V)) : Prop := Case5Out X L₁ L₂

end Defs

@[expose] def ModulePairFV : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X L₁ L₂ : Subgroup (MulAut V)) (τ : MulAut V), PairHyp X L₁ L₂ τ →
      pCoreOf 2 X = ⊥ → IsFFModule X → B53Hyp (ffJ X) → L₁ ≤ ffJ X →
      (∀ x ∈ ffJ X, x ∈ Subgroup.normalizer (L₁ : Set (MulAut V))) → NoBigSL3 L₁ →
      ∀ (𝒜 : Set (Subgroup (MulAut V))) (Q : Subgroup (MulAut V)), IsPGroup 2 Q → Q ≤ ffJ X →
        (∀ A ∈ 𝒜, IsFFStarOffender X A) → (∀ A ∈ 𝒜, A ≤ Q) →
          ∃ w : V, w ∉ fixV L₁ ∧ w ∈ fixV L₂ ∧ ∀ A ∈ 𝒜, w ∈ fixV A

end CFSG.Quasithin.C116Three
