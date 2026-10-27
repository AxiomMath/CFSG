module

public import CFSG.LocalAnalysis.StandardType.ZS.Support
public import CFSG.Quasithin.Background.SimsG4Defs

public section

namespace CFSG.StandardType.ZS

@[expose] def TFNegOrGen (p : ℕ) [Fact p.Prime] (m : ℕ) : Prop :=
  ∀ (U' : Type) [AddCommGroup U'] [Module (ZMod p) U'] [Module.Finite (ZMod p) U']
    (J : Subgroup (U' ≃ₗ[ZMod p] U')), Module.finrank (ZMod p) U' = m → ReflGen p J →
    QTwoLin.TransvectionFree J →
    (∀ W : Submodule (ZMod p) U', (∀ g ∈ J, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) →
    (LinearEquiv.neg (ZMod p) : U' ≃ₗ[ZMod p] U') ∈ J ∨
      ∃ s : Finset (U' ≃ₗ[ZMod p] U'), s.card ≤ m ∧ (∀ x ∈ s, x ∈ J ∧ IsRefl p x) ∧
        J = Subgroup.closure (s : Set (U' ≃ₗ[ZMod p] U'))

@[expose] def TFCoprimeWitness (p : ℕ) [Fact p.Prime] (m : ℕ) : Prop :=
  ∀ (U' : Type) [AddCommGroup U'] [Module (ZMod p) U'] [Module.Finite (ZMod p) U']
    (J : Subgroup (U' ≃ₗ[ZMod p] U')), Module.finrank (ZMod p) U' = m → ReflGen p J →
    QTwoLin.TransvectionFree J →
    (∀ W : Submodule (ZMod p) U', (∀ g ∈ J, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) →
    ∃ D : Subgroup (U' ≃ₗ[ZMod p] U'), D ≤ J ∧ Nat.Coprime (Nat.card D) p ∧
      HardMathSupport.Kantor79.commutatorSpace D = ⊤

@[expose] def TFThroughRefl (p : ℕ) [Fact p.Prime] (m : ℕ) : Prop :=
  ∀ (U' : Type) [AddCommGroup U'] [Module (ZMod p) U'] [Module.Finite (ZMod p) U']
    (J : Subgroup (U' ≃ₗ[ZMod p] U')), Module.finrank (ZMod p) U' = m → ReflGen p J →
    QTwoLin.TransvectionFree J →
    (∀ W : Submodule (ZMod p) U', (∀ g ∈ J, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) →
    ∀ r ∈ J, IsRefl p r → ∃ B : Subgroup (U' ≃ₗ[ZMod p] U'), B ≤ J ∧ r ∈ B ∧ ReflGen p B ∧
      SplitSupport B (m - 1)

@[expose] def TableFactsAt (p : ℕ) [Fact p.Prime] (m : ℕ) : Prop :=
  TFNegOrGen p m ∧ TFCoprimeWitness p m ∧ TFThroughRefl p m

@[expose] def PropOneEightAt (p : ℕ) [Fact p.Prime] (m : ℕ) : Prop :=
  4 ≤ m → ∀ (U : Type) [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (G : Subgroup (U ≃ₗ[ZMod p] U)), Module.finrank (ZMod p) U = m → IsRGroup p G →
    (∀ W : Submodule (ZMod p) U, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤) →
    ¬ Quasithin.SimsG4.IsImprimitiveOnV G → ∀ d : ℕ, DMax p G d → 3 < d →
    ∃ N : Subgroup (U ≃ₗ[ZMod p] U), N ≤ G ∧ ReflGen p N ∧ SplitSupport N (m - 1) ∧ DMax p N d

section OneGroup

variable (p : ℕ) [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

structure TableHyp (J : Subgroup (U ≃ₗ[ZMod p] U)) : Prop where
  reflGen : ReflGen p J
  transvectionFree : QTwoLin.TransvectionFree J
  irreducible : ∀ W : Submodule (ZMod p) U, (∀ g ∈ J, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤
  dLarge : ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)

@[expose] def NegOrGen (m : ℕ) (J : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ J ∨
    ∃ s : Finset (U ≃ₗ[ZMod p] U), s.card ≤ m ∧ (∀ x ∈ s, x ∈ J ∧ IsRefl p x) ∧
      J = Subgroup.closure (s : Set (U ≃ₗ[ZMod p] U))

@[expose] def CoprimeWitness (J : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  ∃ D : Subgroup (U ≃ₗ[ZMod p] U), D ≤ J ∧ Nat.Coprime (Nat.card D) p ∧
    HardMathSupport.Kantor79.commutatorSpace D = ⊤

@[expose] def ThroughRefl (l : ℕ) (J : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  ∀ r ∈ J, IsRefl p r → ∃ B : Subgroup (U ≃ₗ[ZMod p] U), B ≤ J ∧ r ∈ B ∧ ReflGen p B ∧
    SplitSupport B l

@[expose] def TableConclusions (m : ℕ) (J : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  NegOrGen p m J ∧ CoprimeWitness p J ∧ ThroughRefl p (m - 1) J

end OneGroup

variable {p : ℕ} [Fact p.Prime]

theorem tableFactsAt_of_forall {m : ℕ}
    (h : ∀ (U : Type) [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
      (J : Subgroup (U ≃ₗ[ZMod p] U)), Module.finrank (ZMod p) U = m → TableHyp p J →
        TableConclusions p m J) :
    TableFactsAt p m := by
  unfold TableFactsAt
  refine ⟨?_, ?_, ?_⟩
  · intro U _ _ _ J hdim hgen htv hirr hd
    exact (h U J hdim ⟨hgen, htv, hirr, hd⟩).1
  · intro U _ _ _ J hdim hgen htv hirr hd
    exact (h U J hdim ⟨hgen, htv, hirr, hd⟩).2.1
  · intro U _ _ _ J hdim hgen htv hirr hd r hr hrr
    exact (h U J hdim ⟨hgen, htv, hirr, hd⟩).2.2 r hr hrr

end CFSG.StandardType.ZS
