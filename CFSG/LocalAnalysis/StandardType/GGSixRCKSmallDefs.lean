module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CDynE
public import CFSG.LocalAnalysis.StandardType.GGSixRCKCases
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynExc

public section

namespace CFSG.StandardType.RCKSmall

section Tags

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S265C.DynE
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def RCKSmallLieTag (t : StatedLieTag) : Prop :=
  t = .G2 ∨ t = .twistedB2 ∨ t = .twistedF4 ∨ t = .Tits

@[expose] def CompTypeLie2Small : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (labL : GLALabel) (β : MulAut S) (p : ℕ), p.Prime → p ≠ 2 →
    Subgroup.center S = ⊥ → CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S labL β →
    β ^ p = 1 → β ≠ 1 → labL.tag ≠ .G2 → labL.tag ≠ .B2der → labL.tag ≠ .G2der →
    labL.tag ≠ .twF4der → labL.tag ≠ .twB2 → labL.tag ≠ .twF4 →
    ∀ J : Subgroup S, CFSG.Open.IsComponentOf J (fixSubgroup β) →
      TagLieType (fun t => ¬ RCKSmallLieTag t) 2 ↥J ∨ Nat.card (↥J ⧸ Subgroup.center ↥J) = 360

end Tags

section Labels

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

@[expose] def RCKSmallTag (tag : LargeEvenLieTag) : Prop :=
  tag = .G2 ∨ tag = .twB2 ∨ tag = .twF4 ∨ tag = .twF4der

@[expose] def RCKSmallLabel (Jb : Type) [Group Jb] : Prop :=
  LargeEvenMarking Jb (fun lab _ _ _ _ _ => RCKSmallTag lab.tag)

@[expose] def RCKSmallEmpty :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L : Subgroup X),
    RCKSmallLabel ↥J →
    GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    Odd (Nat.card (Subgroup.centralizer (G₀ : Set X))) →
    p.Prime → p ≠ 2 → IsElemAbelian p A → B₁ ≤ A → D ≤ B₁ → Nat.card D = p ^ 2 →
    A ≤ Subgroup.normalizer (G₀ : Set X) →
    LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ) →
    B₁ ≤ Subgroup.normalizer (J : Set X) →
    B₁ ⊓ Subgroup.centralizer (J : Set X) = D → p ^ 4 ≤ Nat.card B₁ →
    (∀ y ∈ (A ⊔ G₀) ⊓ Subgroup.centralizer (A : Set X), orderOf y = p → y ∈ A) →
    p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) ≤ Nat.card A →
    A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ →
    B₁ ≤ Subgroup.normalizer (L : Set X) →
    LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) →
    IsComponentOf J (Subgroup.centralizer (D : Set X) ⊓ G₀) →
    Odd (Nat.card (Subgroup.center ↥J)) →
    L ≤ G₀ → (∃ x ∈ D, x ≠ 1 ∧ IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x})) →
    ¬ D ≤ Subgroup.centralizer (L : Set X) →
    IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set X)) →
    IsEmpty (↥J ≃* alternatingGroup (Fin 6)) →
    False

end Labels

end CFSG.StandardType.RCKSmall
