module

public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Timmesfeld.Transvection.Lines

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank

variable {H : Type*} [Group H]

structure IsFrame (Δ : Set (Subgroup H)) {r : ℕ} (P Q : Fin r → Subgroup H) : Prop where
  memP : ∀ i, P i ∈ Δ
  memQ : ∀ i, Q i ∈ Δ
  opposite : ∀ i, Opposite (P i) (Q i)
  commuting : ∀ i j, i ≠ j → Commuting (P i ⊔ Q i) (P j ⊔ Q j)

structure IsSmallFrame (Δ : Set (Subgroup H)) {r : ℕ} (P Q : Fin r → Subgroup H) (k : Fin r) : Prop
    extends IsFrame Δ P Q where
  residue : ∀ X ∈ Δ, (∀ i, i ≠ k → Commuting X (P i) ∧ Commuting X (Q i)) → X ≤ P k ⊔ Q k

@[expose] def TransvectionConclusionRank (H : Type) [Group H] (Δ : Set (Subgroup H)) (f : ℕ)
    (hf : 1 ≤ f) (r : ℕ) (hr : 2 ≤ r) : Prop :=
  (∃ Φ : ↥(StatedSp r (GaloisField 2 f)) →* H, Function.Bijective Φ ∧ ∀ X : Subgroup H,
      X ∈ Δ ↔ ∃ g, X = (conjSub ((Symplectic.rootDatum r (GaloisField 2 f)).rootGroup
        (Pi.single (⟨r - 1, by omega⟩ : Fin r) 1)) g).map Φ) ∨
    (∃ Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (2 * r)) →* H,
      Function.Surjective Φ ∧ Φ.ker = Subgroup.center _ ∧ ∀ X : Subgroup H, X ∈ Δ ↔
        ∃ g, X = (conjSub ((Unitary.rootDatum (card_galoisField_two_mul hf) (2 * r)).rootGroup
          (unitaryLongRoot (2 * r) (by omega))) g).map Φ)

theorem transvectionConclusion_of_rank {H : Type} [Group H] {Δ : Set (Subgroup H)} {f : ℕ}
    {hf : 1 ≤ f} {r : ℕ} {hr : 2 ≤ r} (h : TransvectionConclusionRank H Δ f hf r hr) :
    TransvectionConclusion H Δ f hf := by
  rcases h with ⟨Φ, hΦ, hmem⟩ | ⟨Φ, hΦ, hker, hmem⟩
  · exact Or.inl ⟨r, hr, Φ, hΦ, hmem⟩
  · exact Or.inr ⟨2 * r, by omega, Φ, hΦ, hker, hmem⟩

@[expose] def TransvectionStatementFrame : Prop :=
  ∀ (H : Type) [Group H] (Δ : Set (Subgroup H)), TransvectionHyp H Δ → MeetsLines Δ →
    ∀ (r : ℕ) (hr : 2 ≤ r) (P Q : Fin r → Subgroup H) (k : Fin r), IsSmallFrame Δ P Q k →
      ∃ f : ℕ, ∃ hf : 1 ≤ f, (∀ A ∈ Δ, Nat.card A = 2 ^ f) ∧
        TransvectionConclusionRank H Δ f hf r hr

end CFSG.Timmesfeld.Transvection
