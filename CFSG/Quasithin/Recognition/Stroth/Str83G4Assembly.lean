module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Frame

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G]

@[expose] def Str83G4CaseAFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    Str83G4Frame L1 L2 S a → str83R L1 L2 S ≤ Q1 L1 L2 S → False

@[expose] def Str83G4CaseBOrder : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    Str83G4Frame L1 L2 S a → ¬ str83R L1 L2 S ≤ Q1 L1 L2 S →
      Nat.card (Q1 L1 L2 S) = (2 ^ (2 * a + 1)) ^ 10

theorem str83Q1Order_of_cases
    (hA : Str83G4CaseAFalse) (hBo : Str83G4CaseBOrder) : Str83Q1Order := by
  intro G _ _ L1 L2 S a hF ha hSz hL2
  have hfr := str83G4Frame_of hF ha hSz hL2
  by_cases hR : str83R L1 L2 S ≤ Q1 L1 L2 S
  · exact (hA G L1 L2 S a hfr hR).elim
  · exact hBo G L1 L2 S a hfr hR

@[expose] def Str83G4Z2Comm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    Str83G4Frame L1 L2 S a → ∀ k ∈ P1 L1 L2 S,
      Z2 L1 L2 S ≤ Subgroup.centralizer (CFSG.Quasithin.conjSub k (Z2 L1 L2 S) : Set G)

@[expose] def Str83G4S1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    Str83G4Frame L1 L2 S a → IsElemAbelian 2 (str83X L1 L2 S)

theorem str83G4S1_of_z2Comm (h : Str83G4Z2Comm) : Str83G4S1 := fun G _ _ L1 L2 S a hfr =>
  HypF91.isElemAbelian_conjClosure_of_forall (SmithC27.isElemAbelian_omegaOneCenterOf _)
    (h G L1 L2 S a hfr)

@[expose] def Str83G4Z1Card : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    Str83G4Frame L1 L2 S a → Nat.card (Z1 L1 L2 S) = 2 ^ (2 * a + 1)

@[expose] def Str83G4XIndex : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    Str83G4Frame L1 L2 S a → ¬ str83R L1 L2 S ≤ Q1 L1 L2 S →
      (Z1 L1 L2 S).relIndex (str83X L1 L2 S) = (2 ^ (2 * a + 1)) ^ 4

@[expose] def Str83G4YIndex : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    Str83G4Frame L1 L2 S a → ¬ str83R L1 L2 S ≤ Q1 L1 L2 S →
      (str83X L1 L2 S).relIndex (str83Y L1 L2 S) = 2 ^ (2 * a + 1)

@[expose] def Str83G4Q1Index : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    Str83G4Frame L1 L2 S a → ¬ str83R L1 L2 S ≤ Q1 L1 L2 S →
      (str83Y L1 L2 S).relIndex (Q1 L1 L2 S) = (2 ^ (2 * a + 1)) ^ 4

theorem str83G4CaseBOrder_of_parts
    (h1 : Str83G4S1) (hZ : Str83G4Z1Card) (hX : Str83G4XIndex) (hY : Str83G4YIndex)
    (hQ : Str83G4Q1Index) : Str83G4CaseBOrder := by
  intro G _ _ L1 L2 S a hfr hR
  have hfr' := hfr
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr'
  have hZ1X : Z1 L1 L2 S ≤ str83X L1 L2 S :=
    (str83_caseI_basics hF hB ha hSz hL2 hZI).2.1.trans (z2_le_str83X L1 L2 S)
  have hXY : str83X L1 L2 S ≤ str83Y L1 L2 S := str83X_le_str83Y hfr (h1 G L1 L2 S a hfr)
  have hYQ : str83Y L1 L2 S ≤ Q1 L1 L2 S := inf_le_left
  have e3 := Subgroup.relIndex_mul_relIndex _ _ _ hXY hYQ
  have e2 := Subgroup.relIndex_mul_relIndex _ _ _ hZ1X (hXY.trans hYQ)
  have e1 := Subgroup.relIndex_mul_relIndex _ _ _ (bot_le : (⊥ : Subgroup G) ≤ Z1 L1 L2 S)
    (hZ1X.trans (hXY.trans hYQ))
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at e1
  rw [← e1, ← e2, ← e3, hZ G L1 L2 S a hfr, hX G L1 L2 S a hfr hR, hY G L1 L2 S a hfr hR,
    hQ G L1 L2 S a hfr hR]
  ring

end CFSG.Quasithin.Stroth

end
