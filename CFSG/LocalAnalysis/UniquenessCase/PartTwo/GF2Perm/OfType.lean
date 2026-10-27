module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2LieOfType

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

@[expose] def PermWitnessPSL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), 4 ≤ m → LieModel G .PSL m 2 1 → PermWitness G

@[expose] def PermWitnessPSU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), 4 ≤ m → LieModel G .PSU m 2 1 → PermWitness G

@[expose] def PermWitnessPSp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), 3 ≤ m → LieModel G .PSp m 2 1 → PermWitness G

@[expose] def PermWitnessOmegaPlus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), 4 ≤ m → LieModel G .POmegaPlus m 2 1 →
    PermWitness G

@[expose] def PermWitnessOmegaMinus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), 4 ≤ m → LieModel G .POmegaMinus m 2 1 →
    PermWitness G

@[expose] def PermWitnessExcUntwisted : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag),
    (t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) → LieModel G t 0 2 1 → PermWitness G

@[expose] def PermWitnessTwistedE6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], LieModel G .twistedE6 0 2 1 → PermWitness G

theorem permWitness_of_gf2PermType (hL : PermWitnessPSL) (hU : PermWitnessPSU)
    (hSp : PermWitnessPSp) (hOp : PermWitnessOmegaPlus) (hOm : PermWitnessOmegaMinus)
    (hE : PermWitnessExcUntwisted) (h2E6 : PermWitnessTwistedE6)
    {G : Type} [Group G] [Finite G] {t : StatedLieTag} {m : ℕ}
    (hadm : StatedLieAdmissible t m 2 1) (ht : GF2PermType t m) (hG : LieModel G t m 2 1) :
    PermWitness G := by
  obtain ⟨hPSL, hD4, hTits⟩ := ht
  have h := hadm.2.2
  cases t with
  | PSL => exact hL G m (Nat.lt_of_not_le fun hm => hPSL ⟨rfl, hm⟩) hG
  | PSU =>
    have hm3 : m ≠ 3 := by
      rintro rfl
      exact h.2 (by norm_num)
    exact hU G m (by have := h.1; omega) hG
  | PSp =>
    have hm2 : m ≠ 2 := by
      rintro rfl
      exact h.2 (by norm_num)
    exact hSp G m (by have := h.1; omega) hG
  | POmegaOdd => exact absurd rfl h.2
  | POmegaPlus => exact hOp G m h hG
  | POmegaMinus => exact hOm G m h hG
  | G2 => exact absurd h.2 (by norm_num)
  | F4 => subst h; exact hE G .F4 (Or.inl rfl) hG
  | E6 => subst h; exact hE G .E6 (Or.inr (Or.inl rfl)) hG
  | E7 => subst h; exact hE G .E7 (Or.inr (Or.inr (Or.inl rfl))) hG
  | E8 => subst h; exact hE G .E8 (Or.inr (Or.inr (Or.inr rfl))) hG
  | twistedE6 => subst h; exact h2E6 G hG
  | trialityD4 => exact absurd rfl hD4
  | twistedB2 => exact absurd h.2.2.2 (by norm_num)
  | twistedF4 => exact absurd h.2.2.2 (by norm_num)
  | twistedG2 => exact absurd h.2.1 (by norm_num)
  | Tits => exact absurd rfl hTits

theorem k_GF2_permutabilityOfType_of_families (hL : PermWitnessPSL) (hU : PermWitnessPSU)
    (hSp : PermWitnessPSp) (hOp : PermWitnessOmegaPlus) (hOm : PermWitnessOmegaMinus)
    (hE : PermWitnessExcUntwisted) (h2E6 : PermWitnessTwistedE6) :
    K_GF2_permutabilityOfType := by
  intro Y _ _ K hK hodd t m hadm ht hLie S hS
  exact exists_permutes_of_permWitness hK hodd
    (permWitness_of_gf2PermType hL hU hSp hOp hOm hE h2E6 hadm ht hLie) hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm
