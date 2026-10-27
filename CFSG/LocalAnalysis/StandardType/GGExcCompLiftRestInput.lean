module

public import CFSG.LocalAnalysis.StandardType.GGExcCompLiftInput
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGNbrHalfSplitArith
import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitMarking

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.RankThree.Chevalley

@[expose] def GGE7LiftHyp (q p : ℕ) : Prop :=
  ¬ (p : ℤ) ∣ (exhaustionPhi 7).eval (q : ℤ) ∧ ¬ (p : ℤ) ∣ (exhaustionPhi 9).eval (q : ℤ) ∧
    ¬ (p : ℤ) ∣ (exhaustionPhi 14).eval (q : ℤ) ∧ ¬ (p : ℤ) ∣ (exhaustionPhi 18).eval (q : ℤ)

@[expose] def GGE8LiftHyp (q p : ℕ) : Prop :=
  ¬ (p : ℤ) ∣ (exhaustionPhi 15).eval (q : ℤ) ∧
    (5 < p → ¬ (p : ℤ) ∣ (exhaustionPhi 20).eval (q : ℤ)) ∧
    ¬ (p : ℤ) ∣ (exhaustionPhi 24).eval (q : ℤ) ∧ ¬ (p : ℤ) ∣ (exhaustionPhi 30).eval (q : ℤ)

@[expose] def GGExcCompLiftRestInput (τ : Tag) (H : ℕ → ℕ → Prop) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card K - 1 → ¬ p ∣ Nat.card K + 1 → H (Nat.card K) p →
    ∀ a b : ↥(adjointGroup τ K), a ^ p = 1 → b ^ p = 1 → a * b = b * a → a ≠ 1 →
    ∀ X : Subgroup ↥(adjointGroup τ K), IsComponentOf X (Subgroup.centralizer {a}) →
      ¬ p ∣ Nat.card ↥X →
        ∃ X' : Subgroup ↥(adjointGroup τ K), IsComponentOf X' (Subgroup.centralizer {b}) ∧
          X ≤ X' ∧ (∃ Q m : ℕ, 1 ≤ m ∧ Q = Nat.card K ^ m ∧ Q ^ 2 - 1 ∣ Nat.card ↥X ∧
            GGCompFieldAt Q X') ∧ GGInnerDiagOn (Subgroup.zpowers a) X'

@[expose] def GGExcSevenTwoInput (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ a : ↥(adjointGroup τ K), a ^ 7 = 1 → a ≠ 1 →
    ∀ X : Subgroup ↥(adjointGroup τ K), IsComponentOf X (Subgroup.centralizer {a}) →
      7 ∣ Nat.card ↥X

theorem markDeg_eq_one_of_iso {lab lab' : LargeEvenLabel}
    (hex : lab = ⟨.A, 8, 1⟩ ∨ lab = ⟨.E6, 0, 1⟩) (h : GGLabelIso lab' lab) : markDeg lab' = 1 := by
  rw [eq_of_ggLabelIso_of_exc hex h]
  rcases hex with rfl | rfl <;> rfl

theorem ggNonsplitCoreNeOneAt_of_liftRest
    {τ : Tag} {H : ℕ → ℕ → Prop}
    (hL : GGExcCompLiftRestInput τ H)
    (hE : GGExcSevenTwoInput τ) (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hq1 : ¬ p ∣ Nat.card K - 1) (hq2 : ¬ p ∣ Nat.card K + 1)
    (hH : H (Nat.card K) p) :
    F4Nonsplit.GGNonsplitCoreNeOneAt ↥(adjointGroup τ K) p := by
  intro a b ha hb hab ha1 X hX hpX
  obtain ⟨X', hX', hXX', ⟨Q, m, hm, hQm, hQX, hQ⟩, hInn⟩ :=
    hL K p hp hp2 hq1 hq2 hH a b ha hb hab ha1 X hX hpX
  refine ⟨X', hX', hXX', fun hmk => ?_⟩
  rcases largeEvenMarking_or hmk with hHS | hPF
  · rcases ggMarkingHalfSplit_dvd_or_exc hQ hHS with h | ⟨lab, hlab, hhas, hp7, hex⟩
    · exact hpX (h.trans hQX)
    · subst hp7
      obtain ⟨labQ, hlabQ, -, hQeq, -, -, -, hhasQ, -⟩ := hQ
      have hdeg : markDeg labQ = 1 :=
        markDeg_eq_one_of_iso hex (ggLabelRigidInput_holds labQ lab _ hlabQ hlab hhasQ hhas)
      have hQ2 : Q = 2 := by rw [← hQeq, hdeg]; norm_num
      have hK : Nat.card K = 2 :=
        ((Nat.Prime.pow_eq_iff Nat.prime_two).1 (hQm.symm.trans hQ2)).1
      exact hpX (hE K hK a ha ha1 X hX)
  · exact ggNbr_not_primeField_known hp hp2 (Subgroup.mem_zpowers a) hInn hPF

theorem ggE7NonsplitCoreRestInput_of_liftRest
    (hL : GGExcCompLiftRestInput .E7 GGE7LiftHyp) (hE : GGExcSevenTwoInput .E7) :
    GGE7NonsplitCoreRestInput := by
  intro K _ _ _ p hp hp2 hq1 hq2 _ h7 h9 h14 h18
  exact ggNonsplitCoreNeOneAt_of_liftRest hL hE K p hp hp2 hq1 hq2 ⟨h7, h9, h14, h18⟩

theorem ggE8NonsplitCoreRestInput_of_liftRest
    (hL : GGExcCompLiftRestInput .E8 GGE8LiftHyp) (hE : GGExcSevenTwoInput .E8) :
    GGE8NonsplitCoreRestInput := by
  intro K _ _ _ p hp hp2 hq1 hq2 _ h15 h20 h24 h30
  exact ggNonsplitCoreNeOneAt_of_liftRest hL hE K p hp hp2 hq1 hq2 ⟨h15, h20, h24, h30⟩

end CFSG.StandardType
