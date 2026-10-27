module

public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem finite_hypSU : Finite (hypSU h 2 0) := by
  have := h.finite
  infer_instance

theorem hypScalars_eq_bot : hypScalars h 2 0 = ⊥ := by
  have := h.charP
  rw [eq_bot_iff]
  rintro g ⟨c, -, hc4, hg⟩
  have hc : (c : K) = 1 := by
    have h4 : ((c : K) + 1) ^ 4 = 0 := by
      have hc4' : (c : K) ^ 4 = 1 := by
        have := congrArg Units.val hc4
        simpa using this
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination hc4' + (2 * (c : K) ^ 3 + 3 * (c : K) ^ 2 + 2 * (c : K) + 1) * h2
    have := pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h4
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at this
    exact this
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hg]
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, hc]

@[expose] noncomputable def hypSUEquivPSU : hypSU h 2 0 ≃* hypPSU h 2 0 :=
  QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq (hypScalars_eq_bot h).symm)

theorem nonempty_hypSU_equiv_statedProj :
    Nonempty (hypSU h 2 0 ≃* StatedProj (StatedSU 4 (2 ^ m) K)) := by
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 0) h
  exact ⟨(hypSUEquivPSU h).trans (hypPSUEquivStatedProj h hR (by norm_num))⟩

theorem exists_hypSU_equiv_of_lieModel {Y : Type} [Group Y]
    (hY : CFSG.Blueprint.LieModel Y .PSU 4 2 m) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 m K), Nonempty (hypSU h 2 0 ≃* Y) := by
  rcases hY with ⟨-, hc⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hc
    have hm : 1 ≤ m := hadm.2.1
    have h : UnitaryFieldData 2 m K := ⟨Nat.prime_two, hm, by rw [hK, ← pow_mul, mul_comm]⟩
    obtain ⟨e₀⟩ := nonempty_hypSU_equiv_statedProj h
    exact ⟨K, inferInstance, h, ⟨e₀.trans e.symm⟩⟩
  all_goals exact absurd hn (by norm_num)

end CFSG.Quasithin.H13.U4Par
