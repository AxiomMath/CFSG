module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.SLnAut
public import CFSG.LocalAnalysis.UniquenessCase.Lie.RankOne
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

theorem uc22pwr1_datum_sln [Finite K] [CharP K 2] {m : ℕ} (hm : 1 ≤ m) {n : ℕ}
    (hK : Nat.card K = 2 ^ n) :
    UC22pwR1Datum (SpecialLinearGroup (Fin (m + 2)) K) (unitriangular (m + 2) K) n := by
  let T : Subgroup (SpecialLinearGroup (Fin (m + 2)) K) := (uc22pwSLnD m K).range
  let w : SpecialLinearGroup (Fin (m + 2)) K := uc22pwSLnJ m K
  have hcardT : Nat.card T = 2 ^ n - 1 := by
    have h1 : Nat.card T = Nat.card Kˣ :=
      (Nat.card_congr (Equiv.ofInjective (uc22pwSLnD m K)
        (uc22pwSLnD_injective (m := m) (K := K)))).symm
    rw [h1, Nat.card_units, hK]
  have hn : n ≠ 0 := by
    intro h0
    have h2 : 1 < 2 ^ n := by rw [← hK]; exact Finite.one_lt_card
    rw [h0] at h2
    norm_num at h2
  refine ⟨T, w, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isCyclic_of_surjective (uc22pwSLnD m K).rangeRestrict
      (uc22pwSLnD m K).rangeRestrict_surjective
  · rw [hcardT]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, hn⟩) odd_one
  · rw [normalizer_unitriangular]
    rintro t ⟨a, rfl⟩
    exact uc22pwSLnD_mem_upperTriangular a
  · intro p _ hp
    rw [hcardT]
    exact hp
  · rw [pow_two]
    exact uc22pwSLnJ_mul_self
  · rintro t ⟨a, rfl⟩ -
    exact uc22pwSLnJ_conj a
  · rw [normalizer_unitriangular]
    exact uc22pwSLn_upper_sup_J
  · intro ψ hψ
    obtain ⟨i, hi⟩ := uc22pwSLn_key hm ψ hψ
    refine ⟨i, ?_⟩
    rintro t ⟨a, rfl⟩ -
    refine ⟨ψ (uc22pwSLnD m K a) * (uc22pwSLnD m K (a ^ 2 ^ i))⁻¹, hi a, ?_⟩
    rw [map_pow (uc22pwSLnD m K) a (2 ^ i), inv_mul_cancel_right]

theorem uc22pwr1_datum_sl4 [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    UC22pwR1Datum (SpecialLinearGroup (Fin 4) K) (unitriangular 4 K) n :=
  uc22pwr1_datum_sln (m := 2) (by norm_num) hK

end CFSG.LocalAnalysis.UniquenessCase.UC22
