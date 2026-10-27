module

public import CFSG.RankThree.PartOne.K1320.L4Torus

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem Tl_apply_of_snd_eq_zero (a : Kˣ) (w : QV K (Fin 2)) (hw : w 1 = 0) :
    ((Tl K a : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) w = (a : K) • w := by
  funext i
  fin_cases i
  · simp only [Tl_apply_zero, Fin.zero_eta, Pi.smul_apply, Algebra.smul_def]
  · simp [Tl_apply_one, hw]

theorem Tl_apply_of_fst_eq_zero (a : Kˣ) (w : QV K (Fin 2)) (hw : w 0 = 0) :
    ((Tl K a : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) w = ((a⁻¹ : Kˣ) : K) • w := by
  funext i
  fin_cases i
  · simp [Tl_apply_zero, hw]
  · simp only [Tl_apply_one, Fin.mk_one, Pi.smul_apply, Algebra.smul_def]

theorem single_decomp (v : QV K (Fin 2)) :
    v = (Pi.single 0 (v 0) : QV K (Fin 2)) + (Pi.single 1 (v 1) : QV K (Fin 2)) := by
  funext i
  fin_cases i <;> simp

theorem eq_Rr_of_card {r : ℕ} (hr : r.Prime) (hrq : r ∣ Nat.card K - 1) (S : Subgroup ↥(M8 K))
    (hS : S ≤ (Tl K).range) (hcard : Nat.card S = r) : S = Rr K r := by
  have hle : S ≤ Rr K r := by
    intro x hx
    obtain ⟨a, rfl⟩ := hS hx
    have hpow : (⟨Tl K a, hx⟩ : S) ^ r = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    have h1 : Tl K a ^ r = 1 := congrArg Subtype.val hpow
    refine ⟨a, ?_, rfl⟩
    show a ∈ rootsOfUnity r K
    rw [mem_rootsOfUnity]
    apply Tl_injective
    rw [map_pow, h1, map_one]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [rootsOfUnity_card hr hrq, hcard])

end CFSG.RankThree.PartOne.K1320
