module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveWeylFiveProj
import CFSG.RankThree.PartOne.AUTSL.SpTwoAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Matrix CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

private theorem formJ_mul_formJ_generic {n : ℕ} {K : Type} [Field K] :
    formJ n K * formJ n K = -1 := by
  rw [formJ, fromBlocks_multiply]
  simp only [Matrix.mul_zero, zero_add, add_zero, Matrix.mul_neg, Matrix.mul_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [fromBlocks, one_apply, Matrix.neg_apply]

private theorem isUnit_det_formJ_generic {n : ℕ} {K : Type} [Field K] :
    IsUnit (formJ n K).det := by
  have h := congrArg Matrix.det (formJ_mul_formJ_generic (n := n) (K := K))
  rw [det_mul, det_neg, det_one, Fintype.card_sum, Fintype.card_fin,
    Even.neg_one_pow (Even.add_self n), one_mul] at h
  exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one h)

theorem weylFivePower_of_model_PSp {X : Type} [Group X] {n p f : ℕ}
    (h : StatedClassicalModel X .PSp n p f) (hn : n ≤ 4) (hp2 : p ≠ 2) (hp31 : p ≠ 31) :
    WeylFivePower X := by
  classical
  unfold StatedClassicalModel at h
  obtain ⟨hAdm, K, hField, hFinite, hcard, ⟨e⟩⟩ := h
  let := hField
  let := hFinite
  have := Fintype.ofFinite K
  unfold StatedLieAdmissible at hAdm
  obtain ⟨hp, hf, hn2, -⟩ := hAdm
  have hchar : ringChar K = p := by
    obtain ⟨m, -, hm⟩ := FiniteField.card K (ringChar K)
    rw [Nat.card_eq_fintype_card] at hcard
    have hdvd : p ∣ ringChar K ^ (m : ℕ) := by
      rw [← hm, hcard]
      exact dvd_pow_self p (by omega : f ≠ 0)
    exact ((Nat.prime_dvd_prime_iff_eq hp (CharP.prime_ringChar K)).mp
      (hp.dvd_of_dvd_pow hdvd)).symm
  have hp31' : ringChar K ≠ 31 := by rw [hchar]; exact hp31
  have hp2' : (2 : K) ≠ 0 := by
    have := ringChar.of_eq hchar
    intro h2
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by simpa using h2)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  refine WeylFivePower.of_mulEquiv e.symm ?_
  refine weylFivePower_statedProj (ι := Fin n ⊕ Fin n) (K := K) hp31' (StatedSp n K) ?_ ?_ ?_
  ·
    intro c hc hc31
    have hc2 : c ^ 2 = 1 := (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff (by omega) c).1 hc
    have h : c ^ 31 = c := by
      calc c ^ 31 = c ^ (2 * 15 + 1) := by norm_num
        _ = (c ^ 2) ^ 15 * c := by rw [pow_add, pow_mul, pow_one]
        _ = 1 ^ 15 * c := by rw [hc2]
        _ = c := by simp
    exact h ▸ hc31
  ·
    refine Or.inr ⟨?_, formJ n K, isUnit_det_formJ_generic, ?_⟩
    · simp only [Fintype.card_sum, Fintype.card_fin]; omega
    · intro x hx
      exact CFSG.Open.StatedAPI.mem_statedSp_iff.mp hx
  ·
    intro α _
    have hgen : ∃ (A : gsp n K) (σ : K ≃+* K),
        α = conjAut n K A * fieldAut n K σ := by
      by_cases h3 : 3 ≤ n
      · exact (automorphism_generation (K := K) (r := n) h3).2 α
      · have hn_eq : n = 2 := by omega
        subst n
        exact (CFSG.RankThree.PartOne.AUTSL.SpTwo.automorphism_generation_two (K := K) hp2').2 α
    obtain ⟨A, σ, hA⟩ := hgen
    refine ⟨1, (A : GL (Fin n ⊕ Fin n) K), σ, by norm_num, ?_⟩
    refine ⟨(conjSp n K A).toMonoidHom.comp (fieldSp n K σ).toMonoidHom, ?_, ?_⟩
    · intro x
      rfl
    · intro x
      rw [pow_one, hA]
      change conjAut n K A (fieldAut n K σ (QuotientGroup.mk x)) =
        QuotientGroup.mk ((conjSp n K A) (fieldSp n K σ x))
      rw [show QuotientGroup.mk x = proj n K x from rfl, fieldAut_proj, conjAut_proj]
      rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
