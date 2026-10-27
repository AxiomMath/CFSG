module

public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOLin
public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOP
public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOPLinB

import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141c2
public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOLinCore

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110h (sl_a5 a5Center_map)

namespace LemmaOLin

theorem outer_numeric_dvd {S : Type} [Group S] {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k] [Finite k]
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hk : Nat.card k = p ^ f) (hf2 : f ≤ 2)
    (hQ : p ^ f = 2 ∨ p ^ f = 4 ∨ p ^ f = 5) (e : S ≃* LinearFlag.projectiveSL n k)
    (h3 : 3 ∣ Nat.card (Outer S)) : 3 ≤ n ∧ 3 ∣ n ∧ p ^ f = 4 := by
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · exfalso
    obtain rfl : n = 2 := by omega
    have hout := (linear_two_outer_order_divisor hp k hk).2 S
      ⟨e.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 k).symm⟩
    have h := h3.trans hout
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · have := Nat.le_of_dvd (by omega) h
      omega
    · have := Nat.le_of_dvd (by norm_num) (h.trans (Nat.gcd_dvd_left 2 _))
      omega
  · have hout := UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound hp hf hn3 hk
    rw [← Nat.card_congr (equivalence e).toEquiv] at hout
    have h := h3.trans hout
    have hg := three_dvd_of_dvd_two_mul hf hf2 h
    have h31 : 3 ∣ p ^ f - 1 := hg.trans (Nat.gcd_dvd_right _ _)
    exact ⟨hn3, hg.trans (Nat.gcd_dvd_left _ _), by omega⟩

end LemmaOLin

open LemmaOLin in
theorem lemmaO_linear_P {S : Type} [Group S] [Finite S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group)) (hq3 : q.p ≠ 3)
    {α : MulAut S} (hα : α ^ 3 = 1) (hout : ∀ c : S, α ≠ MulAut.conj c)
    {K : Subgroup S}
    (hK : CFSG.Open.IsComponentOf K (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α))
    (hA : Nonempty (↥K ≃* alternatingGroup (Fin 5)))
    (hB : ThreeRankLeOneInv S) :
    (r = 1 ∧ (q.card = 64 ∨ q.card = 125)) ∨ (r = 2 ∧ q.card = 4) := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
  obtain ⟨e⟩ := he
  let e' : S ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card q.p q.exponent q.exponent_pos.ne'
  have hcard' : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent := by
    rw [hcard, TauCeti.PrimePower.card_def]
  have hchar3 : ringChar (GaloisField q.p q.exponent) ≠ 3 := by
    rw [ringChar.eq (GaloisField q.p q.exponent) q.p]
    exact hq3
  have hpk : ((3 : ℕ) : GaloisField q.p q.exponent) ≠ 0 := by
    rw [Ne, ringChar.spec]
    intro hdvd
    rw [ringChar.eq (GaloisField q.p q.exponent) q.p] at hdvd
    exact hq3 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hdvd)
  have hβ' : MulAut.congr e' α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hK' := InputsL33.isComponentOf_map_congr e' hK
  have hL : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨eA⟩ := hA
    exact Claims1110h.nonempty_centerQuot_equiv_of_surjective eA.toMonoidHom eA.surjective
      (by rw [(MonoidHom.ker_eq_bot_iff _).2 eA.injective]; exact bot_le)
      (Claims1110e.center_eq_bot_of_isAltType_five ⟨MulEquiv.refl _⟩)
  have hL' := a5Center_map e' hL
  have hcases := (Nat.lt_or_ge r 2).elim
    (fun hr2 => by
      obtain rfl : r = 1 := by omega
      exact Inputs141c.projectiveSL_cases_two (MulAut.congr e' α) hβ')
    (fun hr2 => Inputs141c.projectiveSL_cases_of_three_le (by omega) hchar3
      (MulAut.congr e' α) hβ')
  rcases hcases with ⟨A, c, hA3, hβA⟩ | ⟨h, σ, hσ, hβh⟩
  · rw [hβA] at hK'
    have hle := inner_case_card_le hpk hA3 _ hK' hL'
    rw [hcard] at hle
    have hpow : q.p ^ q.exponent ≤ 5 := by rw [← TauCeti.PrimePower.card_def]; exact hle
    obtain ⟨hf2, hQ⟩ := prime_power_le_five q.prime_p hq3 q.exponent_pos hpow
    have hout3 := three_dvd_card_outer_of_outer_order_three hα hout
    obtain ⟨hn3, hn3d, hQ4⟩ :=
      outer_numeric_dvd (by omega) q.prime_p q.exponent_pos hcard' hf2 hQ e' hout3
    right
    have hq4 : q.card = 4 := by rw [TauCeti.PrimePower.card_def]; exact hQ4
    refine ⟨?_, hq4⟩
    by_contra hr2
    have h4 : q.p ^ q.exponent = 2 ^ 2 := hQ4.trans (by norm_num)
    have hp2 : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1
      (q.prime_p.dvd_of_dvd_pow (h4 ▸ dvd_pow_self q.p q.exponent_pos.ne' : q.p ∣ 2 ^ 2))
    haveI : CharP (GaloisField q.p q.exponent) 2 :=
      ⟨fun n => by rw [← hp2]; exact CharP.cast_eq_zero_iff _ q.p n⟩
    have h6 : 5 ≤ r + 1 := by omega
    obtain ⟨t, u, v, ht, htu, htv, huv, hu, hv3, hnot⟩ :=
      exists_three_rank_two_linear (S := S) h6 (hcard.trans hq4) e'
    exact hnot (hB t u v ht htu htv huv hu hv3)
  · have hβφ : MulAut.congr (h⁻¹ : MulAut _) (MulAut.congr e' α) =
        LinearFlag.fieldAut (r + 1) (GaloisField q.p q.exponent) σ := by
      rw [InputsL33.congr_self_eq, hβh]
      group
    have hK'' := InputsL33.isComponentOf_map_congr (h⁻¹ : MulAut _) hK'
    rw [hβφ] at hK''
    obtain ⟨hn2, hk⟩ := field_case (by omega) σ hσ _ hK'' (a5Center_map (h⁻¹ : MulAut _) hL')
    left
    refine ⟨by omega, ?_⟩
    rwa [hcard] at hk

end CFSG.RankThree.PartTwo.Sec21.FF79
