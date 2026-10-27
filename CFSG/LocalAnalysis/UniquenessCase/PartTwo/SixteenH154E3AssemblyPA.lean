module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Five
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Shape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Good
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Seventeen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s16h_five_le_of_prime_ne {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) (h3 : q ≠ 3) :
    5 ≤ q := by
  by_contra h
  have hlt : q < 5 := by omega
  have hq2 := hq.two_le
  interval_cases q
  · exact h2 rfl
  · exact h3 rfl
  · exact absurd hq (by norm_num)

private theorem s16h_v1Sub_eq_v0_of_odd_card_e3 (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hodd : Odd (Nat.card ↥(lBar V₀ V hV L))) :
    v1Sub D.M V₀ V hV L = V₀ := by
  by_cases h0 : V₀ = ⊥
  · subst h0
    exact s16c167_v1Sub_eq_bot_of_inf_fixV D hV rfl
      (s16c167_wTil_inf_fixV_eq_bot_of_odd hV L hodd)
  · exact v1Sub_of_ne_bot D.M V₀ V hV L h0

theorem s16h_hyp154_of_central_e3 (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hδ : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2 →
      delta15 D.M V₀ V h.hyp151.isElemAbelian L <
        gamma15 D.M V₀ V h.hyp151.isElemAbelian L - 1)
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L)
    (hU₂ : s16h_CondU2 D V₀ V L h.hyp151.isElemAbelian)
    (h3 : 3 ∉ D.sig)
    (hshape : (IsPOnePlusTwo 3 ↥(lBar V₀ V h.hyp151.isElemAbelian L) ∧
        rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V h.hyp151.isElemAbelian))
          (lBar V₀ V h.hyp151.isElemAbelian L)) = 6) ∨
      (IsElemAbelianOfRank 3 2 ↥(lBar V₀ V h.hyp151.isElemAbelian L) ∧
        rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V h.hyp151.isElemAbelian))
          (lBar V₀ V h.hyp151.isElemAbelian L)) = 6) ∨
      (IsElemAbelianOfRank 3 2 ↥(lBar V₀ V h.hyp151.isElemAbelian L) ∧
        rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V h.hyp151.isElemAbelian))
          (lBar V₀ V h.hyp151.isElemAbelian L)) = 8 ∧
        ∀ x ∈ lBar V₀ V h.hyp151.isElemAbelian L, x ≠ 1 →
          rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V h.hyp151.isElemAbelian))
            (Subgroup.zpowers x)) = 6))
    (hodd : Odd (Nat.card ↥(lBar V₀ V h.hyp151.isElemAbelian L))) : Hyp154 D V₀ V L := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨q, hq⟩ := S.hx.sig_nonempty
  have hqprime := (D.sig_prime q hq).1
  have hq2 : q ≠ 2 := (D.sig_prime q hq).2
  have hq3 : q ≠ 3 := fun heq => h3 (heq ▸ hq)
  have hσ3 : ∃ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M := ⟨q, hq, S.hx.three_le q hq⟩
  have hfix : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓ fixV
      (lBar V₀ V hV L) = ⊥ := s16c167_wTil_inf_fixV_eq_bot_of_odd hV L hodd
  have hBB : s16h_BlockBound (Mbar D.M V₀ V hV) (lBar V₀ V hV L) q 1 := by
    intro E hE hEab
    have hle := s16h_card_le_mul_cent_of_shape (s15_Infra_vtil_sq_eq_one V₀ V hV)
      hqprime hq2 hq3 hfix hshape (hE.trans inf_le_right) hEab
    simpa using hle
  have hv1 : v1Sub D.M V₀ V hV L ≤ V₀ := (s16h_v1Sub_eq_v0_of_odd_card_e3 D hV hodd).le
  by_cases hs2 : s15 D.M V₀ V hV L = 2
  · obtain ⟨E, hEM, hEab, hEcard⟩ :=
      c23_exists_elemAbelian_card_pow (p := q) (M := D.M) (k := 3) hqprime
        (by rw [UC6.groupPRank_eq_pRank]; exact S.hx.three_le q hq)
    have hEn := s16h_barSub_le_normalizer_of_s15_le_two D h.hyp151 (by omega)
      (hqprime.odd_of_ne_two hq2) hEM hEab
    have hcard := s16h_card_le_pow_mul_card_inf_preBarSub D h.hyp151 hBB hEM hEab hEn
    have hPcard : q ^ 2 ≤ Nat.card ↥(E ⊓ preBarSub D.M V₀ V hV
        (centSub (wTil V₀ V hV L))) := by
      rw [hEcard, pow_one] at hcard
      have h : q * q ^ 2 ≤ q * Nat.card ↥(E ⊓ preBarSub D.M V₀ V hV
          (centSub (wTil V₀ V hV L))) := by
        calc q * q ^ 2 = q ^ 3 := by ring
          _ ≤ q * Nat.card ↥(E ⊓ preBarSub D.M V₀ V hV
              (centSub (wTil V₀ V hV L))) := hcard
      exact Nat.le_of_mul_le_mul_left h hqprime.pos
    have hW1 := s16h_uniqueMax_of_card_le D S.h61 S.h127 h hq (S.hx.three_le q hq) hEab hPcard
    exact s16h_hyp154_of_unique₁_two D h.hyp151 hs2
      (s16h_unique₁_of_wSub D h.hyp151 hv1 hW1) (hδ hs2)
  · have hs3le : 3 ≤ s15 D.M V₀ V hV L := by omega
    by_cases hs4 : 3 < s15 D.M V₀ V hV L
    · exact s16h_hyp154_of_condU2 D S.h61 h hσ3 hU₂ hs4
    · have hs_eq3 : s15 D.M V₀ V hV L = 3 := by omega
      have h5 : 5 ≤ q := s16h_five_le_of_prime_ne hqprime hq2 hq3
      exact s16h_hyp154_of_blockBound_one_five D S.h61 S.h127 h hs_eq3 hq
        (S.hSig.sig1_sp q (hσ ▸ hq)) (S.hx.three_le q hq) h5 hv1 hBB

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
