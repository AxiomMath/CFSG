module

public import CFSG.LocalAnalysis.UniquenessCase.UC22SeedSL
public import CFSG.CGT.Timmesfeld75.L2Pair

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.CGT.Timmesfeld75 (IsL2Pair)
open Subgroup
open scoped MatrixGroups

theorem isL2Pair_psl_of_card_eq {n : ℕ} (hn : n ≠ 0) {P : Subgroup PSL(2, GaloisField 2 n)}
    (hP : IsPGroup 2 P) (hc : Nat.card P = 2 ^ n) :
    IsL2Pair PSL(2, GaloisField 2 n) P (2 ^ n) := by
  have hcard : Nat.card (PSL(2, GaloisField 2 n)) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr (CFSG.CGT.Timmesfeld75.pslMulEquivSL (F := GaloisField 2 n)).toEquiv,
      CFSG.CGT.Timmesfeld75.card_sl2, GaloisField.card 2 n hn]
  have hidx_eq : P.index = (2 ^ n) ^ 2 - 1 := by
    have h1 : 2 ^ n * P.index = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      calc 2 ^ n * P.index = Nat.card P * P.index := by rw [hc]
        _ = Nat.card (PSL(2, GaloisField 2 n)) := Subgroup.card_mul_index P
        _ = 2 ^ n * ((2 ^ n) ^ 2 - 1) := hcard
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) n) h1
  refine IsL2Pair.of_psl_isPGroup hn ⟨MulEquiv.refl _⟩ hP ?_
  rw [hidx_eq]
  intro hdvd
  have h2sq : 2 ∣ (2 ^ n) ^ 2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left (dvd_pow_self 2 hn) _
  have hone : 2 ∣ 1 := by
    have h := Nat.dvd_sub h2sq hdvd
    rwa [Nat.sub_sub_self (Nat.one_le_pow 2 (2 ^ n) (pow_pos (by norm_num) n))] at h
  exact Nat.prime_two.not_dvd_one hone

theorem exists_not_mem_normalizer_of_isL2Pair {X : Type} [Group X] {S : Subgroup X} {q : ℕ}
    (h : IsL2Pair X S q) : ∃ x : X, x ∉ normalizer (S : Set X) := by
  obtain ⟨F, _, _, _, e, -, -, -, -, hmemN⟩ := h.exists_data
  refine ⟨e.symm (CFSG.CGT.Timmesfeld75.wElt (F := F)), fun hmem => ?_⟩
  have hb : e (e.symm (CFSG.CGT.Timmesfeld75.wElt (F := F))) ∈
      CFSG.CGT.Timmesfeld75.borel F := (hmemN _).1 hmem
  rw [e.apply_symm_apply] at hb
  exact CFSG.CGT.Timmesfeld75.wElt_not_mem_borel hb

theorem eq_bot_of_normal_le_normalizer_of_isL2Pair {X : Type} [Group X] {S : Subgroup X} {q : ℕ}
    (h : IsL2Pair X S q) {N : Subgroup X} [N.Normal] (hN : N ≤ normalizer (S : Set X)) :
    N = ⊥ := by
  obtain ⟨P, hP⟩ := IsL2Pair.exists_sylow_eq h
  obtain ⟨F, _, _, _, e, -, -⟩ := h
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.sl2_eq_bot_of_normal_le_normalizer
    e P N (hP.symm ▸ hN)

theorem eq_bot_of_normal_of_isPGroup_of_isL2Pair {X : Type} [Group X] {S : Subgroup X} {q : ℕ}
    (h : IsL2Pair X S q) {N : Subgroup X} [N.Normal] (hN : IsPGroup 2 N) : N = ⊥ := by
  obtain ⟨F, _, _, _, e, -, -⟩ := h
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.sl2_normal_isPGroup_eq_bot e N hN

end CFSG.LocalAnalysis.WeakClosure81

end
