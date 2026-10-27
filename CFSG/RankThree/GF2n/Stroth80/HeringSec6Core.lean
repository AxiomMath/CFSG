module

public import CFSG.RankThree.GF2n.Stroth80.Sec6Main
public import CFSG.RankThree.GF2n.Stroth80.Sec311Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec12Cases
public import CFSG.RankThree.GF2n.Stroth80.Sec5Core
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatReindex

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS6

theorem exp_succ_of_index {q c k e : ℕ} (hq : 2 ≤ q) (hc2 : 2 ≤ c) (hcq : c ∣ q)
    (h : q ^ e = c * q ^ k) : e = k + 1 := by
  have hcq' : c ≤ q := Nat.le_of_dvd (by omega) hcq
  have h1 : q ^ k < q ^ e := by
    rw [h]
    calc q ^ k = 1 * q ^ k := (one_mul _).symm
      _ < c * q ^ k := Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos (by omega) k)
  have h2 : q ^ e ≤ q ^ (k + 1) := by
    rw [h, pow_succ, mul_comm (q ^ k) q]
    exact Nat.mul_le_mul_right _ hcq'
  have h3 := (Nat.pow_lt_pow_iff_right (by omega : 1 < q)).mp h1
  have h4 := (Nat.pow_le_pow_iff_right (by omega : 1 < q)).mp h2
  omega

theorem slMNat_of_alt {hc : Ctx M Q Z B} {t : G} {m : ℕ}
    (h : SLMNat hc t m ∨ (m = 2 ∧ SpMNat hc t 1)) : SLMNat hc t m := by
  rcases h with h | ⟨rfl, K, fK, finK, hK, hrep⟩
  · exact h
  · exact ⟨K, fK, finK, hK, NaturalRep.sp_one_to_sl_two hrep⟩

theorem two_le_card_Z (hc : Ctx M Q Z B) : 2 ≤ Nat.card Z := by
  have := hc.hyp.q4
  omega

theorem Rt_ne_LB (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Stroth6Hyp hc n t) : Rt M (LB M Q B) t ≠ LB M Q B := by
  intro hR
  have s5 := hs.toSec5
  have hCN := hc.CN_eq_LB_of_Rt_eq s5.mem hR
  have h1 := (stroth_3_5 h34 hc s5.width s5.n_gt s5.noA2 s5.gen).2.2.1
  have h2 := hs.cardN
  rw [hCN] at h2
  have h3 : Nat.card Z ^ (n - 1) = Nat.card Z ^ 1 :=
    Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Q)) (by rw [← h1, h2, pow_one])
  have := Nat.pow_right_injective (two_le_card_Z hc) h3
  have := s5.n_gt
  omega

theorem not_LB_inf_CN_le_Q (h311a : Stroth311aStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Stroth6Hyp hc n t) (hR : Rt M (LB M Q B) t ≠ LB M Q B) :
    ¬ (hc.CN t ⊓ LB M Q B ≤ Q) := by
  intro hle
  have s5 := hs.toSec5
  have hN := h311a G M Q Z B hc n s5.width s5.n_gt s5.noA2 s5.gen t s5.mem s5.notQ hR
  have hNQ : hc.CN t ≤ Q := by
    rw [hN]
    refine iSup₂_le fun h hh => ?_
    intro y hy
    have hyN : y ∈ hc.CN t := hy.2
    have hyL : h⁻¹ * y * h ∈ LB M Q B := mem_conjSubgroup.mp hy.1
    have hyN' : h⁻¹ * y * h ∈ hc.CN t := by
      have := hc.CN_conj_mem s5.mem ((Rt M (LB M Q B) t).inv_mem hh) hyN
      simpa using this
    have hq : h⁻¹ * y * h ∈ Q := hle ⟨hyN', hyL⟩
    have hhM : h ∈ M := hc.Rt_le_M t hh
    have h5 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hhM) _).mp hq
    rwa [show h * (h⁻¹ * y * h) * h⁻¹ = y by group] at h5
  have h6 := Subgroup.card_le_of_le hNQ
  rw [hs.cardN] at h6
  have h7 := two_le_card_Z hc
  have h8 := Nat.card_pos (α := Q)
  nlinarith

theorem card_LB_of_relIndex (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Stroth6Hyp hc n t) {k : ℕ}
    (hidx : (hc.CN t).relIndex (LB M Q B) = Nat.card Z ^ k) :
    n - 1 = k + 1 ∧ Nat.card ↥(LB M Q B) = Nat.card Q * Nat.card Z ^ (k + 1) := by
  have s5 := hs.toSec5
  have hLB := (stroth_3_5 h34 hc s5.width s5.n_gt s5.noA2 s5.gen).2.2.1
  have hne := not_LB_inf_CN_le_Q h311a hc hs (Rt_ne_LB h34 hc hs)
  set A : Subgroup G := hc.CN t ⊓ LB M Q B with hA
  have hQA : Q ≤ A := le_inf (hc.Q_le_CN s5.mem) sec39_Q_le_LB
  have hAN : A ≤ hc.CN t := inf_le_left
  obtain ⟨c, hc'⟩ : Nat.card Q ∣ Nat.card A := Subgroup.card_dvd_of_le hQA
  have hdvd : Nat.card A ∣ Nat.card Q * Nat.card Z := hs.cardN ▸ Subgroup.card_dvd_of_le hAN
  have hcq : c ∣ Nat.card Z := by
    rw [hc'] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.card_pos (α := Q)) hdvd
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc'
    omega
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [mul_one] at hc'
    exact hne (Subgroup.eq_of_le_of_card_ge hQA hc'.le).ge
  have hmul := Subgroup.relIndex_mul_card (H := hc.CN t) (K := LB M Q B)
  rw [hidx, ← hA, hc', hLB] at hmul
  have hpow : Nat.card Z ^ (n - 1) = c * Nat.card Z ^ k := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Q))
    calc Nat.card Q * Nat.card Z ^ (n - 1) = Nat.card Z ^ k * (Nat.card Q * c) := hmul.symm
      _ = Nat.card Q * (c * Nat.card Z ^ k) := by ring
  have hn1 : n - 1 = k + 1 := exp_succ_of_index (two_le_card_Z hc) (by omega) hcq hpow
  exact ⟨hn1, by rw [hLB, hn1]⟩

end HS6

end CFSG.RankThree.GF2n.Stroth80
