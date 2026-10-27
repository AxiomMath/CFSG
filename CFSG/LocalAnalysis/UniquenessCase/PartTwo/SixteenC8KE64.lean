module

import CFSG.Quasithin.H13.GoldschmidtC137SQL32
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.A1bPGroups

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

private theorem c8_e64_card_elem {p n : ℕ} {X : Type} [Group X]
    (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem c8_e64_rank_comm_pow {p n : ℕ} {X : Type} [Group X]
    (h : IsElemAbelianOfRank p n X) :
    (∀ a b : X, a * b = b * a) ∧ ∀ a : X, a ^ p = 1 := by
  obtain ⟨e⟩ := h
  refine ⟨fun a b => e.injective ?_, fun a => e.injective ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · rw [map_pow, map_one]
    ext i
    simp

theorem c8_e64_le_of_no_three {P : Type} [Group P] [Finite P] {N M : Subgroup P} [N.Normal]
    (hL : IsL3 (P ⧸ N) 1) (hM : M.Normal) (h3 : ∀ x ∈ M, ¬ 3 ∣ orderOf x) : M ≤ N := by
  obtain ⟨hsimp, hcardL⟩ :=
    CFSG.Quasithin.H13.U3.GC137.SQ.simple_card_of_lieModel_psl_three_two hL
  have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  haveI : (M.map (QuotientGroup.mk' N)).Normal := hM.map _ hsurj
  rcases hsimp.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' N)) with hbot | htop
  · rw [Subgroup.map_eq_bot_iff] at hbot
    intro m hm
    have hmker : m ∈ (QuotientGroup.mk' N).ker := hbot hm
    rwa [QuotientGroup.ker_mk'] at hmker
  · exfalso
    have h3dvd : 3 ∣ Nat.card (P ⧸ N) := by rw [hcardL]; norm_num
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
    have hyM : y ∈ M.map (QuotientGroup.mk' N) := by rw [htop]; exact Subgroup.mem_top y
    rw [Subgroup.mem_map] at hyM
    obtain ⟨m, hm, hmy⟩ := hyM
    have hdvd : 3 ∣ orderOf m := by
      rw [← hy, ← hmy]
      exact orderOf_map_dvd (QuotientGroup.mk' N) m
    exact h3 m hm hdvd

theorem c8_e64_card {P : Type} [Group P] [Finite P] {N : Subgroup P} [N.Normal]
    (hN : IsElemAbelianOfRank 2 6 ↥N) (hL : IsL3 (P ⧸ N) 1) : Nat.card P = 10752 := by
  obtain ⟨-, hcardL⟩ :=
    CFSG.Quasithin.H13.U3.GC137.SQ.simple_card_of_lieModel_psl_three_two hL
  have hcardN : Nat.card ↥N = 2 ^ 6 := c8_e64_card_elem hN
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hcardL, hcardN]
  norm_num

theorem c8_e64_eq_top {P : Type} [Group P] [Finite P] {N : Subgroup P} [N.Normal]
    (hN : IsElemAbelianOfRank 2 6 ↥N) (hL : IsL3 (P ⧸ N) 1) (hperf : Group.IsPerfect P)
    {R : Subgroup P} (hR : R.Normal) (h3 : ∀ x : P, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ∈ R) :
    R = ⊤ := by
  obtain ⟨hsimp, hcardL⟩ :=
    CFSG.Quasithin.H13.U3.GC137.SQ.simple_card_of_lieModel_psl_three_two hL
  haveI : R.Normal := hR
  have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have h3dvd : 3 ∣ Nat.card (P ⧸ N) := by rw [hcardL]; norm_num
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  obtain ⟨x, hx⟩ := hsurj y
  have hm0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨e, b, hb, hxb⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 3 (by norm_num)
  have hxb1 : (x ^ b) ^ 3 ^ e = 1 := by
    rw [← pow_mul, show b * 3 ^ e = orderOf x by rw [hxb, Nat.mul_comm], pow_orderOf_eq_one]
  have hπb : (QuotientGroup.mk' N) (x ^ b) ≠ 1 := by
    rw [map_pow, hx]
    intro h
    have hord : orderOf (y ^ b) = 3 := by
      rw [Nat.Coprime.orderOf_pow (by
        rw [hy]; exact Nat.prime_three.coprime_iff_not_dvd.mpr hb), hy]
    rw [h, orderOf_one] at hord
    norm_num at hord
  have hx0R : x ^ b ∈ R := h3 (x ^ b) ⟨e, hxb1⟩
  haveI : (R.map (QuotientGroup.mk' N)).Normal := hR.map _ hsurj
  have hRtop : R.map (QuotientGroup.mk' N) = ⊤ := by
    rcases hsimp.eq_bot_or_eq_top_of_normal (R.map (QuotientGroup.mk' N)) with hbot | htop
    · rw [Subgroup.map_eq_bot_iff] at hbot
      exact absurd (MonoidHom.mem_ker.1 (hbot hx0R)) hπb
    · exact htop
  have hsplit : ∀ g : P, ∃ r ∈ R, ∃ n : ↥N, g = r * (n : P) := by
    intro g
    have hg : (QuotientGroup.mk' N) g ∈ R.map (QuotientGroup.mk' N) := by
      rw [hRtop]; exact Subgroup.mem_top _
    rw [Subgroup.mem_map] at hg
    obtain ⟨r, hr, hrπ⟩ := hg
    refine ⟨r, hr, ⟨r⁻¹ * g, ?_⟩, ?_⟩
    · have h1 : (QuotientGroup.mk' N) (r⁻¹ * g) = 1 := by
        rw [map_mul, map_inv, hrπ, inv_mul_cancel]
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h1
    · rw [mul_inv_cancel_left]
  have hcommN : ∀ a b : ↥N, a * b = b * a := (c8_e64_rank_comm_pow hN).1
  have hcomm : ∀ a b : P, ⁅a, b⁆ ∈ R := by
    intro a b
    obtain ⟨r, hr, n, ha⟩ := hsplit a
    obtain ⟨r', hr', n', hb⟩ := hsplit b
    have ha' : (QuotientGroup.mk' R) a = (QuotientGroup.mk' R) (n : P) := by
      rw [ha, map_mul]
      have : (QuotientGroup.mk' R) r = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact hr
      rw [this, one_mul]
    have hb' : (QuotientGroup.mk' R) b = (QuotientGroup.mk' R) (n' : P) := by
      rw [hb, map_mul]
      have : (QuotientGroup.mk' R) r' = 1 := by
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact hr'
      rw [this, one_mul]
    have h1 : ⁅(n : P), (n' : P)⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (congrArg (fun z : ↥N => (z : P)) (hcommN n n'))
    have hker : (QuotientGroup.mk' R) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, ha', hb', ← map_commutatorElement, h1, map_one]
    rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hker
  have hle : commutator P ≤ R := Subgroup.commutator_le.mpr fun a _ b _ => hcomm a b
  rw [hperf.commutator_eq_top] at hle
  exact top_le_iff.mp hle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
