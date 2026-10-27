module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]
variable {A X Q : Subgroup (MulAut W)} {t : MulAut W}

private theorem w16g_two_mul_card_le_sum {ι : Type*} [Fintype ι] (f : ι → ℕ)
    (h2 : ∀ i, 2 ≤ f i) : 2 * Nat.card ι ≤ ∑ i, f i := by
  have h := Finset.sum_le_sum (s := Finset.univ) (f := fun _ : ι => 2) (g := f)
    (fun i _ => h2 i)
  rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    mul_comm] at h
  exact h

private theorem w16g_sum_le_of_two_le {ι : Type*} [Fintype ι] (f : ι → ℕ)
    (h2 : ∀ i, 2 ≤ f i) (h6 : ∑ i, f i ≤ 6) :
    ∀ i, f i ≤ 6 - 2 * (Nat.card ι - 1) := by
  classical
  intro i
  have hmem : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
  have hsplit : f i + ∑ j ∈ (Finset.univ : Finset ι).erase i, f j = ∑ j, f j :=
    Finset.add_sum_erase _ f hmem
  have hconst : ∑ j ∈ (Finset.univ : Finset ι).erase i, 2 = 2 * (Nat.card ι - 1) := by
    rw [Finset.sum_const, Finset.card_erase_of_mem hmem, Finset.card_univ, Nat.nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, mul_comm]
  have hb : 2 * (Nat.card ι - 1) ≤ ∑ j ∈ (Finset.univ : Finset ι).erase i, f j := by
    rw [← hconst]
    exact Finset.sum_le_sum fun j _ => h2 j
  have hmain : f i + 2 * (Nat.card ι - 1) ≤ 6 := by
    calc f i + 2 * (Nat.card ι - 1)
        ≤ f i + ∑ j ∈ (Finset.univ : Finset ι).erase i, f j := add_le_add le_rfl hb
      _ = ∑ j, f j := hsplit
      _ ≤ 6 := h6
  omega

private theorem w16g_dParam_three : dParam 3 = 2 := by
  rw [dParam]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (p := 2) (by decide) (by decide)

theorem s13_three_shape (h : HAb A X Q t 3)
    (hH0 : ∀ y ∈ X, y ≠ 1 → (s13Supp X (Subgroup.zpowers y)).ncard ≠ 1) :
    ((s13Supp X Q).ncard = 2 ∧ Nat.card ↥Q = 3) ∨ ((s13Supp X Q).ncard = 3 ∧ Nat.card ↥Q = 3) ∨
      ((s13Supp X Q).ncard = 3 ∧ Nat.card ↥Q = 9) := by
  classical
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : 3 ≠ 2 := by norm_num
  have hd3 : dParam 3 = 2 := w16g_dParam_three
  haveI : Finite (Subgroup W) :=
    Finite.of_injective (fun S : Subgroup W => (S : Set W)) SetLike.coe_injective
  haveI : Fintype {U : Subgroup W // U ∈ s13Supp X Q} := Fintype.ofFinite _
  have hSsub : s13Supp X Q ⊆ s13IsoComps X := fun U hU => hU.1
  have hSne : (s13Supp X Q).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hSempty
    apply h.hQ1
    have hcomm_bot : commSub ⊤ Q = ⊥ := by
      rw [commSub_top_eq_iSup_s13Supp h.hW hp3 hp32 h.hXe h.hQX, hSempty]
      simp
    apply le_bot_iff.mp
    intro q hq
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun w => ?_
    exact (mem_fixV.mp ((commSub_eq_bot_iff.mp hcomm_bot) trivial)) q hq
  have hsum_eq : (∑ i : {U : Subgroup W // U ∈ s13Supp X Q}, rk ↥(i.1)) =
      rk ↥(commSub ⊤ Q) := by
    rw [rk_commSub_top_eq_sum h.hW hp3 hp32 h.hXe h.hQX]
    rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
  have hsum_le : (∑ i : {U : Subgroup W // U ∈ s13Supp X Q}, rk ↥(i.1)) ≤ 6 := by
    rw [hsum_eq]
    exact (cost_commSub_Q h).2
  have h2rk : ∀ i : {U : Subgroup W // U ∈ s13Supp X Q}, 2 ≤ rk ↥(i.1) := by
    intro i
    obtain ⟨s, hs, hsrk⟩ := rk_s13IsoComps_eq h.hW hp3 hp32 h.hXe i.2.1
    rw [hd3] at hsrk
    omega
  have hcardle : (s13Supp X Q).ncard ≤ 3 := by
    have h2mul := w16g_two_mul_card_le_sum
      (fun i : {U : Subgroup W // U ∈ s13Supp X Q} => rk ↥(i.1)) h2rk
    have hcard : Nat.card {U : Subgroup W // U ∈ s13Supp X Q} = (s13Supp X Q).ncard :=
      Nat.card_coe_set_eq _
    rw [hcard] at h2mul
    omega
  have hne1 : (s13Supp X Q).ncard ≠ 1 := by
    intro h1
    obtain ⟨U, hU⟩ := Set.ncard_eq_one.mp h1
    obtain ⟨q, hqQ, hq1⟩ : ∃ q ∈ Q, q ≠ 1 := by
      by_contra hc
      push Not at hc
      exact h.hQ1 (le_bot_iff.mp fun q hq => by rw [Subgroup.mem_bot]; exact hc q hq)
    have hzple : Subgroup.zpowers q ≤ Q := Subgroup.zpowers_le.mpr hqQ
    have hsub : s13Supp X (Subgroup.zpowers q) ⊆ s13Supp X Q := by
      intro V hV
      exact ⟨hV.1, fun hbot =>
        hV.2 (le_bot_iff.mp ((commSub_mono le_rfl hzple).trans hbot.le))⟩
    have hne : (s13Supp X (Subgroup.zpowers q)).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hemp
      apply hq1
      have hcomm_bot : commSub ⊤ (Subgroup.zpowers q) = ⊥ := by
        rw [commSub_top_eq_iSup_s13Supp h.hW hp3 hp32 h.hXe
          (Subgroup.zpowers_le.mpr (h.hQX hqQ)), hemp]
        simp
      refine MulEquiv.ext fun w => ?_
      exact (mem_fixV.mp ((commSub_eq_bot_iff.mp hcomm_bot) trivial)) q (Subgroup.mem_zpowers q)
    have hsupp_eq : s13Supp X (Subgroup.zpowers q) = {U} := by
      rw [Set.eq_singleton_iff_nonempty_unique_mem]
      refine ⟨hne, ?_⟩
      intro V hV
      have hVS : V ∈ ({U} : Set (Subgroup W)) := by
        rw [← hU]
        exact hsub hV
      exact Set.mem_singleton_iff.mp hVS
    exact hH0 q (h.hQX hqQ) hq1 (by rw [hsupp_eq, Set.ncard_singleton])
  have hncard : (s13Supp X Q).ncard = 2 ∨ (s13Supp X Q).ncard = 3 := by
    have hpos : 0 < (s13Supp X Q).ncard := hSne.ncard_pos
    omega
  have hQle : Q ≤ s13XSupp X (s13Supp X Q) :=
    (le_s13XSupp_iff h.hW hp3 hp32 h.hXe h.hQX).mpr subset_rfl
  have hQcard_le : Nat.card ↥Q ≤ Nat.card ↥(s13XSupp X (s13Supp X Q)) :=
    Nat.le_of_dvd (card_subgroup_pos _) (Subgroup.card_dvd_of_le hQle)
  have hQcard_lt : Nat.card ↥(s13XSupp X (s13Supp X Q)) < 3 ^ (s13Supp X Q).ncard :=
    s13_card_XSupp_lt h.hW hp3 hp32 h.hXe hH0 hSsub hSne
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hpgQ : IsPGroup 3 ↥Q := by
    intro q
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (h.hXe.2 (q : MulAut W) (h.hQX q.2))
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpgQ
  have hQcard_ne1 : Nat.card ↥Q ≠ 1 := by
    intro h1
    exact h.hQ1 (Subgroup.card_eq_one.mp h1)
  have hn_pos : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      exact hQcard_ne1 (by rw [hn, h0]; norm_num)
    · exact hpos
  have hQ_lt : Nat.card ↥Q < 3 ^ (s13Supp X Q).ncard := lt_of_le_of_lt hQcard_le hQcard_lt
  rcases hncard with hS2 | hS3
  · left
    refine ⟨hS2, ?_⟩
    have hlt : 3 ^ n < 3 ^ 2 := by
      have h1 := hQ_lt
      rw [hn, hS2] at h1
      exact h1
    have hn2 : n < 2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hlt
    have hn1 : n = 1 := by omega
    rw [hn, hn1]
    norm_num
  · right
    have hlt : 3 ^ n < 3 ^ 3 := by
      have h1 := hQ_lt
      rw [hn, hS3] at h1
      exact h1
    have hn3 : n < 3 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hlt
    have hQcard : Nat.card ↥Q = 3 ∨ Nat.card ↥Q = 9 := by
      have hn12 : n = 1 ∨ n = 2 := by omega
      rcases hn12 with h1 | h2
      · left; rw [hn, h1]; norm_num
      · right; rw [hn, h2]; norm_num
    rcases hQcard with h | h
    · exact Or.inl ⟨hS3, h⟩
    · exact Or.inr ⟨hS3, h⟩

theorem s13_three_ranks (h : HAb A X Q t 3) :
    ((s13Supp X Q).ncard = 3 → ∀ U ∈ s13Supp X Q, rk ↥U = 2) ∧
      ((s13Supp X Q).ncard = 2 → ∀ U ∈ s13Supp X Q, rk ↥U = 2 ∨ rk ↥U = 4) := by
  classical
  have hp3 : Nat.Prime 3 := by norm_num
  have hp32 : 3 ≠ 2 := by norm_num
  have hd3 : dParam 3 = 2 := w16g_dParam_three
  haveI : Finite (Subgroup W) :=
    Finite.of_injective (fun S : Subgroup W => (S : Set W)) SetLike.coe_injective
  haveI : Fintype {U : Subgroup W // U ∈ s13Supp X Q} := Fintype.ofFinite _
  have hsum_eq : (∑ i : {U : Subgroup W // U ∈ s13Supp X Q}, rk ↥(i.1)) =
      rk ↥(commSub ⊤ Q) := by
    rw [rk_commSub_top_eq_sum h.hW hp3 hp32 h.hXe h.hQX]
    rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
  have hsum_le : (∑ i : {U : Subgroup W // U ∈ s13Supp X Q}, rk ↥(i.1)) ≤ 6 := by
    rw [hsum_eq]
    exact (cost_commSub_Q h).2
  have h2rk : ∀ i : {U : Subgroup W // U ∈ s13Supp X Q}, 2 ≤ rk ↥(i.1) := by
    intro i
    obtain ⟨s, hs, hsrk⟩ := rk_s13IsoComps_eq h.hW hp3 hp32 h.hXe i.2.1
    rw [hd3] at hsrk
    omega
  have hbound := w16g_sum_le_of_two_le
    (fun i : {U : Subgroup W // U ∈ s13Supp X Q} => rk ↥(i.1)) h2rk hsum_le
  have hcardN : Nat.card {U : Subgroup W // U ∈ s13Supp X Q} = (s13Supp X Q).ncard :=
    Nat.card_coe_set_eq _
  constructor
  · intro hcard U hU
    have hbnd : rk ↥U ≤ 6 - 2 * (Nat.card {U : Subgroup W // U ∈ s13Supp X Q} - 1) :=
      hbound ⟨U, hU⟩
    rw [hcardN, hcard] at hbnd
    have h2b : 2 ≤ rk ↥U := h2rk ⟨U, hU⟩
    omega
  · intro hcard U hU
    have hbnd : rk ↥U ≤ 6 - 2 * (Nat.card {U : Subgroup W // U ∈ s13Supp X Q} - 1) :=
      hbound ⟨U, hU⟩
    rw [hcardN, hcard] at hbnd
    obtain ⟨s, hs, hsrk⟩ := rk_s13IsoComps_eq h.hW hp3 hp32 h.hXe hU.1
    rw [hd3] at hsrk
    have hs12 : s = 1 ∨ s = 2 := by omega
    rcases hs12 with h1 | h2
    · left; rw [hsrk, h1]
    · right; rw [hsrk, h2]

end CFSG.LocalAnalysis.WeakClosure81
