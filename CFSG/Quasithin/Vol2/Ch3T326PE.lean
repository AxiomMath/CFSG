module

public import CFSG.Quasithin.Vol2.Ch3T326PD
public import CFSG.Quasithin.Vol2.Ch3T326PC

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Open

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem mem_normalizer_of_comm {X : Subgroup (MulAut W)} {y : MulAut W}
    (hyX : ∀ l ∈ X, y * l = l * y) : y ∈ Subgroup.normalizer (X : Set (MulAut W)) := by
  refine Subgroup.mem_normalizer_iff.2 fun l => ⟨fun hl => ?_, fun hl => ?_⟩
  · rw [hyX l hl, mul_inv_cancel_right]
    exact hl
  · have h1 := hyX _ hl
    have h2 : y * l * y⁻¹ = l := mul_left_cancel (h1.trans (by group))
    rw [h2] at hl
    exact hl

theorem eq_two_pow_mul_five_pow {n : ℕ} (hn : n ≠ 0)
    (h : ∀ q : ℕ, q.Prime → q ∣ n → q = 2 ∨ q = 5) :
    n = 2 ^ n.factorization 2 * 5 ^ n.factorization 5 := by
  have hsupp : n.factorization.support ⊆ {2, 5} := by
    intro q hq
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hq
    rcases h q hq.1 hq.2.1 with rfl | rfl <;> simp
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => pow_zero _),
    Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 5)]

namespace O2Sit

variable {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
  (h : O2Sit M Mp T L V t)
include h

theorem comm_L {x : MulAut W} (hx : x ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) :
    ∀ l ∈ L, x * l = l * x := fun l hl =>
  (Subgroup.mem_centralizer_iff.1 hx.2 l (h.hB.L_le_Mp hl)).symm

theorem comm_Lt {x : MulAut W} (hx : x ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) :
    ∀ l ∈ conjAutSub t L, x * l = l * x := fun l hl =>
  (Subgroup.mem_centralizer_iff.1 hx.2 l (h.hB.Lt_le_Mp hl)).symm

theorem not_three_seven {x : MulAut W}
    (hx : x ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) {p : ℕ} (hp : p.Prime)
    (hxp : x ^ p = 1) (hx1 : x ≠ 1) (h37 : p = 3 ∨ p = 7) : False := by
  have hp2 : p ≠ 2 := by rcases h37 with rfl | rfl <;> norm_num
  have hpL : p ∣ Nat.card ↥L := by
    rw [card_eq_168_of_isPSL32 h.hL3]
    rcases h37 with rfl | rfl <;> norm_num
  exact hx1 (h.hB.eq_one_of_pow_prime hp hp2 hpL hx hxp)

theorem eq_five {x : MulAut W} (hx : x ∈ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hxp : x ^ p = 1) (hx1 : x ≠ 1) : p = 5 := by
  have hM := h.hB.hD.hyp.Mp_normal
  have hyp : ∀ (Y : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))),
      letI := qAct hM; ∀ q ∈ Y, (⟨x, hx.1⟩ : ↥M) ^ p • q = q := by
    intro Y
    let _i := qAct hM
    intro q _
    have h1 : (⟨x, hx.1⟩ : ↥M) ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hxp)
    rw [h1, one_smul]
  by_cases hU : ∀ u ∈ commV L, x u = u
  · have hU' : ∃ u ∈ commV (conjAutSub t L), x u ≠ u := by
      by_contra hcon
      push Not at hcon
      exact hx1 (h.eq_one_of_triv hU hcon)
    have hmove := move_tilde hM h.inf_fixV_Lt hx.1 (mem_normalizer_of_comm (h.comm_Lt hx)) hU'
    rcases prime_of_side h.hB.exp h.side' hx.1 (h.comm_Lt hx) hp hp2 (hyp _) hmove with
      h3 | h7 | ⟨h5, -⟩
    · exact (h.not_three_seven hx hp hxp hx1 (Or.inl h3)).elim
    · exact (h.not_three_seven hx hp hxp hx1 (Or.inr h7)).elim
    · exact h5
  · push Not at hU
    have hmove := move_tilde hM h.hZ hx.1 (mem_normalizer_of_comm (h.comm_L hx)) hU
    rcases prime_of_side h.hB.exp h.side hx.1 (h.comm_L hx) hp hp2 (hyp _) hmove with
      h3 | h7 | ⟨h5, -⟩
    · exact (h.not_three_seven hx hp hxp hx1 (Or.inl h3)).elim
    · exact (h.not_three_seven hx hp hxp hx1 (Or.inr h7)).elim
    · exact h5

theorem card_cent_eq :
    Nat.card ↥(M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) =
      2 ^ (Nat.card ↥(M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))).factorization 2 *
        5 ^ (Nat.card ↥(M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))).factorization 5 := by
  refine eq_two_pow_mul_five_pow Nat.card_pos.ne' fun q hq hqd => ?_
  by_cases hq2 : q = 2
  · exact Or.inl hq2
  · right
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(M ⊓ Subgroup.centralizer
      (Mp : Set (MulAut W)))) q hqd
    have hxq : (x : MulAut W) ^ q = 1 := by
      rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one]
      rfl
    have hx1 : (x : MulAut W) ≠ 1 := by
      intro h1
      have h2 : x = 1 := Subtype.ext h1
      rw [h2, orderOf_one] at hx
      exact hq.one_lt.ne hx
    exact h.eq_five x.2 hq hq2 hxq hx1

end O2Sit

end CFSG.Quasithin.H13.T326
