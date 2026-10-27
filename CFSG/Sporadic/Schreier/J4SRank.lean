
module

public import CFSG.Sporadic.Schreier.J4SRankBase

public import CFSG.Sporadic.Schreier.J4SRankCheck
public import CFSG.Sporadic.Schreier.J4SThree
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SInvData
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SRankData
public meta import CFSG.Sporadic.Schreier.J4SRankData
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.Schreier.J4SThreeDataInputs
public meta import CFSG.Sporadic.Schreier.J4SKCent
public import CFSG.Sporadic.J4.Local

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem rep_Q3GenPairs
    {i : ℕ} (hi : i < 2) : Rep Sp φ (q3gen i) Q3GenPairs[i]! := by
  rw [Q3GenPairs_eq hi]
  exact rep_powP (rep_wordP (rep_x j4Facts.mat) (rep_y j4Facts.mat) _) _

theorem q3Elt_parent
    {k : ℕ} (hk : k < 27) (hpos : 0 < k) :
    q3Elt k = q3Elt (q3Par[k]!)[0]! * q3gen (q3Par[k]!)[1]! := by
  obtain ⟨-, -, hpar, -⟩ := q3_all k hk
  obtain ⟨hp, hg, heq⟩ := hpar hpos
  generalize (q3Par[k]!)[0]! = p at hp heq ⊢
  generalize (q3Par[k]!)[1]! = g at hg heq ⊢
  have h := actsBy_mul (q3Elt_spec (by omega : p < 27)).2 (q3gen_acts hg)
  rw [← heq] at h
  exact eq_of_actsBy (Q3_le_K (q3Elt_spec hk).1)
    (K.mul_mem (Q3_le_K (q3Elt_spec (by omega : p < 27)).1) (q3gen_mem_K g)) (q3Elt_spec hk).2 h

theorem rep_q3PairK :
    ∀ k < 27, Rep Sp φ (q3Elt k) (q3PairK Q3GenPairs k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [q3PairK]
    split_ifs with h
    · rw [q3Elt_parent hk h.1]
      have hg := ((q3_all k hk).2.2.1 h.1).2.1
      exact rep_mulP (ih _ h.2 (by omega)) (rep_Q3GenPairs hg)
    · have hk0 : k = 0 := by
        by_contra hne
        exact h ⟨Nat.pos_of_ne_zero hne, ((q3_all k hk).2.2.1 (Nat.pos_of_ne_zero hne)).1⟩
      subst hk0
      rw [q3Elt_zero]
      exact rep_oneP

theorem card_J_eq :
    Nat.card J = 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43 := by
  rw [card_J j4Facts]; norm_num

theorem card_Q3_sylow_J :
    Nat.card Q3 = 3 ^ (Nat.card J).factorization 3 := by
  rw [card_Q3, card_J_eq]
  have h2 : Nat.Prime 2 := Nat.prime_two
  have h3 : Nat.Prime 3 := Nat.prime_three
  have h5 : Nat.Prime 5 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  have h11 : Nat.Prime 11 := by norm_num
  have h23 : Nat.Prime 23 := by norm_num
  have h29 : Nat.Prime 29 := by norm_num
  have h31 : Nat.Prime 31 := by norm_num
  have h37 : Nat.Prime 37 := by norm_num
  have h43 : Nat.Prime 43 := by norm_num
  repeat rw [Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Finsupp.add_apply, Nat.Prime.factorization_pow h2, Nat.Prime.factorization_pow h3,
    Nat.Prime.factorization h5, Nat.Prime.factorization h7, Nat.Prime.factorization_pow h11,
    Nat.Prime.factorization h23, Nat.Prime.factorization h29, Nat.Prime.factorization h31,
    Nat.Prime.factorization h37, Nat.Prime.factorization h43, Finsupp.single_apply]
  norm_num

theorem R3E_J4_elements_of_order_two_or_three_have_rank_at_least_three :
    ∀ g : J, (orderOf g = 2 ∨ orderOf g = 3) →
      3 ≤ (((g : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) - 1).rank := by
  intro g hg
  rw [← φ_apply]
  rcases hg with h2 | h3
  · obtain ⟨-, c, hc⟩ :=
      CTU_J4_every_inner_involution_conjugate_into_local_binary_subgroup g h2
    rw [← rank_conj c g]
    rcases hc with hc | hc <;> rw [hc]
    · exact three_le_rank_of_rep (rep_etaP j4Facts.mat 1) rows3_eta.1
    · exact three_le_rank_of_rep (rep_etaP j4Facts.mat 14) rows3_eta.2
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hP : IsPGroup 3 (Subgroup.zpowers g) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h3, pow_one])
    obtain ⟨c, hc⟩ := exists_conj_mem_sylow (Sylow.ofCard Q3 card_Q3_sylow_J) hP
    rw [Sylow.coe_ofCard] at hc
    obtain ⟨k, hk, hke⟩ := mem_Q3_iff.1 hc
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [q3Elt_zero] at hke
      have : g = 1 := by
        have e : g = c⁻¹ * (c * g * c⁻¹) * c := by group
        rw [e, ← hke]; group
      rw [this, orderOf_one] at h3
      omega
    rw [← rank_conj c g, ← hke]
    refine three_le_rank_of_rep (rep_q3PairK k hk) ?_
    have h := q3Rows_eq
    unfold q3RowsOK at h
    have := List.all_eq_true.1 h (k - 1) (List.mem_range.2 (by omega))
    rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)] at this

end CFSG.Sporadic.J4Schreier
