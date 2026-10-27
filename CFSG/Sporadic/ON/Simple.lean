
module


public import CFSG.Sporadic.ON.Primitive

public section

namespace CFSG.Sporadic.ON

open Native
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.SmallF2.Native (ordOK)

theorem tupleEq_of_one {X : Table} (hX : Rep nPts X (1 : J)) :
    tupleEq (apT X chainQ) chainQ = true := by
  simp only [tupleEq, Bool.and_eq_true, beq_iff_eq, apT_size, true_and]
  rw [allIn_eq_true]
  intro t _ ht
  rw [apT_get _ _ ht, hX _ (chainQ_lt ht), idx_one]
  simp

theorem eq_one_of_tupleEq {g : J} {X : Table} (hX : Rep nPts X g)
    (h : tupleEq (apT X chainQ) chainQ = true) : g = 1 := by
  apply sep
  intro t ht
  simp only [tupleEq, Bool.and_eq_true, beq_iff_eq] at h
  have := (allIn_eq_true.1 h.2) t (Nat.zero_le _) ht
  simp only [beq_iff_eq] at this
  rw [apT_get _ _ ht, hX _ (chainQ_lt ht)] at this
  exact this

theorem orderOf_of_ordOK
    {g : J} {X : Table} (hX : Rep nPts X g) {pe : ℕ × ℕ}
    (hp : pe.1.Prime) (h : ordOK nPts chainQ X pe = true) : orderOf g = pe.1 ^ pe.2 := by
  simp only [ordOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨he, h1⟩, h2⟩ := h
  have : Fact pe.1.Prime := ⟨hp⟩
  have hpow1 : g ^ pe.1 ^ (pe.2 - 1 + 1) = 1 := by
    rw [Nat.sub_add_cancel he]
    exact eq_one_of_tupleEq (Rep.powT nPts_lt hX _) h1
  have hpow2 : ¬g ^ pe.1 ^ (pe.2 - 1) = 1 := by
    intro e
    have hR := Rep.powT nPts_lt hX (pe.1 ^ (pe.2 - 1))
    rw [e] at hR
    rw [tupleEq_of_one hR] at h2
    exact absurd h2 (by decide)
  have := orderOf_eq_prime_pow hpow2 hpow1
  rwa [Nat.sub_add_cancel he] at this

theorem ord_parts : ordOK nPts chainQ regsT[0]! (2, 1) = true ∧
    ordOK nPts chainQ regsT[1]! (19, 1) = true ∧
    ordOK nPts chainQ (compT nPts regsT[0]! regsT[1]!) (11, 1) = true := by
  have h := facts.ord
  unfold ordChecks at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem orderOf_a : orderOf a = 2 := by
  have := orderOf_of_ordOK rep_regsT_zero (pe := (2, 1)) Nat.prime_two ord_parts.1
  simpa using this

theorem orderOf_b : orderOf b = 19 := by
  have := orderOf_of_ordOK rep_regsT_one (pe := (19, 1)) (by norm_num) ord_parts.2.1
  simpa using this

theorem orderOf_ab : orderOf (a * b) = 11 := by
  have := orderOf_of_ordOK (Rep.compT rep_regsT_zero rep_regsT_one) (pe := (11, 1)) (by norm_num)
    ord_parts.2.2
  simpa using this

theorem isSimpleGroup_J : IsSimpleGroup J := by
  have := isPreprimitive
  refine isSimpleGroup_of_primitive_coprime_orders (Ω := Fin nLines) ?_ a b closure_ab line0 ?_ ?_
  · rw [Nat.card_fin]; decide
  · rw [orderOf_a, orderOf_b]; norm_num
  · rw [orderOf_ab, card_stabilizer_line0]; norm_num

theorem isSimpleGroup_ON :
    IsSimpleGroup Blueprint.NativeSporadic.ON :=
  @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_J onEquivJ

theorem card_ON_eq :
    Nat.card Blueprint.NativeSporadic.ON = 460815505920 := by
  rw [Nat.card_congr onEquivJ.toEquiv, card_J]

end CFSG.Sporadic.ON
