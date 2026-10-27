module

public import CFSG.Monster.Griess.TrialityBasis.Classes
public import CFSG.Monster.Griess.Space

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin Matrix

abbrev ltEdge (p : LtPair) : Sym2 (Fin 24) := s(p.1.1, p.1.2)

@[expose] def IsPairTriangle (p q r : LtPair) : Prop :=
  ∃ i j k : Fin 24, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
    ltEdge p = s(i, j) ∧ ltEdge q = s(i, k) ∧ ltEdge r = s(j, k)

noncomputable instance (p q r : LtPair) : Decidable (IsPairTriangle p q r) := Classical.dec _

theorem IsPairTriangle.swap12 {p q r : LtPair} (h : IsPairTriangle p q r) :
    IsPairTriangle q p r := by
  obtain ⟨i, j, k, hij, hik, hjk, hp, hq, hr⟩ := h
  exact ⟨i, k, j, hik, hij, Ne.symm hjk, hq, hp, hr.trans Sym2.eq_swap⟩

theorem IsPairTriangle.cycle {p q r : LtPair} (h : IsPairTriangle p q r) :
    IsPairTriangle q r p := by
  obtain ⟨i, j, k, hij, hik, hjk, hp, hq, hr⟩ := h
  exact ⟨k, i, j, Ne.symm hik, Ne.symm hjk, hij, hq.trans Sym2.eq_swap, hr.trans Sym2.eq_swap, hp⟩

namespace TwoCoordInvariance

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem ltEdge_not_isDiag (p : LtPair) : ¬ (ltEdge p).IsDiag := by
  rw [Sym2.mk_isDiag_iff]
  exact p.2.ne

theorem ltEdge_injective : Function.Injective ltEdge := by
  intro p q h
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ltPair_eq h1 h2
  · have h3 : q.1.2 < q.1.1 := by
      rw [← h1, ← h2]
      exact p.2
    exact absurd q.2 (lt_asymm h3)

private theorem ind3 (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] :
    (if a then (1 : ℚ) else 0) * (if b then 1 else 0) * (if c then 1 else 0) =
      if a ∧ b ∧ c then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> simp [ha, hb, hc]

theorem walk_unique {p q : LtPair} {i j k : Fin 24} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hp : ltEdge p = s(i, j)) (hq : ltEdge q = s(i, k)) {a b c : Fin 24}
    (h1 : s(a, b) = ltEdge p) (h2 : s(b, c) = ltEdge q) : a = j ∧ b = i ∧ c = k := by
  rw [hp] at h1
  rw [hq] at h2
  have hb : b = i := by
    have hb1 : b = i ∨ b = j := Sym2.mem_iff.1 (h1 ▸ Sym2.mem_mk_right a b)
    have hb2 : b = i ∨ b = k := Sym2.mem_iff.1 (h2 ▸ Sym2.mem_mk_left b c)
    rcases hb1 with hb1 | hb1
    · exact hb1
    · rcases hb2 with hb2 | hb2
      · exact hb2
      · exact absurd (hb1.symm.trans hb2) hjk
  subst hb
  have ha : a = j := by
    rcases Sym2.eq_iff.1 h1 with ⟨h, h'⟩ | ⟨h, -⟩
    · exact absurd h' hij
    · exact h
  have hc : c = k := by
    rcases Sym2.eq_iff.1 h2 with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hik
  exact ⟨ha, rfl, hc⟩

theorem isPairTriangle_of_walk {p q r : LtPair} {a b c : Fin 24} (h1 : s(a, b) = ltEdge p)
    (h2 : s(b, c) = ltEdge q) (h3 : s(c, a) = ltEdge r) : IsPairTriangle p q r := by
  have hab : a ≠ b := fun h => ltEdge_not_isDiag p (h1 ▸ Sym2.mk_isDiag_iff.2 h)
  have hbc : b ≠ c := fun h => ltEdge_not_isDiag q (h2 ▸ Sym2.mk_isDiag_iff.2 h)
  have hca : c ≠ a := fun h => ltEdge_not_isDiag r (h3 ▸ Sym2.mk_isDiag_iff.2 h)
  exact ⟨b, a, c, Ne.symm hab, hbc, Ne.symm hca, h1.symm.trans Sym2.eq_swap, h2.symm,
    h3.symm.trans Sym2.eq_swap⟩

theorem trace_basisA_mul3 (p q r : LtPair) :
    trace ((basisA (ltEdge p) : Matrix (Fin 24) (Fin 24) ℚ) *
      (basisA (ltEdge q) : Matrix (Fin 24) (Fin 24) ℚ) *
      (basisA (ltEdge r) : Matrix (Fin 24) (Fin 24) ℚ)) = if IsPairTriangle p q r then 1 else 0 := by
  have e : trace ((basisA (ltEdge p) : Matrix (Fin 24) (Fin 24) ℚ) *
      (basisA (ltEdge q) : Matrix (Fin 24) (Fin 24) ℚ) *
      (basisA (ltEdge r) : Matrix (Fin 24) (Fin 24) ℚ)) = ∑ a, ∑ c, ∑ b,
        if s(a, b) = ltEdge p ∧ s(b, c) = ltEdge q ∧ s(c, a) = ltEdge r then (1 : ℚ) else 0 := by
    simp only [trace, diag, mul_apply, basisA_apply, Finset.sum_mul, ind3]
  rw [e]
  by_cases h : IsPairTriangle p q r
  · rw [ite_eq_left h]
    obtain ⟨i, j, k, hij, hik, hjk, hp, hq, hr⟩ := h
    have uniq := @walk_unique p q i j k hij hik hjk hp hq
    rw [Finset.sum_eq_single j, Finset.sum_eq_single k, Finset.sum_eq_single i]
    · rw [ite_eq_left ⟨Sym2.eq_swap.trans hp.symm, hq.symm, Sym2.eq_swap.trans hr.symm⟩]
    · intro b _ hb
      exact ite_eq_right fun h' => hb (uniq h'.1 h'.2.1).2.1
    · intro h'
      exact absurd (Finset.mem_univ _) h'
    · intro c _ hc
      refine Finset.sum_eq_zero fun b _ => ite_eq_right fun h' => hc ?_
      exact (uniq h'.1 h'.2.1).2.2
    · intro h'
      exact absurd (Finset.mem_univ _) h'
    · intro a _ ha
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun b _ => ite_eq_right fun h' => ?_
      exact ha (uniq h'.1 h'.2.1).1
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun b _ => ite_eq_right fun h' => h ?_
    exact isPairTriangle_of_walk h'.1 h'.2.1 h'.2.2

@[expose] def edgeVec (p : LtPair) : Fin 24 → ZMod 2 := Pi.single p.1.1 1 + Pi.single p.1.2 1

theorem edgeVec_apply (p : LtPair) (k : Fin 24) :
    edgeVec p k = if k ∈ ltEdge p then 1 else 0 := by
  have hne : p.1.1 ≠ p.1.2 := p.2.ne
  simp only [edgeVec, Pi.add_apply, Pi.single_apply, Sym2.mem_iff]
  by_cases h1 : k = p.1.1
  · have h2 : k ≠ p.1.2 := fun h2 => hne (h1.symm.trans h2)
    simp [h1, hne]
  · by_cases h2 : k = p.1.2
    · simp [h2, Ne.symm hne]
    · simp [h1, h2]

private theorem sum3_ind_zero (x y z : Prop) [Decidable x] [Decidable y] [Decidable z] :
    ((if x then (1 : ZMod 2) else 0) + (if y then 1 else 0) + (if z then 1 else 0) = 0) ↔
      ((x ↔ y) ↔ ¬ z) := by
  by_cases hx : x <;> by_cases hy : y <;> by_cases hz : z <;> simp only [hx, hy, hz] <;> decide

theorem isPairTriangle_of_forall {p q r : LtPair}
    (h : ∀ k, ((k ∈ ltEdge p ↔ k ∈ ltEdge q) ↔ k ∉ ltEdge r)) : IsPairTriangle p q r := by
  have hab : p.1.1 ≠ p.1.2 := p.2.ne
  have hpa : p.1.1 ∈ ltEdge p := Sym2.mem_mk_left _ _
  have hpb : p.1.2 ∈ ltEdge p := Sym2.mem_mk_right _ _
  have memp : ∀ k, k ∈ ltEdge p ↔ k = p.1.1 ∨ k = p.1.2 := fun k => Sym2.mem_iff
  have ha := h p.1.1
  have hb := h p.1.2
  simp only [hpa, hpb, true_iff] at ha hb
  by_cases haq : p.1.1 ∈ ltEdge q
  · have har : p.1.1 ∉ ltEdge r := ha.1 haq
    by_cases hbq : p.1.2 ∈ ltEdge q
    ·
      exfalso
      have hbr : p.1.2 ∉ ltEdge r := hb.1 hbq
      have hq : ltEdge q = s(p.1.1, p.1.2) := (Sym2.mem_and_mem_iff hab).1 ⟨haq, hbq⟩
      have hc : r.1.1 ∈ ltEdge r := Sym2.mem_mk_left _ _
      have hca : r.1.1 ≠ p.1.1 := fun e => har (e ▸ hc)
      have hcb : r.1.1 ≠ p.1.2 := fun e => hbr (e ▸ hc)
      have hcp : r.1.1 ∉ ltEdge p := fun e => ((memp _).1 e).elim hca hcb
      have hcq : r.1.1 ∉ ltEdge q := by
        rw [hq]
        exact hcp
      exact ((h r.1.1).1 (iff_of_false hcp hcq)) hc
    · have hbr : p.1.2 ∈ ltEdge r := by
        by_contra hbr
        exact hbq (hb.2 hbr)
      set c := Sym2.Mem.other haq with hc_def
      have hq : s(p.1.1, c) = ltEdge q := Sym2.other_spec haq
      have hcq : c ∈ ltEdge q := Sym2.other_mem haq
      have hca : c ≠ p.1.1 := Sym2.other_ne (ltEdge_not_isDiag q) haq
      have hcb : c ≠ p.1.2 := fun e => hbq (e ▸ hcq)
      have hcp : c ∉ ltEdge p := fun e => ((memp _).1 e).elim hca hcb
      have hcr : c ∈ ltEdge r := by
        by_contra hcr
        exact hcp (((h c).2 hcr).2 hcq)
      have hr : ltEdge r = s(p.1.2, c) := (Sym2.mem_and_mem_iff (Ne.symm hcb)).1 ⟨hbr, hcr⟩
      exact ⟨p.1.1, p.1.2, c, hab, Ne.symm hca, Ne.symm hcb, rfl, hq.symm, hr⟩
  · have har : p.1.1 ∈ ltEdge r := by
      by_contra har
      exact haq (ha.2 har)
    by_cases hbq : p.1.2 ∈ ltEdge q
    ·
      set c := Sym2.Mem.other hbq with hc_def
      have hq : s(p.1.2, c) = ltEdge q := Sym2.other_spec hbq
      have hcq : c ∈ ltEdge q := Sym2.other_mem hbq
      have hcb : c ≠ p.1.2 := Sym2.other_ne (ltEdge_not_isDiag q) hbq
      have hca : c ≠ p.1.1 := fun e => haq (e ▸ hcq)
      have hcp : c ∉ ltEdge p := fun e => ((memp _).1 e).elim hca hcb
      have hcr : c ∈ ltEdge r := by
        by_contra hcr
        exact hcp (((h c).2 hcr).2 hcq)
      have hr : ltEdge r = s(p.1.1, c) := (Sym2.mem_and_mem_iff (Ne.symm hca)).1 ⟨har, hcr⟩
      exact ⟨p.1.2, p.1.1, c, Ne.symm hab, Ne.symm hcb, Ne.symm hca, Sym2.eq_swap, hq.symm, hr⟩
    ·
      exfalso
      have hbr : p.1.2 ∈ ltEdge r := by
        by_contra hbr
        exact hbq (hb.2 hbr)
      have hr : ltEdge r = s(p.1.1, p.1.2) := (Sym2.mem_and_mem_iff hab).1 ⟨har, hbr⟩
      have hc : q.1.1 ∈ ltEdge q := Sym2.mem_mk_left _ _
      have hca : q.1.1 ≠ p.1.1 := fun e => haq (e ▸ hc)
      have hcb : q.1.1 ≠ p.1.2 := fun e => hbq (e ▸ hc)
      have hcp : q.1.1 ∉ ltEdge p := fun e => ((memp _).1 e).elim hca hcb
      have hcr : q.1.1 ∉ ltEdge r := by
        rw [hr]
        exact hcp
      exact (((h q.1.1).2 hcr).2 hc) |> hcp

theorem forall_of_isPairTriangle {p q r : LtPair} (h : IsPairTriangle p q r) (k : Fin 24) :
    ((k ∈ ltEdge p ↔ k ∈ ltEdge q) ↔ k ∉ ltEdge r) := by
  obtain ⟨i, j, l, hij, hil, hjl, hp, hq, hr⟩ := h
  rw [hp, hq, hr, Sym2.mem_iff, Sym2.mem_iff, Sym2.mem_iff]
  by_cases hi : k = i
  · subst hi
    simp [hij, hil]
  · by_cases hj : k = j
    · subst hj
      simp [hi, hjl]
    · by_cases hl : k = l
      · subst hl
        simp [hi, hj]
      · simp [hi, hj, hl]

theorem edgeVec_sum_eq_zero_iff (p q r : LtPair) :
    edgeVec p + edgeVec q + edgeVec r = 0 ↔ IsPairTriangle p q r := by
  constructor
  · intro h
    refine isPairTriangle_of_forall fun k => ?_
    have hk := congrFun h k
    simp only [Pi.add_apply, Pi.zero_apply, edgeVec_apply] at hk
    exact (sum3_ind_zero _ _ _).1 hk
  · intro h
    funext k
    simp only [Pi.add_apply, Pi.zero_apply, edgeVec_apply]
    exact (sum3_ind_zero _ _ _).2 (forall_of_isPairTriangle h k)

theorem hammingNorm_edgeVec_sum_le (p q r : LtPair) :
    hammingNorm (edgeVec p + edgeVec q + edgeVec r) ≤ 6 := by
  refine le_trans (Finset.card_le_card ?_)
    (Finset.card_le_six (a := p.1.1) (b := p.1.2) (c := q.1.1) (d := q.1.2) (e := r.1.1)
      (f := r.1.2))
  intro k hk
  rw [Finset.mem_filter] at hk
  by_contra hk'
  apply hk.2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hk'
  simp [edgeVec, h1, h2, h3, h4, h5, h6]

theorem edgeVec_sum_mem_C_iff (p q r : LtPair) :
    edgeVec p + edgeVec q + edgeVec r ∈ C ↔ edgeVec p + edgeVec q + edgeVec r = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ C.zero_mem⟩
  by_contra h0
  have := eight_le_wt h h0
  have := hammingNorm_edgeVec_sum_le p q r
  omega

theorem deltaPair_eq_mk (p : LtPair) :
    deltaPair p.1.1 p.1.2 = Submodule.Quotient.mk (edgeVec p) := rfl

private theorem zmod2_sub_eq_add : ∀ a b : ZMod 2, a - b = a + b := by decide

theorem deltaPair_eq_add_iff (p q r : LtPair) :
    deltaPair r.1.1 r.1.2 = deltaPair p.1.1 p.1.2 + deltaPair q.1.1 q.1.2 ↔
      IsPairTriangle p q r := by
  rw [deltaPair_eq_mk, deltaPair_eq_mk, deltaPair_eq_mk, ← Submodule.Quotient.mk_add,
    Submodule.Quotient.eq]
  have e : edgeVec r - (edgeVec p + edgeVec q) = edgeVec p + edgeVec q + edgeVec r := by
    funext k
    simp only [Pi.sub_apply, Pi.add_apply, zmod2_sub_eq_add]
    ring
  rw [e, edgeVec_sum_mem_C_iff, edgeVec_sum_eq_zero_iff]

theorem pair_ΩC_deltaPair (p : LtPair) : pair ΩC (deltaPair p.1.1 p.1.2) = 0 := by
  rw [deltaPair_eq_mk, pair_mk, edgeVec, dotProduct_add, dotProduct_single, dotProduct_single,
    coe_ΩC]
  simp only [Ω, mul_one]
  decide

end TwoCoordInvariance

end CFSG.Monster.Griess
