module

public import CFSG.Permutation.FiveTransitive.Degree16
public import CFSG.Permutation.FiveTransitive.Degree15FourTuples

public section

namespace CFSG

namespace FiveTransitive.Degree16

open MulAction SubMulAction Subgroup

private theorem sylow_prime_fixed_pair_bound
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 16)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    {p : ℕ} (hp : p.Prime) (hpCases : p = 11 ∨ p = 13)
    (S₀ : Sylow p P) (hS₀card : Nat.card S₀ = p) :
    let N := Subgroup.normalizer (S₀ : Set P)
    N.index * (p - 1) * (16 - p).descFactorial 2 ≤ Nat.card P := by
  classical
  dsimp
  letI : Fact p.Prime := ⟨hp⟩
  let A := Degree15.NonidentitySylowElements p P
  let val : A → P :=
    Degree15.nonidentitySylowElementVal p P
  have horder (a : A) : orderOf (val a) = p := by
    rcases a with ⟨S, u⟩
    change orderOf ((u.1 : S) : P) = p
    calc
      orderOf ((u.1 : S) : P) = orderOf u.1 :=
        Subgroup.orderOf_coe _
      _ = p := Degree15.orderOf_eq_prime_of_card_eq_prime
        (Degree15.sylow_card_eq_of_card_eq S₀ hS₀card S) u.2
  have hfixed (a : A) :
      Fintype.card (MulAction.fixedBy X (val a)) = 16 - p := by
    let g : Equiv.Perm X := (val a : P)
    have hgorder : orderOf g = p := by
      calc
        orderOf g = orderOf (val a) := Subgroup.orderOf_coe _
        _ = p := horder a
    have hgcycle : g.IsCycle :=
      Equiv.Perm.isCycle_of_prime_order' (by
        rw [hgorder]
        exact hp) (by
          rw [hcard, hgorder]
          rcases hpCases with rfl | rfl <;> norm_num)
    have hgsupport : g.support.card = p := by
      rw [← hgcycle.orderOf, hgorder]
    rw [Degree15.card_fixedBy_subgroup_perm, hcard]
    change 16 - g.support.card = 16 - p
    rw [hgsupport]
  let T := Fin 2 ↪ X
  have hfixedPair (a : A) :
      Fintype.card (MulAction.fixedBy T (val a)) =
        (16 - p).descFactorial 2 := by
    change
      Fintype.card (MulAction.fixedBy (Fin 2 ↪ X) (val a)) =
        (16 - p).descFactorial 2
    calc
      Fintype.card (MulAction.fixedBy (Fin 2 ↪ X) (val a)) =
          (Fintype.card (MulAction.fixedBy X (val a))).descFactorial
            (Fintype.card (Fin 2)) :=
        Degree15.card_fixedBy_embedding (val a)
      _ = (16 - p).descFactorial 2 := by
        rw [hfixed, Fintype.card_fin]
  have hvalInjective : Function.Injective val :=
    Degree15.nonidentitySylowElementVal_injective S₀ hS₀card
  let N : Subgroup P :=
    Subgroup.normalizer (S₀ : Set P)
  have hAcard :
      Fintype.card A = N.index * (p - 1) := by
    rw [show Fintype.card A =
        Fintype.card (Sylow p P) * (p - 1) by
      exact Degree15.card_nonidentitySylowElements S₀ hS₀card]
    rw [← Nat.card_eq_fintype_card,
      S₀.card_eq_index_normalizer]
  have hselectedSum :
      (∑ a : A,
          Fintype.card (MulAction.fixedBy T (val a))) =
        N.index * (p - 1) * (16 - p).descFactorial 2 := by
    simp_rw [hfixedPair]
    simp [hAcard]
  have hselectedLe :
      (∑ a : A,
          Fintype.card (MulAction.fixedBy T (val a))) ≤
        ∑ q : P, Fintype.card (MulAction.fixedBy T q) := by
    calc
      (∑ a : A,
          Fintype.card (MulAction.fixedBy T (val a))) =
          ∑ q ∈ Finset.univ.image val,
            Fintype.card (MulAction.fixedBy T q) := by
        rw [Finset.sum_image hvalInjective.injOn]
      _ ≤ ∑ q ∈ (Finset.univ : Finset P),
          Fintype.card (MulAction.fixedBy T q) :=
        Finset.sum_le_sum_of_subset (by simp)
      _ = ∑ q : P, Fintype.card (MulAction.fixedBy T q) := by
        simp
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  have hP2 : MulAction.IsMultiplyPretransitive P X 2 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 2) (n := 5) (by omega) (by
        rw [Nat.card_eq_fintype_card, hcard]
        omega)
  letI : MulAction.IsPretransitive P T := by
    change MulAction.IsMultiplyPretransitive P X 2
    exact hP2
  letI : Nonempty T := Fintype.card_pos_iff.mp (by
    change 0 < Fintype.card (Fin 2 ↪ X)
    rw [Fintype.card_embedding_eq, Fintype.card_fin, hcard]
    norm_num)
  letI : Unique (MulAction.orbitRel.Quotient P T) :=
    Classical.choice
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
        P T).mp hP2)
  have hburnside :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group P T
  have hburnside' :
      (∑ q : P, Fintype.card (MulAction.fixedBy T q)) =
        Nat.card P := by
    rw [Fintype.card_unique, one_mul,
      ← Nat.card_eq_fintype_card] at hburnside
    exact hburnside
  calc
    N.index * (p - 1) * (16 - p).descFactorial 2 =
        ∑ a : A,
          Fintype.card (MulAction.fixedBy T (val a)) :=
      hselectedSum.symm
    _ ≤ ∑ q : P, Fintype.card (MulAction.fixedBy T q) :=
      hselectedLe
    _ = Nat.card P := hburnside'

theorem two_family_fixed_pair_bound
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 16)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (A B : Type) [Fintype A] [Fintype B]
    (valA : A → P) (valB : B → P)
    (hvalInjective : Function.Injective (Sum.elim valA valB))
    (cA cB : ℕ)
    (hfixedA :
      ∀ a : A,
        Fintype.card
          (MulAction.fixedBy (Fin 2 ↪ X) (valA a)) = cA)
    (hfixedB :
      ∀ b : B,
        Fintype.card
          (MulAction.fixedBy (Fin 2 ↪ X) (valB b)) = cB) :
    Fintype.card A * cA + Fintype.card B * cB ≤ Nat.card P := by
  classical
  let T := Fin 2 ↪ X
  let val : A ⊕ B → P := Sum.elim valA valB
  have hselectedSum :
      (∑ a : A ⊕ B,
          Fintype.card (MulAction.fixedBy T (val a))) =
        Fintype.card A * cA + Fintype.card B * cB := by
    rw [Fintype.sum_sum_type]
    change
      (∑ a : A,
          Fintype.card (MulAction.fixedBy (Fin 2 ↪ X) (valA a))) +
        (∑ b : B,
          Fintype.card (MulAction.fixedBy (Fin 2 ↪ X) (valB b))) =
        Fintype.card A * cA + Fintype.card B * cB
    simp_rw [hfixedA, hfixedB]
    simp
  have hselectedLe :
      (∑ a : A ⊕ B,
          Fintype.card (MulAction.fixedBy T (val a))) ≤
        ∑ q : P, Fintype.card (MulAction.fixedBy T q) := by
    calc
      (∑ a : A ⊕ B,
          Fintype.card (MulAction.fixedBy T (val a))) =
          ∑ q ∈ Finset.univ.image val,
            Fintype.card (MulAction.fixedBy T q) := by
        rw [Finset.sum_image hvalInjective.injOn]
      _ ≤ ∑ q ∈ (Finset.univ : Finset P),
          Fintype.card (MulAction.fixedBy T q) :=
        Finset.sum_le_sum_of_subset (by simp)
      _ = ∑ q : P, Fintype.card (MulAction.fixedBy T q) := by
        simp
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  have hP2 : MulAction.IsMultiplyPretransitive P X 2 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 2) (n := 5) (by omega) (by
        rw [Nat.card_eq_fintype_card, hcard]
        omega)
  letI : MulAction.IsPretransitive P T := by
    change MulAction.IsMultiplyPretransitive P X 2
    exact hP2
  letI : Nonempty T := Fintype.card_pos_iff.mp (by
    change 0 < Fintype.card (Fin 2 ↪ X)
    rw [Fintype.card_embedding_eq, Fintype.card_fin, hcard]
    norm_num)
  letI : Unique (MulAction.orbitRel.Quotient P T) :=
    Classical.choice
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
        P T).mp hP2)
  have hburnside :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group P T
  have hburnside' :
      (∑ q : P, Fintype.card (MulAction.fixedBy T q)) =
        Nat.card P := by
    rw [Fintype.card_unique, one_mul,
      ← Nat.card_eq_fintype_card] at hburnside
    exact hburnside
  calc
    Fintype.card A * cA + Fintype.card B * cB =
        ∑ a : A ⊕ B,
          Fintype.card (MulAction.fixedBy T (val a)) :=
      hselectedSum.symm
    _ ≤ ∑ q : P, Fintype.card (MulAction.fixedBy T q) :=
      hselectedLe
    _ = Nat.card P := hburnside'

private def degreeSixteenFixedPairArithmeticPredicate
    (x : Fin 60 × Fin 6 × Fin 4) : Prop :=
  let k := degreeSixteenDivisor7920 x.1
  let d13 := degreeSixteenDivisor12 x.2.1
  let d11 := degreeSixteenDivisor10 x.2.2
  (524160 * k / (13 * d13)) % 13 = 1 →
    (524160 * k / (13 * d13)) * 12 * 6 ≤ 524160 * k →
    (11 ∣ k →
      (524160 * k / (11 * d11)) % 11 = 1 ∧
      (524160 * k / (11 * d11)) * 10 * 20 ≤ 524160 * k) →
    k = 12 ∨ k = 24 ∨ k = 90 ∨ k = 180

private theorem degree_sixteen_fixed_pair_arithmetic :
    ∀ x : Fin 60 × Fin 6 × Fin 4,
      degreeSixteenFixedPairArithmeticPredicate x := by
  unfold degreeSixteenFixedPairArithmeticPredicate
  decide +kernel

theorem five_point_stabilizer_card_cases_after_fixed_pairs
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 16)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    {s : Set X} (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) = 12 ∨
      Nat.card (fixingSubgroup P s) = 24 ∨
      Nat.card (fixingSubgroup P s) = 90 ∨
      Nat.card (fixingSubgroup P s) = 180 := by
  classical
  let K : Subgroup P := fixingSubgroup P s
  let k := Nat.card K
  have hkpos : 0 < k := by
    dsimp only [k]
    exact Nat.card_pos
  have hkne : k ≠ 0 := Nat.ne_of_gt hkpos
  have hkdiv : k ∣ 7920 :=
    five_point_stabilizer_card_dvd_seven_thousand_nine_hundred_twenty
      X P hcard h5 hnotAlt hs
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  have hfixIndex := hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hfixIndex
  norm_num at hfixIndex
  have hKindex : K.index = 524160 := by
    change (fixingSubgroup P s).index = 524160
    omega
  have hKindexCard := K.index_mul_card
  have hPcard : Nat.card P = 524160 * k := by
    rw [hKindex] at hKindexCard
    exact hKindexCard.symm
  have hkNot13 : ¬13 ∣ k := by
    intro h
    exact (by norm_num : ¬13 ∣ 7920) (h.trans hkdiv)
  letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  let S13 : Sylow 13 P := Sylow.nonempty.some
  have hS13card : Nat.card S13 = 13 := by
    rw [S13.card_eq_multiplicity, hPcard]
    rw [show 524160 = 13 * 40320 by norm_num, Nat.mul_assoc,
      Nat.factorization_mul (by norm_num)
        (Nat.mul_ne_zero (by norm_num) hkne),
      Finsupp.add_apply, (show Nat.Prime 13 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_mul (by norm_num) hkne,
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd hkNot13]
    norm_num
  let C13 : Subgroup P :=
    Subgroup.centralizer (S13 : Set P)
  let N13 : Subgroup P :=
    Subgroup.normalizer (S13 : Set P)
  let d13 := C13.relIndex N13
  have h13 :
      d13 ∣ 12 ∧ 0 < d13 ∧ N13.index % 13 = 1 ∧
        d13 * N13.index * 13 = Nat.card P := by
    simpa only [C13, N13, d13] using
      sylow_normalizer_constraints_of_not_alternating
        X P hcard h5 hnotAlt (p := 13) (by norm_num)
          (Or.inr rfl) S13 hS13card
  have hquot13 :
      524160 * k / (13 * d13) = N13.index := by
    have hmul :
        (13 * d13) * N13.index = 524160 * k := by
      rw [← hPcard]
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
        h13.2.2.2
    rw [← hmul]
    exact Nat.mul_div_cancel_left _
      (Nat.mul_pos (by norm_num) h13.2.1)
  have hbound13 :
      N13.index * 12 * 6 ≤ 524160 * k := by
    have hbound :=
      sylow_prime_fixed_pair_bound X P hcard h5
        (p := 13) (by norm_num) (Or.inr rfl) S13 hS13card
    rw [hPcard] at hbound
    norm_num at hbound ⊢
    exact hbound
  have hkle : k ≤ 7920 := Nat.le_of_dvd (by norm_num) hkdiv
  let kFin : Fin 7921 := ⟨k, by omega⟩
  obtain ⟨ik, hik⟩ :=
    degree_sixteen_divisor_7920_index kFin hkdiv
  obtain ⟨i13, hi13⟩ :=
    degree_sixteen_divisor_12_index d13 h13.2.1 h13.1
  by_cases hk11 : 11 ∣ k
  · have hkNot121 : ¬121 ∣ k := by
      intro h
      exact (by norm_num : ¬121 ∣ 7920) (h.trans hkdiv)
    have hkFactorization11 : Nat.factorization k 11 = 1 := by
      apply le_antisymm
      · by_contra hle
        have htwo : 2 ≤ Nat.factorization k 11 := by omega
        have hpow :
            11 ^ 2 ∣ k :=
          (show Nat.Prime 11 by norm_num).pow_dvd_iff_le_factorization
            hkne |>.mpr htwo
        norm_num at hpow
        exact hkNot121 hpow
      · exact
          ((show Nat.Prime 11 by norm_num).dvd_iff_one_le_factorization
            hkne).mp hk11
    letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    let S11 : Sylow 11 P := Sylow.nonempty.some
    have hS11card : Nat.card S11 = 11 := by
      rw [S11.card_eq_multiplicity, hPcard,
        Nat.factorization_mul (by norm_num) hkne,
        Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num),
        hkFactorization11]
      norm_num
    let C11 : Subgroup P :=
      Subgroup.centralizer (S11 : Set P)
    let N11 : Subgroup P :=
      Subgroup.normalizer (S11 : Set P)
    let d11 := C11.relIndex N11
    have h11 :
        d11 ∣ 10 ∧ 0 < d11 ∧ N11.index % 11 = 1 ∧
          d11 * N11.index * 11 = Nat.card P := by
      simpa only [C11, N11, d11] using
        sylow_normalizer_constraints_of_not_alternating
          X P hcard h5 hnotAlt (p := 11) (by norm_num)
            (Or.inl rfl) S11 hS11card
    have hquot11 :
        524160 * k / (11 * d11) = N11.index := by
      have hmul :
          (11 * d11) * N11.index = 524160 * k := by
        rw [← hPcard]
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          h11.2.2.2
      rw [← hmul]
      exact Nat.mul_div_cancel_left _
        (Nat.mul_pos (by norm_num) h11.2.1)
    have hbound11 :
        N11.index * 10 * 20 ≤ 524160 * k := by
      have hbound :=
        sylow_prime_fixed_pair_bound X P hcard h5
          (p := 11) (by norm_num) (Or.inl rfl) S11 hS11card
      rw [hPcard] at hbound
      norm_num at hbound ⊢
      exact hbound
    obtain ⟨i11, hi11⟩ :=
      degree_sixteen_divisor_10_index d11 h11.2.1 h11.1
    have harith :=
      degree_sixteen_fixed_pair_arithmetic (ik, i13, i11)
    dsimp only [degreeSixteenFixedPairArithmeticPredicate] at harith
    rw [hik, hi13, hi11] at harith
    have hcases := harith
      (by rw [hquot13]; exact h13.2.2.1)
      (by rw [hquot13]; exact hbound13)
      (fun _ => ⟨by rw [hquot11]; exact h11.2.2.1,
        by rw [hquot11]; exact hbound11⟩)
    simpa only [K, k] using hcases
  · let i11 : Fin 4 := 0
    have hi11 : degreeSixteenDivisor10 i11 = 1 := by
      rfl
    have harith :=
      degree_sixteen_fixed_pair_arithmetic (ik, i13, i11)
    dsimp only [degreeSixteenFixedPairArithmeticPredicate] at harith
    rw [hik, hi13, hi11] at harith
    have hcases := harith
      (by rw [hquot13]; exact h13.2.2.1)
      (by rw [hquot13]; exact hbound13)
      (fun h => (hk11 h).elim)
    simpa only [K, k] using hcases

end FiveTransitive.Degree16

end CFSG
