module

public import CFSG.Permutation.FiveTransitive.Degree16FixedPairs

public section

namespace CFSG

namespace FiveTransitive.Degree16

open MulAction SubMulAction Subgroup

private theorem sylow_seven_thirteen_fixed_pair_bound
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 16)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (S7 : Sylow 7 P) (hS7card : Nat.card S7 = 7)
    (S13 : Sylow 13 P) (hS13card : Nat.card S13 = 13) :
    let N7 := Subgroup.normalizer (S7 : Set P)
    let N13 := Subgroup.normalizer (S13 : Set P)
    N7.index * 6 * 2 + N13.index * 12 * 6 ≤ Nat.card P := by
  classical
  dsimp
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  let A7 := Degree15.NonidentitySylowElements 7 P
  let A13 := Degree15.NonidentitySylowElements 13 P
  let val7 : A7 → P :=
    Degree15.nonidentitySylowElementVal 7 P
  let val13 : A13 → P :=
    Degree15.nonidentitySylowElementVal 13 P
  have horder7 (a : A7) : orderOf (val7 a) = 7 := by
    rcases a with ⟨S, u⟩
    change orderOf ((u.1 : S) : P) = 7
    calc
      orderOf ((u.1 : S) : P) = orderOf u.1 :=
        Subgroup.orderOf_coe _
      _ = 7 := Degree15.orderOf_eq_prime_of_card_eq_prime
        (Degree15.sylow_card_eq_of_card_eq S7 hS7card S) u.2
  have horder13 (a : A13) : orderOf (val13 a) = 13 := by
    rcases a with ⟨S, u⟩
    change orderOf ((u.1 : S) : P) = 13
    calc
      orderOf ((u.1 : S) : P) = orderOf u.1 :=
        Subgroup.orderOf_coe _
      _ = 13 := Degree15.orderOf_eq_prime_of_card_eq_prime
        (Degree15.sylow_card_eq_of_card_eq S13 hS13card S) u.2
  have hfixed7 (a : A7) :
      Fintype.card
          (MulAction.fixedBy (Fin 2 ↪ X) (val7 a)) = 2 := by
    let g : Equiv.Perm X := (val7 a : P)
    have hgorder : orderOf g = 7 := by
      calc
        orderOf g = orderOf (val7 a) := Subgroup.orderOf_coe _
        _ = 7 := horder7 a
    have hgprime : (orderOf g).Prime := by
      rw [hgorder]
      norm_num
    obtain ⟨m, hm⟩ :=
      Equiv.Perm.cycleType_prime_order hgprime
    have hsum := g.sum_cycleType
    rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
      Nat.cast_id, hgorder] at hsum
    have hsupportLe : g.support.card ≤ 16 := by
      calc
        g.support.card ≤ Fintype.card X :=
          Finset.card_le_univ g.support
        _ = 16 := hcard
    have hmTwo : m + 1 = 2 := by
      have hmLe : m + 1 ≤ 2 := by
        nlinarith
      rcases (show m + 1 = 1 ∨ m + 1 = 2 by omega) with
        hmOne | hmTwo
      · have hsupport : g.support.card ≤ 7 := by
          omega
        exact (hnotAlt
          (alternatingGroup_le_of_prime_order_support_le_seven
            X P hcard h5 (val7 a).prop (by norm_num)
              hgorder hsupport)).elim
      · exact hmTwo
    have hgsupport : g.support.card = 14 := by
      omega
    have hfixedPoints :
        Fintype.card (MulAction.fixedBy X (val7 a)) = 2 := by
      rw [Degree15.card_fixedBy_subgroup_perm, hcard]
      change 16 - g.support.card = 2
      rw [hgsupport]
    calc
      Fintype.card
          (MulAction.fixedBy (Fin 2 ↪ X) (val7 a)) =
          (Fintype.card
            (MulAction.fixedBy X (val7 a))).descFactorial
              (Fintype.card (Fin 2)) :=
        Degree15.card_fixedBy_embedding (val7 a)
      _ = 2 := by
        rw [hfixedPoints, Fintype.card_fin]
        norm_num
  have hfixed13 (a : A13) :
      Fintype.card
          (MulAction.fixedBy (Fin 2 ↪ X) (val13 a)) = 6 := by
    let g : Equiv.Perm X := (val13 a : P)
    have hgorder : orderOf g = 13 := by
      calc
        orderOf g = orderOf (val13 a) := Subgroup.orderOf_coe _
        _ = 13 := horder13 a
    have hgcycle : g.IsCycle :=
      Equiv.Perm.isCycle_of_prime_order' (by
        rw [hgorder]
        norm_num) (by
          rw [hcard, hgorder]
          norm_num)
    have hgsupport : g.support.card = 13 := by
      rw [← hgcycle.orderOf, hgorder]
    have hfixedPoints :
        Fintype.card (MulAction.fixedBy X (val13 a)) = 3 := by
      rw [Degree15.card_fixedBy_subgroup_perm, hcard]
      change 16 - g.support.card = 3
      rw [hgsupport]
    calc
      Fintype.card
          (MulAction.fixedBy (Fin 2 ↪ X) (val13 a)) =
          (Fintype.card
            (MulAction.fixedBy X (val13 a))).descFactorial
              (Fintype.card (Fin 2)) :=
        Degree15.card_fixedBy_embedding (val13 a)
      _ = 6 := by
        rw [hfixedPoints, Fintype.card_fin]
        norm_num
  have hvalInjective :
      Function.Injective (Sum.elim val7 val13) := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl
        (Degree15.nonidentitySylowElementVal_injective
          S7 hS7card (by simpa [val7] using hab))
    · have hbad : (7 : ℕ) = 13 := by
        calc
          7 = orderOf (val7 a) := (horder7 a).symm
          _ = orderOf (val13 b) := congrArg orderOf
            (by simpa using hab)
          _ = 13 := horder13 b
      norm_num at hbad
    · have hbad : (13 : ℕ) = 7 := by
        calc
          13 = orderOf (val13 a) := (horder13 a).symm
          _ = orderOf (val7 b) := congrArg orderOf
            (by simpa using hab)
          _ = 7 := horder7 b
      norm_num at hbad
    · exact congrArg Sum.inr
        (Degree15.nonidentitySylowElementVal_injective
          S13 hS13card (by simpa [val13] using hab))
  let N7 : Subgroup P :=
    Subgroup.normalizer (S7 : Set P)
  let N13 : Subgroup P :=
    Subgroup.normalizer (S13 : Set P)
  have hA7card : Fintype.card A7 = N7.index * 6 := by
    rw [show Fintype.card A7 =
        Fintype.card (Sylow 7 P) * (7 - 1) by
      exact Degree15.card_nonidentitySylowElements S7 hS7card]
    rw [← Nat.card_eq_fintype_card,
      S7.card_eq_index_normalizer]
  have hA13card : Fintype.card A13 = N13.index * 12 := by
    rw [show Fintype.card A13 =
        Fintype.card (Sylow 13 P) * (13 - 1) by
      exact Degree15.card_nonidentitySylowElements S13 hS13card]
    rw [← Nat.card_eq_fintype_card,
      S13.card_eq_index_normalizer]
  have hbound :=
    two_family_fixed_pair_bound X P hcard h5
      A7 A13 val7 val13 hvalInjective 2 6 hfixed7 hfixed13
  rw [hA7card, hA13card] at hbound
  simpa [Nat.mul_assoc] using hbound

private def degreeSixteenRemainingFactor (i : Fin 4) : ℕ :=
  ![12, 24, 90, 180] i

private def degreeSixteenSevenCentralizerCard (i : Fin 3) : ℕ :=
  ![7, 14, 28] i

private def degreeSixteenDivisor6 (i : Fin 4) : ℕ :=
  ![1, 2, 3, 6] i

private def degreeSixteenCentralizerArithmeticPredicate
    (x : Fin 4 × Fin 197) : Prop :=
  let k := degreeSixteenRemainingFactor x.1
  let c := x.2.val
  c ∣ 196 → c ∣ 524160 * k → 7 ∣ c →
    ∃ i : Fin 3, degreeSixteenSevenCentralizerCard i = c

private theorem degree_sixteen_centralizer_arithmetic :
    ∀ x : Fin 4 × Fin 197,
      degreeSixteenCentralizerArithmeticPredicate x := by
  unfold degreeSixteenCentralizerArithmeticPredicate
  decide +kernel

private def degreeSixteenSylowSevenArithmeticPredicate
    (x : Fin 4 × Fin 3 × Fin 4 × Fin 6) : Prop :=
  let k := degreeSixteenRemainingFactor x.1
  let c := degreeSixteenSevenCentralizerCard x.2.1
  let r := degreeSixteenDivisor6 x.2.2.1
  let d13 := degreeSixteenDivisor12 x.2.2.2
  (524160 * k / (c * r)) % 7 = 1 →
    (524160 * k / (13 * d13)) % 13 = 1 →
    (524160 * k / (c * r)) * 6 * 2 +
        (524160 * k / (13 * d13)) * 12 * 6 ≤
      524160 * k →
    (k = 24 ∧ c = 28 ∧ r = 6) ∨
      (k = 180 ∧
        ((c = 14 ∧ r = 6) ∨ (c = 28 ∧ r = 3)))

private theorem degree_sixteen_sylow_seven_arithmetic :
    ∀ x : Fin 4 × Fin 3 × Fin 4 × Fin 6,
      degreeSixteenSylowSevenArithmeticPredicate x := by
  unfold degreeSixteenSylowSevenArithmeticPredicate
  decide +kernel

theorem sylow_seven_reduction
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 16)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    {s : Set X} (hs : s.ncard = 5) :
    ∃ S : Sylow 7 P,
      let C := Subgroup.centralizer (S : Set P)
      let N := Subgroup.normalizer (S : Set P)
      (Nat.card (fixingSubgroup P s) = 24 ∧
        Nat.card C = 28 ∧ C.relIndex N = 6) ∨
      (Nat.card (fixingSubgroup P s) = 180 ∧
        ((Nat.card C = 14 ∧ C.relIndex N = 6) ∨
          (Nat.card C = 28 ∧ C.relIndex N = 3))) := by
  classical
  let K : Subgroup P := fixingSubgroup P s
  let k := Nat.card K
  have hKcases :=
    five_point_stabilizer_card_cases_after_fixed_pairs
      X P hcard h5 hnotAlt hs
  change k = 12 ∨ k = 24 ∨ k = 90 ∨ k = 180 at hKcases
  obtain ⟨ik, hik⟩ :
      ∃ i : Fin 4, degreeSixteenRemainingFactor i = k := by
    rcases hKcases with h | h | h | h
    · exact ⟨0, by simpa [degreeSixteenRemainingFactor] using h.symm⟩
    · exact ⟨1, by simpa [degreeSixteenRemainingFactor] using h.symm⟩
    · exact ⟨2, by simpa [degreeSixteenRemainingFactor] using h.symm⟩
    · exact ⟨3, by simpa [degreeSixteenRemainingFactor] using h.symm⟩
  have hkpos : 0 < k := by
    rcases hKcases with h | h | h | h <;> omega
  have hkne : k ≠ 0 := Nat.ne_of_gt hkpos
  have hkNot7 : ¬7 ∣ k := by
    intro hk7
    rcases hKcases with h | h | h | h
    all_goals norm_num [h] at hk7
  have hkNot13 : ¬13 ∣ k := by
    intro hk13
    rcases hKcases with h | h | h | h
    all_goals norm_num [h] at hk13
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
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let S7 : Sylow 7 P := Sylow.nonempty.some
  have hS7card : Nat.card S7 = 7 := by
    rw [S7.card_eq_multiplicity, hPcard]
    rw [show 524160 = 7 * 74880 by norm_num, Nat.mul_assoc,
      Nat.factorization_mul (by norm_num)
        (Nat.mul_ne_zero (by norm_num) hkne),
      Finsupp.add_apply, (show Nat.Prime 7 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_mul (by norm_num) hkne,
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd hkNot7]
    norm_num
  letI : IsCyclic S7 := isCyclic_of_prime_card hS7card
  letI : IsMulCommutative S7 := IsCyclic.isMulCommutative
  obtain ⟨u, hu⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := S7)
  have huorder : orderOf u = 7 := hu.trans hS7card
  let g : Equiv.Perm X := (u : P)
  have hgorder : orderOf g = 7 := by
    calc
      orderOf g = orderOf (u : P) := Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
      _ = 7 := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder] at hsum
  have hsupportLe : g.support.card ≤ 16 := by
    calc
      g.support.card ≤ Fintype.card X :=
        Finset.card_le_univ g.support
      _ = 16 := hcard
  have hmTwo : m + 1 = 2 := by
    have hmLe : m + 1 ≤ 2 := by
      nlinarith
    rcases (show m + 1 = 1 ∨ m + 1 = 2 by omega) with
      hmOne | hmTwo
    · have hsupport : g.support.card ≤ 7 := by
        omega
      exact (hnotAlt
        (alternatingGroup_le_of_prime_order_support_le_seven
          X P hcard h5 (u : P).prop (by norm_num)
            hgorder hsupport)).elim
    · exact hmTwo
  have hcycleType : g.cycleType = {7, 7} := by
    rw [hm, hgorder, hmTwo]
    norm_num
  have hcentralizerPerm :
      Nat.card (Subgroup.centralizer
        ({g} : Set (Equiv.Perm X))) = 196 := by
    rw [Equiv.Perm.nat_card_centralizer, hcycleType, hcard]
    norm_num
  let C : Subgroup P :=
    Subgroup.centralizer (S7 : Set P)
  let N : Subgroup P :=
    Subgroup.normalizer (S7 : Set P)
  let c := Nat.card C
  let r := C.relIndex N
  have hS7C : (S7 : Subgroup P) ≤ C :=
    Subgroup.le_centralizer (S7 : Subgroup P)
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp C.subtype
  have hbaseMapMem :
      ∀ q : C, baseMap q ∈
        Subgroup.centralizer ({g} : Set (Equiv.Perm X)) := by
    intro q
    change ((q.1 : P) : Equiv.Perm X) ∈
      Subgroup.centralizer ({g} : Set (Equiv.Perm X))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((q.2 (u : P) u.prop).symm)
  let centMap :
      C →* Subgroup.centralizer ({g} : Set (Equiv.Perm X)) :=
    baseMap.codRestrict
      (Subgroup.centralizer ({g} : Set (Equiv.Perm X)))
      hbaseMapMem
  have hcentMapInjective : Function.Injective centMap := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    change baseMap a = baseMap b at hab'
    exact C.subtype_injective (P.subtype_injective hab')
  have hCdiv196 : c ∣ 196 := by
    dsimp only [c]
    rw [← hcentralizerPerm]
    exact Subgroup.card_dvd_of_injective
      centMap hcentMapInjective
  have hCdivP : c ∣ 524160 * k := by
    rw [← hPcard]
    exact Subgroup.card_subgroup_dvd_card C
  have h7divC : 7 ∣ c := by
    dsimp only [c]
    rw [← hS7card]
    exact Subgroup.card_dvd_of_le hS7C
  have hcle : c ≤ 196 :=
    Nat.le_of_dvd (by norm_num) hCdiv196
  let cFin : Fin 197 := ⟨c, by omega⟩
  have hcentArith :=
    degree_sixteen_centralizer_arithmetic (ik, cFin)
  dsimp only [degreeSixteenCentralizerArithmeticPredicate] at hcentArith
  rw [hik] at hcentArith
  obtain ⟨ic, hic⟩ :=
    hcentArith hCdiv196 hCdivP h7divC
  have hAutCard : Nat.card (MulAut S7) = 6 := by
    rw [IsCyclic.card_mulAut S7, hS7card,
      Nat.totient_prime (by norm_num)]
  have hrangeDvd :
      Nat.card S7.normalizerMonoidHom.range ∣ 6 := by
    rw [← hAutCard]
    exact Subgroup.card_subgroup_dvd_card _
  have hrEq : r = Nat.card S7.normalizerMonoidHom.range := by
    change
      (Subgroup.centralizer (S7 : Set P)).relIndex
          (Subgroup.normalizer (S7 : Set P)) =
        Nat.card S7.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      S7.normalizerMonoidHom_ker]
    simp only [S7.coe_coe]
  have hrDvd : r ∣ 6 := by
    rw [hrEq]
    exact hrangeDvd
  letI : C.IsFiniteRelIndex N :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hrpos : 0 < r :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hrcases : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 6 := by
    have hrle : r ≤ 6 := Nat.le_of_dvd (by norm_num) hrDvd
    let rFin : Fin 7 := ⟨r, by omega⟩
    have hfinite :
        ∀ q : Fin 7, 0 < q.val → q.val ∣ 6 →
          q.val = 1 ∨ q.val = 2 ∨ q.val = 3 ∨ q.val = 6 := by
      decide
    exact hfinite rFin hrpos hrDvd
  obtain ⟨ir, hir⟩ :
      ∃ i : Fin 4, degreeSixteenDivisor6 i = r := by
    rcases hrcases with h | h | h | h
    · exact ⟨0, by simpa [degreeSixteenDivisor6] using h.symm⟩
    · exact ⟨1, by simpa [degreeSixteenDivisor6] using h.symm⟩
    · exact ⟨2, by simpa [degreeSixteenDivisor6] using h.symm⟩
    · exact ⟨3, by simpa [degreeSixteenDivisor6] using h.symm⟩
  have h7mod : N.index % 7 = 1 := by
    have hsylow :
        (Subgroup.normalizer (S7 : Set P)).index ≡ 1 [MOD 7] := by
      rw [← S7.card_eq_index_normalizer]
      exact card_sylow_modEq_one 7 P
    change N.index % 7 = 1 % 7 at hsylow
    norm_num at hsylow
    exact hsylow
  have hrel : r * N.index = C.index := by
    simpa only [C, N, r] using
      Subgroup.relIndex_mul_index
        (Subgroup.centralizer_le_normalizer (S7 : Set P))
  have hCindex := C.index_mul_card
  have h7eq : r * N.index * c = 524160 * k := by
    rw [← hPcard, ← hCindex, ← hrel]
  have hquot7 :
      524160 * k / (c * r) = N.index := by
    have hmul : (c * r) * N.index = 524160 * k := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h7eq
    rw [← hmul]
    exact Nat.mul_div_cancel_left _
      (Nat.mul_pos (by
        exact Nat.card_pos) hrpos)
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
  obtain ⟨i13, hi13⟩ :=
    degree_sixteen_divisor_12_index d13 h13.2.1 h13.1
  have hbound :
      N.index * 6 * 2 + N13.index * 12 * 6 ≤ 524160 * k := by
    have hb :=
      sylow_seven_thirteen_fixed_pair_bound
        X P hcard h5 hnotAlt S7 hS7card S13 hS13card
    rw [hPcard] at hb
    exact hb
  have harith :=
    degree_sixteen_sylow_seven_arithmetic
      (ik, ic, ir, i13)
  dsimp only [degreeSixteenSylowSevenArithmeticPredicate] at harith
  rw [hik, hic, hir, hi13] at harith
  have hresult := harith
    (by rw [hquot7]; exact h7mod)
    (by rw [hquot13]; exact h13.2.2.1)
    (by rw [hquot7, hquot13]; exact hbound)
  refine ⟨S7, ?_⟩
  simpa only [K, k, C, N, c, r] using hresult

end FiveTransitive.Degree16

end CFSG
