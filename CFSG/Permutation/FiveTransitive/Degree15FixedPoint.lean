module

public import CFSG.Permutation.FiveTransitive.Degree15

public section

namespace CFSG

namespace FiveTransitive.Degree15

@[expose] abbrev NonidentitySylowElements
    (p : ℕ) (G : Type) [Group G] :=
  Σ S : Sylow p G, {u : S // u ≠ 1}

noncomputable instance nonidentitySylowElementsFintype
    (p : ℕ) (G : Type) [Group G] [Fintype G] :
    Fintype (NonidentitySylowElements p G) := by
  classical
  infer_instance

@[expose] def nonidentitySylowElementVal
    (p : ℕ) (G : Type) [Group G] :
    NonidentitySylowElements p G → G
  | ⟨_, u⟩ => u.1

theorem orderOf_eq_prime_of_card_eq_prime
    {H : Type} [Group H] {p : ℕ} [Fact p.Prime]
    (hcard : Nat.card H = p) {u : H} (hu : u ≠ 1) :
    orderOf u = p := by
  calc
    orderOf u = Nat.card H :=
      orderOf_eq_card_of_forall_mem_zpowers
        (fun v => mem_zpowers_of_prime_card hcard hu)
    _ = p := hcard

theorem sylow_card_eq_of_card_eq
    {G : Type} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime]
    (S₀ : Sylow p G) (hS₀ : Nat.card S₀ = p)
    (S : Sylow p G) :
    Nat.card S = p := by
  calc
    Nat.card S = Nat.card S₀ :=
      Nat.card_congr (Sylow.equiv S S₀).toEquiv
    _ = p := hS₀

theorem sylow_eq_of_nonidentity_mem
    {G : Type} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime]
    (S T : Sylow p G)
    (hScard : Nat.card S = p)
    (hTcard : Nat.card T = p)
    {u : G} (hu : u ≠ 1) (huS : u ∈ S) (huT : u ∈ T) :
    S = T := by
  apply Sylow.ext
  apply le_antisymm
  · intro v hv
    let uS : S := ⟨u, huS⟩
    let vS : S := ⟨v, hv⟩
    have huSNe : uS ≠ 1 := by
      intro h
      exact hu (congrArg Subtype.val h)
    have hvgen : vS ∈ Subgroup.zpowers uS :=
      mem_zpowers_of_prime_card hScard huSNe
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hvgen
    have hz' : u ^ z = v :=
      congrArg Subtype.val hz
    rw [← hz']
    exact T.zpow_mem huT z
  · intro v hv
    let uT : T := ⟨u, huT⟩
    let vT : T := ⟨v, hv⟩
    have huTNe : uT ≠ 1 := by
      intro h
      exact hu (congrArg Subtype.val h)
    have hvgen : vT ∈ Subgroup.zpowers uT :=
      mem_zpowers_of_prime_card hTcard huTNe
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hvgen
    have hz' : u ^ z = v :=
      congrArg Subtype.val hz
    rw [← hz']
    exact S.zpow_mem huS z

theorem nonidentitySylowElementVal_injective
    {G : Type} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime]
    (S₀ : Sylow p G) (hS₀ : Nat.card S₀ = p) :
    Function.Injective (nonidentitySylowElementVal p G) := by
  rintro ⟨S, ⟨u, hu⟩⟩ ⟨T, ⟨v, hv⟩⟩ huv
  have huvG : (u : G) = (v : G) := by
    simpa [nonidentitySylowElementVal] using huv
  have huG : (u : G) ≠ 1 := by
    intro h
    apply hu
    exact Subtype.ext h
  have hST : S = T := sylow_eq_of_nonidentity_mem
    S T (sylow_card_eq_of_card_eq S₀ hS₀ S)
      (sylow_card_eq_of_card_eq S₀ hS₀ T)
      huG u.prop (by rw [huvG]; exact v.prop)
  subst T
  have huv' : u = v := Subtype.ext huvG
  subst v
  rfl

theorem card_nonidentity_of_card_eq
    {H : Type} [Fintype H] [One H] [DecidableEq H]
    {p : ℕ} (hcard : Fintype.card H = p) :
    Fintype.card {u : H // u ≠ 1} = p - 1 := by
  rw [Fintype.card_subtype_compl]
  simp [hcard]

theorem card_nonidentitySylowElements
    {G : Type} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime]
    (S₀ : Sylow p G) (hS₀ : Nat.card S₀ = p) :
    Fintype.card (NonidentitySylowElements p G) =
      Fintype.card (Sylow p G) * (p - 1) := by
  classical
  have hfiber (S : Sylow p G) :
      Fintype.card {u : S // u ≠ 1} = p - 1 :=
    card_nonidentity_of_card_eq (by
      rw [← Nat.card_eq_fintype_card]
      exact sylow_card_eq_of_card_eq S₀ hS₀ S)
  rw [Fintype.card_sigma]
  simp_rw [hfiber]
  simp

theorem card_fixedBy_subgroup_perm
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (q : P) :
    Fintype.card (MulAction.fixedBy X q) =
      Fintype.card X - ((q : P) : Equiv.Perm X).support.card := by
  have hs :
      MulAction.fixedBy X q =
        {x : X | x ∉ ((q : P) : Equiv.Perm X).support} := by
    ext x
    change
      ((q : P) : Equiv.Perm X) x = x ↔
        x ∉ ((q : P) : Equiv.Perm X).support
    exact Equiv.Perm.notMem_support.symm
  calc
    Fintype.card (MulAction.fixedBy X q) =
        Fintype.card {x : X //
          x ∉ ((q : P) : Equiv.Perm X).support} :=
      Fintype.card_congr (Set.equivOfEq hs)
    _ = Fintype.card X -
        ((q : P) : Equiv.Perm X).support.card := by
      rw [Fintype.card_subtype_compl, Fintype.card_coe]

private theorem stabilizer_factor_one_eight_or_thirty_impossible
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 15)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (k : ℕ) (hk : k = 1 ∨ k = 8 ∨ k = 30)
    (hPcard : Nat.card P = 360360 * k) :
    False := by
  classical
  have hkpos : 0 < k := by
    rcases hk with rfl | rfl | rfl <;> norm_num
  have hkne : k ≠ 0 := Nat.ne_of_gt hkpos
  have hkNot11 : ¬11 ∣ k := by
    rcases hk with rfl | rfl | rfl <;> norm_num
  have hkNot13 : ¬13 ∣ k := by
    rcases hk with rfl | rfl | rfl <;> norm_num
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let S11 : Sylow 11 P := Sylow.nonempty.some
  have hS11card : Nat.card S11 = 11 := by
    rw [S11.card_eq_multiplicity, hPcard]
    rw [show 360360 = 11 * 32760 by norm_num, Nat.mul_assoc,
      Nat.factorization_mul (by norm_num)
        (Nat.mul_ne_zero (by norm_num) hkne),
      Finsupp.add_apply, (show Nat.Prime 11 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_mul (by norm_num) hkne,
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd hkNot11]
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
  letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  let S13 : Sylow 13 P := Sylow.nonempty.some
  have hS13card : Nat.card S13 = 13 := by
    rw [S13.card_eq_multiplicity, hPcard]
    rw [show 360360 = 13 * 27720 by norm_num, Nat.mul_assoc,
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
  let A11 := NonidentitySylowElements 11 P
  let A13 := NonidentitySylowElements 13 P
  let val11 : A11 → P := nonidentitySylowElementVal 11 P
  let val13 : A13 → P := nonidentitySylowElementVal 13 P
  have horder11 (a : A11) : orderOf (val11 a) = 11 := by
    rcases a with ⟨S, u⟩
    change orderOf ((u.1 : S) : P) = 11
    calc
      orderOf ((u.1 : S) : P) = orderOf u.1 :=
        Subgroup.orderOf_coe _
      _ = 11 := orderOf_eq_prime_of_card_eq_prime
        (sylow_card_eq_of_card_eq S11 hS11card S) u.2
  have horder13 (a : A13) : orderOf (val13 a) = 13 := by
    rcases a with ⟨S, u⟩
    change orderOf ((u.1 : S) : P) = 13
    calc
      orderOf ((u.1 : S) : P) = orderOf u.1 :=
        Subgroup.orderOf_coe _
      _ = 13 := orderOf_eq_prime_of_card_eq_prime
        (sylow_card_eq_of_card_eq S13 hS13card S) u.2
  have hfixed11 (a : A11) :
      Fintype.card (MulAction.fixedBy X (val11 a)) = 4 := by
    let g : Equiv.Perm X := (val11 a : P)
    have hgorder : orderOf g = 11 := by
      calc
        orderOf g = orderOf (val11 a) := Subgroup.orderOf_coe _
        _ = 11 := horder11 a
    have hgcycle : g.IsCycle :=
      Equiv.Perm.isCycle_of_prime_order' (by
        rw [hgorder]
        norm_num) (by
          rw [hcard, hgorder]
          norm_num)
    have hgsupport : g.support.card = 11 := by
      rw [← hgcycle.orderOf, hgorder]
    rw [card_fixedBy_subgroup_perm, hcard]
    change 15 - g.support.card = 4
    rw [hgsupport]
  have hfixed13 (a : A13) :
      Fintype.card (MulAction.fixedBy X (val13 a)) = 2 := by
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
    rw [card_fixedBy_subgroup_perm, hcard]
    change 15 - g.support.card = 2
    rw [hgsupport]
  let val : A11 ⊕ A13 → P :=
    Sum.elim val11 val13
  have hvalInjective : Function.Injective val := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl
        (nonidentitySylowElementVal_injective
          S11 hS11card (by simpa [val, val11] using hab))
    · have hbad : (11 : ℕ) = 13 := by
        calc
          11 = orderOf (val11 a) := (horder11 a).symm
          _ = orderOf (val13 b) := congrArg orderOf
            (by simpa [val] using hab)
          _ = 13 := horder13 b
      norm_num at hbad
    · have hbad : (13 : ℕ) = 11 := by
        calc
          13 = orderOf (val13 a) := (horder13 a).symm
          _ = orderOf (val11 b) := congrArg orderOf
            (by simpa [val] using hab)
          _ = 11 := horder11 b
      norm_num at hbad
    · exact congrArg Sum.inr
        (nonidentitySylowElementVal_injective
          S13 hS13card (by simpa [val, val13] using hab))
  have hA11card :
      Fintype.card A11 = N11.index * 10 := by
    rw [show Fintype.card A11 =
        Fintype.card (Sylow 11 P) * (11 - 1) by
      exact card_nonidentitySylowElements S11 hS11card]
    rw [← Nat.card_eq_fintype_card,
      S11.card_eq_index_normalizer]
  have hA13card :
      Fintype.card A13 = N13.index * 12 := by
    rw [show Fintype.card A13 =
        Fintype.card (Sylow 13 P) * (13 - 1) by
      exact card_nonidentitySylowElements S13 hS13card]
    rw [← Nat.card_eq_fintype_card,
      S13.card_eq_index_normalizer]
  have hselectedSum :
      (∑ a : A11 ⊕ A13,
          Fintype.card (MulAction.fixedBy X (val a))) =
        N11.index * 10 * 4 + N13.index * 12 * 2 := by
    rw [Fintype.sum_sum_type]
    change
      (∑ a : A11,
          Fintype.card (MulAction.fixedBy X (val11 a))) +
        (∑ a : A13,
          Fintype.card (MulAction.fixedBy X (val13 a))) =
        N11.index * 10 * 4 + N13.index * 12 * 2
    simp_rw [hfixed11, hfixed13]
    simp [hA11card, hA13card]
  have hselectedLe :
      (∑ a : A11 ⊕ A13,
          Fintype.card (MulAction.fixedBy X (val a))) ≤
        ∑ q : P, Fintype.card (MulAction.fixedBy X q) := by
    calc
      (∑ a : A11 ⊕ A13,
          Fintype.card (MulAction.fixedBy X (val a))) =
          ∑ q ∈ Finset.univ.image val,
            Fintype.card (MulAction.fixedBy X q) := by
        rw [Finset.sum_image hvalInjective.injOn]
      _ ≤ ∑ q ∈ (Finset.univ : Finset P),
          Fintype.card (MulAction.fixedBy X q) :=
        Finset.sum_le_sum_of_subset (by simp)
      _ = ∑ q : P, Fintype.card (MulAction.fixedBy X q) := by
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
  letI : MulAction.IsMultiplyPretransitive P X 2 := hP2
  letI : MulAction.IsPretransitive P X :=
    MulAction.isPretransitive_of_is_two_pretransitive
  letI : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  letI : Unique (MulAction.orbitRel.Quotient P X) :=
    Classical.choice
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
        P X).mp inferInstance)
  have hburnside :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group P X
  have hburnside' :
      (∑ q : P, Fintype.card (MulAction.fixedBy X q)) =
        360360 * k := by
    rw [Fintype.card_unique, one_mul,
      ← Nat.card_eq_fintype_card, hPcard] at hburnside
    exact hburnside
  have hcount :
      N11.index * 10 * 4 + N13.index * 12 * 2 ≤
        360360 * k := by
    calc
      N11.index * 10 * 4 + N13.index * 12 * 2 =
          ∑ a : A11 ⊕ A13,
            Fintype.card (MulAction.fixedBy X (val a)) :=
        hselectedSum.symm
      _ ≤ ∑ q : P, Fintype.card (MulAction.fixedBy X q) :=
        hselectedLe
      _ = 360360 * k := hburnside'
  have hd11le : d11 ≤ 10 :=
    Nat.le_of_dvd (by norm_num) h11.1
  have hd13le : d13 ≤ 12 :=
    Nat.le_of_dvd (by norm_num) h13.1
  have h11mod := h11.2.2.1
  have h11eq := h11.2.2.2
  have h13mod := h13.2.2.1
  have h13eq := h13.2.2.2
  rcases hk with rfl | rfl | rfl
  · rw [hPcard] at h11eq h13eq
    norm_num at h11mod h11eq h13mod h13eq hcount
    have hd11 : d11 = 2 := by
      interval_cases d11 <;> omega
    have hd13 : d13 = 4 := by
      interval_cases d13 <;> omega
    norm_num [hd11] at h11eq
    norm_num [hd13] at h13eq
    omega
  · rw [hPcard] at h11eq h13eq
    norm_num at h11mod h11eq h13mod h13eq hcount
    have hd11 : d11 = 5 := by
      interval_cases d11 <;> omega
    have hd13 : d13 = 6 := by
      interval_cases d13 <;> omega
    norm_num [hd11] at h11eq
    norm_num [hd13] at h13eq
    omega
  · rw [hPcard] at h11eq h13eq
    norm_num at h11mod h11eq h13mod h13eq hcount
    have hd11 : d11 = 5 := by
      interval_cases d11 <;> omega
    have hd13 : d13 = 3 := by
      interval_cases d13 <;> omega
    norm_num [hd11] at h11eq
    norm_num [hd13] at h13eq
    omega

theorem five_point_stabilizer_card_eq_sixteen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 15)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    {s : Set X} (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) = 16 := by
  let K : Subgroup P := fixingSubgroup P s
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
  have hKindex : K.index = 360360 := by
    change (fixingSubgroup P s).index = 360360
    omega
  have hKindexCard := K.index_mul_card
  have hPcard : Nat.card P = 360360 * Nat.card K := by
    rw [hKindex] at hKindexCard
    exact hKindexCard.symm
  have hcases :=
    five_point_stabilizer_card_cases_after_transfer
      X P hcard h5 hnotAlt hs
  change Nat.card K = 1 ∨ Nat.card K = 8 ∨
    Nat.card K = 16 ∨ Nat.card K = 30 at hcases
  rcases hcases with h | h | h | h
  · exact (stabilizer_factor_one_eight_or_thirty_impossible
      X P hcard h5 hnotAlt (Nat.card K) (Or.inl h) hPcard).elim
  · exact (stabilizer_factor_one_eight_or_thirty_impossible
      X P hcard h5 hnotAlt (Nat.card K)
        (Or.inr (Or.inl h)) hPcard).elim
  · exact h
  · exact (stabilizer_factor_one_eight_or_thirty_impossible
      X P hcard h5 hnotAlt (Nat.card K)
        (Or.inr (Or.inr h)) hPcard).elim

end FiveTransitive.Degree15

end CFSG
