module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract
public import CFSG.RankThree.PartOne.S11c.Sec66PSU
public import CFSG.RankThree.PartOne.CTP.SeitzFineDefs

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.Sec66T (mem_innerAut_of_mem_D center_eq_bot_of_simple')

section Defs

variable {ℓ f : ℕ} {K : Type} [Field K]

@[expose] def suSub (h : UnitaryFieldData ℓ f K) {e : ℕ} {k : Subfield K}
    (h₀ : UnitaryFieldData ℓ e k) (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) (n : ℕ) :
    Subgroup (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
  (subfieldSU h h₀ hbar n).range

end Defs

@[expose] def SubfieldPairSU (n : ℕ) : Prop :=
  ∀ (f f₀ : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K) (k : Subfield K)
    (h₀ : UnitaryFieldData 2 f₀ k) (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) (p : ℕ),
    p.Prime → 5 ≤ p → f = p * f₀ → ¬(n = 3 ∧ f₀ = 1) →
    ∀ A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      (suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom ≠ suSub h h₀ hbar n →
      Subgroup.closure ((suSub h h₀ hbar n : Set (gramSU h
          ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∪
        ((suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom : Set (gramSU h
          ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))) = ⊤

section Fixed

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {e : ℕ} {k : Subfield K}
  (h₀ : UnitaryFieldData ℓ e k) (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) (n : ℕ)

theorem range_subfieldPSU_eq_map :
    (subfieldPSU h h₀ hbar n).range =
      (suSub h h₀ hbar n).map (QuotientGroup.mk' (normOneScalars h
        (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    induction y using QuotientGroup.induction_on with
    | H g => exact ⟨subfieldSU h h₀ hbar n g, ⟨g, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨g, rfl⟩, rfl⟩
    exact ⟨(g : primeFormP h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)), rfl⟩

theorem map_primeFormConjHom_map_mk (A : primeFormUnitary h ((1 : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K)) :
    ((suSub h h₀ hbar n).map (QuotientGroup.mk' (normOneScalars h
        (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n))).map
      (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A).toMonoidHom =
    ((suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom).map
      (QuotientGroup.mk' (normOneScalars h
        (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n)) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

end Fixed

section Main

variable {n : ℕ}

theorem fieldAutData_primeFormP (hn3 : 3 ≤ n) (hn5 : n ≤ 5) (hpair : SubfieldPairSU n)
    {ℓ f p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (hℓ : ℓ = 2)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) : FieldAutData (primeFormP h (idGram K n)) p := by
  subst hℓ
  classical
  have hfin := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hf1 : 1 ≤ f := h.one_le
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hKcard : Nat.card K = 2 ^ (2 * f) := h.card
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_ringEquiv_of_card Nat.prime_two (by omega) hKcard
  have hhigh : n < p ∨ ¬ p ∣ 2 ^ f + 1 := by
    by_cases hnp : n < p
    · exact Or.inl hnp
    · right
      intro hd
      have hpn : p = n := by omega
      exact hg (Nat.dvd_gcd (hpn ▸ dvd_refl p) hd)
  have hZ : ¬ p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) := by
    rw [card_normOneScalars_one h (by omega)]
    exact hg
  refine fieldAutData_of_standard
    (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).range
    {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = primeFormFieldHom h hC σ} ?_ ?_ ?_ ?_ ?_
  ·
    intro E hE hEc
    by_cases hEH : E ≤ innU h n
    · obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hcon
        rw [hbot, Subgroup.card_bot] at hEc
        have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
        omega
      obtain ⟨g, rfl⟩ := hEH haE
      refine ⟨g, ?_, haE⟩
      rintro rfl
      exact ha1 (map_one _)
    · have hcard : Nat.card (E ⊓ innU h n : Subgroup (MulAut (primeFormP h (idGram K n)))) = p := by
        rcases hhigh with hnp | hpq
        · exact (higher_unitary_noninner_plane_local_core_product_odd 2 f n p K h hp hp2 hn3 hnp
            hne ⊤ le_top E le_top hE hEc hEH).2.2.2.1
        · exact (nonsplit_unitary_noninner_plane_local_core_product_odd 2 f n p K h hp
            (by omega) hp2 hpq hn3 hne ⊤ le_top E le_top hE hEc hEH).1
      have h1 : (E ⊓ innU h n : Subgroup (MulAut (primeFormP h (idGram K n)))) ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hcard]
        exact hp.one_lt
      obtain ⟨⟨a, haE, haI⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
      obtain ⟨g, rfl⟩ := haI
      refine ⟨g, ?_, haE⟩
      rintro rfl
      exact ha1 (Subtype.ext (map_one _))
  ·
    intro α hα
    obtain ⟨hord, hout⟩ := hα
    have hαp : α ^ p = 1 := hord ▸ pow_orderOf_eq_one α
    have hσ1 : primeFormFieldFactor h hC hn3 hne α ≠ 1 := by
      intro h1
      have hD : α ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [← ker_primeFormFieldFactor h hC hn3 hne]
        exact h1
      obtain ⟨g, hgk⟩ := mem_innerAut_of_mem_D h hn3 hne hp hg hD hαp
      exact hout g hgk.symm
    have hσp : (primeFormFieldFactor h hC hn3 hne α) ^ p = 1 := by
      rw [← map_pow, hαp, map_one]
    have hσord : orderOf (primeFormFieldFactor h hC hn3 hne α) = p := orderOf_eq_prime hσp hσ1
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3 hne hp hp2 hp2
        α hord _ rfl hσord
    refine ⟨primeFormConjHom h _ M, ⟨M, rfl⟩,
      primeFormFieldHom h hC (primeFormFieldFactor h hC hn3 hne α), ⟨_, hσord, rfl⟩, ?_⟩
    rw [← hM]
    group
  ·
    rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    exact fixedSubgroup_eq_of_zpowers_eq (primeFormFieldHom h hC)
      (zpowers_ringEquiv_eq_of_orderOf Nat.prime_two (by omega) hKcard hσ hτ)
  ·
    rintro _ ⟨σ, hσ, rfl⟩ hdvd x hx hcomm
    obtain ⟨-, -, -, -, -, -, -, -, -, hsimple, h72⟩ :=
      prime_subfield_fixed_group_package h hp hp2 hσ n hn3 hne hZ
    have hFeq : fixedSubgroup (primeFormFieldHom h hC σ) = fieldFixedPSU h n σ :=
      Subgroup.ext fun _ => Iff.rfl
    rw [hFeq] at hx hcomm hdvd
    by_cases hq₀ : n = 3 ∧ 2 ^ (f / p) = 2
    · exfalso
      have h72' := (h72 hq₀ (by omega)).1
      rw [h72'] at hdvd
      have h2 : p ∣ 2 ^ 3 * 3 ^ 2 := by norm_num; exact hdvd
      rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
        omega
    · obtain ⟨hs, hnab, -⟩ := hsimple hq₀
      have hnab' : ∃ a b : ↥(fieldFixedPSU h n σ), a * b ≠ b * a := by
        push Not at hnab
        exact hnab
      have hz : (⟨x, hx⟩ : ↥(fieldFixedPSU h n σ)) ∈ Subgroup.center ↥(fieldFixedPSU h n σ) := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hcomm g g.2).symm
      rw [center_eq_bot_of_simple' hnab', Subgroup.mem_bot] at hz
      exact congrArg Subtype.val hz
  ·
    rintro _ ⟨σ, hσ, rfl⟩ d hd hne'
    obtain ⟨A, rfl⟩ := hd
    obtain ⟨hpf, -, -, -, -, -, hrange, -, -, -, h72⟩ :=
      prime_subfield_fixed_group_package h hp hp2 hσ n hn3 hne hZ
    have hFeq : fixedSubgroup (primeFormFieldHom h hC σ) = fieldFixedPSU h n σ :=
      Subgroup.ext fun _ => Iff.rfl
    by_cases hq₀ : n = 3 ∧ 2 ^ (f / p) = 2
    · right
      rw [hFeq, (h72 hq₀ (by omega)).1]
      intro hdvd
      have h2 : p ∣ 2 ^ 3 * 3 ^ 2 := by norm_num; exact hdvd
      rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
        omega
    · left
      have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
      have hne3 : ¬(n = 3 ∧ f / p = 1) := fun hc => hq₀ ⟨hc.1, by rw [hc.2]; rfl⟩
      rw [hFeq, ← hrange, range_subfieldPSU_eq_map] at hne' ⊢
      have hne'' : (suSub h (fixSubfield_unitaryFieldData h hp hp2 hσ) hbar n).map
          (primeFormConjSU h _ A).toMonoidHom ≠
            suSub h (fixSubfield_unitaryFieldData h hp hp2 hσ) hbar n := by
        intro hh
        apply hne'
        rw [map_primeFormConjHom_map_mk, hh]
      have hgen := hpair f (f / p) K h (fixSubfield σ)
        (fixSubfield_unitaryFieldData h hp hp2 hσ) hbar p hp hp5
        (Nat.mul_div_cancel' hpf).symm hne3 A hne''
      have h4 := congrArg (Subgroup.map (QuotientGroup.mk' (normOneScalars h
        (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n))) hgen
      rw [map_closure_union, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
        at h4
      rw [map_primeFormConjHom_map_mk]
      exact h4

theorem extSeitzAtOuterFor_twistedA_of_pair {m : ℕ} (hm2 : 2 ≤ m) (hm4 : m ≤ 4)
    (hpair : SubfieldPairSU (m + 1)) {q : TauCeti.PrimePower} (hq2 : q.p = 2) (P : ℕ → Prop)
    (hP : ∀ p, P p → p.Prime → 5 ≤ p → ¬ p ∣ Nat.gcd (m + 1) (q.p ^ q.exponent + 1)) :
    ExtSeitzAtOuterFor (.twistedA m q) P := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd hPp E hE hc hout
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hℓ, hf, hn3, hne, F, _, hU, ⟨θ⟩⟩ :=
    exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv e0)
  have hd : FieldAutData K p :=
    (fieldAutData_primeFormP (by omega) (by omega) hpair hU hq2 hne hp hp5
      (hP p hPp hp hp5)).of_mulEquiv θ hp
  left
  exact closure_fixUnion_eq_top_of_fieldAutData hnab hp hd E hc hout

theorem not_dvd_gcd_of_lt {a b p : ℕ} (ha : 0 < a) (hap : a < p) : ¬ p ∣ Nat.gcd a b :=
  fun hd => absurd (Nat.le_of_dvd ha (hd.trans (Nat.gcd_dvd_left a b))) (by omega)

theorem extSeitzAtOuter_twistedA_small_of_pair {m : ℕ} (hm2 : 2 ≤ m) (hm3 : m ≤ 3)
    (hpair : SubfieldPairSU (m + 1)) {q : TauCeti.PrimePower} (hq2 : q.p = 2) :
    ExtSeitzAtOuter (.twistedA m q) := by
  have h := extSeitzAtOuterFor_twistedA_of_pair hm2 (by omega) hpair hq2 (fun _ => True)
    fun p _ _ hp5 => not_dvd_gcd_of_lt (by omega) (by omega)
  exact fun K _ _ _ hnab hiso p hp hp5 hpd E hE hc hout =>
    h K hnab hiso p hp hp5 hpd trivial E hE hc hout

theorem extSeitzAtOuter_twistedA_four_of_pair (hpair : SubfieldPairSU 5)
    {q : TauCeti.PrimePower} (hq2 : q.p = 2) (h5 : ¬ 5 ∣ q.p ^ q.exponent + 1) :
    ExtSeitzAtOuter (.twistedA 4 q) := by
  have h := extSeitzAtOuterFor_twistedA_of_pair (m := 4) (by norm_num) le_rfl hpair hq2
    (fun _ => True) fun p _ hp hp5 hd => by
      have h1 : p ∣ 5 := hd.trans (Nat.gcd_dvd_left 5 _)
      have hp5' : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h1
      subst hp5'
      exact h5 (hd.trans (Nat.gcd_dvd_right 5 _))
  exact fun K _ _ _ hnab hiso p hp hp5 hpd E hE hc hout =>
    h K hnab hiso p hp hp5 hpd trivial E hE hc hout

theorem extSeitzAtOuterFor_twistedA_four_ne_five_of_pair (hpair : SubfieldPairSU 5)
    {q : TauCeti.PrimePower} (hq2 : q.p = 2) :
    ExtSeitzAtOuterFor (.twistedA 4 q) fun p => p ≠ 5 :=
  extSeitzAtOuterFor_twistedA_of_pair (m := 4) (by norm_num) le_rfl hpair hq2 _
    fun p hp5 hp _ hd => hp5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1
      (hd.trans (Nat.gcd_dvd_left 5 _)))

end Main

end CFSG.RankThree.PartOne.CTP
