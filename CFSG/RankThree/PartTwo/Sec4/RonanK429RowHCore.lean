module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowsS

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU)

section Burnside

theorem subsingleton_of_isPerfect_of_card_primeFactors {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] (h : (Nat.card X).primeFactors.card ≤ 2) : Subsingleton X := by
  by_contra hX
  rw [not_subsingleton_iff_nontrivial] at hX
  exact Group.IsPerfect.not_isSolvable X
    (CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two h)

theorem primeFactors_pow_subset' (n k : ℕ) : (n ^ k).primeFactors ⊆ n.primeFactors := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [Nat.primeFactors_pow n hk.ne']

theorem primeFactors_card_le_two_of_dvd {c p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hc : c ∣ p ^ a * q ^ b) : c.primeFactors.card ≤ 2 := by
  have h0 : p ^ a * q ^ b ≠ 0 := mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)
  have hsub : c.primeFactors ⊆ {p, q} := by
    intro r hr
    have hr' := Nat.primeFactors_mono hc h0 hr
    rw [Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)] at hr'
    rcases Finset.mem_union.mp hr' with h | h
    · have := primeFactors_pow_subset' p a h
      rw [hp.primeFactors] at this
      rw [Finset.mem_singleton.mp this]
      exact Finset.mem_insert_self p {q}
    · have := primeFactors_pow_subset' q b h
      rw [hq.primeFactors] at this
      rw [Finset.mem_singleton.mp this]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  exact (Finset.card_le_card hsub).trans (Finset.card_le_two)

@[expose] def smallPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]

theorem prime_of_mem_smallPrimes {p : ℕ} (hp : p ∈ smallPrimes) : p.Prime := by
  simp only [smallPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

@[expose] def twoPrimeOK (c : ℕ) : Bool :=
  smallPrimes.any fun p => smallPrimes.any fun q => decide (c ∣ p ^ 64 * q ^ 64)

theorem primeFactors_card_le_two_of_twoPrimeOK {c : ℕ} (h : twoPrimeOK c = true) :
    c.primeFactors.card ≤ 2 := by
  simp only [twoPrimeOK, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨p, hp, q, hq, hc⟩ := h
  exact primeFactors_card_le_two_of_dvd (prime_of_mem_smallPrimes hp)
    (prime_of_mem_smallPrimes hq) hc

end Burnside

section Orders

@[expose] def typeOrders (M B : ℕ) : List ℕ :=
  ([2520, 95040, 443520, 604800].filter fun t => decide (t ∣ M)) ++
    ((List.range B).filter fun q => decide (2 ≤ q) && decide (q ^ 3 ∣ M) && decide (q % 3 = 1) &&
      decide (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ∣ 3 * M)).map
        (fun q => q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / 3) ++
    ((List.range B).filter fun q => decide (2 < q) && decide (q ^ 3 ∣ M) && decide (q % 3 = 2) &&
      decide (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ∣ 3 * M)).map
        (fun q => q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / 3)

theorem lt_of_pow_three_dvd {M B q : ℕ} (hM0 : 0 < M) (hB : M < B ^ 3) (hq : q ^ 3 ∣ M) :
    q < B := by
  by_contra hqB
  have h1 : B ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (not_lt.mp hqB) 3
  have h2 := Nat.le_of_dvd hM0 hq
  omega

theorem subsingleton_of_mulEquiv_projSU_three_two {X : Type} [Group X] [Finite X]
    [Group.IsPerfect X] (e : X ≃* projSU 3 2 1) : Subsingleton X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := KS14.card_projSU_three_mul_gcd 2 1 le_rfl
  rw [← Nat.card_congr e.toEquiv] at hc
  have h72 : Nat.card X = 72 := by norm_num at hc; omega
  refine subsingleton_of_isPerfect_of_card_primeFactors ?_
  rw [h72]
  exact primeFactors_card_le_two_of_dvd (p := 2) (q := 3) (a := 3) (b := 2) Nat.prime_two
    Nat.prime_three (by norm_num)

theorem mem_typeOrders_of_small {M B t : ℕ} (ht : t ∈ [2520, 95040, 443520, 604800])
    (hM : t ∣ M) : t ∈ typeOrders M B := by
  unfold typeOrders
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_filter.mpr ⟨ht, ?_⟩))
  simpa using hM

theorem mem_typeOrders_of_sl {M B q : ℕ} (hq : q < B) (h2 : 2 ≤ q) (h3 : q ^ 3 ∣ M)
    (h1 : q % 3 = 1) (hd : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ∣ 3 * M) :
    q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / 3 ∈ typeOrders M B := by
  unfold typeOrders
  refine List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr
    ⟨q, List.mem_filter.mpr ⟨List.mem_range.mpr hq, ?_⟩, rfl⟩))
  simp [h2, h3, h1, hd]

theorem mem_typeOrders_of_su {M B q : ℕ} (hq : q < B) (h2 : 2 < q) (h3 : q ^ 3 ∣ M)
    (h1 : q % 3 = 2) (hd : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ∣ 3 * M) :
    q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / 3 ∈ typeOrders M B := by
  unfold typeOrders
  refine List.mem_append_right _ (List.mem_map.mpr
    ⟨q, List.mem_filter.mpr ⟨List.mem_range.mpr hq, ?_⟩, rfl⟩)
  simp [h2, h3, h1, hd]

theorem pow_three_dvd_of_card {M n q m : ℕ} (hq : ¬ 3 ∣ q) (hc : n * 3 = q ^ 3 * m)
    (hM : n ∣ M) : q ^ 3 ∣ M := by
  have hdvd : q ^ 3 ∣ n * 3 := hc ▸ Dvd.intro _ rfl
  have hcop : Nat.Coprime (q ^ 3) 3 := by
    refine Nat.Coprime.pow_left 3 ?_
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    exact hq
  exact (hcop.dvd_of_dvd_mul_right hdvd).trans hM

theorem card_mem_typeOrders {X : Type} [Group X] [Finite X] [Group.IsPerfect X] [Nontrivial X]
    {M B : ℕ} (hM0 : 0 < M) (hB : M < B ^ 3) (hX : IsType429 X) (hM : Nat.card X ∣ M) :
    Nat.card X ∈ typeOrders M B := by
  rcases hX with ⟨p, e, hp, he, hiso⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · have hpp : p.Prime := hp.out
    have hq2 : 2 ≤ p ^ e := hpp.two_le.trans (Nat.le_self_pow (by omega) p)
    rcases hiso with ⟨h1, ⟨φ⟩⟩ | ⟨h2, ⟨φ⟩⟩
    · have hc := KS14.card_projSL_three_mul_gcd (GaloisField p e)
      rw [← Nat.card_congr φ.toEquiv, GaloisField.card p e (by omega)] at hc
      have hg : Nat.gcd 3 (p ^ e - 1) = 3 := Nat.gcd_eq_left (by omega)
      rw [hg] at hc
      have hd3 : (p ^ e) ^ 3 ∣ M := pow_three_dvd_of_card (by omega) hc hM
      have hmem := mem_typeOrders_of_sl (B := B) (lt_of_pow_three_dvd hM0 hB hd3) hq2 hd3 h1
        (by rw [← hc, mul_comm]; exact Nat.mul_dvd_mul_left 3 hM)
      rwa [← hc, Nat.mul_div_cancel _ (by norm_num : 0 < 3)] at hmem
    · by_cases hq : p ^ e = 2
      · exfalso
        have hp2 : p = 2 := by
          rcases (Nat.prime_two.eq_one_or_self_of_dvd p
            (hq ▸ dvd_pow_self p (by omega))) with h | h
          · exact absurd h hpp.one_lt.ne'
          · exact h
        subst hp2
        have he1 : e = 1 := Nat.pow_right_injective (le_refl 2) (by simpa using hq)
        subst he1
        have := subsingleton_of_mulEquiv_projSU_three_two φ
        exact not_subsingleton X this
      · have hc := KS14.card_projSU_three_mul_gcd p e he
        rw [← Nat.card_congr φ.toEquiv] at hc
        have hg : Nat.gcd 3 (p ^ e + 1) = 3 := Nat.gcd_eq_left (by omega)
        rw [hg] at hc
        have hd3 : (p ^ e) ^ 3 ∣ M := pow_three_dvd_of_card (by omega) hc hM
        have hmem := mem_typeOrders_of_su (B := B) (lt_of_pow_three_dvd hM0 hB hd3) (by omega)
          hd3 h2 (by rw [← hc, mul_comm]; exact Nat.mul_dvd_mul_left 3 hM)
        rwa [← hc, Nat.mul_div_cancel _ (by norm_num : 0 < 3)] at hmem
  · have h := Nat.card_congr φ.toEquiv
    rw [KS14.card_alternatingGroup_five_seven_ten.2.1] at h
    rw [h] at hM ⊢
    exact mem_typeOrders_of_small (by simp) hM
  · have h := Nat.card_congr φ.toEquiv
    rw [KS14.card_nativeM12] at h
    rw [h] at hM ⊢
    exact mem_typeOrders_of_small (by simp) hM
  · have h := Nat.card_congr φ.toEquiv
    rw [KS14.card_nativeM22] at h
    rw [h] at hM ⊢
    exact mem_typeOrders_of_small (by simp) hM
  · have h := Nat.card_congr φ.toEquiv
    rw [KS14.card_nativeJ2] at h
    rw [h] at hM ⊢
    exact mem_typeOrders_of_small (by simp) hM

theorem not_isType429_of_dvd {X : Type} [Group X] [Finite X] [Group.IsPerfect X] [Nontrivial X]
    {M B : ℕ} (hM0 : 0 < M) (hB : M < B ^ 3) (hfree : typeOrders M B = []) (hM : Nat.card X ∣ M) :
    ¬ IsType429 X := fun hX => by
  have := card_mem_typeOrders hM0 hB hX hM
  rw [hfree] at this
  exact List.not_mem_nil this

end Orders

section Quotient

variable {S : Type} [Group S] [Finite S]

theorem exists_card_eq_mul_two_pow (K : Subgroup S) :
    ∃ a : ℕ, Nat.card K = Nat.card (K ⧸ CFSG.pCore 2 K) * 2 ^ a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)).exists_card_eq
  exact ⟨a, by rw [← ha, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]⟩

theorem nontrivial_of_isType429 {X : Type} [Group X] [Finite X] (hX : IsType429 X) :
    Nontrivial X := by
  rcases hX with ⟨p, e, hp, he, hiso⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · have hpp : p.Prime := hp.out
    rcases hiso with ⟨h1, ⟨φ⟩⟩ | ⟨h2, ⟨φ⟩⟩
    · have hc := KS14.card_projSL_three_mul_gcd (GaloisField p e)
      rw [← Nat.card_congr φ.toEquiv, GaloisField.card p e (by omega)] at hc
      refine Finite.one_lt_card_iff_nontrivial.mp ?_
      by_contra h
      have h1' : Nat.card X ≤ 1 := not_lt.mp h
      have hq2 : 2 ≤ p ^ e := hpp.two_le.trans (Nat.le_self_pow (by omega) p)
      have hg : Nat.gcd 3 (p ^ e - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
      have hlhs : Nat.card X * Nat.gcd 3 (p ^ e - 1) ≤ 3 :=
        (Nat.mul_le_mul h1' hg).trans (by norm_num)
      have hrhs : 8 ≤ (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) := by
        have h8 : 8 ≤ (p ^ e) ^ 3 := by
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ (p ^ e) ^ 3 := Nat.pow_le_pow_left hq2 3
        have ha : 1 ≤ (p ^ e) ^ 2 - 1 := by
          have : 4 ≤ (p ^ e) ^ 2 := by nlinarith
          omega
        have hb : 1 ≤ (p ^ e) ^ 3 - 1 := by omega
        calc 8 ≤ (p ^ e) ^ 3 * 1 := by omega
          _ ≤ (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) :=
            Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega)
              (by omega)))
      omega
    · have he1 : 1 ≤ e := by
        rcases Nat.eq_zero_or_pos e with rfl | h
        · simp at h2
        · exact h
      have hc := KS14.card_projSU_three_mul_gcd p e he1
      rw [← Nat.card_congr φ.toEquiv] at hc
      refine Finite.one_lt_card_iff_nontrivial.mp ?_
      by_contra h
      have h1' : Nat.card X ≤ 1 := not_lt.mp h
      have hq2 : 2 ≤ p ^ e := hpp.two_le.trans (Nat.le_self_pow (by omega) p)
      have hg : Nat.gcd 3 (p ^ e + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
      have hlhs : Nat.card X * Nat.gcd 3 (p ^ e + 1) ≤ 3 :=
        (Nat.mul_le_mul h1' hg).trans (by norm_num)
      have hrhs : 8 ≤ (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) := by
        have h8 : 8 ≤ (p ^ e) ^ 3 := by
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ (p ^ e) ^ 3 := Nat.pow_le_pow_left hq2 3
        have ha : 1 ≤ (p ^ e) ^ 2 - 1 := by
          have : 4 ≤ (p ^ e) ^ 2 := by nlinarith
          omega
        calc 8 ≤ (p ^ e) ^ 3 * 1 := by omega
          _ ≤ (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) :=
            Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega)
              (by omega)))
      omega
  all_goals
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [Nat.card_congr φ.toEquiv]
  · rw [KS14.card_alternatingGroup_five_seven_ten.2.1]; norm_num
  · rw [KS14.card_nativeM12]; norm_num
  · rw [KS14.card_nativeM22]; norm_num
  · rw [KS14.card_nativeJ2]; norm_num

end Quotient

section Transport

theorem isType429_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : IsType429 X) :
    IsType429 Y := by
  rcases h with ⟨p, e', hp, he, (⟨h1, ⟨φ⟩⟩ | ⟨h2, ⟨φ⟩⟩)⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact Or.inl ⟨p, e', hp, he, Or.inl ⟨h1, ⟨e.symm.trans φ⟩⟩⟩
  · exact Or.inl ⟨p, e', hp, he, Or.inr ⟨h2, ⟨e.symm.trans φ⟩⟩⟩
  · exact Or.inr (Or.inl ⟨e.symm.trans φ⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.symm.trans φ⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans φ⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e.symm.trans φ⟩)))

@[expose] noncomputable def quotPCoreCongr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    X ⧸ CFSG.pCore 2 X ≃* Y ⧸ CFSG.pCore 2 Y :=
  QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)

theorem isType429_quot_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsType429 (X ⧸ CFSG.pCore 2 X)) : IsType429 (Y ⧸ CFSG.pCore 2 Y) :=
  isType429_congr (quotPCoreCongr e) h

end Transport

section Good

variable {S : Type} [Group S]

@[expose] def Good429 (C : Subgroup S) : Prop :=
  ∀ K : Subgroup S, K ≤ C → Group.IsPerfect K → (K.subgroupOf C).IsSubnormal →
    ¬ IsType429 (K ⧸ CFSG.pCore 2 K)

theorem center_eq_bot_of_simple_nonab [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) :
    Subgroup.center S = ⊥ := by
  rcases (inferInstance : (Subgroup.center S).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center S := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem autFix_conj (s : S) : autFix (MulAut.conj s) = Subgroup.centralizer ({s} : Set S) := by
  ext z
  rw [mem_autFix, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc z * s = s * z * s⁻¹ * s := by rw [h]
      _ = s * z := by group
  · intro h
    rw [← h]
    group

variable [Finite S]

theorem noCfgS429_of_good (h : ∀ σ : MulAut S, σ ^ 3 = 1 → σ ≠ 1 → Good429 (autFix σ)) :
    NoCfgS429 S := fun A σ K hc =>
  h σ (hc.isE27.1.2 σ hc.mem) hc.ne_one K hc.le_autFix hc.isPerfect hc.isSubnormal hc.isType

open CFSG.ComponentClassification.OuterAutomorphisms (Outer) in
theorem noCfgS429_of_inner (hZ : Subgroup.center S = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer S))
    (hgood : ∀ s : S, orderOf s = 3 → Good429 (Subgroup.centralizer ({s} : Set S))) :
    NoCfgS429 S := by
  refine noCfgS429_of_good fun σ h3 h1 => ?_
  obtain ⟨s, rfl⟩ := cubeInner_of_not_three_dvd_card_outer hout σ h3
  have hs3 : s ^ 3 = 1 := by
    have h' : MulAut.conj (s ^ 3) = 1 := by rw [map_pow, h3]
    have hz : s ^ 3 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut S => φ g) h'
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * s ^ 3 = s ^ 3 * g * (s ^ 3)⁻¹ * s ^ 3 := by rw [this]
        _ = s ^ 3 * g := by group
    rw [hZ, Subgroup.mem_bot] at hz
    exact hz
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact h1 (map_one _)
  have hso : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  rw [autFix_conj]
  exact hgood s hso

end Good

section Criteria

variable {S : Type} [Group S] [Finite S]

theorem good429_of_card {C : Subgroup S} {M B : ℕ} (hC : Nat.card C = M) (hB : M < B ^ 3)
    (hfree : typeOrders M B = []) : Good429 C := by
  intro K hKC hKp hKs hT
  haveI := hKp
  haveI := nontrivial_of_isType429 hT
  have hM0 : 0 < M := hC ▸ Nat.card_pos
  refine not_isType429_of_dvd hM0 hB hfree ?_ hT
  obtain ⟨a, ha⟩ := exists_card_eq_mul_two_pow K
  have h1 : Nat.card (K ⧸ CFSG.pCore 2 K) ∣ Nat.card K := ha ▸ Dvd.intro _ rfl
  exact h1.trans (hC ▸ Subgroup.card_dvd_of_le hKC)

theorem good429_of_card_dvd {C : Subgroup S} {M B : ℕ} (hC : Nat.card C ∣ M) (hM0 : 0 < M)
    (hB : M < B ^ 3) (hfree : typeOrders M B = []) : Good429 C := by
  intro K hKC hKp hKs hT
  haveI := hKp
  haveI := nontrivial_of_isType429 hT
  refine not_isType429_of_dvd hM0 hB hfree ?_ hT
  obtain ⟨a, ha⟩ := exists_card_eq_mul_two_pow K
  have h1 : Nat.card (K ⧸ CFSG.pCore 2 K) ∣ Nat.card K := ha ▸ Dvd.intro _ rfl
  exact h1.trans ((Subgroup.card_dvd_of_le hKC).trans hC)

theorem le_of_isPerfect_of_card_le {C D K : Subgroup S} (hDC : D ≤ C) (hKC : K ≤ C)
    [hK : Group.IsPerfect K] (hidx : Nat.card C ≤ 4 * Nat.card D) : K ≤ D := by
  set H : Subgroup C := D.subgroupOf C with hH
  have hHcard : Nat.card H = Nat.card D := by
    rw [hH]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv
  have hidxH : H.index ≤ 4 := by
    have hmul := Subgroup.card_mul_index H
    rw [hHcard] at hmul
    have hD0 : 0 < Nat.card D := Nat.card_pos
    by_contra hlt
    push_neg at hlt
    have : Nat.card D * 5 ≤ Nat.card D * H.index := Nat.mul_le_mul_left _ hlt
    omega
  set N := H.normalCore
  have hNidx : N.index ∣ 24 :=
    (H.index_normalCore_dvd_factorial_index).trans (by
      interval_cases h : H.index <;> decide)
  set K' : Subgroup C := K.subgroupOf C
  haveI : Group.IsPerfect K' :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKC).symm.toMonoidHom)
      (MulEquiv.surjective _)
  haveI : Group.IsPerfect (K'.map (QuotientGroup.mk' N)) := Group.IsPerfect.map _
  have hcard : Nat.card (K'.map (QuotientGroup.mk' N)) ∣ 24 :=
    (Subgroup.card_subgroup_dvd_card _).trans hNidx
  haveI : Subsingleton (K'.map (QuotientGroup.mk' N)) :=
    subsingleton_of_isPerfect_of_card_primeFactors (primeFactors_card_le_two_of_dvd
      (a := 3) (b := 1) Nat.prime_two Nat.prime_three (hcard.trans (by norm_num)))
  have hbot : K'.map (QuotientGroup.mk' N) = ⊥ := Subgroup.eq_bot_of_subsingleton _
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  intro k hk
  have hk' : (⟨k, hKC hk⟩ : C) ∈ K' := hk
  exact (H.normalCore_le (hbot hk'))

theorem isSubnormal_subgroupOf_of_le {C D K : Subgroup S} (hDC : D ≤ C) (hKD : K ≤ D)
    (h : (K.subgroupOf C).IsSubnormal) : (K.subgroupOf D).IsSubnormal := by
  have heq : (K.subgroupOf C).comap (Subgroup.inclusion hDC) = K.subgroupOf D := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [← heq]
  exact h.comap _

theorem eq_of_isSubnormal_of_index {D K : Subgroup S} [Group.IsPerfect D] (hKD : K ≤ D)
    (hs : (K.subgroupOf D).IsSubnormal) (h2 : (K.subgroupOf D).index.primeFactors.card ≤ 2) :
    K = D := by
  by_contra hne
  have hne' : K.subgroupOf D ≠ ⊤ := by
    intro htop
    exact hne (le_antisymm hKD (Subgroup.subgroupOf_eq_top.mp htop))
  obtain ⟨N, hN, hKN, hNtop⟩ := hs.exists_normal_and_le_and_lt_top_of_ne hne'
  haveI := hN
  have hdvd : N.index ∣ (K.subgroupOf D).index := Subgroup.index_dvd_of_le hKN
  have h2' : (Nat.card (D ⧸ N)).primeFactors.card ≤ 2 := by
    rw [← Subgroup.index]
    exact (Finset.card_le_card (Nat.primeFactors_mono hdvd
      (Subgroup.index_ne_zero_of_finite))).trans h2
  haveI := subsingleton_of_isPerfect_of_card_primeFactors h2'
  have hNt : N = ⊤ := by
    rw [← Subgroup.index_eq_one]
    rw [Subgroup.index, Nat.card_eq_one_iff_unique]
    exact ⟨inferInstance, ⟨1⟩⟩
  exact hNtop.ne hNt

@[expose] def residOK (M B : ℕ) : Bool :=
  (typeOrders M B).all fun t => (List.range 64).all fun a =>
    !decide (2 ^ a * t ∣ M) || decide (2 ^ a * t = M) || twoPrimeOK (M / (2 ^ a * t))

theorem good429_of_residual {C D : Subgroup S} (hDC : D ≤ C) (hidx : Nat.card C ≤ 4 * Nat.card D)
    [Group.IsPerfect D] {M B : ℕ} (hM : Nat.card D = M) (hB : M < B ^ 3) (h64 : M < 2 ^ 64)
    (hres : residOK M B = true) (hD : ¬ IsType429 (D ⧸ CFSG.pCore 2 D)) : Good429 C := by
  intro K hKC hKp hKs hT
  haveI := hKp
  have hKD : K ≤ D := le_of_isPerfect_of_card_le hDC hKC hidx
  have hs : (K.subgroupOf D).IsSubnormal := isSubnormal_subgroupOf_of_le hDC hKD hKs
  by_cases hKeq : K = D
  · subst hKeq
    exact hD hT
  · apply hKeq
    refine eq_of_isSubnormal_of_index hKD hs ?_
    haveI := nontrivial_of_isType429 hT
    have hM0 : 0 < M := hM ▸ Nat.card_pos
    obtain ⟨a, ha⟩ := exists_card_eq_mul_two_pow K
    have hKdvd : Nat.card K ∣ M := hM ▸ Subgroup.card_dvd_of_le hKD
    have hmem := card_mem_typeOrders hM0 hB hT
      ((show Nat.card (K ⧸ CFSG.pCore 2 K) ∣ Nat.card K from ha ▸ Dvd.intro _ rfl).trans hKdvd)
    have hidxK : (K.subgroupOf D).index = M / Nat.card K := by
      have hmul := Subgroup.card_mul_index (K.subgroupOf D)
      have hc : Nat.card (K.subgroupOf D) = Nat.card K :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKD).toEquiv
      rw [hc, hM] at hmul
      rw [← hmul, Nat.mul_div_cancel_left _ Nat.card_pos]
    have hlt : Nat.card K < M := by
      rw [← hM]
      refine lt_of_le_of_ne (Subgroup.card_le_of_le hKD) fun hEq => hKeq ?_
      exact Subgroup.eq_of_le_of_card_ge hKD hEq.ge
    have ha64 : a < 64 := by
      have h2a : 2 ^ a ≤ M := by
        have : 2 ^ a ∣ M := (Dvd.intro_left _ ha.symm).trans hKdvd
        exact Nat.le_of_dvd hM0 this
      by_contra h
      push_neg at h
      have : 2 ^ 64 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) h
      omega
    simp only [residOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, decide_eq_true_eq] at hres
    rcases hres _ hmem a ha64 with (h1 | h1) | h1
    · exact absurd (by rw [mul_comm, ← ha]; exact hKdvd) h1
    · rw [mul_comm, ← ha] at h1
      omega
    · rw [hidxK, ha, mul_comm]
      exact primeFactors_card_le_two_of_twoPrimeOK h1

@[expose] def noEqOK (M B : ℕ) : Bool :=
  (typeOrders M B).all fun t => (List.range 64).all fun a => decide (2 ^ a * t ≠ M)

theorem not_isType429_quot_of_noEqOK {D : Subgroup S} [Group.IsPerfect D] {M B : ℕ}
    (hM : Nat.card D = M) (hB : M < B ^ 3) (h64 : M < 2 ^ 64) (h : noEqOK M B = true) :
    ¬ IsType429 (D ⧸ CFSG.pCore 2 D) := by
  intro hT
  haveI := nontrivial_of_isType429 hT
  have hM0 : 0 < M := hM ▸ Nat.card_pos
  obtain ⟨a, ha⟩ := exists_card_eq_mul_two_pow D
  have hmem := card_mem_typeOrders hM0 hB hT
    ((show Nat.card (D ⧸ CFSG.pCore 2 D) ∣ Nat.card D from ha ▸ Dvd.intro _ rfl).trans hM.dvd)
  have ha64 : a < 64 := by
    have h2a : 2 ^ a ≤ M := Nat.le_of_dvd hM0 (hM ▸ (Dvd.intro_left _ ha.symm))
    by_contra hge
    push_neg at hge
    have : 2 ^ 64 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hge
    omega
  simp only [noEqOK, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h _ hmem a ha64 (by rw [mul_comm, ← ha, hM])

end Criteria

section Spor

theorem rowSOf429_spor {s : TauCeti.SporadicName}
    (hb : Nonempty (Blueprint.NativeSporadic.Carrier s ≃* Spor s))
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier s) → NoCfgS429 S) :
    RowSOf429 (Spor s) :=
  rowSOf429_of_noCfg fun S _ _ hs hna ⟨e⟩ => by
    obtain ⟨b⟩ := hb
    exact h S hs hna ⟨e.trans b.symm⟩

end Spor

end CFSG.RankThree.PartTwo.Sec4.RonanK429H
