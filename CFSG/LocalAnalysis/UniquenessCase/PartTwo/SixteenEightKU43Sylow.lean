module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43

open Subgroup

section General

variable {T : Type*} [Group T] [Finite T]

theorem card_sylow_eq_prime {p : ℕ} [Fact p.Prime] (P : Sylow p T) (hdvd : p ∣ Nat.card T)
    (hsq : ¬ p ^ 2 ∣ Nat.card T) : Nat.card P = p := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp P.isPGroup'
  have hmul : Nat.card P * (P : Subgroup T).index = Nat.card T := (P : Subgroup T).card_mul_index
  have hnd : ¬ p ∣ (P : Subgroup T).index := P.not_dvd_index
  rcases k with _ | _ | k
  · exfalso
    rw [hk, pow_zero, one_mul] at hmul
    exact hnd (hmul ▸ hdvd)
  · simpa using hk
  · exfalso
    apply hsq
    rw [← hmul, hk]
    exact Dvd.dvd.mul_right (pow_dvd_pow p (by omega)) _

theorem card_sylow_mul_totient_le {p d : ℕ} [Fact p.Prime]
    (hP : ∀ P : Sylow p T, Nat.card P = d ∧ IsCyclic P) :
    Nat.card (Sylow p T) * d.totient ≤ Nat.card {x : T // orderOf x = d} := by
  classical
  haveI : Fintype T := Fintype.ofFinite T
  let f : (Σ P : Sylow p T, {a : (P : Subgroup T) // orderOf a = d}) → {x : T // orderOf x = d} :=
    fun x => ⟨(x.2.1 : T), by rw [Subgroup.orderOf_coe]; exact x.2.2⟩
  have hzp : ∀ (P : Sylow p T) (a : (P : Subgroup T)), orderOf a = d →
      zpowers (a : T) = (P : Subgroup T) := by
    intro P a ha
    refine Subgroup.eq_of_le_of_card_ge ((zpowers_le).mpr a.2) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ha, (hP P).1]
  have hf : Function.Injective f := by
    rintro ⟨P, a, ha⟩ ⟨Q, b, hb⟩ hab
    have hab' : (a : T) = (b : T) := congrArg Subtype.val hab
    have hPQ : P = Q := Sylow.ext ((hzp P a ha).symm.trans (hab' ▸ hzp Q b hb))
    subst hPQ
    have : a = b := Subtype.ext hab'
    subst this
    rfl
  have hcard : ∀ P : Sylow p T, Nat.card {a : (P : Subgroup T) // orderOf a = d} = d.totient := by
    intro P
    haveI := (hP P).2
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_orderOf_eq_totient (by rw [← Nat.card_eq_fintype_card, (hP P).1])
  haveI : Fintype (Sylow p T) := Fintype.ofFinite _
  calc Nat.card (Sylow p T) * d.totient
      = Nat.card (Σ P : Sylow p T, {a : (P : Subgroup T) // orderOf a = d}) := by
        rw [Nat.card_sigma, Finset.sum_congr rfl (fun P _ => hcard P), Finset.sum_const,
          Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
    _ ≤ Nat.card {x : T // orderOf x = d} := Nat.card_le_card_of_injective f hf

theorem card_three_orders_le {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Nat.card {x : T // orderOf x = a} + Nat.card {x : T // orderOf x = b} +
      Nat.card {x : T // orderOf x = c} ≤ Nat.card T := by
  let f : ({x : T // orderOf x = a} ⊕ {x : T // orderOf x = b}) ⊕ {x : T // orderOf x = c} → T :=
    Sum.elim (Sum.elim Subtype.val Subtype.val) Subtype.val
  have hf : Function.Injective f := by
    rintro ((⟨x, hx⟩ | ⟨x, hx⟩) | ⟨x, hx⟩) ((⟨y, hy⟩ | ⟨y, hy⟩) | ⟨y, hy⟩) h <;>
      simp only [f, Sum.elim_inl, Sum.elim_inr] at h <;> subst h
    all_goals first | rfl | (exfalso; omega)
  calc _ = Nat.card (({x : T // orderOf x = a} ⊕ {x : T // orderOf x = b}) ⊕
        {x : T // orderOf x = c}) := by rw [Nat.card_sum, Nat.card_sum]
    _ ≤ Nat.card T := Nat.card_le_card_of_injective f hf

end General

structure U43CountingFacts (S : Type*) [Group S] : Prop where
  card : Nat.card S = 3265920
  not27 : ∀ g : S, orderOf g ≠ 27
  norm5 : ∀ P : Subgroup S, Nat.card P = 5 → Nat.card (normalizer (P : Set S)) ∣ 20
  norm7 : ∀ P : Subgroup S, Nat.card P = 7 → Nat.card (normalizer (P : Set S)) ∣ 21
  norm9 : ∀ g : S, orderOf g = 9 →
    Nat.card (normalizer ((zpowers g : Subgroup S) : Set S)) ∣ 1458

section Transfer

variable {S : Type*} [Group S] [Finite S] (X : Subgroup S)

theorem card_normalizer_dvd_map (Q : Subgroup X) :
    Nat.card (normalizer (Q : Set X)) ∣
      Nat.card (normalizer ((Q.map X.subtype : Subgroup S) : Set S)) := by
  rw [← Subgroup.card_map_of_injective (K := normalizer (Q : Set X)) X.subtype_injective]
  exact Subgroup.card_dvd_of_le (Subgroup.le_normalizer_map X.subtype)

theorem card_map_subtype (Q : Subgroup X) : Nat.card (Q.map X.subtype) = Nat.card Q :=
  Subgroup.card_map_of_injective X.subtype_injective

end Transfer


section Count

def npSet (c d m p : ℕ) : Finset ℕ :=
  if d ∣ m then ((Nat.divisors c).filter (fun N => d ∣ N ∧ N ∣ m ∧ (m / N) % p = 1)).image
    (fun N => m / N) else {0}

theorem mem_npSet {c d m p N n : ℕ} (hc : 0 < c) (hdm : d ∣ m) (hN : N ∣ c) (hdN : d ∣ N)
    (hNn : N * n = m) (hn : n % p = 1) : n ∈ npSet c d m p := by
  have hN0 : 0 < N := Nat.pos_of_dvd_of_pos hN hc
  have hdiv : m / N = n := by rw [← hNn, Nat.mul_div_cancel_left _ hN0]
  simp only [npSet, if_pos hdm]
  exact Finset.mem_image.2 ⟨N, Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨hN, hc.ne'⟩, hdN,
    Dvd.intro _ hNn, by rw [hdiv]; exact hn⟩, hdiv⟩

theorem arith_check : ∀ k ∈ Finset.Icc 1 16, 81 * k ∣ 3265920 →
    ∀ n7 ∈ npSet 21 7 (3265920 / (81 * k)) 7, ∀ n5 ∈ npSet 20 5 (3265920 / (81 * k)) 5,
    ∀ n9 ∈ npSet (Nat.gcd 1458 (3265920 / (81 * k))) 9 (3265920 / (81 * k)) 3,
      3265920 / (81 * k) < 6 * n7 + 4 * n5 + 6 * n9 := by
  decide +kernel

end Count

section General

variable {T : Type*} [Group T] [Finite T]

theorem cyc_data {p d c : ℕ} [hp : Fact p.Prime] (hP : ∀ P : Sylow p T, Nat.card P = d ∧ IsCyclic P)
    (hN : ∀ P : Sylow p T, Nat.card (normalizer (P : Set T)) ∣ c) :
    ∃ N n, N ∣ c ∧ d ∣ N ∧ N * n = Nat.card T ∧ n % p = 1 ∧
      n * d.totient ≤ Nat.card {x : T // orderOf x = d} := by
  obtain ⟨P⟩ : Nonempty (Sylow p T) := inferInstance
  refine ⟨Nat.card (normalizer (P : Set T)), Nat.card (Sylow p T), hN P, ?_, ?_, ?_,
    card_sylow_mul_totient_le hP⟩
  · rw [← (hP P).1]; exact Subgroup.card_dvd_of_le Subgroup.le_normalizer
  · rw [Sylow.card_eq_index_normalizer P]; exact (normalizer _).card_mul_index
  · have h := card_sylow_modEq_one (p := p) (G := T)
    rw [Nat.ModEq, Nat.mod_eq_of_lt hp.out.one_lt] at h
    exact h

end General

theorem noncyclic3_of_facts {S : Type*} [Group S] [Finite S] (hF : U43CountingFacts S)
    (X : Subgroup S) (hX : X.index ≤ 1365) :
    ∃ B : Subgroup S, B ≤ X ∧ IsPGroup 3 B ∧ ¬ IsCyclic B := by
  classical
  by_contra hcon
  push Not at hcon
  haveI h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI h7 : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hcyc : ∀ P : Sylow 3 X, IsCyclic P := by
    intro P
    haveI := hcon ((P : Subgroup X).map X.subtype) (map_subtype_le _) (P.isPGroup'.map _)
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (P : Subgroup X) X.subtype X.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  set m := Nat.card X with hm
  have hmn : m * X.index = 3265920 := by rw [hm, X.card_mul_index, hF.card]
  have hm0 : 0 < m := Nat.card_pos
  have hn0 : X.index ≠ 0 := by intro h; rw [h, mul_zero] at hmn; exact absurd hmn (by norm_num)
  have h27 : ∀ P : Sylow 3 X, ¬ 27 ∣ Nat.card P := by
    intro P h
    haveI := hcyc P
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
    rw [← hg] at h
    have ho := orderOf_pow_orderOf_div (orderOf_pos g).ne' h
    exact hF.not27 ((g ^ (orderOf g / 27) : P) : S)
      (by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ho])
  have hcop : ∀ P : Sylow 3 X, Nat.Coprime 3 (P : Subgroup X).index := fun P =>
    (Nat.Prime.coprime_iff_not_dvd h3.out).2 P.not_dvd_index
  obtain ⟨P3⟩ : Nonempty (Sylow 3 X) := inferInstance
  have hm27 : ¬ 27 ∣ m := by
    intro h
    rw [hm, ← (P3 : Subgroup X).card_mul_index] at h
    exact h27 P3 (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left 3 (hcop P3)) h)
  have h81 : 81 ∣ X.index := by
    have hv : padicValNat 3 m + padicValNat 3 X.index = 6 := by
      rw [← padicValNat.mul hm0.ne' hn0, hmn,
        show (3265920 : ℕ) = 3 ^ 6 * 4480 by norm_num,
        padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    have hvm : padicValNat 3 m < 3 := by
      by_contra h
      have h3m := (padicValNat_dvd_iff_le (p := 3) (n := 3) hm0.ne').2 (by omega)
      norm_num at h3m
      exact hm27 h3m
    have h81 := (padicValNat_dvd_iff_le (p := 3) (n := 4) hn0).2 (by omega)
    norm_num at h81
    exact h81
  have hmdvd : m ∣ 3265920 := Dvd.intro _ hmn
  have d7 : ∃ n ∈ npSet 21 7 m 7, 6 * n ≤ Nat.card {x : X // orderOf x = 7} := by
    by_cases h : 7 ∣ m
    · have hsq : ¬ 7 ^ 2 ∣ m := fun h' => by have := h'.trans hmdvd; norm_num at this
      obtain ⟨N, n, hN, hdN, hNn, hn, hc⟩ := cyc_data (T := X) (p := 7) (d := 7) (c := 21)
        (fun P => ⟨card_sylow_eq_prime P h hsq,
          isCyclic_of_prime_card (card_sylow_eq_prime P h hsq)⟩)
        (fun P => (card_normalizer_dvd_map X P).trans
          (hF.norm7 _ (by rw [card_map_subtype, card_sylow_eq_prime P h hsq])))
      refine ⟨n, mem_npSet (by norm_num) h hN hdN hNn hn, ?_⟩
      rw [Nat.totient_prime h7.out] at hc
      omega
    · exact ⟨0, by simp [npSet, h], Nat.zero_le _⟩
  have d5 : ∃ n ∈ npSet 20 5 m 5, 4 * n ≤ Nat.card {x : X // orderOf x = 5} := by
    by_cases h : 5 ∣ m
    · have hsq : ¬ 5 ^ 2 ∣ m := fun h' => by have := h'.trans hmdvd; norm_num at this
      obtain ⟨N, n, hN, hdN, hNn, hn, hc⟩ := cyc_data (T := X) (p := 5) (d := 5) (c := 20)
        (fun P => ⟨card_sylow_eq_prime P h hsq,
          isCyclic_of_prime_card (card_sylow_eq_prime P h hsq)⟩)
        (fun P => (card_normalizer_dvd_map X P).trans
          (hF.norm5 _ (by rw [card_map_subtype, card_sylow_eq_prime P h hsq])))
      refine ⟨n, mem_npSet (by norm_num) h hN hdN hNn hn, ?_⟩
      rw [Nat.totient_prime h5.out] at hc
      omega
    · exact ⟨0, by simp [npSet, h], Nat.zero_le _⟩
  have d9 : ∃ n ∈ npSet (Nat.gcd 1458 m) 9 m 3, 6 * n ≤ Nat.card {x : X // orderOf x = 9} := by
    by_cases h : 9 ∣ m
    ·
      have hP9 : ∀ P : Sylow 3 X, Nat.card P = 9 := by
        intro P
        obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp P.isPGroup'
        have h9 : 9 ∣ Nat.card P := by
          rw [hm, ← (P : Subgroup X).card_mul_index] at h
          exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left 2 (hcop P)) h
        rw [hj] at h9 ⊢
        have hj2 : j < 3 := by
          by_contra hj3
          have h3j := pow_dvd_pow 3 (show 3 ≤ j by omega)
          norm_num at h3j
          exact h27 P (hj ▸ h3j)
        have hj1 : 2 ≤ j := by
          by_contra hj2'
          have : 3 ^ j ∣ 3 ^ 1 := pow_dvd_pow 3 (by omega)
          have := Nat.le_of_dvd (by norm_num) (h9.trans this)
          omega
        obtain rfl : j = 2 := by omega
        norm_num
      obtain ⟨N, n, hN, hdN, hNn, hn, hc⟩ := cyc_data (T := X) (p := 3) (d := 9)
        (c := Nat.gcd 1458 m) (fun P => ⟨hP9 P, hcyc P⟩) (fun P => by
          refine Nat.dvd_gcd ?_ (Subgroup.card_subgroup_dvd_card _)
          haveI := hcyc P
          obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
          rw [hP9] at ha
          have hzP : zpowers (a : X) = (P : Subgroup X) := by
            refine Subgroup.eq_of_le_of_card_ge ((zpowers_le).mpr a.2) ?_
            rw [Nat.card_zpowers, Subgroup.orderOf_coe, ha, hP9]
          have hmap : (P : Subgroup X).map X.subtype = zpowers ((a : X) : S) := by
            have h' := MonoidHom.map_zpowers X.subtype (a : X)
            rw [hzP] at h'
            exact h'
          refine (card_normalizer_dvd_map X P).trans ?_
          rw [hmap]
          exact hF.norm9 _ (by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ha]))
      refine ⟨n, mem_npSet (Nat.gcd_pos_of_pos_left _ (by norm_num)) h hN hdN hNn hn, ?_⟩
      rw [show Nat.totient 9 = 6 by decide] at hc
      omega
    · exact ⟨0, by simp [npSet, h], Nat.zero_le _⟩
  have htot := card_three_orders_le (T := X) (a := 5) (b := 7) (c := 9) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨n7, hn7, hc7⟩ := d7
  obtain ⟨n5, hn5, hc5⟩ := d5
  obtain ⟨n9, hn9, hc9⟩ := d9
  obtain ⟨k, hk⟩ := h81
  have hkm : m = 3265920 / (81 * k) := by
    rw [← hmn, hk, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (hk ▸ hn0))]
  have hdk : 81 * k ∣ 3265920 := ⟨m, by rw [← hk, ← hmn, mul_comm]⟩
  have hkI : k ∈ Finset.Icc 1 16 := Finset.mem_Icc.2 ⟨by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact absurd (by rw [hk, h0]) hn0
    · exact h0, by omega⟩
  rw [hkm] at hn7 hn5 hn9
  have := arith_check k hkI hdk n7 hn7 n5 hn5 n9 hn9
  rw [← hkm] at this
  omega

section NC

variable {G : Type*} [Group G] [Finite G]

theorem card_normalizer_zpowers_dvd (x : G) :
    Nat.card (normalizer ((zpowers x : Subgroup G) : Set G)) ∣
      Nat.card (centralizer ({x} : Set G)) * (orderOf x).totient := by
  classical
  set H : Subgroup G := zpowers x with hH
  set N : Subgroup G := normalizer (H : Set G) with hN
  haveI : (H.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  let f : N →* MulAut (H.subgroupOf N) := MulAut.conjNormal
  have hxN : x ∈ N := Subgroup.le_normalizer (mem_zpowers x)
  have hxH : (⟨x, hxN⟩ : N) ∈ H.subgroupOf N := by
    rw [Subgroup.mem_subgroupOf]; exact mem_zpowers x
  have hker : Nat.card f.ker ∣ Nat.card (centralizer ({x} : Set G)) := by
    have hle : f.ker.map N.subtype ≤ centralizer ({x} : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := congrArg (fun φ : MulAut (H.subgroupOf N) =>
        (((φ ⟨⟨x, hxN⟩, hxH⟩ : H.subgroupOf N) : N) : G)) (f.mem_ker.mp hy)
      simp only [f, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      have h2 : (y : G) * x * (y : G)⁻¹ = x := h1
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2
    rw [← Subgroup.card_map_of_injective (K := f.ker) N.subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  have hcardH : Nat.card (H.subgroupOf N) = orderOf x := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer)).toEquiv,
      Nat.card_zpowers]
  haveI : IsCyclic (H.subgroupOf N) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer)).symm.toMonoidHom
      (MulEquiv.surjective _)
  have hrange : Nat.card f.range ∣ (orderOf x).totient := by
    have h1 := Subgroup.card_subgroup_dvd_card f.range
    rwa [IsCyclic.card_mulAut, hcardH] at h1
  have hNcard : Nat.card N = Nat.card f.ker * Nat.card f.range := by
    exact (Subgroup.card_ker_mul_card_range f).symm
  rw [hNcard]
  exact Nat.mul_dvd_mul hker hrange

end NC

structure U43CentFacts (S : Type*) [Group S] : Prop where
  card : Nat.card S = 3265920
  not27 : ∀ g : S, orderOf g ≠ 27
  cent5 : ∀ x : S, orderOf x = 5 → Nat.card (centralizer ({x} : Set S)) ∣ 5
  norm7 : ∀ P : Subgroup S, Nat.card P = 7 → Nat.card (normalizer (P : Set S)) ∣ 21
  cent9 : ∀ g : S, orderOf g = 9 → IsPGroup 3 (centralizer ({g} : Set S))

theorem U43CentFacts.toCountingFacts {S : Type*} [Group S] [Finite S] (h : U43CentFacts S) :
    U43CountingFacts S where
  card := h.card
  not27 := h.not27
  norm7 := h.norm7
  norm5 := by
    intro P hP
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    haveI := isCyclic_of_prime_card hP
    obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
    rw [hP] at ha
    have hzP : zpowers (a : S) = P := by
      refine Subgroup.eq_of_le_of_card_ge ((zpowers_le).mpr a.2) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, ha, hP]
    have h1 := card_normalizer_zpowers_dvd (a : S)
    rw [hzP, Subgroup.orderOf_coe, ha, Nat.totient_prime Nat.prime_five] at h1
    exact h1.trans (Nat.mul_dvd_mul_right (h.cent5 _ (by rw [Subgroup.orderOf_coe, ha])) 4)
  norm9 := by
    intro g hg
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h1 := card_normalizer_zpowers_dvd g
    rw [hg, show Nat.totient 9 = 6 by decide] at h1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (h.cent9 g hg)
    have hS : Nat.card (normalizer ((zpowers g : Subgroup S) : Set S)) ∣ 3265920 := by
      rw [← h.card]; exact Subgroup.card_subgroup_dvd_card _
    have h2 := Nat.dvd_gcd h1 hS
    rw [hk] at h2
    refine h2.trans ?_
    rcases Nat.lt_or_ge k 5 with hk6 | hk6
    · refine (Nat.gcd_dvd_left _ _).trans ?_
      rw [show (1458 : ℕ) = 3 ^ 5 * 6 by norm_num]
      exact Nat.mul_dvd_mul_right (pow_dvd_pow 3 (by omega)) 6
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk6
      rw [show 3 ^ (5 + j) * 6 = 1458 * 3 ^ j by ring, show (3265920 : ℕ) = 1458 * 2240 by norm_num,
        Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left j (by norm_num)), mul_one]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43
