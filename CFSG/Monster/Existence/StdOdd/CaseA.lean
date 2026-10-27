module

public import CFSG.Monster.Existence.StdOdd.Coprime
public import CFSG.Monster.Existence.StdOdd.Defs

public section

namespace CFSG.Monster.Existence.StdOdd

open Subgroup
open scoped Pointwise

section Counting

variable {G : Type*} [Group G] [Finite G]

theorem ncard_subgroups_card_prime {r : ℕ} [Fact r.Prime] {S : Subgroup G}
    (hS : Nat.card S = r ^ 2) (hexp : ∀ y ∈ S, y ^ r = 1) :
    {P : Subgroup G | P ≤ S ∧ Nat.card P = r}.ncard = r + 1 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hr := (Fact.out : r.Prime)
  have hr2 : 2 ≤ r := hr.two_le
  have ho : ∀ x ∈ S, x ≠ 1 → orderOf x = r := by
    intro x hx hx1
    have hd : orderOf x ∣ r := orderOf_dvd_of_pow_eq_one (hexp x hx)
    rcases (Nat.dvd_prime hr).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  let Ω : Set (Subgroup G) := {P | P ≤ S ∧ Nat.card P = r}
  have hΩfin : Ω.Finite := Set.toFinite _
  let E : Finset G := Finset.univ.filter (fun x => x ∈ S ∧ x ≠ 1)
  have hEcard : E.card = r ^ 2 - 1 := by
    have h1 : (↑E : Set G) = (S : Set G) \ {1} := by
      ext x
      simp [E]
    have h2 := Set.ncard_coe_finset E
    rw [h1, Set.ncard_sdiff_singleton_of_mem S.one_mem, ← Nat.card_coe_set_eq] at h2
    rw [← h2]
    have : Nat.card (↑(S : Set G) : Type _) = Nat.card S := rfl
    rw [this, hS]
  have hmap : Set.MapsTo (fun x => zpowers x) (↑E : Set G)
      (↑hΩfin.toFinset : Set (Subgroup G)) := by
    intro x hx
    have hx' : x ∈ S ∧ x ≠ 1 := by simpa [E] using hx
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset]
    refine ⟨Subgroup.zpowers_le.2 hx'.1, ?_⟩
    rw [Nat.card_zpowers]
    exact ho x hx'.1 hx'.2
  have hfiber : ∀ P ∈ hΩfin.toFinset, (E.filter (fun x => zpowers x = P)).card = r - 1 := by
    intro P hP
    simp only [Set.Finite.mem_toFinset] at hP
    obtain ⟨hPS, hPr⟩ := hP
    have h1 : E.filter (fun x => zpowers x = P) =
        (Finset.univ.filter (fun x => x ∈ P)).erase 1 := by
      ext x
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, hx1⟩, hxP⟩
        exact ⟨hx1, hxP ▸ Subgroup.mem_zpowers x⟩
      · rintro ⟨hx1, hxP⟩
        refine ⟨⟨hPS hxP, hx1⟩, ?_⟩
        apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxP)
        rw [Nat.card_zpowers, hPr, ho x (hPS hxP) hx1]
    have h2 : (Finset.univ.filter (fun x => x ∈ P)).card = r := by
      have h3 : (↑(Finset.univ.filter (fun x => x ∈ P)) : Set G) = (P : Set G) := by
        ext x
        simp
      have h4 := Set.ncard_coe_finset (Finset.univ.filter (fun x => x ∈ P))
      rw [h3, ← Nat.card_coe_set_eq] at h4
      rw [← h4]
      exact hPr
    rw [h1, Finset.card_erase_of_mem (by simp), h2]
  have hsum := Finset.card_eq_sum_card_fiberwise hmap
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, hEcard] at hsum
  have hΩcard : Ω.ncard = hΩfin.toFinset.card := Set.ncard_eq_toFinset_card Ω hΩfin
  show Ω.ncard = r + 1
  rw [hΩcard]
  have h5 : r ^ 2 - 1 = (r + 1) * (r - 1) := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
    have e1 : s + 2 - 1 = s + 1 := by omega
    have e2 : (s + 2) ^ 2 = (s + 3) * (s + 1) + 1 := by ring
    rw [e1, e2, Nat.add_sub_cancel]
  rw [h5] at hsum
  have hpos : 0 < r - 1 := by omega
  exact (Nat.eq_of_mul_eq_mul_right hpos hsum).symm

local instance conjMulAction : MulAction G (Subgroup G) :=
  MulAction.compHom (Subgroup G) (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom

omit [Finite G] in
private theorem smul_def' (P : Subgroup G) (g : G) : g • P = ConjAct.toConjAct g • P := rfl

omit [Finite G] in
private theorem stabilizer_conj (P : Subgroup G) :
    MulAction.stabilizer G P = normalizer (P : Set G) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, smul_def']
  exact Subgroup.conjAct_pointwise_smul_iff

theorem exists_index_le_three {r : ℕ} [Fact r.Prime] (hr : r = 5 ∨ r = 7)
    (hodd : Odd (Nat.card G)) {S : Subgroup G} [S.Normal] (hS : Nat.card S = r ^ 2)
    (hexp : ∀ y ∈ S, y ^ r = 1) :
    ∃ x : G, x ∈ S ∧ orderOf x = r ∧
      (normalizer ((zpowers x : Subgroup G) : Set G)).index ≤ 3 := by
  let Ω : Set (Subgroup G) := {P | P ≤ S ∧ Nat.card P = r}
  have hcard : Ω.ncard = r + 1 := ncard_subgroups_card_prime hS hexp
  have hΩ : ∀ g : G, ∀ P ∈ Ω, g • P ∈ Ω := by
    intro g P hP
    rw [smul_def']
    refine ⟨?_, ?_⟩
    · intro m hm
      obtain ⟨s, hs, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists m _ P).1 hm
      rw [ConjAct.smul_def]
      simpa using (inferInstance : S.Normal).conj_mem s (hP.1 hs) g
    · rw [← hP.2]
      exact Nat.card_congr (Subgroup.equivSMul (ConjAct.toConjAct g) P).toEquiv.symm
  have hev : Even Ω.ncard := by
    rw [hcard]
    rcases hr with rfl | rfl <;> decide
  have hle : Ω.ncard ≤ 8 := by
    rw [hcard]
    rcases hr with rfl | rfl <;> norm_num
  have hne : Ω.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hcard]; omega)
  obtain ⟨P, hPΩ, hP3⟩ := exists_small_orbit (K := G) hodd Ω (Set.toFinite _) hΩ hev hne hle
  have hidx : (normalizer (P : Set G)).index ≤ 3 := by
    have h := MulAction.index_stabilizer G P
    rw [stabilizer_conj] at h
    omega
  have hcyc : IsCyclic P := isCyclic_of_prime_card hPΩ.2
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgo : orderOf g = r := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg]
    exact hPΩ.2
  have hxo : orderOf (g : G) = r := by rw [Subgroup.orderOf_coe, hgo]
  have hzp : zpowers (g : G) = P := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 g.2)
    rw [Nat.card_zpowers, hxo, hPΩ.2]
  refine ⟨g, hPΩ.1 g.2, hxo, ?_⟩
  rw [hzp]
  exact hidx

end Counting

section CentralizerOdd

variable {G : Type*} [Group G]

theorem odd_card_centralizer (hodd : Odd (Nat.card G)) (x : G) :
    Odd (Nat.card (centralizer ({x} : Set G))) :=
  hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)

theorem CentralizerFacts.c5_odd (hC : CentralizerFacts G) (hodd : Odd (Nat.card G)) {x : G}
    (hx : orderOf x = 5) : Nat.card (centralizer ({x} : Set G)) ∣ 3 ^ 2 * 5 ^ 2 * 7 :=
  odd_dvd_of_dvd_two_pow_mul 6 (odd_card_centralizer hodd x)
    (by simpa only [mul_assoc] using hC.c5 x hx)

theorem CentralizerFacts.c7_odd (hC : CentralizerFacts G) (hodd : Odd (Nat.card G)) {x : G}
    (hx : orderOf x = 7) : Nat.card (centralizer ({x} : Set G)) ∣ 3 ^ 2 * 5 * 7 ^ 2 :=
  odd_dvd_of_dvd_two_pow_mul 6 (odd_card_centralizer hodd x)
    (by simpa only [mul_assoc] using hC.c7 x hx)

theorem CentralizerFacts.c11_odd (hC : CentralizerFacts G) (hodd : Odd (Nat.card G)) {x : G}
    (hx : orderOf x = 11) : Nat.card (centralizer ({x} : Set G)) ∣ 3 * 11 :=
  odd_dvd_of_dvd_two_pow_mul 1 (odd_card_centralizer hodd x)
    (by simpa only [pow_one, mul_assoc] using hC.c11 x hx)

end CentralizerOdd

section Bounds

variable {G : Type*} [Group G] [Finite G]

theorem exists_card_eq_mul_of_cyclic_normal {p c : ℕ} [Fact p.Prime]
    (hcent : ∀ x : G, orderOf x = p → Nat.card (centralizer ({x} : Set G)) ∣ c)
    {S : Subgroup G} [S.Normal] [IsCyclic S] (hS : p ∣ Nat.card S) :
    ∃ m k : ℕ, Nat.card G = m * k ∧ m ∣ c ∧ k ∣ Nat.totient (Nat.card S) := by
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := S) p hS
  obtain ⟨k, hk, hkt⟩ := exists_card_eq_mul_dvd_totient S ⊤
    (by rw [Subgroup.normalizer_eq_top])
  refine ⟨Nat.card (centralizer (S : Set G)), k, ?_, ?_, hkt⟩
  · rw [← Subgroup.card_top (G := G), hk, top_inf_eq]
  · refine (Subgroup.card_dvd_of_le ?_).trans (hcent (y : G) (by rw [Subgroup.orderOf_coe, hy]))
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 y.2)

theorem exists_card_eq_mul_of_elementary {r c : ℕ} [Fact r.Prime] (hr : r = 5 ∨ r = 7)
    (hodd : Odd (Nat.card G))
    (hcent : ∀ x : G, orderOf x = r → Nat.card (centralizer ({x} : Set G)) ∣ c)
    {S : Subgroup G} [S.Normal] (hS : Nat.card S = r ^ 2) (hexp : ∀ y ∈ S, y ^ r = 1) :
    ∃ n m k : ℕ, Nat.card G = n * (m * k) ∧ n ≤ 3 ∧ m ∣ c ∧ k ∣ r - 1 := by
  obtain ⟨x, hxS, hxo, hidx⟩ := exists_index_le_three hr hodd hS hexp
  have : IsCyclic (zpowers x) := inferInstance
  obtain ⟨k, hk, hkt⟩ := exists_card_eq_mul_dvd_totient (zpowers x)
    (normalizer ((zpowers x : Subgroup G) : Set G)) le_rfl
  have hc : zpowers x ≤ normalizer ((zpowers x : Subgroup G) : Set G) :=
    Subgroup.le_normalizer
  refine ⟨(normalizer ((zpowers x : Subgroup G) : Set G)).index,
    Nat.card ↥(normalizer ((zpowers x : Subgroup G) : Set G) ⊓
      centralizer ((zpowers x : Subgroup G) : Set G)), k, ?_, hidx, ?_, ?_⟩
  · rw [← hk]
    exact (Subgroup.index_mul_card _).symm
  · refine (Subgroup.card_dvd_of_le ?_).trans (hcent x hxo)
    refine inf_le_right.trans ?_
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  · rw [Nat.card_zpowers, hxo, Nat.totient_prime (Fact.out : r.Prime)] at hkt
    exact hkt

theorem le_of_card_eq_mul {N m k c n b : ℕ} (hN : N = m * k) (hm : m ∣ c) (hk : k ∣ n)
    (hodd : Odd N) (hc : 0 < c) (hb : ∀ d ∈ Nat.divisors n, Odd d → d ≤ b) (hn : n ≠ 0) :
    N ≤ c * b := by
  have hkodd : Odd k := hodd.of_dvd_nat ⟨m, by rw [hN, mul_comm]⟩
  exact hN ▸ Nat.mul_le_mul (Nat.le_of_dvd hc hm) (hb k (Nat.mem_divisors.2 ⟨hk, hn⟩) hkodd)

end Bounds

section Main

variable {G : Type*} [Group G] [Finite G]

theorem card_le_of_normal_prime {r c b : ℕ} [Fact r.Prime] (hodd : Odd (Nat.card G))
    (hcent : ∀ x : G, orderOf x = r → Nat.card (centralizer ({x} : Set G)) ∣ c) (hc : 0 < c)
    (hb : ∀ d ∈ Nat.divisors (r - 1), Odd d → d ≤ b)
    {S : Subgroup G} [S.Normal] (hS : Nat.card S = r) : Nat.card G ≤ c * b := by
  have hr := (Fact.out : r.Prime)
  have : IsCyclic S := isCyclic_of_prime_card hS
  obtain ⟨m, k, hmk, hm, hk⟩ := exists_card_eq_mul_of_cyclic_normal hcent
    (S := S) (by rw [hS])
  rw [hS, Nat.totient_prime hr] at hk
  exact le_of_card_eq_mul hmk hm hk hodd hc hb (by have := hr.two_le; omega)

theorem card_le_of_normal_sq {r c b b₂ : ℕ} [Fact r.Prime] (hr : r = 5 ∨ r = 7)
    (hodd : Odd (Nat.card G))
    (hcent : ∀ x : G, orderOf x = r → Nat.card (centralizer ({x} : Set G)) ∣ c) (hc : 0 < c)
    (hb : ∀ d ∈ Nat.divisors (r - 1), Odd d → d ≤ b)
    (hb₂ : ∀ d ∈ Nat.divisors (r * (r - 1)), Odd d → d ≤ b₂)
    {S : Subgroup G} [S.Normal] (hS : Nat.card S = r ^ 2) :
    Nat.card G ≤ max (c * b₂) (3 * (c * b)) := by
  have hr0 := (Fact.out : r.Prime)
  have hr2 := hr0.two_le
  by_cases hcyc : ∃ y ∈ S, orderOf y = r ^ 2
  · obtain ⟨y, hyS, hyo⟩ := hcyc
    have : IsCyclic S :=
      isCyclic_of_orderOf_eq_card (⟨y, hyS⟩ : S) (by rw [Subgroup.orderOf_mk, hyo, hS])
    obtain ⟨m, k, hmk, hm, hk⟩ := exists_card_eq_mul_of_cyclic_normal hcent
      (S := S) (by rw [hS]; exact dvd_pow_self r two_ne_zero)
    have hphi : Nat.totient (Nat.card S) = r * (r - 1) := by
      rw [hS, Nat.totient_prime_pow hr0 (by norm_num)]
      simp
    rw [hphi] at hk
    exact le_trans
      (le_of_card_eq_mul hmk hm hk hodd hc hb₂ (Nat.mul_ne_zero (by omega) (by omega)))
      (le_max_left _ _)
  · have hexp : ∀ y ∈ S, y ^ r = 1 := by
      intro y hy
      have hd : orderOf y ∣ r ^ 2 := by
        rw [← hS]
        exact Subgroup.orderOf_dvd_natCard S hy
      obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow hr0).1 hd
      have hi2 : i ≠ 2 := by
        rintro rfl
        exact hcyc ⟨y, hy, hio⟩
      have : orderOf y ∣ r := by
        rw [hio]
        interval_cases i
        · simp
        · simp
        · exact absurd rfl hi2
      exact orderOf_dvd_iff_pow_eq_one.1 this
    obtain ⟨n, m, k, hnmk, hn, hm, hk⟩ := exists_card_eq_mul_of_elementary hr hodd hcent hS hexp
    have h1 : m * k ≤ c * b := by
      have hkodd : Odd k := hodd.of_dvd_nat ⟨n * m, by rw [hnmk]; ring⟩
      exact Nat.mul_le_mul (Nat.le_of_dvd hc hm)
        (hb k (Nat.mem_divisors.2 ⟨hk, by omega⟩) hkodd)
    rw [hnmk]
    exact le_trans (Nat.mul_le_mul hn h1) (le_max_right _ _)

end Main

section Dispatch

theorem prime_dvd_cases {r : ℕ} (hr : r.Prime)
    (h : r ∣ 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19) :
    r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 11 ∨ r = 13 ∨ r = 17 ∨ r = 19 := by
  have hp : ∀ q : ℕ, q.Prime → r ∣ q → r = q := fun q hq h =>
    (Nat.prime_dvd_prime_iff_eq hr hq).1 h
  rcases (Nat.Prime.dvd_mul hr).1 h with h | h
  swap
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hp 19 (by norm_num) h))))))
  rcases (Nat.Prime.dvd_mul hr).1 h with h | h
  swap
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hp 17 (by norm_num) h))))))
  rcases (Nat.Prime.dvd_mul hr).1 h with h | h
  swap
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hp 13 (by norm_num) h)))))
  rcases (Nat.Prime.dvd_mul hr).1 h with h | h
  swap
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hp 11 (by norm_num) h))))
  rcases (Nat.Prime.dvd_mul hr).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · exact Or.inl (hp 3 (by norm_num) (hr.dvd_of_dvd_pow h))
    · exact Or.inr (Or.inl (hp 5 (by norm_num) (hr.dvd_of_dvd_pow h)))
  · exact Or.inr (Or.inr (Or.inl (hp 7 (by norm_num) (hr.dvd_of_dvd_pow h))))

variable {G : Type*} [Group G] [Finite G]

theorem card_le_of_normal_subgroup (hodd : Odd (Nat.card G))
    (hdvd : Nat.card G ∣ 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19) (hC : CentralizerFacts G)
    {r : ℕ} [Fact r.Prime] (hr3 : r ≠ 3) {S : Subgroup G} [S.Normal] (hSp : IsPGroup r S)
    (hS1 : S ≠ ⊥) :
    Nat.card G ≤ 46305 ∧ (¬ 7 ^ 2 ∣ Nat.card G → Nat.card G ≤ 7875) := by
  have hr : r.Prime := Fact.out
  obtain ⟨j, hj⟩ := hSp.exists_card_eq
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hS1 (Subgroup.eq_bot_of_card_eq S (by rw [hj, pow_zero]))
  have hSdvd : r ^ j ∣ Nat.card G := hj ▸ Subgroup.card_subgroup_dvd_card S
  have hrN : r ∣ 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 :=
    ((dvd_pow_self r hj0).trans hSdvd).trans hdvd
  have hSN : r ^ j ∣ 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 := hSdvd.trans hdvd
  have hb4 : ∀ d ∈ Nat.divisors 4, Odd d → d ≤ 1 := by decide
  have hb20 : ∀ d ∈ Nat.divisors 20, Odd d → d ≤ 5 := by decide
  have hb6 : ∀ d ∈ Nat.divisors 6, Odd d → d ≤ 3 := by decide
  have hb42 : ∀ d ∈ Nat.divisors 42, Odd d → d ≤ 21 := by decide
  have hb10 : ∀ d ∈ Nat.divisors 10, Odd d → d ≤ 5 := by decide
  have hb12 : ∀ d ∈ Nat.divisors 12, Odd d → d ≤ 3 := by decide
  have hb16 : ∀ d ∈ Nat.divisors 16, Odd d → d ≤ 1 := by decide
  have hb18 : ∀ d ∈ Nat.divisors 18, Odd d → d ≤ 9 := by decide
  rcases prime_dvd_cases hr hrN with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hr3
  ·
    have hcent : ∀ x : G, orderOf x = 5 →
        Nat.card (centralizer ({x} : Set G)) ∣ 3 ^ 2 * 5 ^ 2 * 7 :=
      fun x hx => hC.c5_odd hodd hx
    have hj3 : j ≤ 2 := by
      by_contra h
      have h3 : 5 ^ 3 ∣ 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 :=
        (pow_dvd_pow 5 (by omega : 3 ≤ j)).trans hSN
      revert h3
      decide
    interval_cases j
    · exact absurd rfl hj0
    · have h := card_le_of_normal_prime hodd hcent (by norm_num) hb4 (S := S) (by simpa using hj)
      exact ⟨by omega, fun _ => by omega⟩
    · have h := card_le_of_normal_sq (Or.inl rfl) hodd hcent (by norm_num) hb4 (by simpa using hb20)
        (S := S) hj
      exact ⟨by omega, fun _ => by omega⟩
  ·
    have hcent : ∀ x : G, orderOf x = 7 →
        Nat.card (centralizer ({x} : Set G)) ∣ 3 ^ 2 * 5 * 7 ^ 2 :=
      fun x hx => hC.c7_odd hodd hx
    have hj3 : j ≤ 2 := by
      by_contra h
      have h3 : 7 ^ 3 ∣ 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 :=
        (pow_dvd_pow 7 (by omega : 3 ≤ j)).trans hSN
      revert h3
      decide
    interval_cases j
    · exact absurd rfl hj0
    · have h := card_le_of_normal_prime hodd hcent (by norm_num) hb6 (S := S) (by simpa using hj)
      exact ⟨by omega, fun _ => by omega⟩
    · have h := card_le_of_normal_sq (Or.inr rfl) hodd hcent (by norm_num) hb6 (by simpa using hb42)
        (S := S) hj
      refine ⟨by omega, fun h49 => absurd ?_ h49⟩
      simpa [hj] using hSdvd
  ·
    have hcent : ∀ x : G, orderOf x = 11 → Nat.card (centralizer ({x} : Set G)) ∣ 3 * 11 :=
      fun x hx => hC.c11_odd hodd hx
    have hj2 : j ≤ 1 := by
      by_contra h
      have h3 : 11 ^ 2 ∣ 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 :=
        (pow_dvd_pow 11 (by omega : 2 ≤ j)).trans hSN
      revert h3
      decide
    have hj1 : j = 1 := by omega
    subst hj1
    have h := card_le_of_normal_prime hodd hcent (by norm_num) hb10 (S := S) (by simpa using hj)
    exact ⟨by omega, fun _ => by omega⟩
  ·
    have hcent : ∀ x : G, orderOf x = 13 → Nat.card (centralizer ({x} : Set G)) ∣ 13 :=
      fun x hx => (hC.c13 x hx).symm ▸ dvd_rfl
    have hj2 : j ≤ 1 := by
      by_contra h
      have h3 : 13 ^ 2 ∣ 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 :=
        (pow_dvd_pow 13 (by omega : 2 ≤ j)).trans hSN
      revert h3
      decide
    have hj1 : j = 1 := by omega
    subst hj1
    have h := card_le_of_normal_prime hodd hcent (by norm_num) hb12 (S := S) (by simpa using hj)
    exact ⟨by omega, fun _ => by omega⟩
  ·
    have hcent : ∀ x : G, orderOf x = 17 → Nat.card (centralizer ({x} : Set G)) ∣ 3 * 17 :=
      fun x hx => odd_dvd_of_dvd_two_pow_mul 0 (odd_card_centralizer hodd x) (by
        simpa using hC.c17 x hx)
    have hj2 : j ≤ 1 := by
      by_contra h
      have h3 : 17 ^ 2 ∣ 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 :=
        (pow_dvd_pow 17 (by omega : 2 ≤ j)).trans hSN
      revert h3
      decide
    have hj1 : j = 1 := by omega
    subst hj1
    have h := card_le_of_normal_prime hodd hcent (by norm_num) hb16 (S := S) (by simpa using hj)
    exact ⟨by omega, fun _ => by omega⟩
  ·
    have hcent : ∀ x : G, orderOf x = 19 → Nat.card (centralizer ({x} : Set G)) ∣ 3 * 19 :=
      fun x hx => hC.c19 x hx
    have hj2 : j ≤ 1 := by
      by_contra h
      have h3 : 19 ^ 2 ∣ 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 :=
        (pow_dvd_pow 19 (by omega : 2 ≤ j)).trans hSN
      revert h3
      decide
    have hj1 : j = 1 := by omega
    subst hj1
    have h := card_le_of_normal_prime hodd hcent (by norm_num) hb18 (S := S) (by simpa using hj)
    exact ⟨by omega, fun _ => by omega⟩

end Dispatch

end CFSG.Monster.Existence.StdOdd
