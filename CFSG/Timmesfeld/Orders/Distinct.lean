module

public import CFSG.Open.Defs
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.Timmesfeld

open CFSG.Open

@[expose] def evenOrdersExceptUnitarySp4 : Set ℕ :=
  {m | ∃ f : ℕ, 1 ≤ f ∧
    ((∃ n, 1 ≤ n ∧ (n, f) ≠ (1, 1) ∧ m = ordA n (2 ^ f)) ∨
      (∃ n, 3 ≤ n ∧ m = ordBC n (2 ^ f)) ∨
      (∃ n, 4 ≤ n ∧ (m = ordD n (2 ^ f) ∨ m = ordTwistedD n (2 ^ f))) ∨
      (2 ≤ f ∧ m = ordG2 (2 ^ f)) ∨
      m = ordTrialityD4 (2 ^ f) ∨ m = ordF4 (2 ^ f) ∨ m = ordE6 (2 ^ f) ∨
      m = ordTwistedE6 (2 ^ f) ∨ m = ordE7 (2 ^ f) ∨ m = ordE8 (2 ^ f) ∨
      (Odd f ∧ 3 ≤ f ∧ (m = ordSuzuki (2 ^ f) ∨ m = ordTwistedF4 (2 ^ f))))} ∪ {ordTits}

theorem evenOrdersExceptUnitarySp4_subset : evenOrdersExceptUnitarySp4 ⊆ lieOrdersChar 2 := by
  have hL : ∀ {m : ℕ} (f : ℕ), 1 ≤ f → m ∈ lieOrdersOver (2 ^ f) → m ∈ lieOrdersChar 2 :=
    fun f hf h => Or.inl (Or.inl (Or.inl ⟨f, hf, h⟩))
  rintro m (⟨f, hf, h⟩ | hm)
  · rcases h with ⟨n, hn, -, rfl⟩ | ⟨n, hn, rfl⟩ | ⟨n, hn, rfl | rfl⟩ | ⟨-, rfl⟩ | rfl | rfl |
      rfl | rfl | rfl | rfl | ⟨hodd, h3, h⟩
    · exact hL f hf (by
        simp only [lieOrdersOver]; left; left; left; left; left; exact ⟨n, hn, rfl⟩)
    · exact hL f hf (by
        simp only [lieOrdersOver]; left; left; left; right; exact ⟨n, by omega, rfl⟩)
    · exact hL f hf (by simp only [lieOrdersOver]; left; left; right; exact ⟨n, hn, rfl⟩)
    · exact hL f hf (by simp only [lieOrdersOver]; left; right; exact ⟨n, hn, rfl⟩)
    iterate 7 · exact hL f hf (by simp [lieOrdersOver])
    obtain ⟨k, rfl⟩ := hodd
    exact Or.inl (Or.inl (Or.inr ⟨rfl, k, by omega, h⟩))
  · rw [Set.mem_singleton_iff] at hm
    exact Or.inr ⟨rfl, hm⟩

namespace Orders

structure Profile (m N : ℕ) (Z : ℕ → Prop) : Prop where
  two : ∃ r, Odd r ∧ m = 2 ^ N * r
  prim : ∀ p k, IsPrimitivePrimeDivisor p k → 0 < k → (p ∣ m ↔ Z k)

theorem eq_of_two_pow_mul_odd {a b r s : ℕ} (hr : Odd r) (hs : Odd s)
    (h : 2 ^ a * r = 2 ^ b * s) : a = b := by
  have h2 := congrArg (padicValNat 2) h
  have hr2 : ¬ 2 ∣ r := by have := Nat.odd_iff.mp hr; omega
  have hs2 : ¬ 2 ∣ s := by have := Nat.odd_iff.mp hs; omega
  rwa [padicValNat.mul (by positivity) hr.pos.ne', padicValNat.mul (by positivity) hs.pos.ne',
    padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hr2,
    padicValNat.eq_zero_of_not_dvd hs2, add_zero, add_zero] at h2

theorem Profile.transfer {m N N' : ℕ} {Z Z' : ℕ → Prop} (h : Profile m N Z)
    (h' : Profile m N' Z') : N = N' ∧ ∀ k, 2 ≤ k → k ≠ 6 → (Z k ↔ Z' k) := by
  refine ⟨?_, fun k hk h6 => ?_⟩
  · obtain ⟨r, hr, hm⟩ := h.two
    obtain ⟨r', hr', hm'⟩ := h'.two
    exact eq_of_two_pow_mul_odd hr hr' (hm.symm.trans hm')
  · obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor hk h6
    exact (h.prim p k hp (by omega)).symm.trans (h'.prim p k hp (by omega))

theorem Profile.ne_of_ne {m N a r : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) (hr : Odd r)
    (ha : N ≠ a) : m ≠ 2 ^ a * r := by
  rintro rfl
  obtain ⟨r', hr', hm⟩ := h.two
  exact ha (eq_of_two_pow_mul_odd hr' hr hm.symm)

theorem Profile.of_eq {m N r : ℕ} {Z : ℕ → Prop} (hm : m = 2 ^ N * r) (hr : Odd r)
    (hZ : ∀ p k, IsPrimitivePrimeDivisor p k → 0 < k → (p ∣ r ↔ Z k)) : Profile m N Z := by
  refine ⟨⟨r, hr, hm⟩, fun p k hp hk => ?_⟩
  rw [hm, ← hZ p k hp hk]
  refine ⟨fun h => ?_, fun h => dvd_mul_of_dvd_right h _⟩
  rcases hp.prime.dvd_mul.mp h with h2 | h2
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp.prime Nat.prime_two).mp
      (hp.prime.dvd_of_dvd_pow h2)) (hp.ne_two hk)
  · exact h2

theorem dvd_div_of_mul_self_dvd {P c d : ℕ} (hdc : d ∣ c) (hcP : c * c ∣ P) (hd : 0 < d) :
    c ∣ P / d := by
  obtain ⟨t, rfl⟩ := hcP
  obtain ⟨e, rfl⟩ := hdc
  rw [show d * e * (d * e) * t = d * (e * (d * e) * t) by ring, Nat.mul_div_cancel_left _ hd]
  exact ⟨e * t, by ring⟩

theorem prime_dvd_div_iff {P c d p : ℕ} (hp : p.Prime) (hdc : d ∣ c) (hcP : c * c ∣ P)
    (hd : 0 < d) : p ∣ P / d ↔ p ∣ P := by
  have hdP : d ∣ P := hdc.trans ((dvd_mul_right c c).trans hcP)
  refine ⟨fun h => h.trans (Nat.div_dvd_of_dvd hdP), fun h => ?_⟩
  rw [← Nat.mul_div_cancel' hdP] at h
  rcases hp.dvd_mul.mp h with h1 | h1
  · exact (h1.trans hdc).trans (dvd_div_of_mul_self_dvd hdc hcP hd)
  · exact h1

theorem Profile.of_div {m N P c d : ℕ} {Z : ℕ → Prop} (hm : m = 2 ^ N * P / d) (hP : Odd P)
    (hdc : d ∣ c) (hcP : c * c ∣ P) (hd : 0 < d)
    (hZ : ∀ p k, IsPrimitivePrimeDivisor p k → 0 < k → (p ∣ P ↔ Z k)) : Profile m N Z := by
  have hdP : d ∣ P := hdc.trans ((dvd_mul_right c c).trans hcP)
  refine Profile.of_eq (hm.trans (Nat.mul_div_assoc _ hdP))
    (hP.of_dvd_nat (Nat.div_dvd_of_dvd hdP)) (fun p k hp hk => ?_)
  rw [prime_dvd_div_iff hp.prime hdc hcP hd]
  exact hZ p k hp hk

theorem odd_two_pow_sub_one {a : ℕ} (ha : 0 < a) : Odd (2 ^ a - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' ha.ne').mpr even_two) odd_one

theorem odd_pow_sub_one {f a : ℕ} (hf : 0 < f) (ha : 0 < a) : Odd ((2 ^ f) ^ a - 1) := by
  rw [← pow_mul]; exact odd_two_pow_sub_one (Nat.mul_pos hf ha)

theorem odd_pow_add_one {f a : ℕ} (hf : 0 < f) (ha : 0 < a) : Odd ((2 ^ f) ^ a + 1) := by
  rw [← pow_mul]; exact ((Nat.even_pow' (Nat.mul_pos hf ha).ne').mpr even_two).add_one

theorem odd_prod {s : Finset ℕ} {g : ℕ → ℕ} (h : ∀ i ∈ s, Odd (g i)) : Odd (∏ i ∈ s, g i) :=
  Finset.prod_induction _ _ (fun _ _ => Odd.mul) odd_one h

theorem add_one_dvd_sq_sub_one (q : ℕ) : q + 1 ∣ q ^ 2 - 1 :=
  ⟨q - 1, by rw [← one_pow 2, Nat.sq_sub_sq, one_pow]⟩

theorem add_one_dvd_pow_add_one (q : ℕ) {a : ℕ} (ha : Odd a) : q + 1 ∣ q ^ a + 1 := by
  simpa using Odd.nat_add_dvd_pow_add_pow q 1 ha

namespace PrimDiv

variable {p k : ℕ}

theorem dvd_pow_sub_one_iff (h : IsPrimitivePrimeDivisor p k) (hk : 0 < k) (f a : ℕ) :
    p ∣ (2 ^ f) ^ a - 1 ↔ k ∣ f * a := by
  rw [← pow_mul]; exact h.dvd_sub_one_iff hk _

theorem dvd_pow_add_one_iff (h : IsPrimitivePrimeDivisor p k) (hk : 0 < k) (f a : ℕ) :
    p ∣ (2 ^ f) ^ a + 1 ↔ k ∣ 2 * (f * a) ∧ ¬ k ∣ f * a := by
  rw [← pow_mul]; exact h.dvd_add_one_iff hk _

theorem index_of_dvd_triality (h : IsPrimitivePrimeDivisor p k) (hk : 0 < k) (f : ℕ) :
    p ∣ (2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1 → (k ∣ f * 12 ∧ ¬ k ∣ f * 4) ∨ k = 2 := by
  intro hp
  have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h4 : 1 ≤ (2 ^ f) ^ 4 := Nat.one_le_pow _ _ hq
  have h12 : 1 ≤ (2 ^ f) ^ 12 := Nat.one_le_pow _ _ hq
  have hfac : (2 ^ f) ^ 12 - 1 = ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) := by
    zify [h4, h12]; ring
  by_cases h4k : k ∣ f * 4
  · right
    have hp4 := (dvd_pow_sub_one_iff h hk f 4).mpr h4k
    have hrel : (2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1 = ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 4 + 2) + 3 := by
      zify [h4]; ring
    rw [hrel] at hp
    exact h.eq_two_of_dvd_three hk ((Nat.dvd_add_right (dvd_mul_of_dvd_left hp4 _)).mp hp)
  · left
    refine ⟨(dvd_pow_sub_one_iff h hk f 12).mp ?_, h4k⟩
    rw [hfac]; exact dvd_mul_of_dvd_right hp _

theorem dvd_triality_of (h : IsPrimitivePrimeDivisor p k) (hk : 0 < k) (f : ℕ)
    (h12 : k ∣ f * 12) (h4 : ¬ k ∣ f * 4) : p ∣ (2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1 := by
  have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h4' : 1 ≤ (2 ^ f) ^ 4 := Nat.one_le_pow _ _ hq
  have h12' : 1 ≤ (2 ^ f) ^ 12 := Nat.one_le_pow _ _ hq
  have hfac : (2 ^ f) ^ 12 - 1 = ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) := by
    zify [h4', h12']; ring
  have hp := (dvd_pow_sub_one_iff h hk f 12).mpr h12
  rw [hfac] at hp
  rcases h.prime.dvd_mul.mp hp with hp | hp
  · exact absurd ((dvd_pow_sub_one_iff h hk f 4).mp hp) h4
  · exact hp

end PrimDiv

def zA (n f k : ℕ) : Prop := ∃ i ∈ Finset.Icc 2 (n + 1), k ∣ f * i

theorem profile_ordA {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) :
    Profile (ordA n (2 ^ f)) (f * (n * (n + 1) / 2)) (zA n f) := by
  have hP : Odd (∏ i ∈ Finset.Icc 2 (n + 1), ((2 ^ f) ^ i - 1)) :=
    odd_prod fun i hi => odd_pow_sub_one hf (by simp at hi; omega)
  have hZ : ∀ p k, IsPrimitivePrimeDivisor p k → 0 < k →
      (p ∣ ∏ i ∈ Finset.Icc 2 (n + 1), ((2 ^ f) ^ i - 1) ↔ zA n f k) := by
    intro p k hp hk
    rw [(Nat.Prime.prime hp.prime).dvd_finsetProd_iff]
    exact exists_congr fun i => and_congr_right fun _ => PrimDiv.dvd_pow_sub_one_iff hp hk f i
  have hm : ordA n (2 ^ f) = 2 ^ (f * (n * (n + 1) / 2)) *
      (∏ i ∈ Finset.Icc 2 (n + 1), ((2 ^ f) ^ i - 1)) / Nat.gcd (n + 1) (2 ^ f - 1) := by
    rw [ordA, pow_mul]
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have hn1 : n = 1 := by omega
    subst hn1
    refine Profile.of_div hm hP (c := 1) ?_ (by simp) (by norm_num) hZ
    rw [show (1 + 1 : ℕ) = 2 by rfl, Nat.coprime_two_left.mpr (odd_two_pow_sub_one hf)]
  · refine Profile.of_div hm hP (Nat.gcd_dvd_right _ _) ?_ (Nat.gcd_pos_of_pos_left _ (by omega))
      hZ
    have h23 : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 (n + 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_Icc]; omega
    have := Finset.prod_dvd_prod_of_subset _ _ (fun i => (2 ^ f) ^ i - 1) h23
    rw [Finset.prod_pair (by norm_num)] at this
    exact (mul_dvd_mul (Nat.sub_one_dvd_pow_sub_one _ 2) (Nat.sub_one_dvd_pow_sub_one _ 3)).trans
      this

theorem toNat_pow_sub_neg_one_pow_of_even {q i : ℕ} (hq : 1 ≤ q) (hi : Even i) :
    ((q : ℤ) ^ i - (-1) ^ i).toNat = q ^ i - 1 := by
  rw [hi.neg_one_pow, ← Nat.cast_pow]
  have : 1 ≤ q ^ i := Nat.one_le_pow _ _ hq
  generalize q ^ i = x at *
  omega

theorem toNat_pow_sub_neg_one_pow_of_odd {q i : ℕ} (hi : Odd i) :
    ((q : ℤ) ^ i - (-1) ^ i).toNat = q ^ i + 1 := by
  rw [hi.neg_one_pow, ← Nat.cast_pow]
  generalize q ^ i = x
  omega

def zU (n g k : ℕ) : Prop :=
  ∃ i ∈ Finset.Icc 2 (n + 1), (Even i ∧ k ∣ g * i) ∨ (Odd i ∧ k ∣ 2 * (g * i) ∧ ¬ k ∣ g * i)

theorem profile_ordTwistedA {n g : ℕ} (hn : 2 ≤ n) (hg : 1 ≤ g) :
    Profile (ordTwistedA n (2 ^ g)) (g * (n * (n + 1) / 2)) (zU n g) := by
  set F : ℕ → ℕ := fun i => (((2 ^ g : ℕ) : ℤ) ^ i - (-1) ^ i).toNat
  have hq : 1 ≤ 2 ^ g := Nat.one_le_two_pow
  have hFe : ∀ i, Even i → F i = (2 ^ g) ^ i - 1 := fun i hi =>
    toNat_pow_sub_neg_one_pow_of_even hq hi
  have hFo : ∀ i, Odd i → F i = (2 ^ g) ^ i + 1 := fun i hi =>
    toNat_pow_sub_neg_one_pow_of_odd hi
  have hP : Odd (∏ i ∈ Finset.Icc 2 (n + 1), F i) := odd_prod fun i hi => by
    have hi0 : 0 < i := by simp at hi; omega
    rcases Nat.even_or_odd i with h | h
    · rw [hFe i h]; exact odd_pow_sub_one hg hi0
    · rw [hFo i h]; exact odd_pow_add_one hg hi0
  have hm : ordTwistedA n (2 ^ g) = 2 ^ (g * (n * (n + 1) / 2)) *
      (∏ i ∈ Finset.Icc 2 (n + 1), F i) / Nat.gcd (n + 1) (2 ^ g + 1) := by
    rw [ordTwistedA, pow_mul]
  have hsq : (2 ^ g + 1) * (2 ^ g + 1) ∣ ∏ i ∈ Finset.Icc 2 (n + 1), F i := by
    have h23 : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 (n + 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_Icc]; omega
    have := Finset.prod_dvd_prod_of_subset _ _ F h23
    rw [Finset.prod_pair (by norm_num), hFe 2 even_two, hFo 3 (by decide)] at this
    exact (mul_dvd_mul (add_one_dvd_sq_sub_one _) (add_one_dvd_pow_add_one _ (by decide))).trans
      this
  refine Profile.of_div hm hP (Nat.gcd_dvd_right _ _) hsq (Nat.gcd_pos_of_pos_left _ (by omega))
    (fun p k hp hk => ?_)
  rw [(Nat.Prime.prime hp.prime).dvd_finsetProd_iff]
  refine exists_congr fun i => and_congr_right fun _ => ?_
  rcases Nat.even_or_odd i with h | h
  · rw [hFe i h, PrimDiv.dvd_pow_sub_one_iff hp hk]
    exact ⟨fun h' => Or.inl ⟨h, h'⟩, fun h' => h'.elim (fun h'' => h''.2)
      (fun h'' => absurd h (Nat.not_even_iff_odd.mpr h''.1))⟩
  · rw [hFo i h, PrimDiv.dvd_pow_add_one_iff hp hk]
    exact ⟨fun h' => Or.inr ⟨h, h'⟩, fun h' => h'.elim
      (fun h'' => absurd h''.1 (Nat.not_even_iff_odd.mpr h)) (fun h'' => h''.2)⟩

def zBC (n f k : ℕ) : Prop := ∃ i ∈ Finset.Icc 1 n, k ∣ f * (2 * i)

theorem profile_ordBC {n f : ℕ} (hf : 1 ≤ f) :
    Profile (ordBC n (2 ^ f)) (f * (n * n)) (zBC n f) := by
  have hP : Odd (∏ i ∈ Finset.Icc 1 n, ((2 ^ f) ^ (2 * i) - 1)) :=
    odd_prod fun i hi => odd_pow_sub_one hf (by simp at hi; omega)
  have hm : ordBC n (2 ^ f) = 2 ^ (f * (n * n)) * ∏ i ∈ Finset.Icc 1 n, ((2 ^ f) ^ (2 * i) - 1) :=
    by rw [ordBC, Nat.coprime_two_left.mpr (odd_two_pow_sub_one hf), Nat.div_one,
      pow_mul 2 f (n * n)]
  refine Profile.of_eq hm hP (fun p k hp hk => ?_)
  rw [(Nat.Prime.prime hp.prime).dvd_finsetProd_iff]
  exact exists_congr fun i => and_congr_right fun _ => PrimDiv.dvd_pow_sub_one_iff hp hk f _

def zD (n f k : ℕ) : Prop := k ∣ f * n ∨ ∃ i ∈ Finset.Icc 1 (n - 1), k ∣ f * (2 * i)

theorem profile_ordD {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) :
    Profile (ordD n (2 ^ f)) (f * (n * (n - 1))) (zD n f) := by
  have hP : Odd (∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ f) ^ (2 * i) - 1)) :=
    odd_prod fun i hi => odd_pow_sub_one hf (by simp at hi; omega)
  have h1 : Odd ((2 ^ f) ^ n - 1) := odd_pow_sub_one hf hn
  have hm : ordD n (2 ^ f) = 2 ^ (f * (n * (n - 1))) *
      (((2 ^ f) ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ f) ^ (2 * i) - 1)) := by
    rw [ordD, Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr h1), Nat.div_one,
      pow_mul 2 f (n * (n - 1)), mul_assoc]
  refine Profile.of_eq hm (h1.mul hP) (fun p k hp hk => ?_)
  rw [hp.prime.dvd_mul, (Nat.Prime.prime hp.prime).dvd_finsetProd_iff,
    PrimDiv.dvd_pow_sub_one_iff hp hk]
  exact or_congr_right
    (exists_congr fun i => and_congr_right fun _ => PrimDiv.dvd_pow_sub_one_iff hp hk f _)

def z2D (n f k : ℕ) : Prop :=
  (k ∣ 2 * (f * n) ∧ ¬ k ∣ f * n) ∨ ∃ i ∈ Finset.Icc 1 (n - 1), k ∣ f * (2 * i)

theorem profile_ordTwistedD {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) :
    Profile (ordTwistedD n (2 ^ f)) (f * (n * (n - 1))) (z2D n f) := by
  have hP : Odd (∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ f) ^ (2 * i) - 1)) :=
    odd_prod fun i hi => odd_pow_sub_one hf (by simp at hi; omega)
  have h1 : Odd ((2 ^ f) ^ n + 1) := odd_pow_add_one hf hn
  have hm : ordTwistedD n (2 ^ f) = 2 ^ (f * (n * (n - 1))) *
      (((2 ^ f) ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ f) ^ (2 * i) - 1)) := by
    rw [ordTwistedD, Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr h1), Nat.div_one,
      pow_mul 2 f (n * (n - 1)), mul_assoc]
  refine Profile.of_eq hm (h1.mul hP) (fun p k hp hk => ?_)
  rw [hp.prime.dvd_mul, (Nat.Prime.prime hp.prime).dvd_finsetProd_iff,
    PrimDiv.dvd_pow_add_one_iff hp hk]
  exact or_congr_right
    (exists_congr fun i => and_congr_right fun _ => PrimDiv.dvd_pow_sub_one_iff hp hk f _)

def zList (f : ℕ) (L : List ℕ) (k : ℕ) : Prop := ∃ a ∈ L, k ∣ f * a

def zG2 (f : ℕ) : ℕ → Prop := zList f [6, 2]

theorem ordG2_eq (f : ℕ) :
    ordG2 (2 ^ f) = 2 ^ (f * 6) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) := by
  rw [ordG2, pow_mul, mul_assoc]

theorem profile_ordG2 {f : ℕ} (hf : 1 ≤ f) : Profile (ordG2 (2 ^ f)) (f * 6) (zG2 f) := by
  refine Profile.of_eq (ordG2_eq f)
    ((odd_pow_sub_one hf (by norm_num)).mul (odd_pow_sub_one hf (by norm_num)))
    (fun p k hp hk => ?_)
  rw [hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk, PrimDiv.dvd_pow_sub_one_iff hp hk]
  simp [zG2, zList]

def zD4 (f k : ℕ) : Prop := (k ∣ f * 12 ∧ ¬ k ∣ f * 4) ∨ k ∣ f * 6 ∨ k ∣ f * 2

theorem profile_ordTrialityD4 {f : ℕ} (hf : 1 ≤ f) :
    Profile (ordTrialityD4 (2 ^ f)) (f * 12) (zD4 f) := by
  have hm : ordTrialityD4 (2 ^ f) = 2 ^ (f * 12) *
      (((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1))) := by
    rw [ordTrialityD4, pow_mul]; ring
  have h1 : Odd ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) := by
    have he : Even ((2 ^ f) ^ 8 + (2 ^ f) ^ 4) := by
      rw [← pow_mul, ← pow_mul]
      exact ((Nat.even_pow' (by omega)).mpr even_two).add ((Nat.even_pow' (by omega)).mpr even_two)
    exact he.add_one
  refine Profile.of_eq hm (h1.mul ((odd_pow_sub_one hf (by norm_num)).mul
    (odd_pow_sub_one hf (by norm_num)))) (fun p k hp hk => ?_)
  rw [hp.prime.dvd_mul, hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk,
    PrimDiv.dvd_pow_sub_one_iff hp hk]
  constructor
  · rintro (h | h | h)
    · rcases PrimDiv.index_of_dvd_triality hp hk f h with h' | rfl
      · exact Or.inl h'
      · exact Or.inr (Or.inr ⟨f, by ring⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl (PrimDiv.dvd_triality_of hp hk f h.1 h.2)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

def zF4 (f : ℕ) : ℕ → Prop := zList f [12, 8, 6, 2]

theorem profile_ordF4 {f : ℕ} (hf : 1 ≤ f) : Profile (ordF4 (2 ^ f)) (f * 24) (zF4 f) := by
  have hm : ordF4 (2 ^ f) = 2 ^ (f * 24) * (((2 ^ f) ^ 12 - 1) * (((2 ^ f) ^ 8 - 1) *
      (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)))) := by
    rw [ordF4, pow_mul]; ring
  refine Profile.of_eq hm (by
    repeat' apply Odd.mul
    all_goals exact odd_pow_sub_one hf (by norm_num)) (fun p k hp hk => ?_)
  simp only [hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk]
  simp [zF4, zList]

def zE6 (f : ℕ) : ℕ → Prop := zList f [12, 9, 8, 6, 5, 2]

theorem profile_ordE6 {f : ℕ} (hf : 1 ≤ f) : Profile (ordE6 (2 ^ f)) (f * 36) (zE6 f) := by
  set q := 2 ^ f with hq
  have hm : ordE6 q = 2 ^ (f * 36) * ((q ^ 12 - 1) * ((q ^ 9 - 1) * ((q ^ 8 - 1) *
      ((q ^ 6 - 1) * ((q ^ 5 - 1) * (q ^ 2 - 1)))))) / Nat.gcd 3 (q - 1) := by
    rw [ordE6, hq, pow_mul]; ring_nf
  refine Profile.of_div hm (by
    repeat' apply Odd.mul
    all_goals exact odd_pow_sub_one hf (by norm_num)) (Nat.gcd_dvd_right _ _) ?_
    (Nat.gcd_pos_of_pos_left _ (by norm_num)) (fun p k hp hk => ?_)
  · exact ⟨_, by
      rw [show (q - 1) * (q - 1) * ((q ^ 12 - 1) / (q - 1) * ((q ^ 9 - 1) / (q - 1)) *
        ((q ^ 8 - 1) * ((q ^ 6 - 1) * ((q ^ 5 - 1) * (q ^ 2 - 1))))) =
        ((q - 1) * ((q ^ 12 - 1) / (q - 1))) * (((q - 1) * ((q ^ 9 - 1) / (q - 1))) *
        ((q ^ 8 - 1) * ((q ^ 6 - 1) * ((q ^ 5 - 1) * (q ^ 2 - 1))))) by ring,
        Nat.mul_div_cancel' (Nat.sub_one_dvd_pow_sub_one q 12),
        Nat.mul_div_cancel' (Nat.sub_one_dvd_pow_sub_one q 9)]⟩
  · simp only [hp.prime.dvd_mul, hq, PrimDiv.dvd_pow_sub_one_iff hp hk]
    simp [zE6, zList]

def z2E6 (f k : ℕ) : Prop :=
  k ∣ f * 12 ∨ (k ∣ 2 * (f * 9) ∧ ¬ k ∣ f * 9) ∨ k ∣ f * 8 ∨ k ∣ f * 6 ∨
    (k ∣ 2 * (f * 5) ∧ ¬ k ∣ f * 5) ∨ k ∣ f * 2

theorem profile_ordTwistedE6 {f : ℕ} (hf : 1 ≤ f) :
    Profile (ordTwistedE6 (2 ^ f)) (f * 36) (z2E6 f) := by
  set q := 2 ^ f with hq
  have hm : ordTwistedE6 q = 2 ^ (f * 36) * ((q ^ 12 - 1) * ((q ^ 9 + 1) * ((q ^ 8 - 1) *
      ((q ^ 6 - 1) * ((q ^ 5 + 1) * (q ^ 2 - 1)))))) / Nat.gcd 3 (q + 1) := by
    rw [ordTwistedE6, hq, pow_mul]; ring_nf
  refine Profile.of_div hm (by
    refine Odd.mul (odd_pow_sub_one hf (by norm_num)) (Odd.mul (odd_pow_add_one hf (by norm_num))
      (Odd.mul (odd_pow_sub_one hf (by norm_num)) (Odd.mul (odd_pow_sub_one hf (by norm_num))
      (Odd.mul (odd_pow_add_one hf (by norm_num)) (odd_pow_sub_one hf (by norm_num))))))
    ) (Nat.gcd_dvd_right _ _) ?_ (Nat.gcd_pos_of_pos_left _ (by norm_num)) (fun p k hp hk => ?_)
  · have h9 := add_one_dvd_pow_add_one q (by decide : Odd 9)
    have h5 := add_one_dvd_pow_add_one q (by decide : Odd 5)
    exact (mul_dvd_mul h9 h5).trans ⟨(q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1),
      by ring⟩
  · simp only [hp.prime.dvd_mul, hq, PrimDiv.dvd_pow_sub_one_iff hp hk,
      PrimDiv.dvd_pow_add_one_iff hp hk]
    rfl

def zE7 (f : ℕ) : ℕ → Prop := zList f [18, 14, 12, 10, 8, 6, 2]

theorem profile_ordE7 {f : ℕ} (hf : 1 ≤ f) : Profile (ordE7 (2 ^ f)) (f * 63) (zE7 f) := by
  have hm : ordE7 (2 ^ f) = 2 ^ (f * 63) * (((2 ^ f) ^ 18 - 1) * (((2 ^ f) ^ 14 - 1) *
      (((2 ^ f) ^ 12 - 1) * (((2 ^ f) ^ 10 - 1) * (((2 ^ f) ^ 8 - 1) * (((2 ^ f) ^ 6 - 1) *
      ((2 ^ f) ^ 2 - 1))))))) := by
    rw [ordE7, Nat.coprime_two_left.mpr (odd_two_pow_sub_one hf), Nat.div_one, pow_mul]; ring
  refine Profile.of_eq hm (by
    repeat' apply Odd.mul
    all_goals exact odd_pow_sub_one hf (by norm_num)) (fun p k hp hk => ?_)
  simp only [hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk]
  simp [zE7, zList]

def zE8 (f : ℕ) : ℕ → Prop := zList f [30, 24, 20, 18, 14, 12, 8, 2]

theorem profile_ordE8 {f : ℕ} (hf : 1 ≤ f) : Profile (ordE8 (2 ^ f)) (f * 120) (zE8 f) := by
  have hm : ordE8 (2 ^ f) = 2 ^ (f * 120) * (((2 ^ f) ^ 30 - 1) * (((2 ^ f) ^ 24 - 1) *
      (((2 ^ f) ^ 20 - 1) * (((2 ^ f) ^ 18 - 1) * (((2 ^ f) ^ 14 - 1) * (((2 ^ f) ^ 12 - 1) *
      (((2 ^ f) ^ 8 - 1) * ((2 ^ f) ^ 2 - 1)))))))) := by
    rw [ordE8, pow_mul]; ring
  refine Profile.of_eq hm (by
    repeat' apply Odd.mul
    all_goals exact odd_pow_sub_one hf (by norm_num)) (fun p k hp hk => ?_)
  simp only [hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk]
  simp [zE8, zList]

def zSz (f k : ℕ) : Prop := (k ∣ 2 * (f * 2) ∧ ¬ k ∣ f * 2) ∨ k ∣ f

theorem profile_ordSuzuki {f : ℕ} (hf : 1 ≤ f) :
    Profile (ordSuzuki (2 ^ f)) (f * 2) (zSz f) := by
  have hm : ordSuzuki (2 ^ f) = 2 ^ (f * 2) * (((2 ^ f) ^ 2 + 1) * (2 ^ f - 1)) := by
    rw [ordSuzuki, pow_mul, mul_assoc]
  refine Profile.of_eq hm ((odd_pow_add_one hf (by norm_num)).mul (odd_two_pow_sub_one hf))
    (fun p k hp hk => ?_)
  rw [hp.prime.dvd_mul, PrimDiv.dvd_pow_add_one_iff hp hk, hp.dvd_sub_one_iff hk]
  rfl

def z2F4 (f k : ℕ) : Prop :=
  (k ∣ 2 * (f * 6) ∧ ¬ k ∣ f * 6) ∨ k ∣ f * 4 ∨ (k ∣ 2 * (f * 3) ∧ ¬ k ∣ f * 3) ∨ k ∣ f

theorem profile_ordTwistedF4 {f : ℕ} (hf : 1 ≤ f) :
    Profile (ordTwistedF4 (2 ^ f)) (f * 12) (z2F4 f) := by
  have hm : ordTwistedF4 (2 ^ f) = 2 ^ (f * 12) * (((2 ^ f) ^ 6 + 1) * (((2 ^ f) ^ 4 - 1) *
      (((2 ^ f) ^ 3 + 1) * (2 ^ f - 1)))) := by
    rw [ordTwistedF4, pow_mul]; ring
  refine Profile.of_eq hm ((odd_pow_add_one hf (by norm_num)).mul
    ((odd_pow_sub_one hf (by norm_num)).mul ((odd_pow_add_one hf (by norm_num)).mul
    (odd_two_pow_sub_one hf)))) (fun p k hp hk => ?_)
  simp only [hp.prime.dvd_mul, PrimDiv.dvd_pow_add_one_iff hp hk,
    PrimDiv.dvd_pow_sub_one_iff hp hk, hp.dvd_sub_one_iff hk]
  rfl

theorem ordTits_eq : ordTits = 2 ^ 11 * 8775 := by decide

theorem le_of_dvd_mul {k f a w : ℕ} (hf : 0 < f) (ha : 0 < a) (haw : f * a ≤ w)
    (h : k ∣ f * a) : k ≤ w :=
  (Nat.le_of_dvd (Nat.mul_pos hf ha) h).trans haw

theorem zList_dvd_closed {f : ℕ} {L : List ℕ} :
    ∀ k j, zList f L k → j ∣ k → 0 < j → zList f L j := by
  rintro k j ⟨a, ha, h⟩ hjk -
  exact ⟨a, ha, hjk.trans h⟩

theorem zList_le {f k w : ℕ} {L : List ℕ} (hf : 0 < f) (hL : ∀ a ∈ L, 0 < a ∧ a ≤ w)
    (hk : zList f L k) : k ≤ f * w := by
  obtain ⟨a, ha, h⟩ := hk
  exact le_of_dvd_mul hf (hL a ha).1 (Nat.mul_le_mul_left _ (hL a ha).2) h

theorem zA_dvd_closed {n f : ℕ} : ∀ k j, zA n f k → j ∣ k → 0 < j → zA n f j := by
  rintro k j ⟨i, hi, h⟩ hjk -
  exact ⟨i, hi, hjk.trans h⟩

theorem zA_le {n f k : ℕ} (hf : 0 < f) (hk : zA n f k) : k ≤ f * (n + 1) := by
  obtain ⟨i, hi, h⟩ := hk
  simp only [Finset.mem_Icc] at hi
  exact le_of_dvd_mul hf (by omega) (Nat.mul_le_mul_left _ hi.2) h

theorem zBC_dvd_closed {n f : ℕ} : ∀ k j, zBC n f k → j ∣ k → 0 < j → zBC n f j := by
  rintro k j ⟨i, hi, h⟩ hjk -
  exact ⟨i, hi, hjk.trans h⟩

theorem zBC_le {n f k : ℕ} (hf : 0 < f) (hk : zBC n f k) : k ≤ f * (2 * n) := by
  obtain ⟨i, hi, h⟩ := hk
  simp only [Finset.mem_Icc] at hi
  exact le_of_dvd_mul hf (by omega) (Nat.mul_le_mul_left _ (by omega)) h

theorem zBC_two_iff {g k : ℕ} : zBC 2 g k ↔ k ∣ g * 4 := by
  constructor
  · rintro ⟨i, hi, h⟩
    simp only [Finset.mem_Icc] at hi
    rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
    · exact h.trans ⟨2, by ring⟩
    · exact h
  · exact fun h => ⟨2, by simp, h⟩

theorem zD_dvd_closed {n f : ℕ} : ∀ k j, zD n f k → j ∣ k → 0 < j → zD n f j := by
  rintro k j (h | ⟨i, hi, h⟩) hjk -
  · exact Or.inl (hjk.trans h)
  · exact Or.inr ⟨i, hi, hjk.trans h⟩

theorem zD_le {n f k : ℕ} (hf : 0 < f) (hn : 2 ≤ n) (hk : zD n f k) :
    k ≤ f * (2 * (n - 1)) := by
  rcases hk with h | ⟨i, hi, h⟩
  · exact le_of_dvd_mul hf (by omega) (Nat.mul_le_mul_left _ (by omega)) h
  · simp only [Finset.mem_Icc] at hi
    exact le_of_dvd_mul hf (by omega) (Nat.mul_le_mul_left _ (by omega)) h

theorem z2D_le {n f k : ℕ} (hf : 0 < f) (hn : 1 ≤ n) (hk : z2D n f k) : k ≤ 2 * (f * n) := by
  rcases hk with ⟨h, -⟩ | ⟨i, hi, h⟩
  · exact Nat.le_of_dvd (by positivity) h
  · simp only [Finset.mem_Icc] at hi
    have := le_of_dvd_mul hf (by omega) (Nat.mul_le_mul_left f (by omega : 2 * i ≤ 2 * n)) h
    linarith

theorem zD4_le {f k : ℕ} (hf : 0 < f) (hk : zD4 f k) : k ≤ f * 12 := by
  rcases hk with ⟨h, -⟩ | h | h <;> exact le_of_dvd_mul hf (by norm_num) (by omega) h

theorem z2E6_le {f k : ℕ} (hf : 0 < f) (hk : z2E6 f k) : k ≤ 2 * (f * 9) := by
  rcases hk with h | ⟨h, -⟩ | h | h | ⟨h, -⟩ | h
  all_goals first
    | exact le_of_dvd_mul hf (by norm_num) (by omega) h
    | exact (Nat.le_of_dvd (by positivity) h).trans (by omega)

theorem zSz_le {f k : ℕ} (hf : 0 < f) (hk : zSz f k) : k ≤ 2 * (f * 2) := by
  rcases hk with ⟨h, -⟩ | h
  · exact Nat.le_of_dvd (by positivity) h
  · exact (Nat.le_of_dvd hf h).trans (by omega)

theorem z2F4_le {f k : ℕ} (hf : 0 < f) (hk : z2F4 f k) : k ≤ 2 * (f * 6) := by
  rcases hk with ⟨h, -⟩ | h | ⟨h, -⟩ | h
  · exact Nat.le_of_dvd (by positivity) h
  · exact le_of_dvd_mul hf (by norm_num) (by omega) h
  · exact (Nat.le_of_dvd (by positivity) h).trans (by omega)
  · exact (Nat.le_of_dvd hf h).trans (by omega)

theorem exists_half {n : ℕ} (hn : 2 ≤ n) : ∃ t, 1 ≤ t ∧ (n = 2 * t ∨ n = 2 * t + 1) :=
  ⟨n / 2, by omega, by omega⟩

theorem tri_even (t : ℕ) : 2 * t * (2 * t + 1) / 2 = t * (2 * t + 1) := by
  rw [mul_assoc, Nat.mul_div_cancel_left _ two_pos]

theorem tri_odd (t : ℕ) : (2 * t + 1) * (2 * t + 1 + 1) / 2 = (2 * t + 1) * (t + 1) := by
  rw [show (2 * t + 1) * (2 * t + 1 + 1) = 2 * ((2 * t + 1) * (t + 1)) by ring,
    Nat.mul_div_cancel_left _ two_pos]

theorem zU_top {n g t : ℕ} (hn : n = 2 * t ∨ n = 2 * t + 1) (ht : 1 ≤ t) (hg : 0 < g) :
    zU n g (2 * (g * (2 * t + 1))) := by
  refine ⟨2 * t + 1, ?_, Or.inr ⟨odd_two_mul_add_one t, dvd_rfl, fun h => ?_⟩⟩
  · simp only [Finset.mem_Icc]; omega
  · have h0 : 0 < g * (2 * t + 1) := by positivity
    have := Nat.le_of_dvd h0 h
    omega

theorem not_zU_mid {n g t : ℕ} (hn : n = 2 * t ∨ n = 2 * t + 1) (ht : 1 ≤ t) (hg : 0 < g) :
    ¬ zU n g (g * (2 * t + 1)) := by
  rintro ⟨i, hi, ⟨he, hd⟩ | ⟨-, hd, hnd⟩⟩
  · simp only [Finset.mem_Icc] at hi
    obtain ⟨c, rfl⟩ := Nat.dvd_of_mul_dvd_mul_left hg hd
    rcases Nat.even_or_odd c with ⟨c', rfl⟩ | hc
    · rcases Nat.eq_zero_or_pos c' with rfl | hc'
      · simp at hi
      · have : (2 * t + 1) * 2 ≤ (2 * t + 1) * (c' + c') := Nat.mul_le_mul_left _ (by omega)
        omega
    · exact (Nat.not_even_iff_odd.mpr ((odd_two_mul_add_one t).mul hc)) he
  · have h1 : 2 * t + 1 ∣ 2 * i :=
      Nat.dvd_of_mul_dvd_mul_left hg (by rwa [mul_left_comm] at hd)
    exact hnd (mul_dvd_mul_left g
      ((Nat.coprime_two_right.mpr (odd_two_mul_add_one t)).dvd_of_dvd_mul_left h1))

theorem zU_le {n g t k : ℕ} (hn : n = 2 * t ∨ n = 2 * t + 1) (hg : 0 < g) (hk : zU n g k) :
    k ≤ 2 * (g * (2 * t + 1)) := by
  obtain ⟨i, hi, ⟨-, hd⟩ | ⟨ho, hd, -⟩⟩ := hk
  · simp only [Finset.mem_Icc] at hi
    calc k ≤ g * i := Nat.le_of_dvd (Nat.mul_pos hg (by omega)) hd
      _ ≤ g * (2 * (2 * t + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (g * (2 * t + 1)) := by ring
  · simp only [Finset.mem_Icc] at hi
    obtain ⟨j, rfl⟩ := ho
    calc k ≤ 2 * (g * (2 * j + 1)) := Nat.le_of_dvd (by positivity) hd
      _ ≤ 2 * (g * (2 * t + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))

theorem eq_or_three_mul_le {k X : ℕ} (hX : 0 < X) (h : k ∣ 2 * X) (h' : ¬ k ∣ X) :
    k = 2 * X ∨ 3 * k ≤ 2 * X := by
  obtain ⟨c, hc⟩ := h
  rcases c with _ | _ | _ | c
  · omega
  · left; omega
  · exact absurd ⟨1, by omega⟩ h'
  · right
    have : k * 3 ≤ k * (c + 3) := Nat.mul_le_mul_left _ (by omega)
    rw [hc]; linarith

theorem zU_gap {n g t k : ℕ} (hn : n = 2 * t ∨ n = 2 * t + 1) (ht : 1 ≤ t) (hg : 0 < g)
    (hk : zU n g k) : k = 2 * (g * (2 * t + 1)) ∨ k + 2 * g ≤ 4 * (g * t) ∨
      k ≤ g * (2 * t + 2) := by
  obtain ⟨i, hi, ⟨-, hd⟩ | ⟨ho, hd, hnd⟩⟩ := hk
  · right; right
    simp only [Finset.mem_Icc] at hi
    calc k ≤ g * i := Nat.le_of_dvd (Nat.mul_pos hg (by omega)) hd
      _ ≤ g * (2 * t + 2) := Nat.mul_le_mul_left _ (by omega)
  · simp only [Finset.mem_Icc] at hi
    obtain ⟨j, rfl⟩ := ho
    have hG : g ≤ g * t := Nat.le_mul_of_pos_right g ht
    rcases Nat.lt_or_ge j t with hj | hj
    · right; left
      have h1 := Nat.le_of_dvd (by positivity) hd
      have h2 : g * (j + 1) ≤ g * t := Nat.mul_le_mul_left _ hj
      have h3 : g * (2 * j + 1) + g = 2 * (g * (j + 1)) := by ring
      omega
    · have hjt : j = t := by omega
      subst hjt
      rcases eq_or_three_mul_le (by positivity) hd hnd with h | h
      · exact Or.inl h
      · right; left
        have h3 : g * (2 * j + 1) = 2 * (g * j) + g := by ring
        omega

theorem ordTwistedA_two_two : ordTwistedA 2 2 = 2 ^ 3 * 9 := by decide

theorem ordTwistedA_three_two : ordTwistedA 3 2 = 2 ^ 6 * 405 := by decide

theorem Profile.ne_small {m N : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) (h3 : N ≠ 3)
    (h6 : N ≠ 6) : m ≠ ordTwistedA 2 2 ∧ m ≠ ordTwistedA 3 2 := by
  rw [ordTwistedA_two_two, ordTwistedA_three_two]
  exact ⟨h.ne_of_ne (by decide) h3, h.ne_of_ne (by decide) h6⟩

theorem two_mul_ne_six {g t : ℕ} (hg : 1 ≤ g) (ht : 1 ≤ t) (hs : ¬ (g = 1 ∧ t = 1)) :
    2 * (g * (2 * t + 1)) ≠ 6 := by
  intro h6
  have : g * 3 ≤ g * (2 * t + 1) := Nat.mul_le_mul_left _ (by omega)
  have hg1 : g = 1 := by omega
  subst hg1
  exact hs ⟨rfl, by omega⟩

theorem mul_ne_six {g t : ℕ} (hg : 1 ≤ g) (ht : 1 ≤ t) (hs : ¬ (g = 2 ∧ t = 1)) :
    g * (2 * t + 1) ≠ 6 := by
  intro h6
  rcases Nat.lt_or_ge t 2 with h | h
  · have : t = 1 := by omega
    subst this
    exact hs ⟨by omega, rfl⟩
  · have : g * 5 ≤ g * (2 * t + 1) := Nat.mul_le_mul_left _ (by omega)
    have hg1 : g = 1 := by omega
    subst hg1
    omega

theorem ne_ordTwistedA_of_dvd_closed {m N : ℕ} {Z : ℕ → Prop} (h : Profile m N Z)
    (hZ : ∀ k j, Z k → j ∣ k → 0 < j → Z j) (hsm : m ≠ ordTwistedA 2 2 ∧ m ≠ ordTwistedA 3 2)
    {n g : ℕ} (hn : 2 ≤ n) (hg : 1 ≤ g) : m ≠ ordTwistedA n (2 ^ g) := by
  intro hm
  obtain ⟨t, ht1, ht⟩ := exists_half hn
  by_cases hs : g = 1 ∧ t = 1
  · obtain ⟨rfl, rfl⟩ := hs
    rcases ht with rfl | rfl
    · exact hsm.1 (by simpa using hm)
    · exact hsm.2 (by simpa using hm)
  have hU := profile_ordTwistedA hn hg
  rw [← hm] at hU
  have hZZ := (h.transfer hU).2
  have h0 : 0 < g * (2 * t + 1) := by positivity
  have hZ1 : Z (2 * (g * (2 * t + 1))) :=
    (hZZ _ (by omega) (two_mul_ne_six hg ht1 hs)).mpr (zU_top ht ht1 (by omega))
  by_cases hs2 : g = 2 ∧ t = 1
  · obtain ⟨rfl, rfl⟩ := hs2
    have h3 := (hZZ 3 (by norm_num) (by norm_num)).mp (hZ _ 3 hZ1 ⟨4, by norm_num⟩ (by norm_num))
    rcases ht with rfl | rfl <;> revert h3 <;> simp only [zU] <;> decide
  · have h3 : 1 * 3 ≤ g * (2 * t + 1) := Nat.mul_le_mul hg (by omega)
    exact not_zU_mid ht ht1 (by omega)
      ((hZZ _ (by omega) (mul_ne_six hg ht1 hs2)).mp (hZ _ _ hZ1 (dvd_mul_left _ 2) h0))

theorem top_eq {m N w : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) (hw : Z w) (hw2 : 2 ≤ w)
    (hw6 : w ≠ 6) (hle : ∀ k, Z k → k ≤ w) {n g t : ℕ} (hn : 2 ≤ n) (hg : 1 ≤ g)
    (ht1 : 1 ≤ t) (ht : n = 2 * t ∨ n = 2 * t + 1) (hs : ¬ (g = 1 ∧ t = 1))
    (hm : m = ordTwistedA n (2 ^ g)) :
    w = 2 * (g * (2 * t + 1)) ∧ N = g * (n * (n + 1) / 2) ∧
      ∀ k, 2 ≤ k → k ≠ 6 → (Z k ↔ zU n g k) := by
  have hU := profile_ordTwistedA hn hg
  rw [← hm] at hU
  obtain ⟨hN, hZZ⟩ := h.transfer hU
  have h0 : 0 < g * (2 * t + 1) := by positivity
  have h1 := hle _ ((hZZ _ (by omega) (two_mul_ne_six hg ht1 hs)).mpr (zU_top ht ht1 (by omega)))
  have h2 := zU_le ht (by omega) ((hZZ _ hw2 hw6).mp hw)
  exact ⟨le_antisymm h2 h1, hN, hZZ⟩

theorem vsSp4 {m N : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) {g : ℕ} (hg : 1 ≤ g)
    (hm : m = ordBC 2 (2 ^ g)) : N = g * 4 ∧ ∀ k, 2 ≤ k → k ≠ 6 → (Z k ↔ k ∣ g * 4) := by
  have hS := profile_ordBC (n := 2) hg
  rw [← hm] at hS
  obtain ⟨hN, hZZ⟩ := h.transfer hS
  exact ⟨by omega, fun k hk h6 => (hZZ k hk h6).trans zBC_two_iff⟩

theorem dvd_of_rel {a b c d f g : ℕ} (hg : 0 < g) (hrel : c * f = d * g) (h : g * a ∣ f * b) :
    a * c ∣ b * d := by
  have h1 : g * a * c ∣ f * b * c := mul_dvd_mul_right h c
  have e1 : f * b * c = b * d * g := by
    calc f * b * c = b * (c * f) := by ring
      _ = b * (d * g) := by rw [hrel]
      _ = b * d * g := by ring
  rw [e1, show g * a * c = a * c * g by ring] at h1
  exact Nat.dvd_of_mul_dvd_mul_right hg h1

theorem ordA_ne_small {n f : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) :
    ordA n (2 ^ f) ≠ ordTwistedA 2 2 ∧ ordA n (2 ^ f) ≠ ordTwistedA 3 2 := by
  by_cases hN : f * (n * (n + 1) / 2) ≠ 3 ∧ f * (n * (n + 1) / 2) ≠ 6
  · exact (profile_ordA hn hf).ne_small hN.1 hN.2
  · have hn3 : n ≤ 3 := by
      by_contra h
      have : 4 * 5 ≤ n * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
      have : n * (n + 1) / 2 ≤ f * (n * (n + 1) / 2) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hf6 : f ≤ 6 := by
      have : 1 * 2 ≤ n * (n + 1) := Nat.mul_le_mul hn (by omega)
      have : f * 1 ≤ f * (n * (n + 1) / 2) := Nat.mul_le_mul_left _ (by omega)
      omega
    interval_cases n <;> interval_cases f <;> first | omega | decide

theorem ordA_ne_ordTwistedA {n f u g : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) (hu : 2 ≤ u) (hg : 1 ≤ g) :
    ordA n (2 ^ f) ≠ ordTwistedA u (2 ^ g) :=
  ne_ordTwistedA_of_dvd_closed (profile_ordA hn hf) zA_dvd_closed (ordA_ne_small hn hf) hu hg

theorem ordA_ne_ordBC_two {n f g : ℕ} (hn : 1 ≤ n) (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordA n (2 ^ f) ≠ ordBC 2 (2 ^ g) := by
  intro hm
  obtain ⟨hN, hZ⟩ := vsSp4 (profile_ordA hn hf) hg hm
  have h4 := zA_le (by omega) ((hZ _ (by omega) (by omega)).mpr dvd_rfl)
  have hn2 : n ≤ 2 := by
    by_contra h
    have : 3 * (n + 1) ≤ n * (n + 1) := Nat.mul_le_mul_right _ (by omega)
    have : f * (n + 1) < f * (n * (n + 1) / 2) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    omega
  have hk : zA n f (f * 2) := ⟨2, by simp; omega, dvd_rfl⟩
  interval_cases n
  · have hf' : f = g * 4 := by simpa using hN
    have h1 := (hZ _ (by omega) (by omega)).mp hk
    rw [hf'] at h1
    have := Nat.le_of_dvd (by omega) h1
    omega
  · have hf' : f * 3 = g * 4 := by simpa using hN
    have h1 := (hZ _ (by omega) (by omega)).mp hk
    rw [← hf'] at h1
    have := Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < f) h1
    omega

theorem ordBC_ne_ordTwistedA {n f u g : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f) (hu : 2 ≤ u)
    (hg : 1 ≤ g) : ordBC n (2 ^ f) ≠ ordTwistedA u (2 ^ g) := by
  have hN : 9 ≤ f * (n * n) := by
    have : 3 * 3 ≤ n * n := Nat.mul_le_mul hn hn
    have : n * n ≤ f * (n * n) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  exact ne_ordTwistedA_of_dvd_closed (profile_ordBC hf) zBC_dvd_closed
    ((profile_ordBC hf).ne_small (by omega) (by omega)) hu hg

theorem ordBC_ne_ordBC_two {n f g : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordBC n (2 ^ f) ≠ ordBC 2 (2 ^ g) := by
  intro hm
  obtain ⟨hN, hZ⟩ := vsSp4 (profile_ordBC hf) hg hm
  have h4 := zBC_le (by omega) ((hZ _ (by omega) (by omega)).mpr dvd_rfl)
  have : f * (2 * n) < f * (n * n) := Nat.mul_lt_mul_of_pos_left (by nlinarith) (by omega)
  omega

theorem ordD_ne_ordTwistedA {n f u g : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) (hu : 2 ≤ u) (hg : 1 ≤ g) :
    ordD n (2 ^ f) ≠ ordTwistedA u (2 ^ g) := by
  have hN : 12 ≤ f * (n * (n - 1)) := by
    have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    have : n * (n - 1) ≤ f * (n * (n - 1)) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  exact ne_ordTwistedA_of_dvd_closed (profile_ordD (by omega) hf) zD_dvd_closed
    ((profile_ordD (by omega) hf).ne_small (by omega) (by omega)) hu hg

theorem ordD_ne_ordBC_two {n f g : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordD n (2 ^ f) ≠ ordBC 2 (2 ^ g) := by
  intro hm
  obtain ⟨hN, hZ⟩ := vsSp4 (profile_ordD (by omega) hf) hg hm
  have h4 := zD_le (by omega) (by omega) ((hZ _ (by omega) (by omega)).mpr dvd_rfl)
  have : f * (2 * (n - 1)) < f * (n * (n - 1)) :=
    Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_right (by omega) (by omega)) (by omega)
  omega

theorem ordTwistedD_ne_ordBC_two {n f g : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordTwistedD n (2 ^ f) ≠ ordBC 2 (2 ^ g) := by
  intro hm
  obtain ⟨hN, hZ⟩ := vsSp4 (profile_ordTwistedD (by omega) hf) hg hm
  have h4 := z2D_le (by omega) (by omega) ((hZ _ (by omega) (by omega)).mpr dvd_rfl)
  have : 2 * (f * n) < f * (n * (n - 1)) := by
    have : f * n * 2 < f * n * (n - 1) :=
      Nat.mul_lt_mul_of_pos_left (by omega) (Nat.mul_pos (by omega) (by omega))
    linarith [mul_comm (f * n) 2, mul_assoc f n (n - 1)]
  omega

theorem ordTwistedD_ne_ordTwistedA {n f u g : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) (hu : 2 ≤ u)
    (hg : 1 ≤ g) : ordTwistedD n (2 ^ f) ≠ ordTwistedA u (2 ^ g) := by
  intro hm
  have hX := profile_ordTwistedD (by omega : 1 ≤ n) hf
  obtain ⟨t, ht1, ht⟩ := exists_half hu
  have hN12 : 12 ≤ f * (n * (n - 1)) := by
    have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    have : n * (n - 1) ≤ f * (n * (n - 1)) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  by_cases hs : g = 1 ∧ t = 1
  · obtain ⟨rfl, rfl⟩ := hs
    have hsm := hX.ne_small (by omega) (by omega)
    rcases ht with rfl | rfl
    · exact hsm.1 (by simpa using hm)
    · exact hsm.2 (by simpa using hm)
  have hfn0 : 0 < f * n := Nat.mul_pos (by omega) (by omega)
  have hfnn : n ≤ f * n := Nat.le_mul_of_pos_left n (by omega)
  have hw : z2D n f (2 * (f * n)) := Or.inl ⟨dvd_rfl, fun h => by
    have := Nat.le_of_dvd hfn0 h; omega⟩
  obtain ⟨hw1, hN, hZ⟩ := top_eq hX hw (by omega) (by omega)
    (fun k hk => z2D_le (by omega) (by omega) hk) hu hg ht1 ht hs hm
  have hfn : f * n = g * (2 * t + 1) := by omega
  have hrel : n = t + 1 ∨ n = t + 2 := by
    rcases ht with rfl | rfl
    · rw [tri_even] at hN
      left
      have h1 : f * n * (n - 1) = f * n * t := by
        calc f * n * (n - 1) = f * (n * (n - 1)) := by ring
          _ = g * (t * (2 * t + 1)) := hN
          _ = f * n * t := by rw [hfn]; ring
      have := Nat.eq_of_mul_eq_mul_left hfn0 h1
      omega
    · rw [tri_odd] at hN
      right
      have h1 : f * n * (n - 1) = f * n * (t + 1) := by
        calc f * n * (n - 1) = f * (n * (n - 1)) := by ring
          _ = g * ((2 * t + 1) * (t + 1)) := hN
          _ = f * n * (t + 1) := by rw [hfn]; ring
      have := Nat.eq_of_mul_eq_mul_left hfn0 h1
      omega
  have hk : z2D n f (2 * (f * (n - 1))) :=
    Or.inr ⟨n - 1, by simp; omega, ⟨1, by ring⟩⟩
  have hk6 : 2 * (f * (n - 1)) ≠ 6 := by
    intro h6
    have h3 : f * (n - 1) = 3 := by omega
    have : f * 3 ≤ f * (n - 1) := Nat.mul_le_mul_left _ (by omega)
    have hf1 : f = 1 := by omega
    subst hf1
    have hn4 : n = 4 := by omega
    subst hn4
    have : g * 3 ≤ g * (2 * t + 1) := Nat.mul_le_mul_left _ (by omega)
    rcases Nat.lt_or_ge g 2 with hg2 | hg2
    · have : g = 1 := by omega
      subst this
      omega
    · have : 2 * 3 ≤ g * 3 := Nat.mul_le_mul_right _ hg2
      omega
  have hk2 : 2 ≤ 2 * (f * (n - 1)) := by
    have : 1 ≤ f * (n - 1) := Nat.mul_pos (by omega) (by omega)
    omega
  have hgap := zU_gap ht ht1 (by omega) ((hZ _ hk2 hk6).mp hk)
  rcases hrel with rfl | rfl
  · simp only [Nat.add_sub_cancel] at hgap
    have ht3 : 3 ≤ t := by omega
    rcases hgap with h | h | h
    · nlinarith
    · nlinarith
    · nlinarith [Nat.mul_le_mul_left (f * t) ht3, Nat.mul_le_mul_left f ht3]
  · simp only [show t + 2 - 1 = t + 1 by omega] at hgap
    have ht2 : 2 ≤ t := by omega
    rcases hgap with h | h | h
    · nlinarith
    · nlinarith
    · nlinarith [Nat.mul_le_mul_left f ht2]

theorem ordG2_ne_ordTwistedA {f u g : ℕ} (hf : 2 ≤ f) (hu : 2 ≤ u) (hg : 1 ≤ g) :
    ordG2 (2 ^ f) ≠ ordTwistedA u (2 ^ g) :=
  ne_ordTwistedA_of_dvd_closed (profile_ordG2 (by omega)) zList_dvd_closed
    ((profile_ordG2 (by omega)).ne_small (by omega) (by omega)) hu hg

theorem ordBC_two_eq {g : ℕ} (hg : 1 ≤ g) :
    ordBC 2 (2 ^ g) = 2 ^ (g * 4) * (((2 ^ g) ^ 2 - 1) * ((2 ^ g) ^ 4 - 1)) := by
  rw [ordBC, show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num),
    Nat.coprime_two_left.mpr (odd_two_pow_sub_one hg), Nat.div_one, pow_mul 2 g 4]

theorem ordG2_ne_ordBC_two {f g : ℕ} (hf : 2 ≤ f) (hg : 1 ≤ g) :
    ordG2 (2 ^ f) ≠ ordBC 2 (2 ^ g) := by
  intro hm
  obtain ⟨hN, -⟩ := vsSp4 (profile_ordG2 (by omega)) hg hm
  rw [ordG2_eq, ordBC_two_eq hg, hN] at hm
  have hm' := Nat.eq_of_mul_eq_mul_left (by positivity) hm
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, hN] at hm'
  have hpos : 0 < 2 ^ (g * 4) - 1 := by
    have := Nat.one_lt_two_pow (n := g * 4) (by omega); omega
  rw [mul_comm] at hm'
  have h2 := Nat.eq_of_mul_eq_mul_right hpos hm'
  have h3 : 2 ^ (f * 2) = 2 ^ (g * 2) := by
    have := Nat.one_le_two_pow (n := f * 2)
    have := Nat.one_le_two_pow (n := g * 2)
    omega
  have := Nat.pow_right_injective le_rfl h3
  omega

theorem ordTrialityD4_ne_ordTwistedA {f u g : ℕ} (hf : 1 ≤ f) (hu : 2 ≤ u) (hg : 1 ≤ g) :
    ordTrialityD4 (2 ^ f) ≠ ordTwistedA u (2 ^ g) := by
  intro hm
  have hX := profile_ordTrialityD4 hf
  obtain ⟨t, ht1, ht⟩ := exists_half hu
  by_cases hs : g = 1 ∧ t = 1
  · obtain ⟨rfl, rfl⟩ := hs
    have hsm := hX.ne_small (by omega) (by omega)
    rcases ht with rfl | rfl
    · exact hsm.1 (by simpa using hm)
    · exact hsm.2 (by simpa using hm)
  have hw : zD4 f (f * 12) := Or.inl ⟨dvd_rfl, fun h => by
    have := Nat.le_of_dvd (by omega) h; omega⟩
  obtain ⟨hw1, hN, hZ⟩ := top_eq hX hw (by omega) (by omega)
    (fun k hk => zD4_le (by omega) hk) hu hg ht1 ht hs hm
  have hg0 : 0 < g * (2 * t + 1) := by positivity
  have hk : ∀ {u : ℕ}, 3 ≤ u → zU u g (g * 4) := fun hu3 =>
    ⟨4, by simp; omega, Or.inl ⟨by decide, dvd_rfl⟩⟩
  rcases ht with rfl | rfl
  · rw [tri_even] at hN
    have h2 : g * (2 * t + 1) * t = g * (2 * t + 1) * 2 := by
      calc g * (2 * t + 1) * t = g * (t * (2 * t + 1)) := by ring
        _ = 2 * (g * (2 * t + 1)) := by omega
        _ = g * (2 * t + 1) * 2 := by ring
    have ht2 := Nat.eq_of_mul_eq_mul_left hg0 h2
    subst ht2
    have hrel : 6 * f = 5 * g := by omega
    rcases (hZ _ (by omega) (by omega)).mpr (hk (by omega)) with ⟨h, -⟩ | h | h
    · exact absurd (dvd_of_rel (by omega) hrel h) (by decide)
    · exact absurd (dvd_of_rel (by omega) hrel h) (by decide)
    · exact absurd (dvd_of_rel (by omega) hrel h) (by decide)
  · rw [tri_odd] at hN
    have h2 : g * (2 * t + 1) * (t + 1) = g * (2 * t + 1) * 2 := by
      calc g * (2 * t + 1) * (t + 1) = g * ((2 * t + 1) * (t + 1)) := by ring
        _ = 2 * (g * (2 * t + 1)) := by omega
        _ = g * (2 * t + 1) * 2 := by ring
    have ht2 := Nat.eq_of_mul_eq_mul_left hg0 h2
    have ht1' : t = 1 := by omega
    subst ht1'
    have hrel : 2 * f = 1 * g := by omega
    rcases (hZ _ (by omega) (by omega)).mpr (hk (by omega)) with ⟨h, -⟩ | h | h
    · exact absurd (dvd_of_rel (by omega) hrel h) (by decide)
    · exact absurd (dvd_of_rel (by omega) hrel h) (by decide)
    · exact absurd (dvd_of_rel (by omega) hrel h) (by decide)

theorem ordTrialityD4_ne_ordBC_two {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordTrialityD4 (2 ^ f) ≠ ordBC 2 (2 ^ g) := by
  intro hm
  obtain ⟨hN, hZ⟩ := vsSp4 (profile_ordTrialityD4 hf) hg hm
  have hrel : g = 3 * f := by omega
  have h := (hZ (f * 4) (by omega) (by omega)).mpr ⟨3, by rw [hrel]; ring⟩
  rcases h with ⟨-, h⟩ | h | h
  · exact h dvd_rfl
  · have := Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < f) h; omega
  · have := Nat.le_of_dvd (by omega) h; omega

theorem ordF4_ne_ordTwistedA {f u g : ℕ} (hf : 1 ≤ f) (hu : 2 ≤ u) (hg : 1 ≤ g) :
    ordF4 (2 ^ f) ≠ ordTwistedA u (2 ^ g) :=
  ne_ordTwistedA_of_dvd_closed (profile_ordF4 hf) zList_dvd_closed
    ((profile_ordF4 hf).ne_small (by omega) (by omega)) hu hg

theorem ordF4_ne_ordBC_two {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordF4 (2 ^ f) ≠ ordBC 2 (2 ^ g) := by
  intro hm
  obtain ⟨hN, hZ⟩ := vsSp4 (profile_ordF4 hf) hg hm
  have := zList_le (w := 12) (by omega) (by simp) ((hZ _ (by omega) (by omega)).mpr dvd_rfl)
  omega

theorem ordE6_ne_ordTwistedA {f u g : ℕ} (hf : 1 ≤ f) (hu : 2 ≤ u) (hg : 1 ≤ g) :
    ordE6 (2 ^ f) ≠ ordTwistedA u (2 ^ g) :=
  ne_ordTwistedA_of_dvd_closed (profile_ordE6 hf) zList_dvd_closed
    ((profile_ordE6 hf).ne_small (by omega) (by omega)) hu hg

theorem ordE6_ne_ordBC_two {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordE6 (2 ^ f) ≠ ordBC 2 (2 ^ g) := by
  intro hm
  obtain ⟨hN, hZ⟩ := vsSp4 (profile_ordE6 hf) hg hm
  have := zList_le (w := 12) (by omega) (by simp) ((hZ _ (by omega) (by omega)).mpr dvd_rfl)
  omega

theorem ordTwistedE6_ne_ordTwistedA {f u g : ℕ} (hf : 1 ≤ f) (hu : 2 ≤ u) (hg : 1 ≤ g) :
    ordTwistedE6 (2 ^ f) ≠ ordTwistedA u (2 ^ g) := by
  intro hm
  have hX := profile_ordTwistedE6 hf
  obtain ⟨t, ht1, ht⟩ := exists_half hu
  by_cases hs : g = 1 ∧ t = 1
  · obtain ⟨rfl, rfl⟩ := hs
    have hsm := hX.ne_small (by omega) (by omega)
    rcases ht with rfl | rfl
    · exact hsm.1 (by simpa using hm)
    · exact hsm.2 (by simpa using hm)
  have hw : z2E6 f (2 * (f * 9)) := Or.inr (Or.inl ⟨dvd_rfl, fun h => by
    have := Nat.le_of_dvd (by omega) h; omega⟩)
  obtain ⟨hw1, hN, hZ⟩ := top_eq hX hw (by omega) (by omega)
    (fun k hk => z2E6_le (by omega) hk) hu hg ht1 ht hs hm
  have hg0 : 0 < g * (2 * t + 1) := by positivity
  rcases ht with rfl | rfl
  · rw [tri_even] at hN
    have h2 : g * (2 * t + 1) * t = g * (2 * t + 1) * 4 := by
      calc g * (2 * t + 1) * t = g * (t * (2 * t + 1)) := by ring
        _ = 4 * (g * (2 * t + 1)) := by omega
        _ = g * (2 * t + 1) * 4 := by ring
    have ht4 := Nat.eq_of_mul_eq_mul_left hg0 h2
    subst ht4
    have hrel : 1 * f = 1 * g := by omega
    have hk : zU (2 * 4) g (g * 14) := ⟨7, by simp, Or.inr ⟨by decide, ⟨1, by ring⟩,
      fun h => by have := Nat.le_of_dvd (by omega) h; omega⟩⟩
    rcases (hZ _ (by omega) (by omega)).mpr hk with h | ⟨h, -⟩ | h | h | ⟨h, -⟩ | h
    all_goals first
      | exact absurd (dvd_of_rel (by omega) hrel h) (by decide)
      | exact absurd (dvd_of_rel (by omega) hrel (by rwa [show 2 * (f * 9) = f * 18 by ring] at h))
          (by decide)
      | exact absurd (dvd_of_rel (by omega) hrel (by rwa [show 2 * (f * 5) = f * 10 by ring] at h))
          (by decide)
  · rw [tri_odd] at hN
    have h2 : g * (2 * t + 1) * (t + 1) = g * (2 * t + 1) * 4 := by
      calc g * (2 * t + 1) * (t + 1) = g * ((2 * t + 1) * (t + 1)) := by ring
        _ = 4 * (g * (2 * t + 1)) := by omega
        _ = g * (2 * t + 1) * 4 := by ring
    have ht4 := Nat.eq_of_mul_eq_mul_left hg0 h2
    have ht3 : t = 3 := by omega
    subst ht3
    have hrel : 9 * f = 7 * g := by omega
    have hk : zU (2 * 3 + 1) g (g * 8) := ⟨8, by simp, Or.inl ⟨by decide, dvd_rfl⟩⟩
    rcases (hZ _ (by omega) (by omega)).mpr hk with h | ⟨h, -⟩ | h | h | ⟨h, -⟩ | h
    all_goals first
      | exact absurd (dvd_of_rel (by omega) hrel h) (by decide)
      | exact absurd (dvd_of_rel (by omega) hrel (by rwa [show 2 * (f * 9) = f * 18 by ring] at h))
          (by decide)
      | exact absurd (dvd_of_rel (by omega) hrel (by rwa [show 2 * (f * 5) = f * 10 by ring] at h))
          (by decide)

theorem ordTwistedE6_ne_ordBC_two {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordTwistedE6 (2 ^ f) ≠ ordBC 2 (2 ^ g) := by
  intro hm
  obtain ⟨hN, hZ⟩ := vsSp4 (profile_ordTwistedE6 hf) hg hm
  have := z2E6_le (by omega) ((hZ _ (by omega) (by omega)).mpr dvd_rfl)
  omega

theorem ordE7_ne_ordTwistedA {f u g : ℕ} (hf : 1 ≤ f) (hu : 2 ≤ u) (hg : 1 ≤ g) :
    ordE7 (2 ^ f) ≠ ordTwistedA u (2 ^ g) :=
  ne_ordTwistedA_of_dvd_closed (profile_ordE7 hf) zList_dvd_closed
    ((profile_ordE7 hf).ne_small (by omega) (by omega)) hu hg

theorem ordE7_ne_ordBC_two {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordE7 (2 ^ f) ≠ ordBC 2 (2 ^ g) := by
  intro hm
  obtain ⟨hN, hZ⟩ := vsSp4 (profile_ordE7 hf) hg hm
  have := zList_le (w := 18) (by omega) (by simp) ((hZ _ (by omega) (by omega)).mpr dvd_rfl)
  omega

theorem ordE8_ne_ordTwistedA {f u g : ℕ} (hf : 1 ≤ f) (hu : 2 ≤ u) (hg : 1 ≤ g) :
    ordE8 (2 ^ f) ≠ ordTwistedA u (2 ^ g) :=
  ne_ordTwistedA_of_dvd_closed (profile_ordE8 hf) zList_dvd_closed
    ((profile_ordE8 hf).ne_small (by omega) (by omega)) hu hg

theorem ordE8_ne_ordBC_two {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordE8 (2 ^ f) ≠ ordBC 2 (2 ^ g) := by
  intro hm
  obtain ⟨hN, hZ⟩ := vsSp4 (profile_ordE8 hf) hg hm
  have := zList_le (w := 30) (by omega) (by simp) ((hZ _ (by omega) (by omega)).mpr dvd_rfl)
  omega

theorem ordSuzuki_ne_ordTwistedA {f u g : ℕ} (hf : Odd f) (hf3 : 3 ≤ f) (hu : 2 ≤ u)
    (hg : 1 ≤ g) : ordSuzuki (2 ^ f) ≠ ordTwistedA u (2 ^ g) := by
  intro hm
  have hX := profile_ordSuzuki (by omega : 1 ≤ f)
  obtain ⟨t, ht1, ht⟩ := exists_half hu
  by_cases hs : g = 1 ∧ t = 1
  · obtain ⟨rfl, rfl⟩ := hs
    by_cases hf3' : f = 3
    · subst hf3'
      rcases ht with rfl | rfl
      · exact absurd hm (by decide)
      · exact absurd hm (by decide)
    · have hsm := hX.ne_small (by omega) (by omega)
      rcases ht with rfl | rfl
      · exact hsm.1 (by simpa using hm)
      · exact hsm.2 (by simpa using hm)
  have hw : zSz f (2 * (f * 2)) := Or.inl ⟨dvd_rfl, fun h => by
    have := Nat.le_of_dvd (by omega) h; omega⟩
  obtain ⟨hw1, hN, hZ⟩ := top_eq hX hw (by omega) (by omega)
    (fun k hk => zSz_le (by omega) hk) hu hg ht1 ht hs hm
  have hg0 : 0 < g * (2 * t + 1) := by positivity
  rcases ht with rfl | rfl
  · rw [tri_even] at hN
    have h2 : g * (2 * t + 1) * t = g * (2 * t + 1) * 1 := by
      calc g * (2 * t + 1) * t = g * (t * (2 * t + 1)) := by ring
        _ = 1 * (g * (2 * t + 1)) := by omega
        _ = g * (2 * t + 1) * 1 := by ring
    have ht1' := Nat.eq_of_mul_eq_mul_left hg0 h2
    subst ht1'
    have hrel : 3 * g = 2 * f := by omega
    have h6 : f ≠ 6 := by rintro rfl; exact absurd hf (by decide)
    obtain ⟨i, hi, ⟨he, h⟩ | ⟨ho, -, h⟩⟩ := (hZ f (by omega) h6).mp (Or.inr dvd_rfl)
    · simp only [Finset.mem_Icc] at hi
      have hi2 : i = 2 ∨ i = 3 := by omega
      rcases hi2 with rfl | rfl
      · exact absurd (dvd_of_rel (a := 1) (b := 2) (by omega) hrel (by simpa using h))
          (by decide)
      · exact absurd he (by decide)
    · simp only [Finset.mem_Icc] at hi
      have hi2 : i = 2 ∨ i = 3 := by omega
      rcases hi2 with rfl | rfl
      · exact absurd ho (by decide)
      · exact h ⟨2, by omega⟩
  · rw [tri_odd] at hN
    have : g * (2 * t + 1) * (t + 1) = g * (2 * t + 1) * 1 := by
      calc g * (2 * t + 1) * (t + 1) = g * ((2 * t + 1) * (t + 1)) := by ring
        _ = 1 * (g * (2 * t + 1)) := by omega
        _ = g * (2 * t + 1) * 1 := by ring
    have := Nat.eq_of_mul_eq_mul_left hg0 this
    omega

theorem ordSuzuki_ne_ordBC_two {f g : ℕ} (hf : Odd f) (hg : 1 ≤ g) :
    ordSuzuki (2 ^ f) ≠ ordBC 2 (2 ^ g) := by
  intro hm
  obtain ⟨hN, -⟩ := vsSp4 (profile_ordSuzuki (by obtain ⟨k, rfl⟩ := hf; omega)) hg hm
  obtain ⟨k, rfl⟩ := hf
  omega

theorem ordTwistedF4_ne_ordTwistedA {f u g : ℕ} (hf : 1 ≤ f) (hu : 2 ≤ u) (hg : 1 ≤ g) :
    ordTwistedF4 (2 ^ f) ≠ ordTwistedA u (2 ^ g) := by
  intro hm
  have hX := profile_ordTwistedF4 hf
  obtain ⟨t, ht1, ht⟩ := exists_half hu
  by_cases hs : g = 1 ∧ t = 1
  · obtain ⟨rfl, rfl⟩ := hs
    have hsm := hX.ne_small (by omega) (by omega)
    rcases ht with rfl | rfl
    · exact hsm.1 (by simpa using hm)
    · exact hsm.2 (by simpa using hm)
  have hw : z2F4 f (2 * (f * 6)) := Or.inl ⟨dvd_rfl, fun h => by
    have := Nat.le_of_dvd (by omega) h; omega⟩
  obtain ⟨hw1, hN, hZ⟩ := top_eq hX hw (by omega) (by omega)
    (fun k hk => z2F4_le (by omega) hk) hu hg ht1 ht hs hm
  have hg0 : 0 < g * (2 * t + 1) := by positivity
  have hk : ∀ {u : ℕ}, 3 ≤ u → zU u g (g * 4) := fun hu3 =>
    ⟨4, by simp; omega, Or.inl ⟨by decide, dvd_rfl⟩⟩
  have e12 : 2 * (f * 6) = f * 12 := by ring
  have e6 : 2 * (f * 3) = f * 6 := by ring
  rcases ht with rfl | rfl
  · rw [tri_even] at hN
    have h2 : g * (2 * t + 1) * t = g * (2 * t + 1) * 2 := by
      calc g * (2 * t + 1) * t = g * (t * (2 * t + 1)) := by ring
        _ = 2 * (g * (2 * t + 1)) := by omega
        _ = g * (2 * t + 1) * 2 := by ring
    have ht2 := Nat.eq_of_mul_eq_mul_left hg0 h2
    subst ht2
    have hrel : 6 * f = 5 * g := by omega
    rcases (hZ _ (by omega) (by omega)).mpr (hk (by omega)) with ⟨h, -⟩ | h | ⟨h, -⟩ | h
    · exact absurd (dvd_of_rel (by omega) hrel (e12 ▸ h)) (by decide)
    · exact absurd (dvd_of_rel (by omega) hrel h) (by decide)
    · exact absurd (dvd_of_rel (by omega) hrel (e6 ▸ h)) (by decide)
    · exact absurd (dvd_of_rel (a := 4) (b := 1) (by omega) hrel (by simpa using h)) (by decide)
  · rw [tri_odd] at hN
    have h2 : g * (2 * t + 1) * (t + 1) = g * (2 * t + 1) * 2 := by
      calc g * (2 * t + 1) * (t + 1) = g * ((2 * t + 1) * (t + 1)) := by ring
        _ = 2 * (g * (2 * t + 1)) := by omega
        _ = g * (2 * t + 1) * 2 := by ring
    have ht2 := Nat.eq_of_mul_eq_mul_left hg0 h2
    have ht1' : t = 1 := by omega
    subst ht1'
    have hrel : 2 * f = 1 * g := by omega
    rcases (hZ _ (by omega) (by omega)).mpr (hk (by omega)) with ⟨h, -⟩ | h | ⟨h, -⟩ | h
    · exact absurd (dvd_of_rel (by omega) hrel (e12 ▸ h)) (by decide)
    · exact absurd (dvd_of_rel (by omega) hrel h) (by decide)
    · exact absurd (dvd_of_rel (by omega) hrel (e6 ▸ h)) (by decide)
    · exact absurd (dvd_of_rel (a := 4) (b := 1) (by omega) hrel (by simpa using h)) (by decide)

theorem ordTwistedF4_ne_ordBC_two {f g : ℕ} (hf : 3 ≤ f) (hg : 1 ≤ g) :
    ordTwistedF4 (2 ^ f) ≠ ordBC 2 (2 ^ g) := by
  intro hm
  obtain ⟨hN, hZ⟩ := vsSp4 (profile_ordTwistedF4 (by omega)) hg hm
  have hrel : g = 3 * f := by omega
  have h := (hZ (f * 3) (by omega) (by omega)).mpr ⟨4, by rw [hrel]; ring⟩
  rcases h with ⟨-, h⟩ | h | ⟨-, h⟩ | h
  · exact h ⟨2, by ring⟩
  · have := Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < f) h; omega
  · exact h dvd_rfl
  · have := Nat.le_of_dvd (by omega) h; omega

theorem ordTits_ne_ordTwistedA {u g : ℕ} (hu : 2 ≤ u) (hg : 1 ≤ g) :
    ordTits ≠ ordTwistedA u (2 ^ g) := by
  rw [ordTits_eq]
  refine fun h => (profile_ordTwistedA hu hg).ne_of_ne (by decide) ?_ h.symm
  intro h11
  rcases Nat.lt_or_ge u 5 with hu5 | hu5
  · interval_cases u <;> omega
  · have : 5 * 6 ≤ u * (u + 1) := Nat.mul_le_mul hu5 (by omega)
    have : u * (u + 1) / 2 ≤ g * (u * (u + 1) / 2) := Nat.le_mul_of_pos_left _ (by omega)
    omega

theorem ordTits_ne_ordBC_two {g : ℕ} (hg : 1 ≤ g) : ordTits ≠ ordBC 2 (2 ^ g) := by
  rw [ordTits_eq]
  exact fun h => (profile_ordBC (n := 2) hg).ne_of_ne (by decide) (by omega) h.symm

end Orders

open Orders in
theorem evenOrdersExceptUnitarySp4_ne {m : ℕ} (hm : m ∈ evenOrdersExceptUnitarySp4) :
    (∀ n f : ℕ, 2 ≤ n → 1 ≤ f → m ≠ ordTwistedA n (2 ^ f)) ∧
      (∀ f : ℕ, 1 ≤ f → m ≠ ordBC 2 (2 ^ f)) := by
  rcases hm with ⟨f, hf, h⟩ | hm
  · rcases h with ⟨n, hn, -, rfl⟩ | ⟨n, hn, rfl⟩ | ⟨n, hn, rfl | rfl⟩ | ⟨hf2, rfl⟩ | rfl | rfl |
      rfl | rfl | rfl | rfl | ⟨hodd, h3, rfl | rfl⟩
    · exact ⟨fun u g hu hg => ordA_ne_ordTwistedA hn hf hu hg,
        fun g hg => ordA_ne_ordBC_two hn hf hg⟩
    · exact ⟨fun u g hu hg => ordBC_ne_ordTwistedA hn hf hu hg,
        fun g hg => ordBC_ne_ordBC_two hn hf hg⟩
    · exact ⟨fun u g hu hg => ordD_ne_ordTwistedA hn hf hu hg,
        fun g hg => ordD_ne_ordBC_two hn hf hg⟩
    · exact ⟨fun u g hu hg => ordTwistedD_ne_ordTwistedA hn hf hu hg,
        fun g hg => ordTwistedD_ne_ordBC_two hn hf hg⟩
    · exact ⟨fun u g hu hg => ordG2_ne_ordTwistedA hf2 hu hg,
        fun g hg => ordG2_ne_ordBC_two hf2 hg⟩
    · exact ⟨fun u g hu hg => ordTrialityD4_ne_ordTwistedA hf hu hg,
        fun g hg => ordTrialityD4_ne_ordBC_two hf hg⟩
    · exact ⟨fun u g hu hg => ordF4_ne_ordTwistedA hf hu hg,
        fun g hg => ordF4_ne_ordBC_two hf hg⟩
    · exact ⟨fun u g hu hg => ordE6_ne_ordTwistedA hf hu hg,
        fun g hg => ordE6_ne_ordBC_two hf hg⟩
    · exact ⟨fun u g hu hg => ordTwistedE6_ne_ordTwistedA hf hu hg,
        fun g hg => ordTwistedE6_ne_ordBC_two hf hg⟩
    · exact ⟨fun u g hu hg => ordE7_ne_ordTwistedA hf hu hg,
        fun g hg => ordE7_ne_ordBC_two hf hg⟩
    · exact ⟨fun u g hu hg => ordE8_ne_ordTwistedA hf hu hg,
        fun g hg => ordE8_ne_ordBC_two hf hg⟩
    · exact ⟨fun u g hu hg => ordSuzuki_ne_ordTwistedA hodd h3 hu hg,
        fun g hg => ordSuzuki_ne_ordBC_two hodd hg⟩
    · exact ⟨fun u g hu hg => ordTwistedF4_ne_ordTwistedA hf hu hg,
        fun g hg => ordTwistedF4_ne_ordBC_two h3 hg⟩
  · rw [Set.mem_singleton_iff] at hm
    subst hm
    exact ⟨fun u g hu hg => ordTits_ne_ordTwistedA hu hg, fun g hg => ordTits_ne_ordBC_two hg⟩

theorem evenOrdersExceptUnitarySp4_spec {m : ℕ} (hm : m ∈ evenOrdersExceptUnitarySp4) :
    m ∈ lieOrdersChar 2 ∧ (∀ n f : ℕ, 2 ≤ n → 1 ≤ f → m ≠ ordTwistedA n (2 ^ f)) ∧
      (∀ f : ℕ, 1 ≤ f → m ≠ ordBC 2 (2 ^ f)) :=
  ⟨evenOrdersExceptUnitarySp4_subset hm, evenOrdersExceptUnitarySp4_ne hm⟩

end CFSG.Timmesfeld
