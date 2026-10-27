module

public import CFSG.RankThree.PartOne.K159.AutTits
public import CFSG.RankThree.PartOne.KLR.CoreGroup
public import Certificates.Certificate14978

public section

namespace CFSG.RankThree.PartOne.TCF

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits
open CFSG.RankThree.PartOne.K159 CFSG.RankThree.PartOne.Sec1511
open CFSG.RankThree.PartOne.KLR (exists_conj_mem_of_card_dvd)

section Generic

variable {G : Type*} [Group G]

theorem conj_pair_pow {a b x : G} (hab : a * b = b * a) {i j k l : ℕ}
    (hxa : x * a * x⁻¹ = a ^ i * b ^ j) (hxb : x * b * x⁻¹ = a ^ k * b ^ l) (s t : ℕ) :
    x * (a ^ s * b ^ t) * x⁻¹ = a ^ (i * s + k * t) * b ^ (j * s + l * t) := by
  have hc : Commute a b := hab
  have h2 : x * (a ^ s * b ^ t) * x⁻¹ = (x * a * x⁻¹) ^ s * (x * b * x⁻¹) ^ t := by
    rw [conj_pow, conj_pow]
    group
  rw [h2, hxa, hxb]
  have e1 : (a ^ i * b ^ j) ^ s = a ^ (i * s) * b ^ (j * s) := by
    rw [(Commute.pow_pow hc i j).mul_pow, ← pow_mul, ← pow_mul]
  have e2 : (a ^ k * b ^ l) ^ t = a ^ (k * t) * b ^ (l * t) := by
    rw [(Commute.pow_pow hc k l).mul_pow, ← pow_mul, ← pow_mul]
  rw [e1, e2]
  have hc2 : Commute (b ^ (j * s)) (a ^ (k * t)) := Commute.pow_pow hc.symm _ _
  calc a ^ (i * s) * b ^ (j * s) * (a ^ (k * t) * b ^ (l * t))
      = a ^ (i * s) * (b ^ (j * s) * a ^ (k * t)) * b ^ (l * t) := by simp only [mul_assoc]
    _ = a ^ (i * s) * (a ^ (k * t) * b ^ (j * s)) * b ^ (l * t) := by rw [hc2.eq]
    _ = a ^ (i * s + k * t) * b ^ (j * s + l * t) := by
        rw [pow_add, pow_add]; simp only [mul_assoc]

theorem pair_mul {a b : G} (hab : a * b = b * a) (i j k l : ℕ) :
    (a ^ i * b ^ j) * (a ^ k * b ^ l) = a ^ (i + k) * b ^ (j + l) := by
  have hc2 : Commute (b ^ j) (a ^ k) := Commute.pow_pow (show Commute b a from hab.symm) _ _
  calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by
        simp only [mul_assoc]
    _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [hc2.eq]
    _ = a ^ (i + k) * b ^ (j + l) := by rw [pow_add, pow_add]; simp only [mul_assoc]

theorem exists_orderOf_two_pow {g : G} {k : ℕ} (h : g ^ (2 ^ k) = 1) :
    ∃ j : ℕ, orderOf g = 2 ^ j := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h)
  exact ⟨j, hj⟩

theorem conj_inv_pow (c t : G) (n : ℕ) : (c⁻¹ * t * c) ^ n = c⁻¹ * t ^ n * c := by
  simpa using conj_pow (a := c⁻¹) (b := t) (i := n)

theorem exists_two_part [Finite G] (x : G) :
    ∃ y : G, (∃ k : ℕ, y ^ (2 ^ k) = 1) ∧
      (∀ c : G, Commute (x ^ 2) c → y * c * y⁻¹ = x * c * x⁻¹) ∧
      (∀ c : G, Commute (x ^ 2) c → Commute (y ^ 2) c) := by
  obtain ⟨k, m, hm, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  obtain ⟨r, hr⟩ := hm
  have hxm : x ^ m = x * (x ^ 2) ^ r := by rw [hr, pow_succ', pow_mul]
  refine ⟨x ^ m, ⟨k, ?_⟩, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, ← hN]
    exact pow_orderOf_eq_one x
  · intro c hc
    have h1 : (x ^ 2) ^ r * c * ((x ^ 2) ^ r)⁻¹ = c := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (hc.pow_left r).eq
    calc x ^ m * c * (x ^ m)⁻¹ = x * ((x ^ 2) ^ r * c * ((x ^ 2) ^ r)⁻¹) * x⁻¹ := by
          rw [hxm]; group
      _ = x * c * x⁻¹ := by rw [h1]
  · intro c hc
    have : (x ^ m) ^ 2 = (x ^ 2) ^ m := by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [this]
    exact hc.pow_left m

theorem not_commute_of_conj_inv {y z : G} (hz5 : z ^ 5 = 1) (hz1 : z ≠ 1)
    (hyz : y * z * y⁻¹ = z⁻¹) (hy2 : Commute (y ^ 2) z) : ¬ Commute y (z * y * z⁻¹) := by
  intro hcomm
  have e1 : y * z = z⁻¹ * y := mul_inv_eq_iff_eq_mul.1 hyz
  have lhs : y * (z * y * z⁻¹) = z⁻¹ * y ^ 2 * z⁻¹ := by
    calc y * (z * y * z⁻¹) = (y * z) * y * z⁻¹ := by group
      _ = z⁻¹ * y * y * z⁻¹ := by rw [e1]
      _ = z⁻¹ * y ^ 2 * z⁻¹ := by rw [pow_two]; group
  have rhs : (z * y * z⁻¹) * y = z * y ^ 2 * z := by
    calc (z * y * z⁻¹) * y = z * y * (z⁻¹ * y) := by group
      _ = z * y * (y * z) := by rw [← e1]
      _ = z * y ^ 2 * z := by rw [pow_two]; group
  have hc : z⁻¹ * y ^ 2 * z⁻¹ = z * y ^ 2 * z := by
    rw [← lhs, ← rhs]
    exact hcomm.eq
  have c1 : y ^ 2 * z⁻¹ = z⁻¹ * y ^ 2 := hy2.inv_right.eq
  have c2 : y ^ 2 * z = z * y ^ 2 := hy2.eq
  have h3 : (z⁻¹ * z⁻¹) * y ^ 2 = (z * z) * y ^ 2 := by
    calc (z⁻¹ * z⁻¹) * y ^ 2 = z⁻¹ * (z⁻¹ * y ^ 2) := by group
      _ = z⁻¹ * (y ^ 2 * z⁻¹) := by rw [c1]
      _ = z⁻¹ * y ^ 2 * z⁻¹ := by group
      _ = z * y ^ 2 * z := hc
      _ = z * (y ^ 2 * z) := by group
      _ = z * (z * y ^ 2) := by rw [c2]
      _ = (z * z) * y ^ 2 := by group
  have h4 : z⁻¹ * z⁻¹ = z * z := mul_right_cancel h3
  have h5 : z ^ 4 = 1 := by
    calc z ^ 4 = (z * z) * (z * z) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
      _ = (z⁻¹ * z⁻¹) * (z * z) := by rw [h4]
      _ = 1 := by group
  apply hz1
  calc z = z ^ 5 * (z ^ 4)⁻¹ := by group
    _ = 1 := by rw [hz5, h5]; simp

theorem card_pairSub_eq [Finite G] {p : ℕ} (hp : 0 < p) {a b : G} (ha : a ^ p = 1)
    (hb : b ^ p = 1) (hab : a * b = b * a)
    (hinj : ∀ i j i' j' : ℕ, i < p → j < p → i' < p → j' < p →
      a ^ i * b ^ j = a ^ i' * b ^ j' → i = i' ∧ j = j') :
    Nat.card (pairSub p hp a b ha hb hab) = p ^ 2 := by
  set U := pairSub p hp a b ha hb hab with hU
  apply le_antisymm
  · have hsurj : Function.Surjective
        (fun y : Fin p × Fin p => (⟨a ^ (y.1 : ℕ) * b ^ (y.2 : ℕ), y.1, y.2, rfl⟩ : U)) := by
      rintro ⟨_, i, j, rfl⟩
      refine ⟨(⟨i % p, Nat.mod_lt _ hp⟩, ⟨j % p, Nat.mod_lt _ hp⟩), ?_⟩
      apply Subtype.ext
      show a ^ (i % p) * b ^ (j % p) = a ^ i * b ^ j
      rw [← pow_eq_pow_mod i ha, ← pow_eq_pow_mod j hb]
    have := Nat.card_le_card_of_surjective _ hsurj
    simpa [Nat.card_eq_fintype_card, sq] using this
  · have hinj' : Function.Injective
        (fun y : Fin p × Fin p => (⟨a ^ (y.1 : ℕ) * b ^ (y.2 : ℕ), y.1, y.2, rfl⟩ : U)) := by
      rintro ⟨i, j⟩ ⟨i', j'⟩ h
      have h' := congrArg Subtype.val h
      obtain ⟨e1, e2⟩ := hinj i j i' j' i.2 j.2 i'.2 j'.2 h'
      simp [Fin.ext e1, Fin.ext e2]
    have := Nat.card_le_card_of_injective _ hinj'
    simpa [Nat.card_eq_fintype_card, sq] using this

end Generic

@[expose] def ReflOK (m : ℕ × ℕ × ℕ × ℕ) (s t : ℕ) : Prop :=
  (m.1 * s + m.2.2.1 * t) % 5 = s % 5 ∧ (m.2.1 * s + m.2.2.2 * t) % 5 = t % 5 ∧
  (m.1 * m.1 + m.2.2.1 * m.2.1) % 5 = 1 ∧ (m.2.1 * m.1 + m.2.2.2 * m.2.1) % 5 = 0 ∧
  (m.1 * m.2.2.1 + m.2.2.1 * m.2.2.2) % 5 = 0 ∧ (m.2.1 * m.2.2.1 + m.2.2.2 * m.2.2.2) % 5 = 1 ∧
  ∃ s' < 5, ∃ t' < 5, (s' ≠ 0 ∨ t' ≠ 0) ∧ (m.1 * s' + m.2.2.1 * t' + s') % 5 = 0 ∧
    (m.2.1 * s' + m.2.2.2 * t' + t') % 5 = 0

instance (m : ℕ × ℕ × ℕ × ℕ) (s t : ℕ) : Decidable (ReflOK m s t) := by
  unfold ReflOK; infer_instance

theorem tits_refl_data : ∀ s < 5, ∀ t < 5, (s ≠ 0 ∨ t ≠ 0) →
    ∃ n < 48, ReflOK (titsBigDat n) s t := by
  decide +kernel

section Core

variable {G : Type*} [Group G] [Finite G]

theorem two_pair_core {a b X : G} (ha : a ^ 5 = 1) (hb : b ^ 5 = 1) (hab : a * b = b * a)
    (hinj : ∀ i j i' j' : ℕ, i < 5 → j < 5 → i' < 5 → j' < 5 →
      a ^ i * b ^ j = a ^ i' * b ^ j' → i = i' ∧ j = j')
    {i j k l : ℕ} (hXa : X * a * X⁻¹ = a ^ i * b ^ j) (hXb : X * b * X⁻¹ = a ^ k * b ^ l)
    {s t : ℕ} (hs : s < 5) (ht : t < 5) (hrefl : ReflOK (i, j, k, l) s t) :
    ∃ t₁ t₂ : G, (∃ n : ℕ, t₁ ^ (2 ^ n) = 1) ∧ (∃ n : ℕ, t₂ ^ (2 ^ n) = 1) ∧
      t₁ * (a ^ s * b ^ t) = (a ^ s * b ^ t) * t₁ ∧
      t₂ * (a ^ s * b ^ t) = (a ^ s * b ^ t) * t₂ ∧ t₁ * t₂ ≠ t₂ * t₁ := by
  obtain ⟨hf1, hf2, hm1, hm2, hm3, hm4, s', hs', t', ht', hne', he1, he2⟩ := hrefl
  have hc : Commute a b := hab
  have hX2a : Commute (X ^ 2) a := by
    have h1 : X * (X * a * X⁻¹) * X⁻¹ = a := by
      rw [hXa, conj_pair_pow hab hXa hXb, pow_eq_pow_mod (i * i + k * j) ha,
        pow_eq_pow_mod (j * i + l * j) hb]
      simp only [] at hm1 hm2
      rw [hm1, hm2]
      simp
    have h2 : X ^ 2 * a * (X ^ 2)⁻¹ = a := by
      calc X ^ 2 * a * (X ^ 2)⁻¹ = X * (X * a * X⁻¹) * X⁻¹ := by rw [pow_two]; group
        _ = a := h1
    exact mul_inv_eq_iff_eq_mul.1 h2
  have hX2b : Commute (X ^ 2) b := by
    have h1 : X * (X * b * X⁻¹) * X⁻¹ = b := by
      rw [hXb, conj_pair_pow hab hXa hXb, pow_eq_pow_mod (i * k + k * l) ha,
        pow_eq_pow_mod (j * k + l * l) hb]
      simp only [] at hm3 hm4
      rw [hm3, hm4]
      simp
    have h2 : X ^ 2 * b * (X ^ 2)⁻¹ = b := by
      calc X ^ 2 * b * (X ^ 2)⁻¹ = X * (X * b * X⁻¹) * X⁻¹ := by rw [pow_two]; group
        _ = b := h1
    exact mul_inv_eq_iff_eq_mul.1 h2
  obtain ⟨y, ⟨n, hyn⟩, hyconj, hy2comm⟩ := exists_two_part X
  have hya : y * a * y⁻¹ = a ^ i * b ^ j := (hyconj a hX2a).trans hXa
  have hyb : y * b * y⁻¹ = a ^ k * b ^ l := (hyconj b hX2b).trans hXb
  have hyu : y * (a ^ s * b ^ t) * y⁻¹ = a ^ s * b ^ t := by
    rw [conj_pair_pow hab hya hyb, pow_eq_pow_mod (i * s + k * t) ha,
      pow_eq_pow_mod (j * s + l * t) hb]
    simp only [] at hf1 hf2
    rw [hf1, hf2, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht]
  set z : G := a ^ s' * b ^ t' with hzdef
  have hyz : y * z * y⁻¹ = z⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [hzdef, conj_pair_pow hab hya hyb, pair_mul hab, pow_eq_pow_mod (i * s' + k * t' + s') ha,
      pow_eq_pow_mod (j * s' + l * t' + t') hb]
    simp only [] at he1 he2
    rw [he1, he2]
    simp
  have hz5 : z ^ 5 = 1 := by
    rw [hzdef, (Commute.pow_pow hc s' t').mul_pow, ← pow_mul, ← pow_mul, mul_comm s' 5,
      mul_comm t' 5, pow_mul, pow_mul, ha, hb]
    simp
  have hz1 : z ≠ 1 := by
    intro h
    have h' : a ^ s' * b ^ t' = a ^ 0 * b ^ 0 := by rw [← hzdef, h]; simp
    obtain ⟨e1, e2⟩ := hinj s' t' 0 0 hs' ht' (by norm_num) (by norm_num) h'
    rcases hne' with h1 | h1
    · exact h1 e1
    · exact h1 e2
  have hy2z : Commute (y ^ 2) z :=
    hy2comm z (((hX2a.pow_right s').mul_right (hX2b.pow_right t')))
  have hzu : Commute z (a ^ s * b ^ t) := by
    have A : Commute (a ^ s') (a ^ s * b ^ t) :=
      (Commute.pow_pow_self a s' s).mul_right (Commute.pow_pow hc s' t)
    have B : Commute (b ^ t') (a ^ s * b ^ t) :=
      (Commute.pow_pow hc.symm t' s).mul_right (Commute.pow_pow_self b t' t)
    exact A.mul_left B
  have hyu' : Commute y (a ^ s * b ^ t) := mul_inv_eq_iff_eq_mul.1 hyu
  refine ⟨y, z * y * z⁻¹, ⟨n, hyn⟩, ⟨n, ?_⟩, hyu'.eq, ?_, ?_⟩
  · rw [conj_pow, hyn]
    simp
  · exact ((hzu.mul_left hyu').mul_left hzu.inv_left).eq
  · intro h
    exact not_commute_of_conj_inv hz5 hz1 hyz hy2z h

end Core

section Family

variable {G : Type*} [Group G] [Finite G]

theorem exists_two_pair_of_family (hSyl : 5 ^ (Nat.card G).factorization 5 ∣ 25)
    {a b : G} (ha : a ^ 5 = 1) (hb : b ^ 5 = 1) (hab : a * b = b * a)
    (hinj : ∀ i j i' j' : ℕ, i < 5 → j < 5 → i' < 5 → j' < 5 →
      a ^ i * b ^ j = a ^ i' * b ^ j' → i = i' ∧ j = j')
    (x : ℕ → G) (d : ℕ → ℕ × ℕ × ℕ × ℕ)
    (hxa : ∀ n < 48, x n * a * (x n)⁻¹ = a ^ (d n).1 * b ^ (d n).2.1)
    (hxb : ∀ n < 48, x n * b * (x n)⁻¹ = a ^ (d n).2.2.1 * b ^ (d n).2.2.2)
    (hdat : ∀ s < 5, ∀ t < 5, (s ≠ 0 ∨ t ≠ 0) → ∃ n < 48, ReflOK (d n) s t) :
    ∀ g : G, orderOf g = 5 → ∃ t₁ t₂ : G, (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
      (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * g = g * t₁ ∧ t₂ * g = g * t₂ ∧
      t₁ * t₂ ≠ t₂ * t₁ := by
  intro g hg
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set U : Subgroup G := pairSub 5 (by norm_num) a b ha hb hab with hU
  have hUcard : Nat.card U = 5 ^ 2 := card_pairSub_eq (by norm_num) ha hb hab hinj
  have hdvd : 5 ^ (Nat.card G).factorization 5 ∣ Nat.card U := by
    rw [hUcard]
    exact hSyl
  obtain ⟨c, hc⟩ := exists_conj_mem_of_card_dvd U hdvd hg
  obtain ⟨s₀, t₀, hst⟩ := hc
  have hst' : c * g * c⁻¹ = a ^ (s₀ % 5) * b ^ (t₀ % 5) := by
    rw [hst, ← pow_eq_pow_mod s₀ ha, ← pow_eq_pow_mod t₀ hb]
  have hs5 : s₀ % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have ht5 : t₀ % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hne : s₀ % 5 ≠ 0 ∨ t₀ % 5 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have : c * g * c⁻¹ = 1 := by rw [hst', h1, h2]; simp
    have hg1 : g = 1 := by
      have := congrArg (fun w => c⁻¹ * w * c) this
      simpa [mul_assoc] using this
    rw [hg1, orderOf_one] at hg
    omega
  obtain ⟨n, hn, hrefl⟩ := hdat _ hs5 _ ht5 hne
  have hn' := hxa n hn
  have hn'' := hxb n hn
  obtain ⟨t₁, t₂, ⟨k₁, h₁⟩, ⟨k₂, h₂⟩, hc1, hc2, hnc⟩ :=
    two_pair_core (X := x n) ha hb hab hinj
      (i := (d n).1) (j := (d n).2.1) (k := (d n).2.2.1) (l := (d n).2.2.2) hn' hn'' hs5 ht5
      hrefl
  rw [← hst'] at hc1 hc2
  refine ⟨c⁻¹ * t₁ * c, c⁻¹ * t₂ * c, ?_, ?_, ?_, ?_, ?_⟩
  · exact exists_orderOf_two_pow (k := k₁) (by rw [conj_inv_pow, h₁]; simp)
  · exact exists_orderOf_two_pow (k := k₂) (by rw [conj_inv_pow, h₂]; simp)
  · calc c⁻¹ * t₁ * c * g = c⁻¹ * (t₁ * (c * g * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * g * c⁻¹) * t₁) * c := by rw [hc1]
      _ = g * (c⁻¹ * t₁ * c) := by group
  · calc c⁻¹ * t₂ * c * g = c⁻¹ * (t₂ * (c * g * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * g * c⁻¹) * t₂) * c := by rw [hc2]
      _ = g * (c⁻¹ * t₂ * c) := by group
  · intro h
    apply hnc
    calc t₁ * t₂ = c * ((c⁻¹ * t₁ * c) * (c⁻¹ * t₂ * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * t₂ * c) * (c⁻¹ * t₁ * c)) * c⁻¹ := by rw [h]
      _ = t₂ * t₁ := by group

end Family

theorem five_pow_factorization_titsD :
    5 ^ (Nat.card ↥titsD).factorization 5 ∣ 25 := by
  rw [card_titsD]
  have h : (17971200 : ℕ) = 5 ^ 2 * 718848 := by norm_num
  have hf : (17971200 : ℕ).factorization 5 = 2 := by
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [hf]
  norm_num

theorem tits_two_pair :
    ∀ g : ↥titsD, orderOf g = 5 → ∃ t₁ t₂ : ↥titsD, (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
      (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * g = g * t₁ ∧ t₂ * g = g * t₂ ∧
      t₁ * t₂ ≠ t₂ * t₁ := by
  obtain ⟨hlA, hlB, -, hA5, hB5, hAB, hdist, -, -, -⟩ := Certificates.certificate14973
  obtain ⟨hlen, hnodup, hall⟩ := Certificates.certificate14978
  have rA := rep_wordArr_titsT hlA
  have rB := rep_wordArr_titsT hlB
  set a := wordIn 13 titsT titsAWord with ha_def
  set b := wordIn 13 titsT titsBWord with hb_def
  have hpa : ∀ k, Rep 1755 (powArr titsAArr k) (a ^ k) := rep_powArr rA
  have hpb : ∀ k, Rep 1755 (powArr titsBArr k) (b ^ k) := rep_powArr rB
  have ha5 : a ^ 5 = 1 := eq_of_eqA (hpa 5) rep_idA hA5
  have hb5 : b ^ 5 = 1 := eq_of_eqA (hpb 5) rep_idA hB5
  have hab : a * b = b * a := eq_of_eqA (rep_compA rA rB) (rep_compA rB rA) hAB
  have hinj : ∀ i j i' j' : ℕ, i < 5 → j < 5 → i' < 5 → j' < 5 →
      a ^ i * b ^ j = a ^ i' * b ^ j' → i = i' ∧ j = j' := by
    intro i j i' j' hi hj hi' hj' h
    have h1 := allLt_spec (allLt_spec (allLt_spec (allLt_spec hdist hi) hj) hi') hj'
    have heq : eqA 1755 (pairArr i j) (pairArr i' j') = true :=
      (eqA_iff (rep_compA (hpa i) (hpb j)) (rep_compA (hpa i') (hpb j'))).2 h
    simp only [heq, Bool.not_true, Bool.or_false, Bool.and_eq_true, beq_iff_eq] at h1
    exact h1
  have hfam : ∀ n < 48, (titsBigDat n).1 < 5 ∧ (titsBigDat n).2.1 < 5 ∧
      (titsBigDat n).2.2.1 < 5 ∧ (titsBigDat n).2.2.2 < 5 ∧
      wordIn 13 titsT (titsBigWord n) * a * (wordIn 13 titsT (titsBigWord n))⁻¹ =
        a ^ (titsBigDat n).1 * b ^ (titsBigDat n).2.1 ∧
      wordIn 13 titsT (titsBigWord n) * b * (wordIn 13 titsT (titsBigWord n))⁻¹ =
        a ^ (titsBigDat n).2.2.1 * b ^ (titsBigDat n).2.2.2 := by
    intro n hn
    have h := allLt_spec hall hn
    simp only [titsBigOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hl, h1⟩, h2⟩, h3⟩, h4⟩, hea⟩, heb⟩ := h
    have rx : Rep 1755 (titsBigArr n) (wordIn 13 titsT (titsBigWord n)) :=
      rep_wordArr_titsT hl
    refine ⟨h1, h2, h3, h4, ?_, ?_⟩
    · exact mul_inv_eq_iff_eq_mul.2
        (eq_of_eqA (rep_compA rx rA) (rep_compA (rep_compA (hpa _) (hpb _)) rx) hea)
    · exact mul_inv_eq_iff_eq_mul.2
        (eq_of_eqA (rep_compA rx rB) (rep_compA (rep_compA (hpa _) (hpb _)) rx) heb)
  have haD : a ∈ titsD := wordIn_titsT_mem_titsD titsAWord
  have hbD : b ∈ titsD := wordIn_titsT_mem_titsD titsBWord
  have hxD : ∀ n, wordIn 13 titsT (titsBigWord n) ∈ titsD := fun n =>
    wordIn_titsT_mem_titsD _
  refine exists_two_pair_of_family (G := ↥titsD) five_pow_factorization_titsD
    (a := ⟨a, haD⟩) (b := ⟨b, hbD⟩) (Subtype.ext ?_) (Subtype.ext ?_) (Subtype.ext ?_) ?_
    (fun n => ⟨wordIn 13 titsT (titsBigWord n), hxD n⟩) titsBigDat ?_ ?_ tits_refl_data
  · simpa using ha5
  · simpa using hb5
  · simpa using hab
  · intro i j i' j' hi hj hi' hj' h
    exact hinj i j i' j' hi hj hi' hj' (by simpa using congrArg Subtype.val h)
  · intro n hn
    exact Subtype.ext (by simpa using (hfam n hn).2.2.2.2.1)
  · intro n hn
    exact Subtype.ext (by simpa using (hfam n hn).2.2.2.2.2)

end CFSG.RankThree.PartOne.TCF
