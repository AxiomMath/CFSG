module

public import CFSG.Quasithin.Vol2.GoldschmidtE217L27Odd

public section

namespace CFSG.Quasithin

open E217R4

namespace E217L27

variable {X : Type*} [Group X]

structure Setting (X : Type*) [Group X] (K : Subgroup X) : Prop where
  normal : K.Normal
  l27 : L27c ↥K
  idx : ∀ x y : X, x ∉ K → y ∉ K → x⁻¹ * y ∈ K
  outer : ∃ n : X, n ∉ K

@[expose] def OddOracle (K : Subgroup X) : Prop :=
  ∀ w : X, w ∉ K → w * w = 1 →
    ∃ N : Subgroup ↥K, N ≠ ⊥ ∧ Odd (Nat.card N) ∧
      (∀ n ∈ N, w * (n : X) = (n : X) * w) ∧
      ∀ k : ↥K, w * (k : X) = (k : X) * w → k ∈ Subgroup.normalizer (N : Set ↥K)

variable {K : Subgroup X}

theorem Setting.sq_mem (hS : Setting X K) (x : X) : x * x ∈ K := by
  by_cases hx : x ∈ K
  · exact K.mul_mem hx hx
  · have hxi : x⁻¹ ∉ K := fun h => hx (by simpa using K.inv_mem h)
    simpa using hS.idx x⁻¹ x hxi hx

theorem Setting.conj_mem (hS : Setting X K) {k : X} (hk : k ∈ K) (x : X) : x * k * x⁻¹ ∈ K :=
  haveI := hS.normal
  Subgroup.Normal.conj_mem inferInstance k hk x

theorem not_mem_conj {k : X} (hk : k ∈ K) {x : X} (hx : x ∉ K) : k * x * k⁻¹ ∉ K := by
  intro h
  apply hx
  have := K.mul_mem (K.mul_mem (K.inv_mem hk) h) hk
  simpa [mul_assoc] using this

theorem Setting.cent3 (hS : Setting X K) {a g : X} (ha : a ∈ K) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hg : g ∈ K) (hcomm : g * a = a * g) : ∃ i : ℕ, g = a ^ i := by
  obtain ⟨i, hi⟩ := hS.l27.l27.cent3 ⟨a, ha⟩ (Subtype.ext (by simpa using ha3))
    (fun h => ha1 (congrArg Subtype.val h)) ⟨g, hg⟩ (Subtype.ext hcomm)
  exact ⟨i, by simpa using congrArg Subtype.val hi⟩

theorem Setting.sylow3 (hS : Setting X K) {a a' : X} (ha : a ∈ K) (ha3 : a ^ 3 = 1)
    (ha1 : a ≠ 1) (ha' : a' ∈ K) (ha'3 : a' ^ 3 = 1) (ha'1 : a' ≠ 1) :
    ∃ κ ∈ K, ∃ i : ℕ, κ * a * κ⁻¹ = a' ^ i := by
  obtain ⟨g, i, hg⟩ := hS.l27.l27.sylow3 ⟨a, ha⟩ ⟨a', ha'⟩ (Subtype.ext (by simpa using ha3))
    (fun h => ha1 (congrArg Subtype.val h)) (Subtype.ext (by simpa using ha'3))
    (fun h => ha'1 (congrArg Subtype.val h))
  exact ⟨g, g.2, i, by simpa using congrArg Subtype.val hg⟩

theorem pow_three_cases {z : X} (hz3 : z ^ 3 = 1) (i : ℕ) :
    z ^ i = 1 ∨ z ^ i = z ∨ z ^ i = z⁻¹ := by
  have h : z ^ i = z ^ (i % 3) := by
    conv_lhs => rw [← Nat.mod_add_div i 3, pow_add, pow_mul, hz3, one_pow, mul_one]
  rw [h]
  have : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hi : i % 3
  · left; simp
  · right; left; simp
  · right; right
    have : z ^ 2 * z = 1 := by rw [← pow_succ]; exact hz3
    exact eq_inv_of_mul_eq_one_left this

theorem pow_eq_one_of_two_mul {z : X} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) {j : ℕ}
    (h : z ^ (2 * j) = 1) : z ^ j = 1 := by
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have h3 : 3 ∣ 2 * j := by rw [← hord]; exact orderOf_dvd_of_pow_eq_one h
  have h3' : 3 ∣ j := (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 3 2) h3)
  rw [← hord] at h3'
  exact orderOf_dvd_iff_pow_eq_one.1 h3'

theorem Setting.exists_config (hS : Setting X K) (hOdd : OddOracle K) {v z : X} (hv : v ∈ K)
    (hv2 : v * v = 1) (hv1 : v ≠ 1) (hz : z ∈ K) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hvz : v * z * v⁻¹ = z⁻¹) :
    ∃ c₀ z' : X, c₀ ∉ K ∧ c₀ * c₀ = 1 ∧ c₀ * z = z * c₀ ∧ c₀ * v = v * c₀ ∧
      z' ∈ K ∧ z' ^ 3 = 1 ∧ z' ≠ 1 ∧ (z⁻¹ * v * z) * z' * (z⁻¹ * v * z)⁻¹ = z'⁻¹ ∧
      (z⁻¹ * v * z) * c₀ * z' = z' * ((z⁻¹ * v * z) * c₀) := by
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hvz' : v * z * v = z⁻¹ := by rw [hvi] at hvz; exact hvz
  obtain ⟨n, hn⟩ := hS.outer
  have ha : n * z * n⁻¹ ∈ K := hS.conj_mem hz n
  have ha3 : (n * z * n⁻¹) ^ 3 = 1 := by rw [conj_pow, hz3]; group
  have ha1 : n * z * n⁻¹ ≠ 1 := fun h => hz1 (by simpa using h)
  obtain ⟨κ, hκ, i, hκi⟩ := hS.sylow3 ha ha3 ha1 hz hz3 hz1
  have hn₁ : κ * n ∉ K := fun h => hn (by simpa using K.mul_mem (K.inv_mem hκ) h)
  have hn₁z : (κ * n) * z * (κ * n)⁻¹ = z ^ i := by
    rw [← hκi]; group
  obtain ⟨n₂, hn₂K, hn₂z⟩ : ∃ n₂ : X, n₂ ∉ K ∧ n₂ * z = z * n₂ := by
    rcases pow_three_cases hz3 i with h1 | h2 | h3
    · exfalso
      rw [h1] at hn₁z
      apply hz1
      calc z = (κ * n)⁻¹ * ((κ * n) * z * (κ * n)⁻¹) * (κ * n) := by group
        _ = 1 := by rw [hn₁z]; group
    · refine ⟨κ * n, hn₁, ?_⟩
      rw [h2] at hn₁z
      calc κ * n * z = (κ * n) * z * (κ * n)⁻¹ * (κ * n) := by group
        _ = z * (κ * n) := by rw [hn₁z]
    · refine ⟨κ * n * v, fun h => hn₁ (by simpa using K.mul_mem h (K.inv_mem hv)), ?_⟩
      rw [h3] at hn₁z
      have e1 : (κ * n) * z⁻¹ * (κ * n)⁻¹ = z := by
        have := congrArg (·⁻¹) hn₁z
        simpa [mul_assoc] using this
      have hvzv : (v * z * v) * v = v * z := by rw [mul_assoc (v * z) v v, hv2, mul_one]
      calc κ * n * v * z = κ * n * (v * z) := by group
        _ = κ * n * ((v * z * v) * v) := by rw [hvzv]
        _ = κ * n * z⁻¹ * v := by rw [hvz']; group
        _ = ((κ * n) * z⁻¹ * (κ * n)⁻¹) * (κ * n) * v := by group
        _ = z * (κ * n * v) := by rw [e1]; group
  obtain ⟨j, hj⟩ := hS.cent3 hz hz3 hz1 (hS.sq_mem n₂)
    (by rw [mul_assoc, hn₂z, ← mul_assoc, hn₂z, mul_assoc])
  have hc₀z : n₂ ^ 3 * z = z * n₂ ^ 3 := (Commute.pow_left hn₂z 3).eq
  have hc₀K : n₂ ^ 3 ∉ K := by
    intro h
    apply hn₂K
    have h2 : n₂ ^ 3 * (n₂ * n₂)⁻¹ ∈ K := K.mul_mem h (K.inv_mem (hS.sq_mem n₂))
    simpa [pow_succ, mul_assoc] using h2
  have hc₀2 : n₂ ^ 3 * n₂ ^ 3 = 1 := by
    have e : n₂ ^ 3 * n₂ ^ 3 = (n₂ ^ 2) ^ 3 := by rw [← pow_add, ← pow_mul]
    have hj' : n₂ ^ 2 = z ^ j := by rw [pow_two]; exact hj
    rw [e, hj', ← pow_mul, mul_comm, pow_mul, hz3, one_pow]
  set c₀ := n₂ ^ 3 with hc₀def
  have hc₀zi : c₀ * z⁻¹ = z⁻¹ * c₀ := by
    have := congrArg (fun t => z⁻¹ * t * z⁻¹) hc₀z
    simp only [mul_assoc, inv_mul_cancel_left] at this
    simpa [mul_assoc] using this.symm
  have hc₀v : c₀ * v = v * c₀ := by
    have hvzi : v⁻¹ * z * v = z⁻¹ := by rw [hvi]; exact hvz'
    have hc₁z : (v * c₀ * v⁻¹) * z = z * (v * c₀ * v⁻¹) := by
      have e1 : v * z⁻¹ * v⁻¹ = z := by
        have := congrArg (·⁻¹) hvz
        simpa [mul_assoc] using this
      calc (v * c₀ * v⁻¹) * z = v * c₀ * (v⁻¹ * z * v) * v⁻¹ := by group
        _ = v * c₀ * z⁻¹ * v⁻¹ := by rw [hvzi]
        _ = v * (z⁻¹ * c₀) * v⁻¹ := by rw [mul_assoc v c₀, hc₀zi, ← mul_assoc]
        _ = (v * z⁻¹ * v⁻¹) * (v * c₀ * v⁻¹) := by group
        _ = z * (v * c₀ * v⁻¹) := by rw [e1]
    have hc₁K : v * c₀ * v⁻¹ ∉ K := not_mem_conj hv hc₀K
    have hmem : c₀⁻¹ * (v * c₀ * v⁻¹) ∈ K := hS.idx c₀ _ hc₀K hc₁K
    obtain ⟨k, hk⟩ := hS.cent3 hz hz3 hz1 hmem (by
      have hz' : c₀⁻¹ * z = z * c₀⁻¹ := by
        have := congrArg (fun t => c₀⁻¹ * t * c₀⁻¹) hc₀z
        simp only [mul_assoc, inv_mul_cancel_left] at this
        simpa [mul_assoc] using this.symm
      calc c₀⁻¹ * (v * c₀ * v⁻¹) * z = c₀⁻¹ * ((v * c₀ * v⁻¹) * z) := by group
        _ = c₀⁻¹ * (z * (v * c₀ * v⁻¹)) := by rw [hc₁z]
        _ = (c₀⁻¹ * z) * (v * c₀ * v⁻¹) := by group
        _ = z * c₀⁻¹ * (v * c₀ * v⁻¹) := by rw [hz']
        _ = z * (c₀⁻¹ * (v * c₀ * v⁻¹)) := by group)
    have hc₁eq : v * c₀ * v⁻¹ = c₀ * z ^ k := by
      calc v * c₀ * v⁻¹ = c₀ * (c₀⁻¹ * (v * c₀ * v⁻¹)) := by group
        _ = c₀ * z ^ k := by rw [hk]
    have hc₁2 : (v * c₀ * v⁻¹) * (v * c₀ * v⁻¹) = 1 := by
      calc (v * c₀ * v⁻¹) * (v * c₀ * v⁻¹) = v * (c₀ * c₀) * v⁻¹ := by group
        _ = 1 := by rw [hc₀2]; group
    have hzk : z ^ (2 * k) = 1 := by
      have hcz : c₀ * z ^ k = z ^ k * c₀ := (Commute.pow_right hc₀z.symm.symm k).eq
      have : (c₀ * z ^ k) * (c₀ * z ^ k) = z ^ (2 * k) := by
        calc (c₀ * z ^ k) * (c₀ * z ^ k) = c₀ * (z ^ k * c₀) * z ^ k := by group
          _ = c₀ * (c₀ * z ^ k) * z ^ k := by rw [← hcz]
          _ = (c₀ * c₀) * (z ^ k * z ^ k) := by group
          _ = z ^ (2 * k) := by rw [hc₀2, one_mul, ← pow_add, two_mul]
      rw [← this, ← hc₁eq]
      exact hc₁2
    have hzk1 : z ^ k = 1 := pow_eq_one_of_two_mul hz3 hz1 hzk
    rw [hzk1, mul_one] at hc₁eq
    calc c₀ * v = (v * c₀ * v⁻¹) * v := by rw [hc₁eq]
      _ = v * c₀ := by group
  have hcK : z⁻¹ * v * z ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hz) hv) hz
  have hc2 : (z⁻¹ * v * z) * (z⁻¹ * v * z) = 1 := by
    calc (z⁻¹ * v * z) * (z⁻¹ * v * z) = z⁻¹ * (v * v) * z := by group
      _ = 1 := by rw [hv2]; group
  have hc1 : z⁻¹ * v * z ≠ 1 := by
    intro h
    apply hv1
    calc v = z * (z⁻¹ * v * z) * z⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hc₀c : c₀ * (z⁻¹ * v * z) = (z⁻¹ * v * z) * c₀ := by
    calc c₀ * (z⁻¹ * v * z) = (c₀ * z⁻¹) * v * z := by group
      _ = z⁻¹ * (c₀ * v) * z := by rw [hc₀zi]; group
      _ = z⁻¹ * (v * c₀) * z := by rw [hc₀v]
      _ = z⁻¹ * v * (c₀ * z) := by group
      _ = z⁻¹ * v * (z * c₀) := by rw [hc₀z]
      _ = (z⁻¹ * v * z) * c₀ := by group
  have hwK : (z⁻¹ * v * z) * c₀ ∉ K := by
    intro h
    apply hc₀K
    have := K.mul_mem (K.inv_mem hcK) h
    simpa [mul_assoc] using this
  have hw2 : ((z⁻¹ * v * z) * c₀) * ((z⁻¹ * v * z) * c₀) = 1 := by
    calc ((z⁻¹ * v * z) * c₀) * ((z⁻¹ * v * z) * c₀)
        = (z⁻¹ * v * z) * (c₀ * (z⁻¹ * v * z)) * c₀ := by group
      _ = (z⁻¹ * v * z) * ((z⁻¹ * v * z) * c₀) * c₀ := by rw [hc₀c]
      _ = ((z⁻¹ * v * z) * (z⁻¹ * v * z)) * (c₀ * c₀) := by group
      _ = 1 := by rw [hc2, hc₀2, one_mul]
  obtain ⟨N, hN1, hNodd, hNcent, hNnorm⟩ := hOdd _ hwK hw2
  set cK : ↥K := ⟨z⁻¹ * v * z, hcK⟩ with hcKdef
  have hy2 : cK * cK = 1 := Subtype.ext hc2
  have hy1 : cK ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hcw : ((z⁻¹ * v * z) * c₀) * (z⁻¹ * v * z) = (z⁻¹ * v * z) * ((z⁻¹ * v * z) * c₀) := by
    calc ((z⁻¹ * v * z) * c₀) * (z⁻¹ * v * z) = (z⁻¹ * v * z) * (c₀ * (z⁻¹ * v * z)) := by group
      _ = (z⁻¹ * v * z) * ((z⁻¹ * v * z) * c₀) := by rw [hc₀c]
  have hyN : cK ∈ Subgroup.normalizer (N : Set ↥K) := hNnorm cK hcw
  obtain ⟨a, haN, ha3, ha1, hya⟩ := exists_inv_three hS.l27 hN1 hNodd hy2 hy1 hyN
  refine ⟨c₀, (a : X), hc₀K, hc₀2, hc₀z, hc₀v, a.2, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg Subtype.val ha3
  · exact fun h => ha1 (Subtype.ext h)
  · exact congrArg Subtype.val hya
  · exact hNcent a haN

theorem Setting.exists_conj_of_inv (hS : Setting X K) {v z : X} (hv : v ∈ K)
    (hv2 : v * v = 1) (hz : z ∈ K) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hvz : v * z * v⁻¹ = z⁻¹) {u ζ : X} (hu : u ∈ K) (hζ : ζ ∈ K) (hζ3 : ζ ^ 3 = 1)
    (hζ1 : ζ ≠ 1) (huζ : u * ζ * u⁻¹ = ζ⁻¹) :
    ∃ κ ∈ K, ∃ m : ℕ, κ * u * κ⁻¹ = z ^ m * v * (z ^ m)⁻¹ ∧
      (κ * ζ * κ⁻¹ = z ∨ κ * ζ * κ⁻¹ = z⁻¹) := by
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  obtain ⟨κ, hκ, i, hκi⟩ := hS.sylow3 hζ hζ3 hζ1 hz hz3 hz1
  have hκu : κ * u * κ⁻¹ ∈ K := K.mul_mem (K.mul_mem hκ hu) (K.inv_mem hκ)
  have hinv : (κ * u * κ⁻¹) * (z ^ i) * (κ * u * κ⁻¹)⁻¹ = (z ^ i)⁻¹ := by
    rw [← hκi]
    calc κ * u * κ⁻¹ * (κ * ζ * κ⁻¹) * (κ * u * κ⁻¹)⁻¹ = κ * (u * ζ * u⁻¹) * κ⁻¹ := by group
      _ = (κ * ζ * κ⁻¹)⁻¹ := by rw [huζ]; group
  have hz_inv : (κ * u * κ⁻¹) * z * (κ * u * κ⁻¹)⁻¹ = z⁻¹ := by
    rcases pow_three_cases hz3 i with h1 | h2 | h3
    · exfalso
      rw [h1] at hκi
      apply hζ1
      calc ζ = κ⁻¹ * (κ * ζ * κ⁻¹) * κ := by group
        _ = 1 := by rw [hκi]; group
    · rw [h2] at hinv; exact hinv
    · rw [h3] at hinv
      have := congrArg (·⁻¹) hinv
      simpa [mul_assoc] using this
  have hcomm : (v * (κ * u * κ⁻¹)) * z = z * (v * (κ * u * κ⁻¹)) := by
    have e1 : (κ * u * κ⁻¹) * z = z⁻¹ * (κ * u * κ⁻¹) := by
      calc (κ * u * κ⁻¹) * z = ((κ * u * κ⁻¹) * z * (κ * u * κ⁻¹)⁻¹) * (κ * u * κ⁻¹) := by group
        _ = z⁻¹ * (κ * u * κ⁻¹) := by rw [hz_inv]
    have e2 : v * z⁻¹ = z * v := by
      calc v * z⁻¹ = (v * z⁻¹ * v⁻¹) * v := by group
        _ = z * v := by
          have := congrArg (·⁻¹) hvz
          simp only [mul_inv_rev, inv_inv] at this
          rw [show v * z⁻¹ * v⁻¹ = z by
            simpa [mul_assoc] using congrArg (·⁻¹) hvz]
    calc (v * (κ * u * κ⁻¹)) * z = v * ((κ * u * κ⁻¹) * z) := by group
      _ = v * (z⁻¹ * (κ * u * κ⁻¹)) := by rw [e1]
      _ = (v * z⁻¹) * (κ * u * κ⁻¹) := by group
      _ = z * (v * (κ * u * κ⁻¹)) := by rw [e2]; group
  obtain ⟨m, hm⟩ := hS.cent3 hz hz3 hz1 (K.mul_mem hv hκu) hcomm
  refine ⟨κ, hκ, m, ?_, ?_⟩
  ·
    have hu' : κ * u * κ⁻¹ = v * z ^ m := by
      calc κ * u * κ⁻¹ = v⁻¹ * (v * (κ * u * κ⁻¹)) := by group
        _ = v * z ^ m := by rw [hm, hvi]
    have hvm : v * z ^ m * v⁻¹ = (z ^ m)⁻¹ := by rw [← conj_pow, hvz, inv_pow]
    have h3m : (z ^ m) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hz3, one_pow]
    have hzm : z ^ m * z ^ m = (z ^ m)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      calc z ^ m * z ^ m * z ^ m = (z ^ m) ^ 3 := by group
        _ = 1 := h3m
    rw [hu']
    calc v * z ^ m = ((v * z ^ m * v⁻¹)) * v := by group
      _ = (z ^ m)⁻¹ * v := by rw [hvm]
      _ = (z ^ m * z ^ m) * v := by rw [hzm]
      _ = z ^ m * (v * (z ^ m)⁻¹ * v⁻¹) * v := by
          have : v * (z ^ m)⁻¹ * v⁻¹ = z ^ m := by
            have := congrArg (·⁻¹) hvm
            simpa [mul_assoc] using this
          rw [this]
      _ = z ^ m * v * (z ^ m)⁻¹ := by group
  · rcases pow_three_cases hz3 i with h1 | h2 | h3
    · exfalso
      rw [h1] at hκi
      apply hζ1
      calc ζ = κ⁻¹ * (κ * ζ * κ⁻¹) * κ := by group
        _ = 1 := by rw [hκi]; group
    · left; rw [hκi, h2]
    · right; rw [hκi, h3]

theorem Setting.exists_conj_of_inv' (hS : Setting X K) {v z : X} (hv : v ∈ K)
    (hv2 : v * v = 1) (hz : z ∈ K) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hvz : v * z * v⁻¹ = z⁻¹) {u ζ : X} (hu : u ∈ K) (hζ : ζ ∈ K) (hζ3 : ζ ^ 3 = 1)
    (hζ1 : ζ ≠ 1) (huζ : u * ζ * u⁻¹ = ζ⁻¹) :
    ∃ κ ∈ K, κ * u * κ⁻¹ = v ∧ (κ * ζ * κ⁻¹ = z ∨ κ * ζ * κ⁻¹ = z⁻¹) := by
  obtain ⟨κ, hκ, m, hm1, hm2⟩ := hS.exists_conj_of_inv hv hv2 hz hz3 hz1 hvz hu hζ hζ3 hζ1 huζ
  refine ⟨(z ^ m)⁻¹ * κ, K.mul_mem (K.inv_mem (K.pow_mem hz m)) hκ, ?_, ?_⟩
  · calc (z ^ m)⁻¹ * κ * u * ((z ^ m)⁻¹ * κ)⁻¹ = (z ^ m)⁻¹ * (κ * u * κ⁻¹) * z ^ m := by group
      _ = v := by rw [hm1]; group
  · have e : (z ^ m)⁻¹ * κ * ζ * ((z ^ m)⁻¹ * κ)⁻¹ = (z ^ m)⁻¹ * (κ * ζ * κ⁻¹) * z ^ m := by
      group
    rw [e]
    rcases hm2 with h | h
    · left
      rw [h]
      group
    · right
      rw [h]
      group

end E217L27

end CFSG.Quasithin
