module

public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.Quasithin.H13.A6

open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def conjEndOf (X : Subgroup G) {s : G} (hs : s ∈ Subgroup.normalizer (X : Set G)) :
    ↥X →* ↥X where
  toFun a := ⟨s * a * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs a).mp a.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

theorem conjEndOf_coe (X : Subgroup G) {s : G} (hs : s ∈ Subgroup.normalizer (X : Set G))
    (a : ↥X) : ((conjEndOf X hs a : ↥X) : G) = s * a * s⁻¹ := rfl

section Quot

variable {X O : Subgroup G}

theorem subgroupOf_normal_of (hXO : X ≤ Subgroup.normalizer (O : Set G)) :
    (O.subgroupOf X).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hXO g.2) n).mp hn⟩

theorem conj_mod_trivial_of_two_pow (hXO : X ≤ Subgroup.normalizer (O : Set G))
    {Zc : Subgroup G} (hZX : Zc ≤ X)
    (hZ3 : ∀ z ∈ Zc, z ^ 3 ∈ O) {s : G} (hsX : s ∈ Subgroup.normalizer (X : Set G))
    (hsO : s ∈ Subgroup.normalizer (O : Set G)) (hsZ : ∀ z ∈ Zc, s * z * s⁻¹ * z⁻¹ ∈ O)
    {m : ℕ} (hs2 : s ^ 2 ^ m = 1)
    (hd : ∀ a ∈ X, ∃ z ∈ Zc, (s * a * s⁻¹ * a⁻¹) * z⁻¹ ∈ O) :
    ∀ a ∈ X, s * a * s⁻¹ * a⁻¹ ∈ O := by
  have := subgroupOf_normal_of hXO
  set N := O.subgroupOf X with hN
  set E := ↥X ⧸ N
  let mk : ↥X →* E := QuotientGroup.mk' N
  have hmk : ∀ a b : ↥X, mk a = mk b ↔ (a : G)⁻¹ * b ∈ O := by
    intro a b
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simp
  have hmk1 : ∀ a : ↥X, mk a = 1 ↔ (a : G) ∈ O := by
    intro a
    rw [show (1 : E) = mk 1 from (map_one mk).symm, hmk]
    simp
  have hle : N ≤ N.comap (conjEndOf X hsX) := by
    intro n hn
    rw [Subgroup.mem_comap, hN, Subgroup.mem_subgroupOf, conjEndOf_coe]
    exact (Subgroup.mem_normalizer_iff.mp hsO n).mp hn
  let φ : E →* E := QuotientGroup.map N N (conjEndOf X hsX) hle
  have hφ : ∀ a : ↥X, φ (mk a) = mk (conjEndOf X hsX a) := fun a => rfl
  have hiter : ∀ n : ℕ, ∀ a : ↥X, (⇑φ)^[n] (mk a) =
      mk ⟨s ^ n * a * (s ^ n)⁻¹, (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hsX n) a).mp
        a.2⟩ := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply', ih, hφ]
      congr 1
      ext
      simp only [conjEndOf_coe]
      rw [pow_succ']
      group
  intro a ha
  obtain ⟨z, hz, hdz⟩ := hd a ha
  have hzE : φ (mk ⟨z, hZX hz⟩) = mk ⟨z, hZX hz⟩ := by
    rw [hφ, hmk]
    have hc := hsZ z hz
    simp only [conjEndOf_coe]
    have hw : s * z * s⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hsX z).mp (hZX hz)
    have e : (s * z * s⁻¹)⁻¹ * z = (s * z * s⁻¹)⁻¹ * (s * z * s⁻¹ * z⁻¹)⁻¹ * (s * z * s⁻¹)⁻¹⁻¹ :=
      by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hXO (X.inv_mem hw)) _).mp (O.inv_mem hc)
  have hstep : φ (mk ⟨a, ha⟩) = mk ⟨z, hZX hz⟩ * mk ⟨a, ha⟩ := by
    rw [hφ, ← map_mul, hmk]
    simp only [conjEndOf_coe, Subgroup.coe_mul]
    have e : (s * a * s⁻¹)⁻¹ * (z * a) = s * a⁻¹ * s⁻¹ * (s * a * s⁻¹ * a⁻¹ * z⁻¹)⁻¹ *
        (s * a⁻¹ * s⁻¹)⁻¹ := by group
    rw [e]
    have hsa : s * a⁻¹ * s⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hsX _).mp (X.inv_mem ha)
    exact (Subgroup.mem_normalizer_iff.mp (hXO hsa) _).mp (O.inv_mem hdz)
  have hpow : ∀ n : ℕ, (⇑φ)^[n] (mk ⟨a, ha⟩) = mk ⟨z, hZX hz⟩ ^ n * mk ⟨a, ha⟩ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, map_pow, hzE, hstep, pow_succ]
      group
  have h2 : mk ⟨z, hZX hz⟩ ^ 2 ^ m = 1 := by
    have h := hpow (2 ^ m)
    rw [hiter] at h
    have e : (⟨s ^ 2 ^ m * a * (s ^ 2 ^ m)⁻¹, (Subgroup.mem_normalizer_iff.mp
        (Subgroup.pow_mem _ hsX (2 ^ m)) a).mp ha⟩ : ↥X) = ⟨a, ha⟩ := by
      ext; simp [hs2]
    rw [e] at h
    exact (mul_eq_right.mp h.symm)
  have h3 : mk ⟨z, hZX hz⟩ ^ 3 = 1 := by
    rw [← map_pow, hmk1]
    exact hZ3 z hz
  have hz1 : mk ⟨z, hZX hz⟩ = 1 := by
    have hcop : Nat.Coprime (2 ^ m) 3 := Nat.Coprime.pow_left _ (by decide)
    have h := orderOf_dvd_of_pow_eq_one h2
    have h' := orderOf_dvd_of_pow_eq_one h3
    have h1 : orderOf (mk ⟨z, hZX hz⟩) ∣ 1 := by
      have := Nat.dvd_gcd h h'
      rwa [hcop.gcd_eq_one] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  have hsa : s * a * s⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hsX a).mp ha
  have hfix : mk ⟨s * a * s⁻¹, hsa⟩ = mk ⟨a, ha⟩ := by
    have := hstep
    rw [hz1, one_mul] at this
    exact this
  rw [hmk] at hfix
  simp only at hfix
  have e : s * a * s⁻¹ * a⁻¹ = (s * a * s⁻¹) * ((s * a * s⁻¹)⁻¹ * a)⁻¹ * (s * a * s⁻¹)⁻¹ := by
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hXO hsa) _).mp (O.inv_mem hfix)

theorem commutator_inf_le_of_acts (hXO : X ≤ Subgroup.normalizer (O : Set G))
    {Zc S : Subgroup G} {t : G}
    (hab : ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ O) (h3 : ∀ a ∈ X, a ^ 3 ∈ O)
    (hSX : S ≤ Subgroup.normalizer (X : Set G)) (hSO : S ≤ Subgroup.normalizer (O : Set G))
    (ht : t ∈ S)
    (hact : ∀ s ∈ S, (∀ a ∈ X, s * a * s⁻¹ * a⁻¹ ∈ O) ∨
      (∀ a ∈ X, (s * a * s⁻¹) * (t * a * t⁻¹)⁻¹ ∈ O))
    (ht2 : ∀ a ∈ X, (t * t) * a * (t * t)⁻¹ * a⁻¹ ∈ O)
    (htZ : ∀ z ∈ Zc, t * z * t⁻¹ * z⁻¹ ∈ O) :
    ⁅X, S⁆ ⊓ Zc ≤ O := by
  have := subgroupOf_normal_of hXO
  set N := O.subgroupOf X with hN
  set E := ↥X ⧸ N
  let mk : ↥X →* E := QuotientGroup.mk' N
  have hmk : ∀ a b : ↥X, mk a = mk b ↔ (a : G)⁻¹ * b ∈ O := by
    intro a b
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simp
  have hmk1 : ∀ a : ↥X, mk a = 1 ↔ (a : G) ∈ O := by
    intro a
    rw [show (1 : E) = mk 1 from (map_one mk).symm, hmk]
    simp
  have hcomm : ∀ e₁ e₂ : E, e₁ * e₂ = e₂ * e₁ := by
    intro e₁ e₂
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N e₁
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N e₂
    rw [← map_mul, ← map_mul, hmk]
    simp only [Subgroup.coe_mul]
    have h := hab _ (X.inv_mem b.2) _ (X.inv_mem a.2)
    have e2 : ((a : G) * b)⁻¹ * (b * a) = (b : G)⁻¹ * (a : G)⁻¹ * (b : G)⁻¹⁻¹ * (a : G)⁻¹⁻¹ :=
      by group
    rw [e2]
    exact h
  have htX := hSX ht
  have htO := hSO ht
  let ct := conjEndOf X htX
  let χ : ↥X →* E :=
    { toFun := fun a => mk a * mk (ct a)
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul]
        calc mk a * mk b * (mk (ct a) * mk (ct b)) = mk a * (mk b * mk (ct a)) * mk (ct b) := by
              group
          _ = mk a * (mk (ct a) * mk b) * mk (ct b) := by rw [hcomm (mk b)]
          _ = mk a * mk (ct a) * (mk b * mk (ct b)) := by group }
  have hχ : ∀ a : ↥X, χ a = mk a * mk (ct a) := fun a => rfl
  have hct : ∀ a b : ↥X, mk a = mk b → mk (ct a) = mk (ct b) := by
    intro a b h
    rw [hmk] at h ⊢
    simp only [conjEndOf_coe, ct]
    have e : (t * a * t⁻¹)⁻¹ * (t * b * t⁻¹) = t * ((a : G)⁻¹ * b) * t⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp htO _).mp h
  have hχt : ∀ a : ↥X, χ (ct a) = χ a := by
    intro a
    have h2 : mk (ct (ct a)) = mk a := by
      rw [hmk]
      simp only [conjEndOf_coe, ct]
      have e : (t * (t * (a : G) * t⁻¹) * t⁻¹)⁻¹ * a =
          (t * t) * (a : G)⁻¹ * (t * t)⁻¹ * ((a : G)⁻¹)⁻¹ := by
        simp only [mul_inv_rev, inv_inv, mul_assoc]
      rw [e]
      exact ht2 _ (X.inv_mem a.2)
    rw [hχ, hχ, h2, hcomm]
  have hgen : ∀ a ∈ X, ∀ s ∈ S, ⁅a, s⁆ ∈ X ∧ ∀ h : ⁅a, s⁆ ∈ X, χ ⟨⁅a, s⁆, h⟩ = 1 := by
    intro a ha s hs
    have hsX := hSX hs
    have hsa : s * a⁻¹ * s⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hsX _).mp (X.inv_mem ha)
    have hmem : ⁅a, s⁆ ∈ X := by
      rw [commutatorElement_def]
      have e : a * s * a⁻¹ * s⁻¹ = a * (s * a⁻¹ * s⁻¹) := by group
      rw [e]
      exact X.mul_mem ha hsa
    refine ⟨hmem, fun h => ?_⟩
    have hsa' : s * a * s⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hsX _).mp ha
    have e : (⟨⁅a, s⁆, h⟩ : ↥X) = ⟨a, ha⟩ * (⟨s * a * s⁻¹, hsa'⟩)⁻¹ := by
      ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e, map_mul, map_inv, mul_inv_eq_one]
    rcases hact s hs with h1 | h1
    · have hmk' : mk ⟨s * a * s⁻¹, hsa'⟩ = mk ⟨a, ha⟩ := by
        rw [hmk]
        simp only
        have e : (s * a * s⁻¹)⁻¹ * a = s * a⁻¹ * s⁻¹ * (a⁻¹)⁻¹ := by group
        rw [e]
        exact h1 _ (X.inv_mem ha)
      rw [hχ, hχ, hmk', hct _ _ hmk']
    · have hmk' : mk ⟨s * a * s⁻¹, hsa'⟩ = mk (ct ⟨a, ha⟩) := by
        rw [hmk]
        simp only [conjEndOf_coe, ct]
        have e : (s * a * s⁻¹)⁻¹ * (t * a * t⁻¹) =
            (s * a * s⁻¹)⁻¹ * ((s * a * s⁻¹) * (t * a * t⁻¹)⁻¹)⁻¹ * (s * a * s⁻¹)⁻¹⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hXO (X.inv_mem hsa')) _).mp (O.inv_mem (h1 a ha))
      rw [hχ (⟨s * a * s⁻¹, hsa'⟩), hmk', hct _ _ hmk', ← hχ, hχt]
  have hle : ⁅X, S⁆ ≤ χ.ker.map X.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha s hs
    obtain ⟨hmem, hχ1⟩ := hgen a ha s hs
    exact ⟨⟨_, hmem⟩, hχ1 hmem, rfl⟩
  rintro y ⟨hyK, hyZ⟩
  obtain ⟨y', hy', rfl⟩ := hle hyK
  have hχy : χ y' = 1 := hy'
  have hty : mk (ct y') = mk y' := by
    rw [hmk]
    simp only [conjEndOf_coe, ct]
    have hc := htZ _ hyZ
    have hw : (t * y' * t⁻¹ : G) ∈ X := (conjEndOf X htX y').2
    have e : (t * y' * t⁻¹)⁻¹ * y' = (t * y' * t⁻¹)⁻¹ * (t * y' * t⁻¹ * (y' : G)⁻¹)⁻¹ *
        (t * y' * t⁻¹)⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hXO (X.inv_mem hw)) _).mp (O.inv_mem hc)
  rw [hχ, hty] at hχy
  have h2 : mk y' ^ 2 = 1 := by rw [sq]; exact hχy
  have h3' : mk y' ^ 3 = 1 := by rw [← map_pow, hmk1]; simpa using h3 _ y'.2
  have h1 : mk y' = 1 := by
    have e : mk y' = mk y' ^ 3 * (mk y' ^ 2)⁻¹ := by group
    rw [e, h2, h3', inv_one, mul_one]
  exact (hmk1 y').mp h1

theorem comm_mod_of_gen (hXO : X ≤ Subgroup.normalizer (O : Set G)) {N : Subgroup G} {c : G}
    (hNX : N ≤ X) (hcX : c ∈ X) (hN : ∀ n ∈ N, ∀ a ∈ X, n * a * n⁻¹ * a⁻¹ ∈ O)
    (hgen : ∀ a ∈ X, a ∈ N ∨ a * c⁻¹ ∈ N ∨ a * c ∈ N) :
    ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ O := by
  have := subgroupOf_normal_of hXO
  set E := ↥X ⧸ O.subgroupOf X
  let mk : ↥X →* E := QuotientGroup.mk' _
  have hmk1 : ∀ a : ↥X, mk a = 1 ↔ (a : G) ∈ O := by
    intro a
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcent : ∀ n (hn : n ∈ N), ∀ e : E, mk ⟨n, hNX hn⟩ * e = e * mk ⟨n, hNX hn⟩ := by
    intro n hn e
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ e
    have h : mk (⟨n, hNX hn⟩ * a * (⟨n, hNX hn⟩)⁻¹ * a⁻¹) = 1 := by
      rw [hmk1]
      exact hN n hn a a.2
    simp only [map_mul, map_inv] at h
    calc mk ⟨n, hNX hn⟩ * mk a = (mk ⟨n, hNX hn⟩ * mk a * (mk ⟨n, hNX hn⟩)⁻¹ * (mk a)⁻¹) *
          (mk a * mk ⟨n, hNX hn⟩) := by group
      _ = mk a * mk ⟨n, hNX hn⟩ := by rw [h, one_mul]
  have hform : ∀ a (ha : a ∈ X), ∃ n, ∃ hn : n ∈ N, ∃ i : ℤ,
      mk ⟨a, ha⟩ = mk ⟨n, hNX hn⟩ * mk ⟨c, hcX⟩ ^ i := by
    intro a ha
    rcases hgen a ha with h | h | h
    · exact ⟨a, h, 0, by simp⟩
    · refine ⟨_, h, 1, ?_⟩
      rw [zpow_one, ← map_mul]
      congr 1
      ext
      simp
    · refine ⟨_, h, -1, ?_⟩
      rw [zpow_neg, zpow_one, ← map_inv, ← map_mul]
      congr 1
      ext
      simp
  intro a ha b hb
  obtain ⟨n, hn, i, hi⟩ := hform a ha
  obtain ⟨n', hn', j, hj⟩ := hform b hb
  have hab : mk ⟨a, ha⟩ * mk ⟨b, hb⟩ = mk ⟨b, hb⟩ * mk ⟨a, ha⟩ := by
    rw [hi, hj]
    have h1 := hcent n hn
    have h2 := hcent n' hn'
    calc mk ⟨n, hNX hn⟩ * mk ⟨c, hcX⟩ ^ i * (mk ⟨n', hNX hn'⟩ * mk ⟨c, hcX⟩ ^ j)
        = mk ⟨n, hNX hn⟩ * (mk ⟨c, hcX⟩ ^ i * mk ⟨n', hNX hn'⟩) * mk ⟨c, hcX⟩ ^ j := by group
      _ = mk ⟨n, hNX hn⟩ * (mk ⟨n', hNX hn'⟩ * mk ⟨c, hcX⟩ ^ i) * mk ⟨c, hcX⟩ ^ j := by
          rw [h2 (mk ⟨c, hcX⟩ ^ i)]
      _ = (mk ⟨n, hNX hn⟩ * mk ⟨n', hNX hn'⟩) * (mk ⟨c, hcX⟩ ^ i * mk ⟨c, hcX⟩ ^ j) := by group
      _ = (mk ⟨n', hNX hn'⟩ * mk ⟨n, hNX hn⟩) * (mk ⟨c, hcX⟩ ^ j * mk ⟨c, hcX⟩ ^ i) := by
          rw [h1 (mk ⟨n', hNX hn'⟩), ← zpow_add, ← zpow_add, add_comm]
      _ = mk ⟨n', hNX hn'⟩ * (mk ⟨n, hNX hn⟩ * mk ⟨c, hcX⟩ ^ j) * mk ⟨c, hcX⟩ ^ i := by group
      _ = mk ⟨n', hNX hn'⟩ * (mk ⟨c, hcX⟩ ^ j * mk ⟨n, hNX hn⟩) * mk ⟨c, hcX⟩ ^ i := by
          rw [h1 (mk ⟨c, hcX⟩ ^ j)]
      _ = mk ⟨n', hNX hn'⟩ * mk ⟨c, hcX⟩ ^ j * (mk ⟨n, hNX hn⟩ * mk ⟨c, hcX⟩ ^ i) := by group
  have h : mk (⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩)⁻¹ * (⟨b, hb⟩)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hab]
    group
  exact (hmk1 _).mp h

end Quot

end CFSG.Quasithin.H13.A6
