module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.RankThree.PartTwo.Sec21.Item21LateProofGL33

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof

open Item21LateProof

variable {V : Type*} [Group V]

@[expose] def fixQuot (T : Subgroup V) : Subgroup (MulAut V) where
  carrier := {φ | ∀ x : V, x⁻¹ * φ x ∈ T}
  mul_mem' := by
    intro φ ψ hφ hψ x
    have h : x⁻¹ * (φ * ψ) x = (x⁻¹ * ψ x) * ((ψ x)⁻¹ * φ (ψ x)) := by
      rw [MulAut.mul_apply]
      group
    rw [h]
    exact T.mul_mem (hψ x) (hφ (ψ x))
  one_mem' := by
    intro x
    simp
  inv_mem' := by
    intro φ hφ x
    have h : x⁻¹ * φ⁻¹ x = ((φ⁻¹ x)⁻¹ * φ (φ⁻¹ x))⁻¹ := by
      rw [MulAut.apply_inv_self]
      group
    rw [h]
    exact T.inv_mem (hφ _)

theorem apply_mem_of_mem_fixQuot {T : Subgroup V} {φ : MulAut V} (hφ : φ ∈ fixQuot T) {x : V}
    (hx : x ∈ T) : φ x ∈ T := by
  have h : φ x = x * (x⁻¹ * φ x) := by group
  rw [h]
  exact T.mul_mem hx (hφ x)

theorem apply_eq_of_mul_self (hV3 : ∀ x : V, x ^ 3 = 1) {σ : MulAut V} (hσ : σ * σ = 1)
    {N : Subgroup V} (hN : ∀ n ∈ N, σ n = n) {x : V} (hx : x⁻¹ * σ x ∈ N) : σ x = x := by
  set n := x⁻¹ * σ x with hn
  have e1 : σ x = x * n := by rw [hn]; group
  have e2 : σ (σ x) = x := by rw [← MulAut.mul_apply, hσ, MulAut.one_apply]
  rw [e1, map_mul, e1, hN n hx] at e2
  have hn2 : n * n = 1 := by
    have h := congrArg (x⁻¹ * ·) e2
    simp only [inv_mul_cancel] at h
    rw [← h]
    group
  have hn1 : n = 1 := by
    calc n = n ^ 3 * (n * n)⁻¹ := by group
      _ = 1 := by rw [hV3 n, hn2]; group
  rw [e1, hn1, mul_one]

theorem pow_three_eq_one_of_fix (hV3 : ∀ x : V, x ^ 3 = 1) {σ : MulAut V} {N : Subgroup V}
    (hN : ∀ n ∈ N, σ n = n) (hσ : ∀ x : V, x⁻¹ * σ x ∈ N) : σ ^ 3 = 1 := by
  ext x
  set n := x⁻¹ * σ x with hn
  have e1 : σ x = x * n := by rw [hn]; group
  have hσn : σ n = n := hN n (hσ x)
  have h2 : σ (σ x) = x * n * n := by rw [e1, map_mul, e1, hσn]
  have h3 : σ (σ (σ x)) = x * n * n * n := by rw [h2, map_mul, map_mul, e1, hσn]
  rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, h3, MulAut.one_apply]
  calc x * n * n * n = x * n ^ 3 := by rw [pow_three]; simp only [mul_assoc]
    _ = x := by rw [hV3 n, mul_one]

@[expose] def fixSub (σ : MulAut V) : Subgroup V :=
  MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id V)

theorem quaternion_facts {H : Type*} [Group H] {Q8 : Subgroup H}
    (eQ8 : Q8 ≃* QuaternionGroup 2) :
    ∃ z ∈ Q8, ∃ g ∈ Q8, z ≠ 1 ∧ z * z = 1 ∧ g * g = z ∧ (∀ φ ∈ Q8, φ * z = z * φ) ∧
      (∀ φ ∈ Q8, φ * φ = 1 ∨ φ * φ = z) ∧ (∀ φ ∈ Q8, φ * φ = 1 → φ = 1 ∨ φ = z) ∧
      Nat.card Q8 = 8 := by
  set z' : Q8 := eQ8.symm (QuaternionGroup.a 2) with hz'
  set g' : Q8 := eQ8.symm (QuaternionGroup.a 1) with hg'
  have hcoe : ∀ u v : Q8, eQ8 u = eQ8 v → (u : H) = v := fun u v h =>
    congrArg Subtype.val (eQ8.injective h)
  have hz'e : eQ8 z' = QuaternionGroup.a 2 := by rw [hz', MulEquiv.apply_symm_apply]
  have hg'e : eQ8 g' = QuaternionGroup.a 1 := by rw [hg', MulEquiv.apply_symm_apply]
  refine ⟨z', z'.2, g', g'.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 : z' = 1 := Subtype.ext h
    have h2 := congrArg eQ8 h1
    rw [hz'e, map_one] at h2
    exact absurd h2 (by decide)
  · have h := hcoe (z' * z') 1 (by rw [map_mul, hz'e, map_one]; decide)
    simpa using h
  · have h := hcoe (g' * g') z' (by rw [map_mul, hg'e, hz'e]; decide)
    simpa using h
  · intro φ hφ
    have key : ∀ q : QuaternionGroup 2, q * QuaternionGroup.a 2 = QuaternionGroup.a 2 * q := by
      decide
    have h := hcoe (⟨φ, hφ⟩ * z') (z' * ⟨φ, hφ⟩) (by rw [map_mul, map_mul, hz'e, key])
    simpa using h
  · intro φ hφ
    have key : ∀ q : QuaternionGroup 2, q * q = 1 ∨ q * q = QuaternionGroup.a 2 := by decide
    rcases key (eQ8 ⟨φ, hφ⟩) with h | h
    · left
      have h' := hcoe (⟨φ, hφ⟩ * ⟨φ, hφ⟩) 1 (by rw [map_mul, h, map_one])
      simpa using h'
    · right
      have h' := hcoe (⟨φ, hφ⟩ * ⟨φ, hφ⟩) z' (by rw [map_mul, h, hz'e])
      simpa using h'
  · intro φ hφ hφφ
    have key : ∀ q : QuaternionGroup 2, q * q = 1 → q = 1 ∨ q = QuaternionGroup.a 2 := by
      decide
    have hq : eQ8 ⟨φ, hφ⟩ * eQ8 ⟨φ, hφ⟩ = 1 := by
      rw [← map_mul, ← map_one eQ8]
      congr 1
      exact Subtype.ext hφφ
    rcases key _ hq with h | h
    · left
      have h' := hcoe ⟨φ, hφ⟩ 1 (by rw [h, map_one])
      simpa using h'
    · right
      have h' := hcoe ⟨φ, hφ⟩ z' (by rw [h, hz'e])
      simpa using h'
  · rw [Nat.card_congr eQ8.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

section Hyperplane

variable [Finite V]

omit [Finite V] in
theorem card_zpowers_eq_three (hV3 : ∀ x : V, x ^ 3 = 1) {x : V} (hx : x ≠ 1) :
    Nat.card (Subgroup.zpowers x) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_zpowers, orderOf_eq_prime (hV3 x) hx]

theorem card_eq_three_mul_of_lt {H K : Subgroup V} (hKH : K ≤ H) (hne : K ≠ H)
    (hdvd : Nat.card H ∣ 3 * Nat.card K) : Nat.card H = 3 * Nat.card K := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hKH
  have hK0 : 0 < Nat.card K := Nat.card_pos
  rw [hm, mul_comm 3] at hdvd
  have hm3 : m ∣ 3 := Nat.dvd_of_mul_dvd_mul_left hK0 hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with h | h
  · exfalso
    apply hne
    exact Subgroup.eq_of_le_of_card_ge hKH (by rw [hm, h, mul_one])
  · rw [hm, h, mul_comm]

theorem card_eq_nine (hV3 : ∀ x : V, x ^ 3 = 1) (hV27 : Nat.card V = 27) {T : Subgroup V}
    (hT : T ≠ ⊤) {Q8 : Subgroup (MulAut V)} (eQ8 : Q8 ≃* QuaternionGroup 2)
    (hQ8 : Q8 ≤ fixQuot T) : Nat.card T = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz, g, hg, hz1, hzz, hgg, -, -, -, -⟩ := quaternion_facts eQ8
  have hdvd : Nat.card T ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hV27]
    exact Subgroup.card_subgroup_dvd_card T
  obtain ⟨k, hk, hTk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  ·
    exfalso
    have hT1 : T = ⊥ := Subgroup.eq_bot_of_card_eq T (by rw [hTk]; norm_num)
    apply hz1
    ext x
    have h := hQ8 hz x
    rw [hT1, Subgroup.mem_bot, inv_mul_eq_one] at h
    rw [MulAut.one_apply, ← h]
  ·
    exfalso
    have hT3 : Nat.card T = 3 := by rw [hTk]; norm_num
    have hzT : ∀ v ∈ T, z v = v := by
      intro v hv
      by_cases hv1 : v = 1
      · rw [hv1, map_one]
      have hZ : Subgroup.zpowers v = T :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hv)
          (by rw [hT3, card_zpowers_eq_three hV3 hv1])
      have hgv : g v ∈ Subgroup.zpowers v := by
        rw [hZ]
        exact apply_mem_of_mem_fixQuot (hQ8 hg) hv
      obtain ⟨j, hj, hj'⟩ := exists_pow_lt_three_of_mem_zpowers (hV3 v) hgv
      rw [← hgg, MulAut.mul_apply, hj', map_pow, hj', ← pow_mul]
      interval_cases j
      · exfalso
        rw [pow_zero] at hj'
        exact hv1 (g.injective (by rw [hj', map_one]))
      · rw [pow_one]
      · rw [show 2 * 2 = 3 + 1 by norm_num, pow_add, hV3 v, one_mul, pow_one]
    apply hz1
    ext x
    rw [MulAut.one_apply]
    exact apply_eq_of_mul_self hV3 hzz hzT (hQ8 hz x)
  · exact hTk
  · exfalso
    apply hT
    exact Subgroup.eq_top_of_card_eq T (by rw [hTk, hV27]; norm_num)

theorem eq_one_of_fix_of_mem (hVc : ∀ x y : V, x * y = y * x) (hV3 : ∀ x : V, x ^ 3 = 1)
    {T : Subgroup V} (hT9 : Nat.card T = 9) {z g : MulAut V} (hz : z ∈ fixQuot T)
    (hg : g ∈ fixQuot T) (hz1 : z ≠ 1) (hzz : z * z = 1) (hgg : g * g = z) {v : V}
    (hvT : v ∈ T) (hzv : z v = v) : v = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hv1
  obtain ⟨w₀, hw₀T, hw₀⟩ : ∃ w₀ ∈ T, z w₀ ≠ w₀ := by
    by_contra hno
    push Not at hno
    apply hz1
    ext x
    rw [MulAut.one_apply]
    exact apply_eq_of_mul_self hV3 hzz hno (hz x)
  set N := Subgroup.zpowers v with hN
  have hN3 : Nat.card N = 3 := card_zpowers_eq_three hV3 hv1
  have hNT : N ≤ T := Subgroup.zpowers_le.mpr hvT
  have hzN : ∀ n ∈ N, z n = n := by
    intro n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [map_zpow, hzv]
  have hw₀N : w₀ ∉ N := fun h => hw₀ (hzN w₀ h)
  have hTN : Nat.card T = 3 * Nat.card N := by rw [hT9, hN3]
  have hcommT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x _ y _ => hVc x y
  have h3T : ∀ x ∈ T, x ^ 3 = 1 := fun x _ => hV3 x
  have hgz : ∀ x, g (z x) = z (g x) := by
    intro x
    rw [← hgg, ← MulAut.mul_apply, ← MulAut.mul_apply, mul_assoc]
  have hgvN : g v ∈ N := by
    by_contra hgv
    have hgvT : g v ∈ T := apply_mem_of_mem_fixQuot hg hvT
    have hzgv : z (g v) = g v := by rw [← hgz, hzv]
    set M := N ⊔ Subgroup.zpowers (g v) with hM
    have hMT : M ≤ T := sup_le hNT (Subgroup.zpowers_le.mpr hgvT)
    have hNM : N ≠ M := by
      intro h
      apply hgv
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hM9 : Nat.card M = 9 := by
      have h1 := card_eq_three_mul_of_lt (le_sup_left : N ≤ M) hNM
        (by rw [hN3, show (3 : ℕ) * 3 = 9 by norm_num, ← hT9]
            exact Subgroup.card_dvd_of_le hMT)
      rw [h1, hN3]
    have hMeq : M = T := Subgroup.eq_of_le_of_card_ge hMT (by rw [hM9, hT9])
    have hMfix : M ≤ fixSub z := by
      refine sup_le (fun n hn => hzN n hn) ?_
      rw [Subgroup.zpowers_le]
      exact hzgv
    exact hw₀ (hMfix (hMeq ▸ hw₀T))
  have hgN : ∀ n ∈ N, g n ∈ N := by
    intro n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [map_zpow]
    exact Subgroup.zpow_mem _ hgvN k
  obtain ⟨b, hb, y₀, hy₀N, hgw₀⟩ :=
    exists_pow_mul_of_card hcommT h3T hNT hTN hw₀T hw₀N _ (apply_mem_of_mem_fixQuot hg hw₀T)
  have hzw₀ : z w₀ = g (g w₀) := by rw [← hgg, MulAut.mul_apply]
  interval_cases b
  ·
    rw [pow_zero, one_mul] at hgw₀
    apply hw₀
    have h1 : z w₀ ∈ N := by
      rw [hzw₀, hgw₀]
      exact hgN _ hy₀N
    have h2 : z (z w₀) = w₀ := by rw [← MulAut.mul_apply, hzz, MulAut.one_apply]
    rw [hzN _ h1] at h2
    exact h2
  · rw [pow_one] at hgw₀
    apply hw₀
    refine apply_eq_of_mul_self hV3 hzz hzN ?_
    have e : z w₀ = w₀ * (y₀ * g y₀) := by
      rw [hzw₀, hgw₀, map_mul, hgw₀, mul_assoc]
    rw [e, show w₀⁻¹ * (w₀ * (y₀ * g y₀)) = y₀ * g y₀ by group]
    exact N.mul_mem hy₀N (hgN _ hy₀N)
  · apply hw₀
    refine apply_eq_of_mul_self hV3 hzz hzN ?_
    have hc : Commute (w₀ ^ 2) y₀ := hVc _ _
    have e : z w₀ = w₀ * (y₀ ^ 2 * g y₀) := by
      rw [hzw₀, hgw₀, map_mul, map_pow, hgw₀, hc.mul_pow, ← pow_mul,
        show 2 * 2 = 3 + 1 by norm_num, pow_add, hV3 w₀, one_mul, pow_one, mul_assoc]
    rw [e, show w₀⁻¹ * (w₀ * (y₀ ^ 2 * g y₀)) = y₀ ^ 2 * g y₀ by group]
    exact N.mul_mem (N.pow_mem hy₀N 2) (hgN _ hy₀N)

theorem apply_eq_inv_of_mem (hVc : ∀ x y : V, x * y = y * x) (hV3 : ∀ x : V, x ^ 3 = 1)
    {T : Subgroup V} (hT9 : Nat.card T = 9) {z g : MulAut V} (hz : z ∈ fixQuot T)
    (hg : g ∈ fixQuot T) (hz1 : z ≠ 1) (hzz : z * z = 1) (hgg : g * g = z) {v : V}
    (hvT : v ∈ T) : z v = v⁻¹ := by
  have hzzv : z (z v) = v := by rw [← MulAut.mul_apply, hzz, MulAut.one_apply]
  have h := eq_one_of_fix_of_mem hVc hV3 hT9 hz hg hz1 hzz hgg
    (T.mul_mem hvT (apply_mem_of_mem_fixQuot hz hvT))
    (by rw [map_mul, hzzv, hVc])
  rw [eq_inv_iff_mul_eq_one, hVc]
  exact h

theorem eq_one_of_mem_quaternion (hVc : ∀ x y : V, x * y = y * x) (hV3 : ∀ x : V, x ^ 3 = 1)
    {T : Subgroup V} (hT9 : Nat.card T = 9) {Q8 : Subgroup (MulAut V)}
    (eQ8 : Q8 ≃* QuaternionGroup 2) (hQ8 : Q8 ≤ fixQuot T) {φ : MulAut V} (hφ : φ ∈ Q8)
    (hφ1 : φ ≠ 1) {v : V} (hvT : v ∈ T) (hφv : φ v = v) : v = 1 := by
  obtain ⟨z, hz, g, hg, hz1, hzz, hgg, -, hsq, hsq1, -⟩ := quaternion_facts eQ8
  have hzv : z v = v := by
    rcases hsq φ hφ with h | h
    · rcases hsq1 φ hφ h with h' | h'
      · exact absurd h' hφ1
      · rw [← h', hφv]
    · rw [← h, MulAut.mul_apply, hφv, hφv]
  exact eq_one_of_fix_of_mem hVc hV3 hT9 (hQ8 hz) (hQ8 hg) hz1 hzz hgg hvT hzv

theorem exists_mem_quaternion_apply_eq (hVc : ∀ x y : V, x * y = y * x)
    (hV3 : ∀ x : V, x ^ 3 = 1) {T : Subgroup V} (hT9 : Nat.card T = 9)
    {Q8 : Subgroup (MulAut V)} (eQ8 : Q8 ≃* QuaternionGroup 2) (hQ8 : Q8 ≤ fixQuot T)
    {v w : V} (hvT : v ∈ T) (hv1 : v ≠ 1) (hwT : w ∈ T) (hw1 : w ≠ 1) :
    ∃ φ ∈ Q8, φ v = w := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hQ8card⟩ := quaternion_facts eQ8
  set f : Q8 → V := fun φ => (φ : MulAut V) v with hf
  have hinj : Function.Injective f := by
    intro φ ψ h
    have h1 : ((ψ⁻¹ * φ : Q8) : MulAut V) v = v := by
      simp only [hf] at h
      rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply, h, MulAut.inv_apply_self]
    by_contra hne
    have hne' : ((ψ⁻¹ * φ : Q8) : MulAut V) ≠ 1 := by
      intro h2
      apply hne
      have h3 : ψ⁻¹ * φ = 1 := Subtype.ext h2
      rw [inv_mul_eq_one] at h3
      exact h3.symm
    exact hv1 (eq_one_of_mem_quaternion hVc hV3 hT9 eQ8 hQ8 (ψ⁻¹ * φ).2 hne' hvT h1)
  have hsub : Set.range f ⊆ (T : Set V) \ {1} := by
    rintro _ ⟨φ, rfl⟩
    refine ⟨apply_mem_of_mem_fixQuot (hQ8 φ.2) hvT, fun h => hv1 ?_⟩
    have h' : (φ : MulAut V) v = 1 := h
    exact (φ : MulAut V).injective (by rw [h', map_one])
  have hcardS : ((T : Set V) \ {1}).ncard = 8 := by
    rw [Set.ncard_sdiff_singleton_of_mem (T.one_mem), ← Nat.card_coe_set_eq]
    change Nat.card T - 1 = 8
    rw [hT9]
  have heq : Set.range f = (T : Set V) \ {1} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcardS, Set.ncard_range_of_injective hinj, hQ8card])
  have hw : w ∈ Set.range f := by
    rw [heq]
    exact ⟨hwT, hw1⟩
  obtain ⟨φ, hφ⟩ := hw
  exact ⟨φ, φ.2, hφ⟩

theorem exists_fixed_of_quaternion (hVc : ∀ x y : V, x * y = y * x) (hV3 : ∀ x : V, x ^ 3 = 1)
    (hV27 : Nat.card V = 27) {T : Subgroup V} (hT9 : Nat.card T = 9)
    {Q8 : Subgroup (MulAut V)} (eQ8 : Q8 ≃* QuaternionGroup 2) (hQ8 : Q8 ≤ fixQuot T) :
    ∃ f' : V, f' ∉ T ∧ ∀ φ ∈ Q8, φ f' = f' := by
  obtain ⟨z, hz, g, hg, hz1, hzz, hgg, hcen, -, -, -⟩ := quaternion_facts eQ8
  obtain ⟨f, hf⟩ : ∃ f : V, f ∉ T := by
    by_contra h
    push Not at h
    have h1 : T = ⊤ := eq_top_iff.mpr fun x _ => h x
    rw [h1, Subgroup.card_top, hV27] at hT9
    norm_num at hT9
  have hzzf : z (z f) = f := by rw [← MulAut.mul_apply, hzz, MulAut.one_apply]
  set f' := f * z f with hf'
  have hzf' : z f' = f' := by rw [hf', map_mul, hzzf, hVc]
  have hf'T : f' ∉ T := by
    intro h
    apply hf
    have h1 : f * f ∈ T := by
      have e : f * f = f' * (f⁻¹ * z f)⁻¹ := by rw [hf']; group
      rw [e]
      exact T.mul_mem h (T.inv_mem (hQ8 hz f))
    have e2 : f = (f * f) * (f * f) := by
      calc f = f ^ 3 * f := by rw [hV3 f, one_mul]
        _ = (f * f) * (f * f) := by rw [pow_three]; group
    rw [e2]
    exact T.mul_mem h1 h1
  refine ⟨f', hf'T, fun φ hφ => ?_⟩
  set s := f'⁻¹ * φ f' with hs
  have hsT : s ∈ T := hQ8 hφ f'
  have hφf' : φ f' = f' * s := by rw [hs]; group
  have hzφ : z (φ f') = φ f' := by
    rw [← MulAut.mul_apply, ← hcen φ hφ, MulAut.mul_apply, hzf']
  rw [hφf', map_mul, hzf'] at hzφ
  have hzs : z s = s := mul_left_cancel hzφ
  rw [hφf', eq_one_of_fix_of_mem hVc hV3 hT9 (hQ8 hz) (hQ8 hg) hz1 hzz hgg hsT hzs, mul_one]

theorem eq_of_apply_eq_three (hV3 : ∀ x : V, x ^ 3 = 1) (hV27 : Nat.card V = 27)
    {T : Subgroup V} (hT9 : Nat.card T = 9) {d t f' : V} (hdT : d ∈ T) (hd1 : d ≠ 1)
    (htT : t ∈ T) (htd : t ∉ Subgroup.zpowers d) (hf'T : f' ∉ T) {φ ψ : MulAut V}
    (hd : φ d = ψ d) (ht : φ t = ψ t) (hf : φ f' = ψ f') : φ = ψ := by
  have hd3 : Nat.card (Subgroup.zpowers d) = 3 := card_zpowers_eq_three hV3 hd1
  have hH1 : Subgroup.zpowers d ⊔ Subgroup.zpowers t = T := by
    have hle : Subgroup.zpowers d ⊔ Subgroup.zpowers t ≤ T :=
      sup_le (Subgroup.zpowers_le.mpr hdT) (Subgroup.zpowers_le.mpr htT)
    have hne : Subgroup.zpowers d ≠ Subgroup.zpowers d ⊔ Subgroup.zpowers t := by
      intro h
      apply htd
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have h9 := card_eq_three_mul_of_lt le_sup_left hne
      (by rw [hd3, show (3 : ℕ) * 3 = 9 by norm_num, ← hT9]
          exact Subgroup.card_dvd_of_le hle)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h9, hd3, hT9])
  have hH2 : T ⊔ Subgroup.zpowers f' = ⊤ := by
    have hne : T ≠ T ⊔ Subgroup.zpowers f' := by
      intro h
      apply hf'T
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers f')
    have h27 := card_eq_three_mul_of_lt le_sup_left hne
      (by rw [hT9, show (3 : ℕ) * 9 = 27 by norm_num, ← hV27]
          exact Subgroup.card_subgroup_dvd_card _)
    exact Subgroup.eq_top_of_card_eq _ (by rw [h27, hT9, hV27])
  have hcl : Subgroup.closure ({d, t, f'} : Set V) = ⊤ := by
    rw [eq_top_iff, ← hH2, ← hH1]
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le] <;>
      exact Subgroup.subset_closure (by simp)
  have h := MonoidHom.eq_of_eqOn_dense hcl (f := φ.toMonoidHom) (g := ψ.toMonoidHom) (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hd
    · exact ht
    · exact hf)
  exact MulEquiv.ext fun x => DFunLike.congr_fun h x

end Hyperplane

section Lines

@[expose] def lineSet (T : Subgroup V) : Set (Subgroup V) :=
  {ℓ | ℓ ≤ T ∧ Nat.card ℓ = 3}

theorem map_mem_lineSet {T : Subgroup V} {φ : MulAut V} (hφ : φ ∈ fixQuot T) {ℓ : Subgroup V}
    (hℓ : ℓ ∈ lineSet T) : ℓ.map φ.toMonoidHom ∈ lineSet T := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact apply_mem_of_mem_fixQuot hφ (hℓ.1 hx)
  · rw [Subgroup.card_map_of_injective φ.injective]
    exact hℓ.2

@[expose] noncomputable def linePerm (T : Subgroup V) : fixQuot T →* Equiv.Perm (lineSet T) where
  toFun φ :=
    { toFun := fun ℓ => ⟨ℓ.1.map (φ : MulAut V).toMonoidHom, map_mem_lineSet φ.2 ℓ.2⟩
      invFun := fun ℓ => ⟨ℓ.1.map ((φ : MulAut V)⁻¹).toMonoidHom,
        map_mem_lineSet ((fixQuot T).inv_mem φ.2) ℓ.2⟩
      left_inv := fun ℓ => by
        apply Subtype.ext
        change (ℓ.1.map (φ : MulAut V).toMonoidHom).map ((φ : MulAut V)⁻¹).toMonoidHom = ℓ.1
        rw [Subgroup.map_map]
        convert Subgroup.map_id ℓ.1
        ext x
        simp
      right_inv := fun ℓ => by
        apply Subtype.ext
        change (ℓ.1.map ((φ : MulAut V)⁻¹).toMonoidHom).map (φ : MulAut V).toMonoidHom = ℓ.1
        rw [Subgroup.map_map]
        convert Subgroup.map_id ℓ.1
        ext x
        simp }
  map_one' := by
    ext ℓ : 2
    change ℓ.1.map (1 : MulAut V).toMonoidHom = ℓ.1
    convert Subgroup.map_id ℓ.1
    ext x
    rfl
  map_mul' φ ψ := by
    ext ℓ : 2
    change ℓ.1.map ((φ : MulAut V) * ψ).toMonoidHom =
      (ℓ.1.map (ψ : MulAut V).toMonoidHom).map (φ : MulAut V).toMonoidHom
    rw [Subgroup.map_map]
    congr 1

theorem zpowers_mem_lineSet (hV3 : ∀ x : V, x ^ 3 = 1) {T : Subgroup V} {x : V} (hxT : x ∈ T)
    (hx1 : x ≠ 1) : Subgroup.zpowers x ∈ lineSet T :=
  ⟨Subgroup.zpowers_le.mpr hxT, card_zpowers_eq_three hV3 hx1⟩

theorem zpowers_eq_of_mem_lineSet [Finite V] (hV3 : ∀ x : V, x ^ 3 = 1) {T ℓ : Subgroup V}
    (hℓ : ℓ ∈ lineSet T) {x : V} (hxℓ : x ∈ ℓ) (hx1 : x ≠ 1) : Subgroup.zpowers x = ℓ :=
  Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxℓ)
    (by rw [hℓ.2, card_zpowers_eq_three hV3 hx1])

theorem card_lineSet [Finite V] (hV3 : ∀ x : V, x ^ 3 = 1) {T : Subgroup V}
    (hT9 : Nat.card T = 9) : Nat.card (lineSet T) = 4 := by
  classical
  have : Fintype (lineSet T) := Fintype.ofFinite _
  set S : Set V := (T : Set V) \ {1} with hS
  let f : S → lineSet T := fun x => ⟨Subgroup.zpowers x.1, zpowers_mem_lineSet hV3 x.2.1 x.2.2⟩
  have hfib : ∀ ℓ : lineSet T, Nat.card {x : S // f x = ℓ} = 2 := by
    intro ℓ
    have e : {x : S // f x = ℓ} ≃ ((ℓ.1 : Set V) \ {1} : Set V) :=
      { toFun := fun x => ⟨x.1.1, by
          refine ⟨?_, x.1.2.2⟩
          have h : Subgroup.zpowers x.1.1 = ℓ.1 := congrArg Subtype.val x.2
          change x.1.1 ∈ ℓ.1
          rw [← h]
          exact Subgroup.mem_zpowers _, ⟩
        invFun := fun x => ⟨⟨x.1, ℓ.2.1 x.2.1, x.2.2⟩, Subtype.ext
          (zpowers_eq_of_mem_lineSet hV3 ℓ.2 x.2.1 x.2.2)⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem ℓ.1.one_mem,
      ← Nat.card_coe_set_eq]
    change Nat.card ℓ.1 - 1 = 2
    rw [ℓ.2.2]
  have hS8 : Nat.card S = 8 := by
    rw [Nat.card_coe_set_eq, hS, Set.ncard_sdiff_singleton_of_mem T.one_mem,
      ← Nat.card_coe_set_eq]
    change Nat.card T - 1 = 8
    rw [hT9]
  have h := Nat.card_congr (Equiv.sigmaFiberEquiv f)
  rw [Nat.card_sigma, hS8] at h
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  rw [Nat.card_eq_fintype_card]
  omega

theorem sign_eq_of_mul_self {α : Type*} [Fintype α] [DecidableEq α] {σ : Equiv.Perm α}
    (h : σ * σ = 1) :
    Equiv.Perm.sign σ = (-1) ^ ((Nat.card α - Nat.card (Function.fixedPoints σ)) / 2) := by
  classical
  have h2 : σ ^ 2 = 1 := by rw [sq, h]
  have hct : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate_card.2 ((Equiv.Perm.pow_prime_eq_one_iff (p := 2)).1 h2)
  rw [Equiv.Perm.sign_of_cycleType_eq_replicate (by norm_num) hct, ite_eq_right (by decide),
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

theorem sign_eq_one_of_pow_three {α : Type*} [Fintype α] [DecidableEq α] {σ : Equiv.Perm α}
    (h : σ ^ 3 = 1) : Equiv.Perm.sign σ = 1 := by
  have h1 : Equiv.Perm.sign σ ^ 3 = 1 := by rw [← map_pow, h, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h2 | h2
  · exact h2
  · rw [h2] at h1
    exact absurd h1 (by decide)

end Lines

section Main

variable [Finite V]

theorem mem_zpowers_of_mem_zpowers (hV3 : ∀ x : V, x ^ 3 = 1) {t x : V}
    (hx : x ∈ Subgroup.zpowers t) (hx1 : x ≠ 1) : t ∈ Subgroup.zpowers x := by
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact hx1 (by simpa using hx)
  have h : Subgroup.zpowers x = Subgroup.zpowers t :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx)
      (by rw [card_zpowers_eq_three hV3 hx1, card_zpowers_eq_three hV3 ht1])
  rw [h]
  exact Subgroup.mem_zpowers t

theorem fix_or_inv_of_lines (hVc : ∀ x y : V, x * y = y * x) (hV3 : ∀ x : V, x ^ 3 = 1)
    {φ : MulAut V} {d t : V} (hd1 : d ≠ 1) (htd : t ∉ Subgroup.zpowers d)
    (hd : φ d ∈ Subgroup.zpowers d) (ht : φ t ∈ Subgroup.zpowers t)
    (hdt : φ (d * t) ∈ Subgroup.zpowers (d * t)) :
    (φ d = d ∧ φ t = t) ∨ (φ d = d⁻¹ ∧ φ t = t⁻¹) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ht1 : t ≠ 1 := fun h => htd (h ▸ Subgroup.one_mem _)
  obtain ⟨a, ha, ha'⟩ := exists_pow_lt_three_of_mem_zpowers (hV3 d) hd
  obtain ⟨b, hb, hb'⟩ := exists_pow_lt_three_of_mem_zpowers (hV3 t) ht
  obtain ⟨c, hc, hc'⟩ := exists_pow_lt_three_of_mem_zpowers (hV3 (d * t)) hdt
  have hdt' : Commute d t := hVc d t
  rw [map_mul, ha', hb', hdt'.mul_pow] at hc'
  have key : t ^ b * (t ^ c)⁻¹ = (d ^ a)⁻¹ * d ^ c := by
    calc t ^ b * (t ^ c)⁻¹ = (d ^ a)⁻¹ * (d ^ a * t ^ b) * (t ^ c)⁻¹ := by group
      _ = (d ^ a)⁻¹ * (d ^ c * t ^ c) * (t ^ c)⁻¹ := by rw [hc']
      _ = (d ^ a)⁻¹ * d ^ c := by group
  have htt : t ^ b * (t ^ c)⁻¹ = 1 := by
    by_contra hne
    apply htd
    have h1 : t ^ b * (t ^ c)⁻¹ ∈ Subgroup.zpowers t :=
      Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers t) b)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers t) c))
    have h2 : t ^ b * (t ^ c)⁻¹ ∈ Subgroup.zpowers d := by
      rw [key]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers d) a))
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers d) c)
    exact (Subgroup.zpowers_le.mpr h2) (mem_zpowers_of_mem_zpowers hV3 h1 hne)
  have hdd : (d ^ a)⁻¹ * d ^ c = 1 := by rw [← key, htt]
  rw [mul_inv_eq_one] at htt
  rw [inv_mul_eq_one] at hdd
  have hod : orderOf d = 3 := orderOf_eq_prime (hV3 d) hd1
  have hot : orderOf t = 3 := orderOf_eq_prime (hV3 t) ht1
  have hac : a = c := by
    have h := pow_inj_mod.mp hdd
    rw [hod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] at h
    exact h
  have hbc : b = c := by
    have h := pow_inj_mod.mp htt
    rw [hot, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc] at h
    exact h
  rw [hac] at ha'
  rw [hbc] at hb'
  interval_cases c
  · exact absurd (φ.injective (by rw [ha', pow_zero, map_one])) hd1
  · left
    exact ⟨by rw [ha', pow_one], by rw [hb', pow_one]⟩
  · right
    exact ⟨by rw [ha', sq_eq_inv_of_pow_three (hV3 d)],
      by rw [hb', sq_eq_inv_of_pow_three (hV3 t)]⟩

theorem linePerm_eq_one_of_inv {T : Subgroup V} {z : MulAut V} (hz : z ∈ fixQuot T)
    (hinv : ∀ v ∈ T, z v = v⁻¹) : linePerm T ⟨z, hz⟩ = 1 := by
  ext ℓ : 2
  change ℓ.1.map z.toMonoidHom = ℓ.1
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [Subgroup.card_map_of_injective z.injective])
  rintro _ ⟨x, hx, rfl⟩
  change z x ∈ ℓ.1
  rw [hinv x (ℓ.2.1 hx)]
  exact ℓ.1.inv_mem hx

theorem card_sup_eq (hVc : ∀ x y : V, x * y = y * x) (hV3 : ∀ x : V, x ^ 3 = 1)
    (hV27 : Nat.card V = 27) {T : Subgroup V} (hT9 : Nat.card T = 9) {d : V} (hdT : d ∈ T)
    (hd1 : d ≠ 1) {Q8 Q9 : Subgroup (MulAut V)} (eQ8 : Q8 ≃* QuaternionGroup 2)
    (hQ8 : Q8 ≤ fixQuot T) (hQ9 : ∀ φ ∈ Q9, ∀ x : V, x⁻¹ * φ x ∈ Subgroup.zpowers d)
    (hQ9d : ∀ φ ∈ Q9, φ d = d) (hQ9card : Nat.card Q9 = 9) :
    Nat.card (Q8 ⊔ Q9 : Subgroup (MulAut V)) = 216 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz, g, hg, hz1, hzz, hgg, -, hsq, hsq1, hQ8card⟩ := quaternion_facts eQ8
  have hdZT : Subgroup.zpowers d ≤ T := Subgroup.zpowers_le.mpr hdT
  have hQ9T : Q9 ≤ fixQuot T := fun φ hφ x => hdZT (hQ9 φ hφ x)
  set 𝒜 := Q8 ⊔ Q9 with h𝒜
  have h𝒜T : 𝒜 ≤ fixQuot T := sup_le hQ8 hQ9T
  have hinv : ∀ v ∈ T, z v = v⁻¹ := fun v hv =>
    apply_eq_inv_of_mem hVc hV3 hT9 (hQ8 hz) (hQ8 hg) hz1 hzz hgg hv
  have hQ9fix : ∀ φ ∈ Q9, ∀ n ∈ Subgroup.zpowers d, φ n = n := by
    intro φ hφ n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [map_zpow, hQ9d φ hφ]
  have hQ93 : ∀ φ ∈ Q9, φ ^ 3 = 1 := fun φ hφ =>
    pow_three_eq_one_of_fix hV3 (hQ9fix φ hφ) (hQ9 φ hφ)
  obtain ⟨f', hf'T, hQ8f'⟩ := exists_fixed_of_quaternion hVc hV3 hV27 hT9 eQ8 hQ8
  obtain ⟨t, htT, htd⟩ : ∃ t ∈ T, t ∉ Subgroup.zpowers d := by
    by_contra h
    push Not at h
    have hle : T ≤ Subgroup.zpowers d := fun x hx => h x hx
    have h1 := Subgroup.card_le_of_le hle
    rw [hT9, card_zpowers_eq_three hV3 hd1] at h1
    norm_num at h1
  have hdet : ∀ {φ ψ : MulAut V}, φ d = ψ d → φ t = ψ t → φ f' = ψ f' → φ = ψ :=
    fun hd ht hf => eq_of_apply_eq_three hV3 hV27 hT9 hdT hd1 htT htd hf'T hd ht hf
  obtain ⟨q, hq, hqf'⟩ : ∃ q ∈ Q9, q f' = f' * d := by
    obtain ⟨q₀, hq₀, hq₀f'⟩ : ∃ q₀ ∈ Q9, q₀ f' ≠ f' := by
      by_contra h
      push Not at h
      let F : Q9 → Subgroup.zpowers d := fun ψ => ⟨t⁻¹ * (ψ : MulAut V) t, hQ9 ψ ψ.2 t⟩
      have hF : Function.Injective F := by
        intro ψ₁ ψ₂ h12
        have h12' : t⁻¹ * (ψ₁ : MulAut V) t = t⁻¹ * (ψ₂ : MulAut V) t :=
          congrArg Subtype.val h12
        apply Subtype.ext
        exact hdet (by rw [hQ9d _ ψ₁.2, hQ9d _ ψ₂.2]) (mul_left_cancel h12')
          (by rw [h _ ψ₁.2, h _ ψ₂.2])
      have h1 := Nat.card_le_card_of_injective F hF
      rw [hQ9card, card_zpowers_eq_three hV3 hd1] at h1
      norm_num at h1
    obtain ⟨k, hk, hk'⟩ := exists_pow_lt_three_of_mem_zpowers (hV3 d) (hQ9 q₀ hq₀ f')
    have hq₀e : q₀ f' = f' * d ^ k := by rw [← hk']; group
    interval_cases k
    · exact absurd (by rw [hq₀e, pow_zero, mul_one]) hq₀f'
    · exact ⟨q₀, hq₀, by rw [hq₀e, pow_one]⟩
    · refine ⟨q₀ * q₀, Q9.mul_mem hq₀ hq₀, ?_⟩
      rw [MulAut.mul_apply, hq₀e, map_mul, map_pow, hQ9d q₀ hq₀, hq₀e, mul_assoc, ← pow_add,
        show 2 + 2 = 3 + 1 by norm_num, pow_add, hV3 d, one_mul, pow_one]
  obtain ⟨u, hu, hu1, huf'⟩ : ∃ u ∈ Q9, u ≠ 1 ∧ u f' = f' := by
    let F : Q9 → Subgroup.zpowers d := fun ψ => ⟨f'⁻¹ * (ψ : MulAut V) f', hQ9 ψ ψ.2 f'⟩
    have hF : ¬ Function.Injective F := by
      intro hF
      have h1 := Nat.card_le_card_of_injective F hF
      rw [hQ9card, card_zpowers_eq_three hV3 hd1] at h1
      norm_num at h1
    obtain ⟨ψ₁, ψ₂, h12, hne⟩ : ∃ ψ₁ ψ₂, F ψ₁ = F ψ₂ ∧ ψ₁ ≠ ψ₂ := by
      by_contra h
      push Not at h
      exact hF fun a b hab => h a b hab
    refine ⟨(ψ₂ : MulAut V)⁻¹ * ψ₁, Q9.mul_mem (Q9.inv_mem ψ₂.2) ψ₁.2, ?_, ?_⟩
    · intro h
      apply hne
      apply Subtype.ext
      rw [inv_mul_eq_one] at h
      exact h.symm
    · have h12' : f'⁻¹ * (ψ₁ : MulAut V) f' = f'⁻¹ * (ψ₂ : MulAut V) f' :=
        congrArg Subtype.val h12
      rw [MulAut.mul_apply, mul_left_cancel h12', MulAut.inv_apply_self]
  have hlow : 216 ∣ Nat.card 𝒜 := by
    have horbit : MulAction.orbit 𝒜 f' = (fun s => f' * s) '' (T : Set V) := by
      ext x
      constructor
      · rintro ⟨φ, rfl⟩
        refine ⟨f'⁻¹ * (φ : MulAut V) f', h𝒜T φ.2 f', ?_⟩
        change f' * (f'⁻¹ * (φ : MulAut V) f') = φ • f'
        rw [Subgroup.smul_def, MulAut.smul_def]
        group
      · rintro ⟨s, hsT, rfl⟩
        by_cases hs1 : s = 1
        · exact ⟨1, by
            show (1 : 𝒜) • f' = f' * s
            rw [hs1, mul_one, one_smul]⟩
        obtain ⟨φ, hφ, hφd⟩ :=
          exists_mem_quaternion_apply_eq hVc hV3 hT9 eQ8 hQ8 hdT hd1 hsT hs1
        refine ⟨⟨φ * q, 𝒜.mul_mem (Subgroup.mem_sup_left hφ) (Subgroup.mem_sup_right hq)⟩, ?_⟩
        show _ • f' = f' * s
        rw [Subgroup.smul_def, MulAut.smul_def]
        change (φ * q) f' = f' * s
        rw [MulAut.mul_apply, hqf', map_mul, hQ8f' φ hφ, hφd]
    have hcardorbit : (MulAction.orbit 𝒜 f').ncard = 9 := by
      rw [horbit, Set.ncard_image_of_injective _ (mul_right_injective f'),
        ← Nat.card_coe_set_eq]
      exact hT9
    have hcard := Subgroup.index_mul_card (MulAction.stabilizer 𝒜 f')
    rw [MulAction.index_stabilizer, hcardorbit] at hcard
    have hu𝒜 : u ∈ 𝒜 := Subgroup.mem_sup_right hu
    have hustab : (⟨u, hu𝒜⟩ : 𝒜) ∈ MulAction.stabilizer 𝒜 f' := by
      rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, MulAut.smul_def]
      exact huf'
    have hord : orderOf (⟨⟨u, hu𝒜⟩, hustab⟩ : MulAction.stabilizer 𝒜 f') = 3 := by
      apply orderOf_eq_prime
      · apply Subtype.ext
        apply Subtype.ext
        exact hQ93 u hu
      · intro h
        apply hu1
        exact congrArg (fun w : MulAction.stabilizer 𝒜 f' => ((w : 𝒜) : MulAut V)) h
    have h3 : 3 ∣ Nat.card (MulAction.stabilizer 𝒜 f') := hord ▸ orderOf_dvd_natCard _
    have h27 : 27 ∣ Nat.card 𝒜 := by
      rw [← hcard]
      obtain ⟨m, hm⟩ := h3
      exact ⟨m, by rw [hm]; ring⟩
    have h8 : 8 ∣ Nat.card 𝒜 := by
      rw [← hQ8card]
      exact Subgroup.card_dvd_of_le le_sup_left
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h8 h27
  have hup : Nat.card 𝒜 ≤ 216 := by
    have : Fintype (lineSet T) := Fintype.ofFinite _
    have hL4 : Fintype.card (lineSet T) = 4 := by
      rw [← Nat.card_eq_fintype_card, card_lineSet hV3 hT9]
    have : Nontrivial (lineSet T) := Fintype.one_lt_card_iff_nontrivial.mp (by rw [hL4]; norm_num)
    let π : 𝒜 →* Equiv.Perm (lineSet T) := (linePerm T).comp (Subgroup.inclusion h𝒜T)
    have hcard := Subgroup.index_mul_card π.ker
    rw [Subgroup.index_ker] at hcard
    have hline : ∀ {x : V}, x ∈ T → x ≠ 1 → Subgroup.zpowers x ∈ lineSet T :=
      fun hx hx1 => zpowers_mem_lineSet hV3 hx hx1
    have hQ8even : ∀ φ (hφ : φ ∈ Q8), Equiv.Perm.sign (linePerm T ⟨φ, hQ8 hφ⟩) = 1 := by
      intro φ hφ
      have hz1' : linePerm T ⟨z, hQ8 hz⟩ = 1 := linePerm_eq_one_of_inv (hQ8 hz) hinv
      rcases hsq φ hφ with h | h
      · rcases hsq1 φ hφ h with h' | h'
        · have e : (⟨φ, hQ8 hφ⟩ : fixQuot T) = 1 := Subtype.ext h'
          rw [e, map_one, Equiv.Perm.sign_one]
        · have e : (⟨φ, hQ8 hφ⟩ : fixQuot T) = ⟨z, hQ8 hz⟩ := Subtype.ext h'
          rw [e, hz1', Equiv.Perm.sign_one]
      · have hP2 : linePerm T ⟨φ, hQ8 hφ⟩ * linePerm T ⟨φ, hQ8 hφ⟩ = 1 := by
          rw [← map_mul]
          have e : (⟨φ, hQ8 hφ⟩ * ⟨φ, hQ8 hφ⟩ : fixQuot T) = ⟨z, hQ8 hz⟩ := Subtype.ext h
          rw [e, hz1']
        have hφ1 : φ ≠ 1 := by
          rintro rfl
          rw [one_mul] at h
          exact hz1 h.symm
        have hfix : Function.fixedPoints (linePerm T ⟨φ, hQ8 hφ⟩) = ∅ := by
          ext ℓ
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hℓ
          have hℓ' : ℓ.1.map φ.toMonoidHom = ℓ.1 := congrArg Subtype.val hℓ
          obtain ⟨x, hxℓ, hx1⟩ : ∃ x ∈ ℓ.1, x ≠ 1 := by
            by_contra hno
            push Not at hno
            have h1 : ℓ.1 = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hno
            have h2 := ℓ.2.2
            rw [h1, Subgroup.card_bot] at h2
            norm_num at h2
          have hxT : x ∈ T := ℓ.2.1 hxℓ
          have hφx : φ x ∈ Subgroup.zpowers x := by
            rw [zpowers_eq_of_mem_lineSet hV3 ℓ.2 hxℓ hx1, ← hℓ']
            exact ⟨x, hxℓ, rfl⟩
          obtain ⟨k, hk, hk'⟩ := exists_pow_lt_three_of_mem_zpowers (hV3 x) hφx
          interval_cases k
          · exact hx1 (φ.injective (by rw [hk', pow_zero, map_one]))
          · exact hx1 (eq_one_of_mem_quaternion hVc hV3 hT9 eQ8 hQ8 hφ hφ1 hxT
              (by rw [hk', pow_one]))
          · have hzx : z x = x := by
              rw [← h, MulAut.mul_apply, hk', map_pow, hk', ← pow_mul,
                show 2 * 2 = 3 + 1 by norm_num, pow_add, hV3 x, one_mul, pow_one]
            exact hx1 (eq_one_of_fix_of_mem hVc hV3 hT9 (hQ8 hz) (hQ8 hg) hz1 hzz hgg hxT hzx)
        rw [sign_eq_of_mul_self hP2, hfix, Nat.card_eq_fintype_card, hL4]
        simp
    have hQ9even : ∀ φ (hφ : φ ∈ Q9), Equiv.Perm.sign (linePerm T ⟨φ, hQ9T hφ⟩) = 1 := by
      intro φ hφ
      apply sign_eq_one_of_pow_three
      rw [← map_pow]
      have e : (⟨φ, hQ9T hφ⟩ ^ 3 : fixQuot T) = 1 := Subtype.ext (hQ93 φ hφ)
      rw [e, map_one]
    have hrange : π.range ≤ alternatingGroup (lineSet T) := by
      set B : Subgroup (MulAut V) :=
        ((alternatingGroup (lineSet T)).comap (linePerm T)).map (fixQuot T).subtype with hB
      have hQ8B : Q8 ≤ B := fun φ hφ =>
        ⟨⟨φ, hQ8 hφ⟩, Equiv.Perm.mem_alternatingGroup.mpr (hQ8even φ hφ), rfl⟩
      have hQ9B : Q9 ≤ B := fun φ hφ =>
        ⟨⟨φ, hQ9T hφ⟩, Equiv.Perm.mem_alternatingGroup.mpr (hQ9even φ hφ), rfl⟩
      rintro _ ⟨φ, rfl⟩
      obtain ⟨ψ, hψ, hψφ⟩ := (sup_le hQ8B hQ9B) φ.2
      have e : Subgroup.inclusion h𝒜T φ = ψ := Subtype.ext hψφ.symm
      change linePerm T (Subgroup.inclusion h𝒜T φ) ∈ _
      rw [e]
      exact hψ
    have hrange12 : Nat.card π.range ≤ 12 := by
      have h1 := Subgroup.card_le_of_le hrange
      have h2 : 2 * Nat.card (alternatingGroup (lineSet T)) = 24 := by
        rw [Nat.card_eq_fintype_card]
        convert two_mul_card_alternatingGroup (α := lineSet T) using 1
        rw [Fintype.card_perm, hL4]
        rfl
      omega
    have hker18 : Nat.card π.ker ≤ 18 := by
      have hdt1 : d * t ≠ 1 := by
        intro h
        apply htd
        rw [mul_eq_one_iff_eq_inv'] at h
        rw [h]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers d)
      have hdtT : d * t ∈ T := T.mul_mem hdT htT
      have hfix : ∀ ψ : π.ker, ((ψ : 𝒜) : MulAut V) d = d ∧ ((ψ : 𝒜) : MulAut V) t = t ∨
          ((ψ : 𝒜) : MulAut V) d = d⁻¹ ∧ ((ψ : 𝒜) : MulAut V) t = t⁻¹ := by
        intro ψ
        have hψ : linePerm T (Subgroup.inclusion h𝒜T ψ.1) = 1 := ψ.2
        have hmap : ∀ {x : V} (hx : x ∈ T) (hx1 : x ≠ 1),
            ((ψ : 𝒜) : MulAut V) x ∈ Subgroup.zpowers x := by
          intro x hx hx1
          have h1 := congrArg (fun P : Equiv.Perm (lineSet T) =>
            ((P ⟨Subgroup.zpowers x, hline hx hx1⟩ : lineSet T) : Subgroup V)) hψ
          change (Subgroup.zpowers x).map ((ψ : 𝒜) : MulAut V).toMonoidHom =
            Subgroup.zpowers x at h1
          rw [← h1]
          exact ⟨x, Subgroup.mem_zpowers x, rfl⟩
        exact fix_or_inv_of_lines hVc hV3 hd1 htd (hmap hdT hd1)
          (hmap htT (fun h => htd (h ▸ Subgroup.one_mem _))) (hmap hdtT hdt1)
      have hdinv : d⁻¹ ≠ d := by
        intro h
        apply hd1
        have h2 : d * d = 1 := by
          calc d * d = d⁻¹ * d := by rw [h]
            _ = 1 := inv_mul_cancel d
        calc d = d ^ 3 * (d * d)⁻¹ := by group
          _ = 1 := by rw [hV3 d, h2]; group
      let F : π.ker → Bool × T := fun ψ =>
        (decide (((ψ : 𝒜) : MulAut V) d = d),
          ⟨f'⁻¹ * ((ψ : 𝒜) : MulAut V) f', h𝒜T (ψ : 𝒜).2 f'⟩)
      have hF : Function.Injective F := by
        intro ψ₁ ψ₂ h12
        simp only [F, Prod.mk.injEq] at h12
        obtain ⟨hb, hf⟩ := h12
        have hf' : ((ψ₁ : 𝒜) : MulAut V) f' = ((ψ₂ : 𝒜) : MulAut V) f' :=
          mul_left_cancel (congrArg Subtype.val hf)
        have hdt : ((ψ₁ : 𝒜) : MulAut V) d = ((ψ₂ : 𝒜) : MulAut V) d ∧
            ((ψ₁ : 𝒜) : MulAut V) t = ((ψ₂ : 𝒜) : MulAut V) t := by
          rcases hfix ψ₁ with ⟨h1d, h1t⟩ | ⟨h1d, h1t⟩ <;>
            rcases hfix ψ₂ with ⟨h2d, h2t⟩ | ⟨h2d, h2t⟩
          · exact ⟨by rw [h1d, h2d], by rw [h1t, h2t]⟩
          · exfalso
            rw [h1d, h2d] at hb
            simp [hdinv] at hb
          · exfalso
            rw [h1d, h2d] at hb
            simp [hdinv] at hb
          · exact ⟨by rw [h1d, h2d], by rw [h1t, h2t]⟩
        apply Subtype.ext
        apply Subtype.ext
        exact hdet hdt.1 hdt.2 hf'
      have h1 := Nat.card_le_card_of_injective F hF
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, hT9] at h1
      exact h1
    calc Nat.card 𝒜 = Nat.card π.range * Nat.card π.ker := hcard.symm
      _ ≤ 12 * 18 := Nat.mul_le_mul hrange12 hker18
      _ = 216 := by norm_num
  have hpos : 0 < Nat.card 𝒜 := Nat.card_pos
  obtain ⟨m, hm⟩ := hlow
  have hm1 : m = 1 := by
    rcases m with _ | _ | m
    · omega
    · rfl
    · omega
  rw [hm, hm1]

end Main

end CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof
