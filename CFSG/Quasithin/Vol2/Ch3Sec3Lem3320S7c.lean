module

public import CFSG.Quasithin.Vol2.Ch3Sec3InputsA131
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324Main

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.ASInputs
open scoped commutatorElement

namespace S3320

variable {G : Type} [Group G]

section Sec

variable {U V K : Subgroup G}

theorem map_conj_subgroupOf {x : G} (hxU : x ∈ Subgroup.normalizer (U : Set G))
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) :
    (V.subgroupOf U).map (U.normalizerMonoidHom ⟨x, hxU⟩ : ↥U →* ↥U) = V.subgroupOf U := by
  have hmem : ∀ a : ↥U, (U.normalizerMonoidHom ⟨x, hxU⟩ a : ↥U) ∈ V.subgroupOf U ↔
      a ∈ V.subgroupOf U := by
    intro a
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp hxV a).symm
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (hmem b).mpr hb
  · intro ha
    refine ⟨(U.normalizerMonoidHom ⟨x, hxU⟩).symm a, ?_, MulEquiv.apply_symm_apply _ a⟩
    show (U.normalizerMonoidHom ⟨x, hxU⟩).symm a ∈ V.subgroupOf U
    rw [← hmem, MulEquiv.apply_symm_apply]
    exact ha

noncomputable def secAut [(V.subgroupOf U).Normal] (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) : ↥K →* MulAut (↥U ⧸ V.subgroupOf U) where
  toFun x := QuotientGroup.congr _ _ (U.normalizerMonoidHom ⟨x, hKU x.2⟩)
    (map_conj_subgroupOf (hKU x.2) (hKV x.2))
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [QuotientGroup.congr_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      show ((1 : ↥K) : G) * a * ((1 : ↥K) : G)⁻¹ = a
      simp
  map_mul' := fun x y => by
    ext q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk]
      congr 1
      apply Subtype.ext
      show (x * y : G) * a * (x * y : G)⁻¹ = (x : G) * ((y : G) * a * (y : G)⁻¹) * (x : G)⁻¹
      group

theorem secAut_mk [(V.subgroupOf U).Normal] (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (x : ↥K) (a : ↥U) :
    secAut hKU hKV x (a : ↥U ⧸ V.subgroupOf U) =
      ((⟨(x : G) * a * (x : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKU x.2) a).mp a.2⟩ : ↥U) :
        ↥U ⧸ V.subgroupOf U) :=
  QuotientGroup.congr_mk _ _ _ (map_conj_subgroupOf (hKU x.2) (hKV x.2)) a

theorem secAut_mk_eq_iff [(V.subgroupOf U).Normal] (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (x : ↥K) (a : ↥U) :
    secAut hKU hKV x (a : ↥U ⧸ V.subgroupOf U) = (a : ↥U ⧸ V.subgroupOf U) ↔
      (a : G)⁻¹ * ((x : G) * a * (x : G)⁻¹) ∈ V := by
  rw [secAut_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have := V.inv_mem h
    simpa [mul_assoc] using this
  · intro h
    have := V.inv_mem h
    simpa [mul_assoc] using this

theorem isPGroup_section [(V.subgroupOf U).Normal] {p : ℕ}
    (hUp : ∀ u ∈ U, ∃ k : ℕ, u ^ p ^ k ∈ V) : IsPGroup p (↥U ⧸ V.subgroupOf U) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H a =>
    obtain ⟨k, hk⟩ := hUp a a.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hk

variable [Finite G]

theorem exists_fixed_section {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hVU : V < U)
    (hUV : U ≤ Subgroup.normalizer (V : Set G)) (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (hPV : P ≤ Subgroup.normalizer (V : Set G)) (hP : IsPGroup p P)
    (hUp : ∀ u ∈ U, ∃ k : ℕ, u ^ p ^ k ∈ V) :
    ∃ u ∈ U, u ∉ V ∧ ∀ q ∈ P, u⁻¹ * (q * u * q⁻¹) ∈ V := by
  have : (V.subgroupOf U).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUV
  let _ : MulAction ↥P (↥U ⧸ V.subgroupOf U) := MulAction.compHom _ (secAut hPU hPV)
  have hW := isPGroup_section (U := U) (V := V) hUp
  obtain ⟨u₀, hu₀U, hu₀V⟩ : ∃ u ∈ U, u ∉ V := by
    by_contra h
    push Not at h
    exact (not_le_of_gt hVU) fun u hu => h u hu
  have hnt : (⟨u₀, hu₀U⟩ : ↥U) ∉ V.subgroupOf U := hu₀V
  have hcard : p ∣ Nat.card (↥U ⧸ V.subgroupOf U) := by
    rcases hW.card_eq_or_dvd with h | h
    · exfalso
      apply hnt
      have : Subsingleton (↥U ⧸ V.subgroupOf U) := (Nat.card_eq_one_iff_unique.mp h).1
      exact (QuotientGroup.eq_one_iff _).mp (Subsingleton.elim _ _)
    · exact h
  have h1 : (1 : ↥U ⧸ V.subgroupOf U) ∈ MulAction.fixedPoints ↥P (↥U ⧸ V.subgroupOf U) :=
    fun q => map_one (secAut hPU hPV q)
  obtain ⟨w, hw, hw1⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point _ hcard h1
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective w
  refine ⟨u, u.2, fun h => hw1 ((QuotientGroup.eq_one_iff u).mpr h).symm, fun q hq => ?_⟩
  have h2 : secAut hPU hPV ⟨q, hq⟩ (u : ↥U ⧸ V.subgroupOf U) = (u : ↥U ⧸ V.subgroupOf U) :=
    hw ⟨q, hq⟩
  exact (secAut_mk_eq_iff hPU hPV ⟨q, hq⟩ u).mp h2

theorem exists_dvd_two_pow_sub_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hUV : U ≤ Subgroup.normalizer (V : Set G)) {y : G}
    (hyU : y ∈ Subgroup.normalizer (U : Set G)) (hyV : y ∈ Subgroup.normalizer (V : Set G))
    (hy : orderOf y = p) (hmove : ∃ u ∈ U, u⁻¹ * (y * u * y⁻¹) ∉ V) {n : ℕ}
    (hn : V.relIndex U = 2 ^ n) : ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ p ∣ 2 ^ k - 1 := by
  have : (V.subgroupOf U).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUV
  have hKU : Subgroup.zpowers y ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.zpowers_le).mpr hyU
  have hKV : Subgroup.zpowers y ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.zpowers_le).mpr hyV
  have hKp : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  let φ := secAut hKU hKV
  let _ : MulAction ↥(Subgroup.zpowers y) (↥U ⧸ V.subgroupOf U) := MulAction.compHom _ φ
  have hmod := hKp.card_modEq_card_fixedPoints (↥U ⧸ V.subgroupOf U)
  let F : Subgroup (↥U ⧸ V.subgroupOf U) :=
    { carrier := MulAction.fixedPoints ↥(Subgroup.zpowers y) (↥U ⧸ V.subgroupOf U)
      mul_mem' := fun {a b} ha hb k => by
        show φ k (a * b) = a * b
        rw [map_mul]
        exact congrArg₂ (· * ·) (ha k) (hb k)
      one_mem' := fun k => map_one (φ k)
      inv_mem' := fun {a} ha k => by
        show φ k a⁻¹ = a⁻¹
        rw [map_inv]
        exact congrArg (·⁻¹) (ha k) }
  have hFcard : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers y) (↥U ⧸ V.subgroupOf U)) =
      Nat.card ↥F := rfl
  have hWcard : Nat.card (↥U ⧸ V.subgroupOf U) = 2 ^ n := hn
  obtain ⟨c, hc, hcF⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (hWcard ▸ Subgroup.card_subgroup_dvd_card F)
  have hcn : c < n := by
    rcases lt_or_eq_of_le hc with h | h
    · exact h
    · exfalso
      obtain ⟨u, huU, hu⟩ := hmove
      have hFtop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [hcF, hWcard, h])
      have h1 : ((⟨u, huU⟩ : ↥U) : ↥U ⧸ V.subgroupOf U) ∈ F := hFtop ▸ Subgroup.mem_top _
      exact hu ((secAut_mk_eq_iff hKU hKV ⟨y, Subgroup.mem_zpowers y⟩ ⟨u, huU⟩).mp
        (h1 ⟨y, Subgroup.mem_zpowers y⟩))
  refine ⟨n - c, by omega, by omega, ?_⟩
  rw [hFcard, hcF, hWcard] at hmod
  have h1 : p ∣ 2 ^ n - 2 ^ c :=
    (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by norm_num) hc)).mp hmod.symm
  have h2 : 2 ^ n - 2 ^ c = 2 ^ c * (2 ^ (n - c) - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hc]
  rw [h2] at h1
  have hcop : Nat.Coprime p (2 ^ c) :=
    Nat.Coprime.pow_right c ((Nat.coprime_primes Fact.out Nat.prime_two).mpr hp2)
  exact hcop.dvd_of_dvd_mul_left h1

theorem not_dvd_two_pow_sub_one {p k : ℕ} (hp : p.Prime) (hp24 : p % 24 = 11 ∨ p % 24 = 13)
    (hk : 1 ≤ k) (hk9 : k ≤ 9) : ¬ p ∣ 2 ^ k - 1 := by
  have hm : ∀ q : ℕ, q.Prime → p ∣ q → p % 24 = q % 24 := fun q hq hpq => by
    rw [(Nat.prime_dvd_prime_iff_eq hp hq).mp hpq]
  intro h
  interval_cases k
  · norm_num at h
    exact hp.one_lt.ne' h
  · norm_num at h
    have := hm 3 Nat.prime_three h
    omega
  · norm_num at h
    have := hm 7 (by norm_num) h
    omega
  · rw [show 2 ^ 4 - 1 = 3 * 5 by norm_num] at h
    rcases hp.dvd_mul.mp h with h | h
    · have := hm 3 Nat.prime_three h
      omega
    · have := hm 5 (by norm_num) h
      omega
  · norm_num at h
    have := hm 31 (by norm_num) h
    omega
  · rw [show 2 ^ 6 - 1 = 3 * 3 * 7 by norm_num] at h
    rcases hp.dvd_mul.mp h with h | h
    · rcases hp.dvd_mul.mp h with h | h <;>
      · have := hm 3 Nat.prime_three h
        omega
    · have := hm 7 (by norm_num) h
      omega
  · norm_num at h
    have := hm 127 (by norm_num) h
    omega
  · rw [show 2 ^ 8 - 1 = 3 * 5 * 17 by norm_num] at h
    rcases hp.dvd_mul.mp h with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · have := hm 3 Nat.prime_three h
        omega
      · have := hm 5 (by norm_num) h
        omega
    · have := hm 17 (by norm_num) h
      omega
  · rw [show 2 ^ 9 - 1 = 7 * 73 by norm_num] at h
    rcases hp.dvd_mul.mp h with h | h
    · have := hm 7 (by norm_num) h
      omega
    · have := hm 73 (by norm_num) h
      omega

end Sec

section Fix

variable {U V S : Subgroup G}

def fixSub (U V S : Subgroup G) (hUV : U ≤ Subgroup.normalizer (V : Set G)) : Subgroup G where
  carrier := {u | u ∈ U ∧ ∀ z ∈ S, u⁻¹ * (z * u * z⁻¹) ∈ V}
  mul_mem' := by
    rintro a b ⟨haU, ha⟩ ⟨hbU, hb⟩
    refine ⟨U.mul_mem haU hbU, fun z hz => ?_⟩
    have h1 : b⁻¹ * (a⁻¹ * (z * a * z⁻¹)) * b ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hUV (U.inv_mem hbU)) _).mp (ha z hz)
      simpa using this
    have e : (a * b)⁻¹ * (z * (a * b) * z⁻¹) =
        (b⁻¹ * (a⁻¹ * (z * a * z⁻¹)) * b) * (b⁻¹ * (z * b * z⁻¹)) := by group
    rw [e]
    exact V.mul_mem h1 (hb z hz)
  one_mem' := ⟨U.one_mem, fun z _ => by simp⟩
  inv_mem' := by
    rintro a ⟨haU, ha⟩
    refine ⟨U.inv_mem haU, fun z hz => ?_⟩
    have h1 : a * (a⁻¹ * (z * a * z⁻¹))⁻¹ * a⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hUV haU) _).mp (V.inv_mem (ha z hz))
    have e : a⁻¹⁻¹ * (z * a⁻¹ * z⁻¹) = a * (a⁻¹ * (z * a * z⁻¹))⁻¹ * a⁻¹ := by group
    rw [e]
    exact h1

theorem mem_fixSub {hUV : U ≤ Subgroup.normalizer (V : Set G)} {u : G} :
    u ∈ fixSub U V S hUV ↔ u ∈ U ∧ ∀ z ∈ S, u⁻¹ * (z * u * z⁻¹) ∈ V := Iff.rfl

theorem fixSub_le (hUV : U ≤ Subgroup.normalizer (V : Set G)) : fixSub U V S hUV ≤ U :=
  fun _ h => h.1

theorem le_fixSub (hUV : U ≤ Subgroup.normalizer (V : Set G)) (hVU : V ≤ U)
    (hSV : S ≤ Subgroup.normalizer (V : Set G)) : V ≤ fixSub U V S hUV := by
  intro v hv
  refine ⟨hVU hv, fun z hz => V.mul_mem (V.inv_mem hv) ?_⟩
  exact (Subgroup.mem_normalizer_iff.mp (hSV hz) v).mp hv

theorem le_normalizer_fixSub (hUV : U ≤ Subgroup.normalizer (V : Set G)) :
    Subgroup.normalizer (U : Set G) ⊓ Subgroup.normalizer (V : Set G) ⊓
      Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (fixSub U V S hUV : Set G) := by
  refine Main3324.le_normalizer_of_conj fun y hy u hu => ⟨?_, fun z hz => ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hy.1.1 u).mp hu.1
  · have hz' : y⁻¹ * z * y ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy.2) z).mp hz
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.mp hy.1.2 _).mp (hu.2 _ hz')
    have e : (y * u * y⁻¹)⁻¹ * (z * (y * u * y⁻¹) * z⁻¹) =
        y * (u⁻¹ * (y⁻¹ * z * y * u * (y⁻¹ * z * y)⁻¹)) * y⁻¹ := by group
    rw [e]
    exact h1

theorem commutator_le_of_fixSub_eq {hUV : U ≤ Subgroup.normalizer (V : Set G)}
    (h : fixSub U V S hUV = U) : ⁅U, S⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro u hu z hz
  have h1 := ((h.symm ▸ U.inv_mem hu : u⁻¹ ∈ fixSub U V S hUV)).2 z hz
  have e : ⁅u, z⁆ = u⁻¹⁻¹ * (z * u⁻¹ * z⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact h1

end Fix

section Stab

variable {U V : Subgroup G}

def stabSub (V : Subgroup G) (u : G) : Subgroup G where
  carrier := {z | z ∈ Subgroup.normalizer (V : Set G) ∧ u⁻¹ * (z * u * z⁻¹) ∈ V}
  mul_mem' := by
    rintro z₁ z₂ ⟨h₁N, h₁⟩ ⟨h₂N, h₂⟩
    refine ⟨Subgroup.mul_mem _ h₁N h₂N, ?_⟩
    have h3 : z₁ * (u⁻¹ * (z₂ * u * z₂⁻¹)) * z₁⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp h₁N _).mp h₂
    have e : u⁻¹ * (z₁ * z₂ * u * (z₁ * z₂)⁻¹) =
        (u⁻¹ * (z₁ * u * z₁⁻¹)) * (z₁ * (u⁻¹ * (z₂ * u * z₂⁻¹)) * z₁⁻¹) := by group
    rw [e]
    exact V.mul_mem h₁ h3
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  inv_mem' := by
    rintro z ⟨hN, h⟩
    refine ⟨Subgroup.inv_mem _ hN, ?_⟩
    have h3 : z⁻¹ * (u⁻¹ * (z * u * z⁻¹))⁻¹ * z⁻¹⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hN) _).mp (V.inv_mem h)
    have e : u⁻¹ * (z⁻¹ * u * z⁻¹⁻¹) = z⁻¹ * (u⁻¹ * (z * u * z⁻¹))⁻¹ * z⁻¹⁻¹ := by group
    rw [e]
    exact h3

theorem mem_stabSub {u z : G} :
    z ∈ stabSub V u ↔ z ∈ Subgroup.normalizer (V : Set G) ∧ u⁻¹ * (z * u * z⁻¹) ∈ V := Iff.rfl

theorem mem_fixSub_zpowers {hUV : U ≤ Subgroup.normalizer (V : Set G)} {x u : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) :
    u ∈ fixSub U V (Subgroup.zpowers x) hUV ↔ u ∈ U ∧ u⁻¹ * (x * u * x⁻¹) ∈ V := by
  constructor
  · rintro ⟨hu, h⟩
    exact ⟨hu, h x (Subgroup.mem_zpowers x)⟩
  · rintro ⟨hu, h⟩
    have hle : Subgroup.zpowers x ≤ stabSub V u := (Subgroup.zpowers_le).mpr ⟨hxV, h⟩
    exact ⟨hu, fun z hz => (hle hz).2⟩

end Stab

section Chief

variable {Y U V : Subgroup G}

theorem chief_eq (hc : IsTwoChiefFactor Y U V) {C : Subgroup G} (hVC : V ≤ C) (hCU : C ≤ U)
    (hYC : Y ≤ Subgroup.normalizer (C : Set G)) (hne : C ≠ V) : C = U := by
  by_contra h
  exact hc.2.2.2.2.1 C (lt_of_le_of_ne hVC (Ne.symm hne)) (lt_of_le_of_ne hCU h) hYC

theorem exists_mem_not_mem (hc : IsTwoChiefFactor Y U V) : ∃ u ∈ U, u ∉ V := by
  by_contra h
  push Not at h
  exact (not_le_of_gt hc.1) fun u hu => h u hu

variable [Finite G]

theorem commutator_le_of_chief (hc : IsTwoChiefFactor Y U V) : ⁅U, U⁆ ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUV : U ≤ Subgroup.normalizer (V : Set G) := hc.2.1.trans hc.2.2.2.1
  have : (V.subgroupOf U).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUV
  have hW := isPGroup_section (p := 2) (U := U) (V := V) hc.2.2.2.2.2
  obtain ⟨u₀, hu₀U, hu₀V⟩ := exists_mem_not_mem hc
  have : Nontrivial (↥U ⧸ V.subgroupOf U) :=
    ⟨⟨((⟨u₀, hu₀U⟩ : ↥U) : ↥U ⧸ V.subgroupOf U), 1,
      fun h => hu₀V ((QuotientGroup.eq_one_iff (N := V.subgroupOf U)
        (⟨u₀, hu₀U⟩ : ↥U)).mp h)⟩⟩
  have := hW.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center (↥U ⧸ V.subgroupOf U)))
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (z : ↥U ⧸ V.subgroupOf U)
  have hfix : (u : G) ∈ fixSub U V U hUV := by
    refine ⟨u.2, fun u' hu' => ?_⟩
    have h1 := (Subgroup.mem_center_iff.mp z.2) ((⟨u', hu'⟩ : ↥U) : ↥U ⧸ V.subgroupOf U)
    rw [← hu] at h1
    have h2 : ((u : ↥U) : ↥U ⧸ V.subgroupOf U) =
        ((⟨u', hu'⟩ * u * (⟨u', hu'⟩ : ↥U)⁻¹ : ↥U) : ↥U ⧸ V.subgroupOf U) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1,
        mul_inv_cancel_right]
    have h3 := QuotientGroup.eq.mp h2
    rw [Subgroup.mem_subgroupOf] at h3
    simpa using h3
  have hne : fixSub U V U hUV ≠ V := by
    intro h
    rw [h] at hfix
    apply hz
    apply Subtype.ext
    rw [← hu]
    exact (QuotientGroup.eq_one_iff u).mpr hfix
  have hYC : Y ≤ Subgroup.normalizer (fixSub U V U hUV : Set G) :=
    (le_inf (le_inf hc.2.2.1 hc.2.2.2.1) hc.2.2.1).trans (le_normalizer_fixSub hUV)
  exact commutator_le_of_fixSub_eq
    (chief_eq hc (le_fixSub hUV hc.1.le hUV) (fixSub_le hUV) hYC hne)

theorem sq_mem_of_chief (hc : IsTwoChiefFactor Y U V) : ∀ u ∈ U, u * u ∈ V := by
  have hUV : U ≤ Subgroup.normalizer (V : Set G) := hc.2.1.trans hc.2.2.2.1
  have hcomm := commutator_le_of_chief hc
  let C : Subgroup G :=
    { carrier := {u | u ∈ U ∧ u * u ∈ V}
      mul_mem' := by
        rintro a b ⟨haU, ha⟩ ⟨hbU, hb⟩
        refine ⟨U.mul_mem haU hbU, ?_⟩
        have h1 : a * ⁅b, a⁆ * a⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.mp (hUV haU) _).mp
            (hcomm (Subgroup.commutator_mem_commutator hbU haU))
        have e : a * b * (a * b) = (a * ⁅b, a⁆ * a⁻¹) * (a * a * (b * b)) := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact V.mul_mem h1 (V.mul_mem ha hb)
      one_mem' := ⟨U.one_mem, by simp⟩
      inv_mem' := by
        rintro a ⟨haU, ha⟩
        refine ⟨U.inv_mem haU, ?_⟩
        have := V.inv_mem ha
        simpa using this }
  have hVC : V ≤ C := fun v hv => ⟨hc.1.le hv, V.mul_mem hv hv⟩
  have hCU : C ≤ U := fun _ h => h.1
  have hYC : Y ≤ Subgroup.normalizer (C : Set G) := by
    refine Main3324.le_normalizer_of_conj fun y hy c hc' => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hc.2.2.1 hy) c).mp hc'.1
    · have := (Subgroup.mem_normalizer_iff.mp (hc.2.2.2.1 hy) _).mp hc'.2
      have e : y * c * y⁻¹ * (y * c * y⁻¹) = y * (c * c) * y⁻¹ := by group
      rw [e]
      exact this
  have hne : C ≠ V := by
    classical
    obtain ⟨u₀, hu₀U, hu₀V⟩ := exists_mem_not_mem hc
    have hex : ∃ k : ℕ, u₀ ^ 2 ^ k ∈ V := hc.2.2.2.2.2 u₀ hu₀U
    have hk₀ : u₀ ^ 2 ^ Nat.find hex ∈ V := Nat.find_spec hex
    have hk₀0 : Nat.find hex ≠ 0 := by
      intro h
      rw [h, pow_zero, pow_one] at hk₀
      exact hu₀V hk₀
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk₀0
    have hj' : u₀ ^ 2 ^ j ∉ V := Nat.find_min hex (by omega)
    intro h
    apply hj'
    have hmem : u₀ ^ 2 ^ j ∈ C := by
      refine ⟨U.pow_mem hu₀U _, ?_⟩
      rw [← pow_add, ← two_mul, ← pow_succ']
      rw [hj] at hk₀
      exact hk₀
    rw [h] at hmem
    exact hmem
  have heq := chief_eq hc hVC hCU hYC hne
  intro u hu
  have hu' : u ∈ C := heq ▸ hu
  exact hu'.2

theorem commutator_pCoreOf_le_of_chief (hc : IsTwoChiefFactor Y U V) :
    ⁅U, pCoreOf 2 Y⁆ ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUV : U ≤ Subgroup.normalizer (V : Set G) := hc.2.1.trans hc.2.2.2.1
  have hPY : pCoreOf 2 Y ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  obtain ⟨u, huU, huV, hu⟩ := exists_fixed_section (p := 2) hc.1 hUV (hPY.trans hc.2.2.1)
    (hPY.trans hc.2.2.2.1) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) hc.2.2.2.2.2
  have hYC : Y ≤ Subgroup.normalizer (fixSub U V (pCoreOf 2 Y) hUV : Set G) :=
    (le_inf (le_inf hc.2.2.1 hc.2.2.2.1) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)).trans
      (le_normalizer_fixSub hUV)
  have hne : fixSub U V (pCoreOf 2 Y) hUV ≠ V := fun h => huV (h ▸ ⟨huU, hu⟩)
  exact commutator_le_of_fixSub_eq
    (chief_eq hc (le_fixSub hUV hc.1.le (hPY.trans hc.2.2.2.1)) (fixSub_le hUV) hYC hne)

end Chief

section SecNC

@[expose] def IsSecNC (X A B : Subgroup G) : Prop :=
  B < A ∧ A ≤ Subgroup.normalizer (B : Set G) ∧ X ≤ Subgroup.normalizer (A : Set G) ∧
    X ≤ Subgroup.normalizer (B : Set G) ∧
    (∀ C : Subgroup G, B < C → C < A → ¬ X ≤ Subgroup.normalizer (C : Set G)) ∧
    (∀ a ∈ A, ∃ k : ℕ, a ^ 2 ^ k ∈ B) ∧ ¬ ⁅A, X⁆ ≤ B

@[expose] def HasSecNC (X N₁ N₂ : Subgroup G) (k : ℕ) : Prop :=
  ∃ A B : Fin k → Subgroup G, (∀ i, IsSecNC X (A i) (B i) ∧ N₁ ≤ B i ∧ A i ≤ N₂) ∧
    ∀ i j, i < j → A i ≤ B j

theorem inf_X_factor {X A B : Subgroup G} (h : IsSecNC X A B)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    IsTwoChiefFactor X (A ⊓ X) (B ⊓ X) ∧ ¬ ⁅A ⊓ X, X⁆ ≤ B ⊓ X := by
  obtain ⟨hBA, hAB, hXA, hXB, hmin, h2, hn⟩ := h
  have hXAN : X ≤ Subgroup.normalizer ((A ⊓ X : Subgroup G) : Set G) := fun x hx =>
    ChiefCount.mem_normalizer_inf (hXA hx) (Subgroup.le_normalizer hx)
  have hXBN : X ≤ Subgroup.normalizer ((B ⊓ X : Subgroup G) : Set G) := fun x hx =>
    ChiefCount.mem_normalizer_inf (hXB hx) (Subgroup.le_normalizer hx)
  have hANB : A ⊓ X ≤ Subgroup.normalizer (B : Set G) := inf_le_left.trans hAB
  have hAXc : ⁅A, X⁆ ≤ A ⊓ X := le_inf (commutator_le_of_le_normalizer hXA)
    (by rw [Subgroup.commutator_comm]; exact commutator_le_of_le_normalizer hAX)
  have hin : ¬ A ⊓ X ≤ B := fun h => hn (hAXc.trans h)
  have hABe : (A ⊓ X) ⊔ B = A := by
    by_contra hne
    refine hmin ((A ⊓ X) ⊔ B) (lt_of_le_of_ne le_sup_right fun h => hin ?_)
      (lt_of_le_of_ne (sup_le inf_le_left hBA.le) hne) fun x hx =>
        ChiefCount.mem_normalizer_sup (hXAN hx) (hXB hx)
    rw [h]
    exact le_sup_left
  refine ⟨⟨lt_of_le_of_ne (inf_le_inf_right X hBA.le) fun h => hin (h ▸ inf_le_left),
    inf_le_right, hXAN, hXBN, fun C hC1 hC2 hXC => ?_, fun a ha => ?_⟩, fun hle => ?_⟩
  · have hCX : C ≤ X := hC2.le.trans inf_le_right
    have hCB : C ≤ Subgroup.normalizer (B : Set G) := hC2.le.trans hANB
    by_cases h1 : C ⊔ B = B
    · exact (not_le_of_gt hC1) (le_inf (h1 ▸ le_sup_left) hCX)
    by_cases h3 : C ⊔ B = A
    · apply (not_le_of_gt hC2)
      have h4 : X ⊓ (C ⊔ B) ≤ C ⊔ (X ⊓ B) := inf_sup_le hCX hCB
      rw [h3, inf_comm X A, inf_comm X B] at h4
      exact h4.trans (sup_le le_rfl hC1.le)
    exact hmin (C ⊔ B) (lt_of_le_of_ne le_sup_right (Ne.symm h1))
      (lt_of_le_of_ne (sup_le (hC2.le.trans inf_le_left) hBA.le) h3) fun x hx =>
        ChiefCount.mem_normalizer_sup (hXC hx) (hXB hx)
  · obtain ⟨k, hk⟩ := h2 a ha.1
    exact ⟨k, hk, X.pow_mem ha.2 _⟩
  · apply hn
    rw [← hABe]
    exact commutator_sup_le (hle.trans inf_le_left) hXB hANB

theorem hasNoncentralTwoChief_of_hasSecNC {X N₁ N₂ : Subgroup G} {k : ℕ}
    (h : HasSecNC X N₁ N₂ k) (hN₂ : N₂ ≤ Subgroup.normalizer (X : Set G)) :
    HasNoncentralTwoChief X k := by
  obtain ⟨A, B, hAB, hle⟩ := h
  exact ⟨fun i => A i ⊓ X, fun i => B i ⊓ X, fun i => inf_X_factor (hAB i).1
    ((hAB i).2.2.trans hN₂), fun i j hij => inf_le_inf_right X (hle i j hij)⟩

theorem HasSecNC.cons {X N₁ N₂ A₀ B₀ : Subgroup G} {k : ℕ} (h₀ : IsSecNC X A₀ B₀)
    (h₁ : N₁ ≤ B₀) (h₂ : A₀ ≤ N₂) (h : HasSecNC X A₀ N₂ k) : HasSecNC X N₁ N₂ (k + 1) := by
  obtain ⟨A, B, hAB, hle⟩ := h
  refine ⟨Fin.cons A₀ A, Fin.cons B₀ B, fun i => ?_, fun i j hij => ?_⟩
  · induction i using Fin.cases with
    | zero => exact ⟨h₀, h₁, h₂⟩
    | succ i =>
      obtain ⟨hc, hB, hA⟩ := hAB i
      exact ⟨hc, h₁.trans (h₀.1.le.trans hB), hA⟩
  · induction j using Fin.cases with
    | zero => exact absurd hij (Fin.not_lt_zero i)
    | succ j =>
      induction i using Fin.cases with
      | zero => exact (hAB j).2.1
      | succ i => exact hle i j (Fin.succ_lt_succ_iff.mp hij)

theorem HasSecNC.mono_left {X N₁ N₁' N₂ : Subgroup G} {k : ℕ} (h : HasSecNC X N₁ N₂ k)
    (h' : N₁' ≤ N₁) : HasSecNC X N₁' N₂ k := by
  obtain ⟨A, B, hAB, hle⟩ := h
  exact ⟨A, B, fun i => ⟨(hAB i).1, h'.trans (hAB i).2.1, (hAB i).2.2⟩, hle⟩

theorem HasSecNC.append {X N₁ M N₂ : Subgroup G} {k l : ℕ} (h₁ : HasSecNC X N₁ M k)
    (h₂ : HasSecNC X M N₂ l) (hN₁M : N₁ ≤ M) (hMN₂ : M ≤ N₂) :
    HasSecNC X N₁ N₂ (k + l) := by
  obtain ⟨A₁, B₁, hAB₁, hle₁⟩ := h₁
  obtain ⟨A₂, B₂, hAB₂, hle₂⟩ := h₂
  refine ⟨Fin.append A₁ A₂, Fin.append B₁ B₂, fun i => ?_, fun i j hij => ?_⟩
  · induction i using Fin.addCases with
    | left i =>
      rw [Fin.append_left, Fin.append_left]
      exact ⟨(hAB₁ i).1, (hAB₁ i).2.1, (hAB₁ i).2.2.trans hMN₂⟩
    | right i =>
      rw [Fin.append_right, Fin.append_right]
      exact ⟨(hAB₂ i).1, hN₁M.trans (hAB₂ i).2.1, (hAB₂ i).2.2⟩
  · induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j =>
        rw [Fin.append_left, Fin.append_left]
        refine hle₁ i j ?_
        rw [Fin.lt_def] at hij ⊢
        rw [Fin.val_castAdd, Fin.val_castAdd] at hij
        exact hij
      | right j =>
        rw [Fin.append_left, Fin.append_right]
        exact (hAB₁ i).2.2.trans (hAB₂ j).2.1
    | right i =>
      induction j using Fin.addCases with
      | left j =>
        exfalso
        rw [Fin.lt_def] at hij
        rw [Fin.val_natAdd, Fin.val_castAdd] at hij
        omega
      | right j =>
        rw [Fin.append_right, Fin.append_right]
        refine hle₂ i j ?_
        rw [Fin.lt_def] at hij ⊢
        rw [Fin.val_natAdd, Fin.val_natAdd] at hij
        omega

end SecNC

section Three

theorem mem_four_of_mem_closure {Q : Type*} [Group Q] {a b : Q} (ha : a * a = 1)
    (hb : b * b = 1) (hab : b * a = a * b) {g : Q}
    (hg : g ∈ Subgroup.closure ({a, b} : Set Q)) : g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
  have e4 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have e5 : b * (a * b) = a := by rw [← mul_assoc, hab, mul_assoc, hb, mul_one]
  have e6 : a * b * a = b := by rw [mul_assoc, hab, ← mul_assoc, ha, one_mul]
  have e7 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have e8 : a * b * (a * b) = 1 := by rw [← mul_assoc, e6, hb]
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul g h _ _ hg hh =>
    rcases hg with rfl | rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl | rfl <;>
      simp only [one_mul, mul_one, ha, hb, hab, e4, e5, e6, e7, e8, true_or, or_true]
  | inv g _ hg =>
    rcases hg with rfl | rfl | rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right ha))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hb)))
    · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right e8)))

variable [Finite G]

omit [Finite G] in
theorem le_normalizer_of_between {U V C : Subgroup G} (hcomm : ⁅U, U⁆ ≤ V) (hVC : V ≤ C)
    (hCU : C ≤ U) : U ≤ Subgroup.normalizer (C : Set G) := by
  refine Main3324.le_normalizer_of_conj fun u hu c hc => ?_
  have e : u * c * u⁻¹ = ⁅u, c⁆ * c := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact C.mul_mem (hVC (hcomm (Subgroup.commutator_mem_commutator hu (hCU hc)))) hc

theorem relIndex_fixSub_le {U V' V₁ : Subgroup G} {x : G}
    (hUV' : U ≤ Subgroup.normalizer (V' : Set G)) (hUV₁ : U ≤ Subgroup.normalizer (V₁ : Set G))
    (hV₁U : V₁ ≤ U) (hxV' : x ∈ Subgroup.normalizer (V' : Set G))
    (hxV₁ : x ∈ Subgroup.normalizer (V₁ : Set G)) (hcomm : ⁅U, U⁆ ≤ V') :
    (fixSub U V' (Subgroup.zpowers x) hUV').relIndex (fixSub U V₁ (Subgroup.zpowers x) hUV₁) ≤
      V'.relIndex V₁ := by
  have : (V'.subgroupOf V₁).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hV₁U.trans hUV')
  set F₁ := fixSub U V₁ (Subgroup.zpowers x) hUV₁ with hF₁
  have hm : ∀ u : ↥F₁, (u : G)⁻¹ * (x * u * x⁻¹) ∈ V₁ := fun u =>
    ((mem_fixSub_zpowers hxV₁).mp u.2).2
  have hmU : ∀ u : ↥F₁, (u : G)⁻¹ * (x * u * x⁻¹) ∈ U := fun u => hV₁U (hm u)
  let δ : ↥F₁ →* ↥V₁ ⧸ V'.subgroupOf V₁ :=
    { toFun := fun u => ((⟨(u : G)⁻¹ * (x * u * x⁻¹), hm u⟩ : ↥V₁) : ↥V₁ ⧸ V'.subgroupOf V₁)
      map_one' := by
        apply (QuotientGroup.eq_one_iff _).mpr
        rw [Subgroup.mem_subgroupOf]
        simp
      map_mul' := fun u v => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have hvU : (v : G) ∈ U := (v.2 : (v : G) ∈ F₁).1
        have h1 : ⁅((u : G)⁻¹ * (x * u * x⁻¹))⁻¹, (v : G)⁻¹⁆ ∈ V' :=
          hcomm (Subgroup.commutator_mem_commutator (U.inv_mem (hmU u)) (U.inv_mem hvU))
        have h2 := (Subgroup.mem_normalizer_iff.mp (hUV' (U.inv_mem (hmU v))) _).mp h1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        convert V'.inv_mem h2 using 1
        simp only [commutatorElement_def]
        group }
  have hker : δ.ker = (fixSub U V' (Subgroup.zpowers x) hUV').subgroupOf F₁ := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_fixSub_zpowers hxV']
    show ((⟨(u : G)⁻¹ * (x * u * x⁻¹), hm u⟩ : ↥V₁) : ↥V₁ ⧸ V'.subgroupOf V₁) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨(u.2 : (u : G) ∈ F₁).1, h⟩, fun h => h.2⟩
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, Subgroup.relIndex, Subgroup.index]
  exact Subgroup.card_le_card_group _

theorem exists_bottom_factor {U V' X : Subgroup G} {x : G} (hx3 : x ^ 3 = 1)
    (hV'U : V' ≤ U) (hUV : U ≤ Subgroup.normalizer (V' : Set G))
    (hxU : x ∈ Subgroup.normalizer (U : Set G)) (hxV : x ∈ Subgroup.normalizer (V' : Set G))
    (hXV : X ≤ Subgroup.normalizer (V' : Set G)) (hxX : x ∈ X) (hcomm : ⁅U, U⁆ ≤ V')
    (hsq : ∀ u ∈ U, u * u ∈ V')
    (hX : ∀ C : Subgroup G, V' ≤ C → C ≤ U → x ∈ Subgroup.normalizer (C : Set G) →
      X ≤ Subgroup.normalizer (C : Set G))
    {a : G} (haU : a ∈ U) (ha : a⁻¹ * (x * a * x⁻¹) ∉ V') :
    ∃ V₁ : Subgroup G, V' ≤ V₁ ∧ V₁ ≤ U ∧ IsSecNC X V₁ V' ∧ V'.relIndex V₁ ≤ 4 := by
  have : (V'.subgroupOf U).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUV
  have hWc : ∀ g h : ↥U ⧸ V'.subgroupOf U, h * g = g * h := by
    intro g h
    induction g using QuotientGroup.induction_on with
    | H u =>
      induction h using QuotientGroup.induction_on with
      | H v =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have h1 := hcomm (Subgroup.commutator_mem_commutator (U.inv_mem u.2) (U.inv_mem v.2))
        have e : (((v * u)⁻¹ * (u * v) : ↥U) : G) = ⁅(u : G)⁻¹, (v : G)⁻¹⁆ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, inv_inv]
          group
        rw [e]
        exact h1
  have hW2 : ∀ g : ↥U ⧸ V'.subgroupOf U, g * g = 1 := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H u =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hsq u u.2
  have hKU : Subgroup.zpowers x ≤ Subgroup.normalizer (U : Set G) := (Subgroup.zpowers_le).mpr hxU
  have hKV : Subgroup.zpowers x ≤ Subgroup.normalizer (V' : Set G) :=
    (Subgroup.zpowers_le).mpr hxV
  set σ := secAut hKU hKV ⟨x, Subgroup.mem_zpowers x⟩ with hσ
  have hσmk : ∀ (u : G) (hu : u ∈ U), σ ((⟨u, hu⟩ : ↥U) : ↥U ⧸ V'.subgroupOf U) =
      ((⟨x * u * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxU u).mp hu⟩ : ↥U) :
        ↥U ⧸ V'.subgroupOf U) := fun u hu => secAut_mk hKU hKV _ ⟨u, hu⟩
  set w := a⁻¹ * (x * a * x⁻¹) with hw
  have hwU : w ∈ U := U.mul_mem (U.inv_mem haU) ((Subgroup.mem_normalizer_iff.mp hxU a).mp haU)
  have hw₁U : x * w * x⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hxU w).mp hwU
  have hw₂U : x * (x * w * x⁻¹) * x⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hxU _).mp hw₁U
  have hxxx : x * x * x = 1 := by rw [← hx3, pow_three, mul_assoc]
  have htel : w * (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹) = 1 := by
    have e : w * (x * w * x⁻¹) * (x * (x * w * x⁻¹) * x⁻¹) =
        a⁻¹ * ((x * x * x) * a * (x * x * x)⁻¹) := by
      rw [hw]
      group
    rw [e, hxxx]
    group
  set α : ↥U ⧸ V'.subgroupOf U := ((⟨w, hwU⟩ : ↥U) : ↥U ⧸ V'.subgroupOf U) with hα
  set β : ↥U ⧸ V'.subgroupOf U := ((⟨_, hw₁U⟩ : ↥U) : ↥U ⧸ V'.subgroupOf U) with hβ
  have hσα : σ α = β := hσmk w hwU
  have hσβ : σ β = α * β := by
    rw [hσmk _ hw₁U]
    have h1 : α * β * ((⟨_, hw₂U⟩ : ↥U) : ↥U ⧸ V'.subgroupOf U) = 1 := by
      rw [hα, hβ, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul]
      rw [htel]
      exact V'.one_mem
    have h2 := eq_inv_of_mul_eq_one_right h1
    rw [h2, mul_inv_rev, inv_eq_of_mul_eq_one_right (hW2 β),
      inv_eq_of_mul_eq_one_right (hW2 α), hWc]
  have hσαβ : σ (α * β) = α := by
    rw [map_mul, hσα, hσβ, ← mul_assoc, hWc α β, mul_assoc, hW2, mul_one]
  have hα1 : α ≠ 1 := fun h => ha ((QuotientGroup.eq_one_iff (N := V'.subgroupOf U)
    (⟨w, hwU⟩ : ↥U)).mp h)
  have hαβ : α ≠ β := by
    intro h
    apply hα1
    have h1 : σ β = α := by rw [← h, hσα, ← h]
    rw [hσβ, ← h, hW2] at h1
    exact h1.symm
  set Lb := Subgroup.closure ({α, β} : Set (↥U ⧸ V'.subgroupOf U)) with hLb
  have hαL : α ∈ Lb := Subgroup.subset_closure (Set.mem_insert _ _)
  have hβL : β ∈ Lb := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hfour : ∀ g ∈ Lb, g = 1 ∨ g = α ∨ g = β ∨ g = α * β := fun g hg =>
    mem_four_of_mem_closure (hW2 α) (hW2 β) (hWc α β) hg
  have hσL : ∀ g ∈ Lb, σ g ∈ Lb := by
    intro g hg
    rcases hfour g hg with rfl | rfl | rfl | rfl
    · rw [map_one]
      exact Lb.one_mem
    · rw [hσα]
      exact hβL
    · rw [hσβ]
      exact Lb.mul_mem hαL hβL
    · rw [hσαβ]
      exact hαL
  set V₁ := (Lb.comap (QuotientGroup.mk' (V'.subgroupOf U))).map U.subtype with hV₁
  have hmemV₁ : ∀ g : G, g ∈ V₁ ↔ ∃ hg : g ∈ U,
      ((⟨g, hg⟩ : ↥U) : ↥U ⧸ V'.subgroupOf U) ∈ Lb := by
    intro g
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, hu⟩
    · rintro ⟨hg, h⟩
      exact ⟨⟨g, hg⟩, h, rfl⟩
  have hV'V₁ : V' ≤ V₁ := fun v hv => (hmemV₁ v).mpr ⟨hV'U hv, by
    rw [(QuotientGroup.eq_one_iff (N := V'.subgroupOf U) (⟨v, hV'U hv⟩ : ↥U)).mpr hv]
    exact Lb.one_mem⟩
  have hV₁U : V₁ ≤ U := Subgroup.map_subtype_le _
  have hwV₁ : w ∈ V₁ := (hmemV₁ w).mpr ⟨hwU, hαL⟩
  have hconj : ∀ g ∈ V₁, x * g * x⁻¹ ∈ V₁ := by
    intro g hg
    obtain ⟨hgU, hgL⟩ := (hmemV₁ g).mp hg
    refine (hmemV₁ _).mpr ⟨(Subgroup.mem_normalizer_iff.mp hxU g).mp hgU, ?_⟩
    rw [← hσmk g hgU]
    exact hσL _ hgL
  have hxV₁ : x ∈ Subgroup.normalizer (V₁ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨hconj g, fun h => ?_⟩
    have h1 := hconj _ (hconj _ h)
    have e : x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * g * (x * x * x)⁻¹ := by group
    rw [e, hxxx] at h1
    simpa using h1
  have hXV₁ : X ≤ Subgroup.normalizer (V₁ : Set G) := hX V₁ hV'V₁ hV₁U hxV₁
  refine ⟨V₁, hV'V₁, hV₁U, ⟨lt_of_le_of_ne hV'V₁ fun h => ha (h ▸ hwV₁), hV₁U.trans hUV,
    hXV₁, hXV, fun C hC1 hC2 hXC => ?_, fun g hg => ⟨1, ?_⟩, fun hle => ?_⟩, ?_⟩
  ·
    have hxC : x ∈ Subgroup.normalizer (C : Set G) := hXC hxX
    obtain ⟨c, hcC, hcV'⟩ : ∃ c ∈ C, c ∉ V' := by
      by_contra h
      push Not at h
      exact (not_le_of_gt hC1) fun c hc => h c hc
    obtain ⟨hcU, hcL⟩ := (hmemV₁ c).mp (hC2.le hcC)
    set Cb := (C.subgroupOf U).map (QuotientGroup.mk' (V'.subgroupOf U)) with hCb
    have hσC : ∀ g ∈ Cb, σ g ∈ Cb := by
      rintro g ⟨u, hu, rfl⟩
      refine ⟨⟨x * u * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxU u).mp u.2⟩,
        (Subgroup.mem_normalizer_iff.mp hxC u).mp hu, ?_⟩
      exact (hσmk u u.2).symm
    have hcCb : ((⟨c, hcU⟩ : ↥U) : ↥U ⧸ V'.subgroupOf U) ∈ Cb :=
      Subgroup.mem_map_of_mem _ (show (⟨c, hcU⟩ : ↥U) ∈ C.subgroupOf U from hcC)
    have hc1 : ((⟨c, hcU⟩ : ↥U) : ↥U ⧸ V'.subgroupOf U) ≠ 1 := fun h =>
      hcV' ((QuotientGroup.eq_one_iff (N := V'.subgroupOf U) (⟨c, hcU⟩ : ↥U)).mp h)
    have hαβC : α ∈ Cb ∧ β ∈ Cb := by
      rcases hfour _ hcL with h | h | h | h
      · exact absurd h hc1
      · rw [h] at hcCb
        exact ⟨hcCb, hσα ▸ hσC _ hcCb⟩
      · rw [h] at hcCb
        have h1 := hσC _ hcCb
        rw [hσβ] at h1
        refine ⟨?_, hcCb⟩
        have e : α = α * β * β := by rw [mul_assoc, hW2, mul_one]
        rw [e]
        exact Cb.mul_mem h1 hcCb
      · rw [h] at hcCb
        have h1 := hσC _ hcCb
        rw [hσαβ] at h1
        refine ⟨h1, ?_⟩
        have e : β = α * (α * β) := by rw [← mul_assoc, hW2, one_mul]
        rw [e]
        exact Cb.mul_mem h1 hcCb
    have hLC : Lb ≤ Cb := (Subgroup.closure_le _).mpr (by
      rintro g (rfl | rfl)
      · exact hαβC.1
      · exact hαβC.2)
    apply (not_le_of_gt hC2)
    intro g hg
    obtain ⟨hgU, hgL⟩ := (hmemV₁ g).mp hg
    obtain ⟨u, hu, hug⟩ := hLC hgL
    have h1 := QuotientGroup.eq.mp hug
    have hu' : (u : G) ∈ C := hu
    have h1' : (u : G)⁻¹ * g ∈ V' := by
      rw [Subgroup.mem_subgroupOf] at h1
      simpa using h1
    have e : g = (u : G) * ((u : G)⁻¹ * g) := by group
    rw [e]
    exact C.mul_mem hu' (hC1.le h1')
  ·
    rw [pow_one, sq]
    exact hsq g (hV₁U hg)
  ·
    apply hαβ
    have h1 : ⁅w, x⁆ ∈ V' := hle (Subgroup.commutator_mem_commutator hwV₁ hxX)
    have h2 : w⁻¹ * (x * w * x⁻¹) ∈ V' := by
      have h3 := (Subgroup.mem_normalizer_iff.mp (hUV (U.inv_mem hwU)) _).mp (V'.inv_mem h1)
      have e : w⁻¹ * (x * w * x⁻¹) = w⁻¹ * ⁅w, x⁆⁻¹ * w⁻¹⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact h3
    rw [hα, hβ, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact h2
  ·
    let ψ : ↥V₁ →* ↥U ⧸ V'.subgroupOf U :=
      (QuotientGroup.mk' (V'.subgroupOf U)).comp (Subgroup.inclusion hV₁U)
    have hker : ψ.ker = V'.subgroupOf V₁ := by
      ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show ((Subgroup.inclusion hV₁U g : ↥U) : ↥U ⧸ V'.subgroupOf U) = 1 ↔ _
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rfl
    have hrange : ψ.range ≤ Lb := by
      rintro _ ⟨g, rfl⟩
      exact ((hmemV₁ g).mp g.2).2
    have hcardL : Nat.card ↥Lb ≤ 4 := by
      let f : Fin 4 → ↥Lb := ![⟨1, Lb.one_mem⟩, ⟨α, hαL⟩, ⟨β, hβL⟩, ⟨α * β, Lb.mul_mem hαL hβL⟩]
      have hf : Function.Surjective f := by
        rintro ⟨g, hg⟩
        rcases hfour g hg with rfl | rfl | rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨3, rfl⟩
      have := Nat.card_le_card_of_surjective f hf
      rwa [Nat.card_fin] at this
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
    exact (Subgroup.card_le_of_le hrange).trans hcardL

theorem hasSecNC_of_lt {U V X : Subgroup G} {x : G} (hx3 : x ^ 3 = 1)
    (hxU : x ∈ Subgroup.normalizer (U : Set G)) (hxX : x ∈ X)
    (hcomm : ⁅U, U⁆ ≤ V) (hsq : ∀ u ∈ U, u * u ∈ V)
    (hX : ∀ C : Subgroup G, V ≤ C → C ≤ U → x ∈ Subgroup.normalizer (C : Set G) →
      X ≤ Subgroup.normalizer (C : Set G)) :
    ∀ (c : ℕ) (V' : Subgroup G), V ≤ V' → V' ≤ U → ∀ hUV' : U ≤ Subgroup.normalizer (V' : Set G),
      X ≤ Subgroup.normalizer (V' : Set G) →
      4 ^ c < (fixSub U V' (Subgroup.zpowers x) hUV').relIndex U → HasSecNC X V' U (c + 1) := by
  have hmove : ∀ (V' : Subgroup G) (hUV' : U ≤ Subgroup.normalizer (V' : Set G)),
      x ∈ Subgroup.normalizer (V' : Set G) →
      1 < (fixSub U V' (Subgroup.zpowers x) hUV').relIndex U →
      ∃ a ∈ U, a⁻¹ * (x * a * x⁻¹) ∉ V' := by
    intro V' hUV' hxV' hlt
    by_contra h
    push Not at h
    have heq : fixSub U V' (Subgroup.zpowers x) hUV' = U :=
      le_antisymm (fixSub_le hUV') fun u hu => (mem_fixSub_zpowers hxV').mpr ⟨hu, h u hu⟩
    rw [heq, Subgroup.relIndex_self] at hlt
    exact lt_irrefl 1 hlt
  intro c
  induction c with
  | zero =>
    intro V' hV hV'U hUV' hXV' hlt
    obtain ⟨a, haU, ha⟩ := hmove V' hUV' (hXV' hxX) (by simpa using hlt)
    obtain ⟨V₁, hV'V₁, hV₁U, hsec, -⟩ := exists_bottom_factor hx3 hV'U hUV' hxU (hXV' hxX) hXV'
      hxX (hcomm.trans hV) (fun u hu => hV (hsq u hu)) (fun C h1 h2 h3 => hX C (hV.trans h1) h2 h3)
      haU ha
    exact HasSecNC.cons hsec le_rfl hV₁U ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ c ih =>
    intro V' hV hV'U hUV' hXV' hlt
    have h1 : 1 < (fixSub U V' (Subgroup.zpowers x) hUV').relIndex U :=
      lt_of_le_of_lt (Nat.one_le_pow _ _ (by norm_num)) hlt
    obtain ⟨a, haU, ha⟩ := hmove V' hUV' (hXV' hxX) h1
    obtain ⟨V₁, hV'V₁, hV₁U, hsec, h4⟩ := exists_bottom_factor hx3 hV'U hUV' hxU (hXV' hxX) hXV'
      hxX (hcomm.trans hV) (fun u hu => hV (hsq u hu)) (fun C h1 h2 h3 => hX C (hV.trans h1) h2 h3)
      haU ha
    have hUV₁ : U ≤ Subgroup.normalizer (V₁ : Set G) :=
      le_normalizer_of_between hcomm (hV.trans hV'V₁) hV₁U
    have hXV₁ : X ≤ Subgroup.normalizer (V₁ : Set G) := hsec.2.2.1
    have hF : fixSub U V' (Subgroup.zpowers x) hUV' ≤ fixSub U V₁ (Subgroup.zpowers x) hUV₁ :=
      fun u hu => ⟨hu.1, fun z hz => hV'V₁ (hu.2 z hz)⟩
    have hidx := Subgroup.relIndex_mul_relIndex (fixSub U V' (Subgroup.zpowers x) hUV')
      (fixSub U V₁ (Subgroup.zpowers x) hUV₁) U hF (fixSub_le hUV₁)
    have hstep := relIndex_fixSub_le hUV' hUV₁ hV₁U (hXV' hxX) (hXV₁ hxX) (hcomm.trans hV)
    have hlt' : 4 ^ c < (fixSub U V₁ (Subgroup.zpowers x) hUV₁).relIndex U := by
      by_contra h
      push Not at h
      have h5 : (fixSub U V' (Subgroup.zpowers x) hUV').relIndex U ≤ 4 * 4 ^ c := by
        rw [← hidx]
        exact Nat.mul_le_mul (hstep.trans h4) h
      rw [pow_succ] at hlt
      omega
    exact HasSecNC.cons hsec le_rfl hV₁U (ih V₁ (hV.trans hV'V₁) hV₁U hUV₁ hXV₁ hlt')

end Three

end S3320

end CFSG.Quasithin.H13
