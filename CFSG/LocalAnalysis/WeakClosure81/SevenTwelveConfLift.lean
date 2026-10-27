module

public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfMap

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup
open scoped commutatorElement

theorem exists_twoPart_of_central_odd {X : Type} [Group X] [Finite X] (P N : Subgroup X)
    (hN : N ≤ Subgroup.center X) (hNP : N ≤ P) (hodd : Odd (Nat.card N))
    (hP : ∀ x ∈ P, ∃ k : ℕ, x ^ 2 ^ k ∈ N) :
    ∃ Q : Subgroup X, IsPGroup 2 Q ∧ (∀ x, x ∈ Q ↔ x ∈ P ∧ ∃ k : ℕ, x ^ 2 ^ k = 1) ∧
      ∀ x ∈ P, ∃ q ∈ Q, ∃ z ∈ N, x = q * z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcenter : N.subgroupOf P ≤ Subgroup.center ↥P := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hN hz) (y : X))
  haveI : (N.subgroupOf P).Normal := Subgroup.normal_of_le_center hcenter
  have hquot : IsPGroup 2 (↥P ⧸ N.subgroupOf P) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf P) q
    obtain ⟨k, hk⟩ := hP x.1 x.2
    refine ⟨k, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    simpa [Subgroup.mem_subgroupOf] using hk
  haveI : Group.IsNilpotent (↥P ⧸ N.subgroupOf P) := hquot.isNilpotent
  haveI : Group.IsNilpotent ↥P :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' (N.subgroupOf P))
      (by rw [QuotientGroup.ker_mk']; exact hcenter)
  let P₀ : Sylow 2 ↥P := Classical.arbitrary _
  haveI : Finite (Sylow 2 ↥P) := Sylow.finite_of_finiteIndex P₀
  haveI hP₀normal : (P₀ : Subgroup ↥P).Normal := inferInstance
  haveI : Unique (Sylow 2 ↥P) := Sylow.unique_of_normal P₀ hP₀normal
  let Q : Subgroup X := (P₀ : Subgroup ↥P).map P.subtype
  have hQ2 : IsPGroup 2 Q := P₀.isPGroup'.map P.subtype
  have hQchar : ∀ x, x ∈ Q ↔ x ∈ P ∧ ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨k, hk⟩ := P₀.isPGroup' ⟨y, hy⟩
      have hkP : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      exact ⟨y.2, k, by simpa using congrArg Subtype.val hkP⟩
    · rintro ⟨hxP, k, hk⟩
      have hx0 : (⟨x, hxP⟩ : ↥P) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
      have hsub2 : IsPGroup 2 (Subgroup.zpowers (⟨x, hxP⟩ : ↥P)) := by
        apply IsPGroup.of_card_dvd_pow (n := k)
        rw [Nat.card_zpowers]
        exact orderOf_dvd_iff_pow_eq_one.mpr hx0
      obtain ⟨R, hR⟩ := IsPGroup.exists_le_sylow hsub2
      have hReq : R = P₀ := Subsingleton.elim R P₀
      have hx0R : (⟨x, hxP⟩ : ↥P) ∈ (P₀ : Subgroup ↥P) := by
        rw [← hReq]
        exact hR (Subgroup.mem_zpowers _)
      exact Subgroup.mem_map_of_mem P.subtype hx0R
  refine ⟨Q, hQ2, hQchar, ?_⟩
  intro x hx
  obtain ⟨a, ha⟩ : ∃ a : ℕ,
      (QuotientGroup.mk' (N.subgroupOf P) (⟨x, hx⟩ : ↥P)) ^ 2 ^ a = 1 :=
    hquot (QuotientGroup.mk' (N.subgroupOf P) ⟨x, hx⟩)
  have hxN : x ^ 2 ^ a ∈ N := by
    have hmem : (⟨x, hx⟩ : ↥P) ^ 2 ^ a ∈ N.subgroupOf P := by
      rw [← QuotientGroup.eq_one_iff]
      rwa [← map_pow, QuotientGroup.mk'_apply] at ha
    simpa [Subgroup.mem_subgroupOf] using hmem
  have hcop : (Nat.card N).Coprime (2 ^ a) :=
    (Nat.coprime_two_right.mpr hodd).pow_right a
  obtain ⟨z₀, hzpow⟩ : ∃ z₀ : ↥N, z₀ ^ 2 ^ a = ⟨x ^ 2 ^ a, hxN⟩ :=
    (Nat.Coprime.pow_left_bijective hcop).2 ⟨x ^ 2 ^ a, hxN⟩
  have hzX : (z₀ : X) ^ 2 ^ a = x ^ 2 ^ a := by
    have := congrArg Subtype.val hzpow
    simpa using this
  have hzc : Commute x (z₀ : X) := Subgroup.mem_center_iff.mp (hN z₀.2) x
  refine ⟨x * (z₀ : X)⁻¹, ?_, (z₀ : X), z₀.2, ?_⟩
  · rw [hQchar]
    refine ⟨P.mul_mem hx (P.inv_mem (hNP z₀.2)), a, ?_⟩
    calc (x * (z₀ : X)⁻¹) ^ 2 ^ a
        = x ^ 2 ^ a * ((z₀ : X)⁻¹) ^ 2 ^ a := hzc.inv_right.mul_pow (2 ^ a)
      _ = x ^ 2 ^ a * ((z₀ : X) ^ 2 ^ a)⁻¹ := by rw [inv_pow]
      _ = x ^ 2 ^ a * (x ^ 2 ^ a)⁻¹ := by rw [hzX]
      _ = 1 := mul_inv_cancel _
  · group

variable {X X' : Type} [Group X] [Finite X] [Group X']

theorem exists_twoSubgroup_lift (π : X →* X') (hcen : π.ker ≤ Subgroup.center X)
    (hodd : Odd (Nat.card π.ker)) (M : Subgroup X) {A : Subgroup X'} (hA : IsPGroup 2 A) :
    ∃ Q : Subgroup X, IsPGroup 2 Q ∧
      (∀ x, x ∈ Q ↔ x ∈ M ∧ π x ∈ A ∧ ∃ k : ℕ, x ^ 2 ^ k = 1) ∧
      ∀ x ∈ M, π x ∈ A → ∃ q ∈ Q, ∃ z ∈ π.ker, x = q * z := by
  have hNP : π.ker ⊓ M ≤ M ⊓ A.comap π :=
    le_inf inf_le_right (le_trans inf_le_left (by
      intro x hx
      rw [Subgroup.mem_comap]
      exact (MonoidHom.mem_ker.mp hx : π x = 1) ▸ A.one_mem))
  obtain ⟨Q, hQ2, hQchar, hQdec⟩ :=
    exists_twoPart_of_central_odd (M ⊓ A.comap π) (π.ker ⊓ M)
      (le_trans inf_le_left hcen) hNP
      (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left))
      (fun x hx => by
        obtain ⟨k, hk⟩ := hA ⟨π x, hx.2⟩
        have hk' : (π x) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        exact ⟨k, by
          rw [Subgroup.mem_inf]
          exact ⟨by simpa using hk', M.pow_mem hx.1 (2 ^ k)⟩⟩)
  refine ⟨Q, hQ2, ?_, ?_⟩
  · intro x
    rw [hQchar]
    constructor
    · rintro ⟨hx, hx2⟩
      exact ⟨hx.1, hx.2, hx2⟩
    · rintro ⟨hxM, hxA, hx2⟩
      exact ⟨⟨hxM, hxA⟩, hx2⟩
  · intro x hxM hxA
    obtain ⟨q, hq, z, hz, hxz⟩ := hQdec x ⟨hxM, hxA⟩
    exact ⟨q, hq, z, hz.1, hxz⟩

theorem sevenTwelveConfig_lift_reflect (π : X →* X') {t g₂ g₃ : X} {y' : X'}
    {W' T' : Subgroup X'}
    (h : SevenTwelveConfig (Subgroup.zpowers (π t)) (π g₂) (π g₃) y' W' T') :
    conjSubgroup (Subgroup.zpowers t) g₂ ≠ Subgroup.zpowers t ∧
      ⁅Subgroup.zpowers t, conjSubgroup (Subgroup.zpowers t) g₃⁆ ≠ ⊥ ∧
      ⁅conjSubgroup (Subgroup.zpowers t) g₂, conjSubgroup (Subgroup.zpowers t) g₃⁆ ≠ ⊥ ∧
      ∀ y : X, y ∈ Subgroup.normalizer (Subgroup.zpowers t : Set X) →
        π y ∈ Subgroup.normalizer (Subgroup.zpowers (π t) : Set X') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro heq
    exact h.ne (by
      have := congrArg (Subgroup.map π) heq
      rwa [sevenTwelve_map_conjSubgroup, MonoidHom.map_zpowers] at this)
  · intro heq
    exact h.comm₁₃ (by
      have := congrArg (Subgroup.map π) heq
      rwa [Subgroup.map_commutator, sevenTwelve_map_conjSubgroup, MonoidHom.map_zpowers,
        Subgroup.map_bot] at this)
  · intro heq
    exact h.comm₂₃ (by
      have := congrArg (Subgroup.map π) heq
      rwa [Subgroup.map_commutator, sevenTwelve_map_conjSubgroup, sevenTwelve_map_conjSubgroup,
        MonoidHom.map_zpowers, Subgroup.map_bot] at this)
  · intro y hy
    have hmap := Subgroup.le_normalizer_map (H := Subgroup.zpowers t) π
      (Subgroup.mem_map_of_mem π hy)
    rwa [MonoidHom.map_zpowers] at hmap

private lemma sevenTwelveLift_conj_sq_eq_one {t g : X} (ht : t * t = 1) :
    (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
  rw [show (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, ht]
  group

private lemma sevenTwelveLift_zpowers_involution_eq {a x : X'} (ha : a * a = 1)
    (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have ha2 : a ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, ha]
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, ha2, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, ha2, one_zpow]
    simp

private lemma sevenTwelveLift_ker_sq_eq_one (π : X →* X')
    (hodd : Odd (Nat.card π.ker)) {z : X} (hz : z ∈ π.ker) (hzsq : z * z = 1) : z = 1 := by
  have hdiv : orderOf z ∣ Nat.card π.ker := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hz)
  have hoddz : Odd (orderOf z) := Odd.of_dvd_nat hodd hdiv
  have h2 : orderOf z ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact hzsq
  obtain ⟨m, hm⟩ := hoddz
  have h1 : orderOf z = 1 := by
    have : orderOf z ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    omega
  exact orderOf_eq_one_iff.mp h1

private lemma sevenTwelveLift_involution_mem_zpowers (π : X →* X')
    (hcen : π.ker ≤ Subgroup.center X) (hodd : Odd (Nat.card π.ker)) {t s : X}
    (ht : t * t = 1) (hs : s * s = 1) (hmem : π s ∈ Subgroup.zpowers (π t)) :
    s = 1 ∨ s = t := by
  have hπt : π t * π t = 1 := by rw [← map_mul, ht, map_one]
  rcases sevenTwelveLift_zpowers_involution_eq hπt hmem with h1 | h1
  · left
    exact sevenTwelveLift_ker_sq_eq_one π hodd (by rw [MonoidHom.mem_ker]; exact h1) hs
  · right
    have hzker : s * t⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    have hzmem : s * t⁻¹ ∈ Subgroup.center X := hcen hzker
    have hzt : s = (s * t⁻¹) * t := by group
    have hzz : s * s = (s * t⁻¹) * (s * t⁻¹) := by
      have hc : t * (s * t⁻¹) = (s * t⁻¹) * t := Subgroup.mem_center_iff.mp hzmem t
      conv_lhs => rw [hzt]
      calc ((s * t⁻¹) * t) * ((s * t⁻¹) * t)
          = (s * t⁻¹) * (t * (s * t⁻¹)) * t := by group
        _ = (s * t⁻¹) * ((s * t⁻¹) * t) * t := by rw [hc]
        _ = ((s * t⁻¹) * (s * t⁻¹)) * (t * t) := by group
        _ = ((s * t⁻¹) * (s * t⁻¹)) * 1 := by rw [ht]
        _ = (s * t⁻¹) * (s * t⁻¹) := by rw [mul_one]
    have hzsq : (s * t⁻¹) * (s * t⁻¹) = 1 := by rw [← hzz, hs]
    have hz1 : s * t⁻¹ = 1 := sevenTwelveLift_ker_sq_eq_one π hodd hzker hzsq
    rw [hzt, hz1, one_mul]

private lemma sevenTwelveLift_mem_commutator_of_mem (π : X →* X')
    (hcen : π.ker ≤ Subgroup.center X) (hodd : Odd (Nat.card π.ker)) {t g₂ g₃ : X}
    (hperf : ⁅sevenTwelveGen (Subgroup.zpowers (π t)) (π g₂) (π g₃),
        sevenTwelveGen (Subgroup.zpowers (π t)) (π g₂) (π g₃)⁆ =
      sevenTwelveGen (Subgroup.zpowers (π t)) (π g₂) (π g₃))
    {s : X} (hsL : s ∈ sevenTwelveGen (Subgroup.zpowers t) g₂ g₃) (hssq : s * s = 1) :
    s ∈ ⁅sevenTwelveGen (Subgroup.zpowers t) g₂ g₃,
      sevenTwelveGen (Subgroup.zpowers t) g₂ g₃⁆ := by
  have hLmap : (sevenTwelveGen (Subgroup.zpowers t) g₂ g₃).map π =
      sevenTwelveGen (Subgroup.zpowers (π t)) (π g₂) (π g₃) := by
    rw [map_sevenTwelveGen, MonoidHom.map_zpowers]
  have hcommmap : (⁅sevenTwelveGen (Subgroup.zpowers t) g₂ g₃,
      sevenTwelveGen (Subgroup.zpowers t) g₂ g₃⁆).map π =
      sevenTwelveGen (Subgroup.zpowers (π t)) (π g₂) (π g₃) := by
    rw [Subgroup.map_commutator, hLmap, hperf]
  have hπs : π s ∈ (sevenTwelveGen (Subgroup.zpowers t) g₂ g₃).map π :=
    Subgroup.mem_map_of_mem π hsL
  rw [hLmap, ← hcommmap] at hπs
  obtain ⟨c, hc, hcπ⟩ := Subgroup.mem_map.mp hπs
  have hcL : c ∈ sevenTwelveGen (Subgroup.zpowers t) g₂ g₃ :=
    (Subgroup.commutator_le_of_le le_rfl le_rfl) hc
  let z : X := c⁻¹ * s
  have hzker : z ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    have hzπ : π z = (π c)⁻¹ * π s := by simp [z]
    rw [hzπ, hcπ, inv_mul_cancel]
  have hzL : z ∈ sevenTwelveGen (Subgroup.zpowers t) g₂ g₃ := mul_mem (inv_mem hcL) hsL
  have hzc : c * z = z * c := (Subgroup.mem_center_iff.mp (hcen hzker)) c
  have hsz : c * z = s := by rw [show z = c⁻¹ * s from rfl]; group
  have hzz : z * z = (c * c)⁻¹ := by
    have h1 : c * c * (z * z) = 1 := by
      calc c * c * (z * z) = c * (c * z) * z := by group
        _ = c * (z * c) * z := by rw [hzc]
        _ = (c * z) * (c * z) := by group
        _ = s * s := by rw [hsz]
        _ = 1 := hssq
    have h' : (z * z)⁻¹ = c * c := inv_eq_of_mul_eq_one_left h1
    rw [← h', inv_inv]
  have hzzmem : z * z ∈ ⁅sevenTwelveGen (Subgroup.zpowers t) g₂ g₃,
      sevenTwelveGen (Subgroup.zpowers t) g₂ g₃⁆ := by
    rw [hzz]
    exact inv_mem (mul_mem hc hc)
  have hzodd : Odd (orderOf z) := by
    have hdiv : orderOf z ∣ Nat.card π.ker := by
      rw [← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hzker)
    exact Odd.of_dvd_nat hodd hdiv
  have hzmem : z ∈ ⁅sevenTwelveGen (Subgroup.zpowers t) g₂ g₃,
      sevenTwelveGen (Subgroup.zpowers t) g₂ g₃⁆ := by
    have hzo : z = (z * z) ^ ((orderOf z + 1) / 2) := by
      obtain ⟨m, hm⟩ := hzodd
      have h2m : orderOf z + 1 = 2 * (m + 1) := by omega
      rw [h2m, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
      rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf z + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [hzo]
    exact pow_mem hzzmem _
  rw [← hsz]
  exact mul_mem hc hzmem

theorem sevenTwelveConfig_lift_perfect (π : X →* X') (hcen : π.ker ≤ Subgroup.center X)
    (hodd : Odd (Nat.card π.ker)) {t g₂ g₃ : X} (ht : t * t = 1)
    (hperf : ⁅sevenTwelveGen (Subgroup.zpowers (π t)) (π g₂) (π g₃),
        sevenTwelveGen (Subgroup.zpowers (π t)) (π g₂) (π g₃)⁆ =
      sevenTwelveGen (Subgroup.zpowers (π t)) (π g₂) (π g₃)) :
    ⁅sevenTwelveGen (Subgroup.zpowers t) g₂ g₃, sevenTwelveGen (Subgroup.zpowers t) g₂ g₃⁆ =
      sevenTwelveGen (Subgroup.zpowers t) g₂ g₃ := by
  have hx₂sq : (g₂⁻¹ * t * g₂) * (g₂⁻¹ * t * g₂) = 1 := sevenTwelveLift_conj_sq_eq_one ht
  have hx₃sq : (g₃⁻¹ * t * g₃) * (g₃⁻¹ * t * g₃) = 1 := sevenTwelveLift_conj_sq_eq_one ht
  have htL : t ∈ sevenTwelveGen (Subgroup.zpowers t) g₂ g₃ :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have hx₂L : g₂⁻¹ * t * g₂ ∈ sevenTwelveGen (Subgroup.zpowers t) g₂ g₃ :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (by
      rw [sevenTwelve_conjSubgroup_zpowers]; exact Subgroup.mem_zpowers _))
  have hx₃L : g₃⁻¹ * t * g₃ ∈ sevenTwelveGen (Subgroup.zpowers t) g₂ g₃ :=
    Subgroup.mem_sup_right (by
      rw [sevenTwelve_conjSubgroup_zpowers]; exact Subgroup.mem_zpowers _)
  have htmem := sevenTwelveLift_mem_commutator_of_mem π hcen hodd hperf htL ht
  have hx₂mem := sevenTwelveLift_mem_commutator_of_mem π hcen hodd hperf hx₂L hx₂sq
  have hx₃mem := sevenTwelveLift_mem_commutator_of_mem π hcen hodd hperf hx₃L hx₃sq
  refine le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) ?_
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [Subgroup.zpowers_le]
    exact htmem
  · rw [sevenTwelve_conjSubgroup_zpowers]
    exact Subgroup.zpowers_le.mpr hx₂mem
  · rw [sevenTwelve_conjSubgroup_zpowers]
    exact Subgroup.zpowers_le.mpr hx₃mem

theorem sevenTwelveConfig_lift_w (π : X →* X') (hcen : π.ker ≤ Subgroup.center X)
    (hodd : Odd (Nat.card π.ker)) {t g₂ g₃ : X} (ht : t * t = 1) {W' : Subgroup X'}
    (hW : IsPGroup 2 W') (h₁ : Subgroup.zpowers (π t) ≤ W')
    (h₂ : conjSubgroup (Subgroup.zpowers (π t)) (π g₂) ≤ W') :
    ∃ W : Subgroup X, IsPGroup 2 W ∧ Subgroup.zpowers t ≤ W ∧
      conjSubgroup (Subgroup.zpowers t) g₂ ≤ W ∧
      W ≤ sevenTwelveGen (Subgroup.zpowers t) g₂ g₃ ∧
      ∀ y ∈ sevenTwelveGen (Subgroup.zpowers t) g₂ g₃,
        π y ∈ Subgroup.normalizer (W' : Set X') → y ∈ Subgroup.normalizer (W : Set X) := by
  obtain ⟨W, hW2, hWchar, -⟩ :=
    exists_twoSubgroup_lift π hcen hodd (sevenTwelveGen (Subgroup.zpowers t) g₂ g₃) hW
  have hx₂sq : (g₂⁻¹ * t * g₂) * (g₂⁻¹ * t * g₂) = 1 := sevenTwelveLift_conj_sq_eq_one ht
  refine ⟨W, hW2, ?_, ?_, ?_, ?_⟩
  · refine Subgroup.zpowers_le.mpr ?_
    rw [hWchar]
    exact ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers t)),
      h₁ (Subgroup.mem_zpowers (π t)), ⟨1, by rw [pow_one, pow_two]; exact ht⟩⟩
  · rw [sevenTwelve_conjSubgroup_zpowers]
    refine Subgroup.zpowers_le.mpr ?_
    rw [hWchar]
    exact ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_right (by
        rw [sevenTwelve_conjSubgroup_zpowers]; exact Subgroup.mem_zpowers _)),
      h₂ (by
        rw [sevenTwelve_conjSubgroup_zpowers]
        simpa using Subgroup.mem_zpowers ((π g₂)⁻¹ * (π t) * (π g₂))),
      ⟨1, by rw [pow_one, pow_two]; exact hx₂sq⟩⟩
  · intro x hx
    exact (hWchar x).mp hx |>.1
  · intro y hyL hyW'
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hWchar, hWchar]
    have hLconj : y * x * y⁻¹ ∈ sevenTwelveGen (Subgroup.zpowers t) g₂ g₃ ↔
        x ∈ sevenTwelveGen (Subgroup.zpowers t) g₂ g₃ := by
      constructor
      · intro h
        have := (sevenTwelveGen (Subgroup.zpowers t) g₂ g₃).mul_mem
          ((sevenTwelveGen (Subgroup.zpowers t) g₂ g₃).mul_mem
            ((sevenTwelveGen (Subgroup.zpowers t) g₂ g₃).inv_mem hyL) h) hyL
        simpa [mul_assoc] using this
      · intro h
        exact (sevenTwelveGen (Subgroup.zpowers t) g₂ g₃).mul_mem
          ((sevenTwelveGen (Subgroup.zpowers t) g₂ g₃).mul_mem hyL h)
          ((sevenTwelveGen (Subgroup.zpowers t) g₂ g₃).inv_mem hyL)
    have hWconj : π (y * x * y⁻¹) ∈ W' ↔ π x ∈ W' := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hyW' (π x)).symm
    have hpow : ∀ k, (y * x * y⁻¹) ^ (2 ^ k) = y * x ^ (2 ^ k) * y⁻¹ := by
      intro k
      rw [← MulAut.conj_apply y x, ← map_pow, MulAut.conj_apply]
    have hiff : (∃ k, (y * x * y⁻¹) ^ (2 ^ k) = 1) ↔ ∃ k, x ^ (2 ^ k) = 1 := by
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have hk' : y * x ^ (2 ^ k) * y⁻¹ = 1 := by rwa [hpow k] at hk
        have := congrArg (fun z => y⁻¹ * z * y) hk'
        simpa [mul_assoc] using this
      · rintro ⟨k, hk⟩
        exact ⟨k, by rw [hpow k, hk]; group⟩
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨hLconj.mpr h1, hWconj.mpr h2, hiff.mpr h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨hLconj.mp h1, hWconj.mp h2, hiff.mp h3⟩

theorem sevenTwelveConfig_lift_t (π : X →* X') (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center X) (hodd : Odd (Nat.card π.ker)) {t g₂ g₃ : X}
    (ht : t * t = 1)
    (hgen : Subgroup.normalClosure ((Subgroup.zpowers t : Subgroup X) : Set X) = ⊤)
    {T' : Subgroup X'} (hT : IsPGroup 2 T')
    (hle : T' ≤ Subgroup.normalizer (Subgroup.zpowers (π t) : Set X'))
    (hgen' : sevenTwelveGen (Subgroup.zpowers (π t)) (π g₂) (π g₃) ⊔ T' = ⊤) :
    ∃ T : Subgroup X, IsPGroup 2 T ∧
      T ≤ Subgroup.normalizer (Subgroup.zpowers t : Set X) ∧
      sevenTwelveGen (Subgroup.zpowers t) g₂ g₃ ⊔ T = ⊤ ∧
      ∀ y : X, π y ∈ Subgroup.normalizer (T' : Set X') → y ∈ Subgroup.normalizer (T : Set X) := by
  obtain ⟨Q, hQ2, hQchar, hQdec⟩ := exists_twoSubgroup_lift π hcen hodd ⊤ hT
  have hQchars : ∀ x, x ∈ Q ↔ π x ∈ T' ∧ ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x
    rw [hQchar x]
    exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨trivial, h.1, h.2⟩⟩
  refine ⟨Q, hQ2, ?_, ?_, ?_⟩
  · intro u hu
    have hπu : π u ∈ Subgroup.normalizer (Subgroup.zpowers (π t) : Set X') :=
      hle ((hQchars u).mp hu).1
    have hutu_sq : (u * t * u⁻¹) * (u * t * u⁻¹) = 1 := by
      simpa using sevenTwelveLift_conj_sq_eq_one (g := u⁻¹) ht
    have hmem : π (u * t * u⁻¹) ∈ Subgroup.zpowers (π t) := by
      have := (Subgroup.mem_normalizer_iff.mp hπu (π t)).mp (Subgroup.mem_zpowers (π t))
      simpa only [map_mul, map_inv] using this
    rcases sevenTwelveLift_involution_mem_zpowers π hcen hodd ht hutu_sq hmem with h1 | h1
    · have ht1 : t = 1 := by
        calc t = u⁻¹ * (u * t * u⁻¹) * u := by group
          _ = 1 := by rw [h1]; group
      rw [ht1, Subgroup.zpowers_one_eq_bot, Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top u
    · refine conjSubgroup_eq_iff_mem_normalizer.mp ?_
      rw [sevenTwelve_conjSubgroup_zpowers]
      have hfix : u⁻¹ * t * u = t := by
        calc u⁻¹ * t * u = u⁻¹ * (u * t * u⁻¹) * u := by rw [h1]
          _ = t := by group
      rw [hfix]
  · let M₀ : Subgroup X := sevenTwelveGen (Subgroup.zpowers t) g₂ g₃ ⊔ Q
    have hLmap : (sevenTwelveGen (Subgroup.zpowers t) g₂ g₃).map π =
        sevenTwelveGen (Subgroup.zpowers (π t)) (π g₂) (π g₃) := by
      rw [map_sevenTwelveGen, MonoidHom.map_zpowers]
    have hTmap : Q.map π = T' := by
      apply le_antisymm
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        exact ((hQchars y).mp hy).1
      · intro x' hx'
        obtain ⟨x, rfl⟩ := hπ x'
        obtain ⟨q, hq, z, hz, hxz⟩ := hQdec x trivial hx'
        have hπz : π z = 1 := MonoidHom.mem_ker.mp hz
        exact Subgroup.mem_map.mpr ⟨q, hq, by rw [hxz, map_mul, hπz, mul_one]⟩
    have hMtop : M₀.map π = ⊤ := by
      dsimp only [M₀]
      rw [Subgroup.map_sup, hLmap, hTmap, hgen']
    have hMker_top : M₀ ⊔ π.ker = ⊤ := by
      have hmap : (M₀ ⊔ π.ker).map π = ⊤ :=
        le_antisymm le_top (hMtop ▸ Subgroup.map_mono (f := π) le_sup_left)
      have hcm := Subgroup.comap_map_eq_self (f := π) (H := M₀ ⊔ π.ker) le_sup_right
      rw [hmap, Subgroup.comap_top] at hcm
      exact hcm.symm
    have hker_norm : π.ker ≤ Subgroup.normalizer (M₀ : Set X) := by
      intro z hz
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hcz : z * x = x * z := ((Subgroup.mem_center_iff.mp (hcen hz)) x).symm
      have heq : z * x * z⁻¹ = x := by rw [hcz]; group
      simp [heq]
    have hnorm_top : Subgroup.normalizer (M₀ : Set X) = ⊤ := by
      apply top_le_iff.mp
      rw [← hMker_top]
      exact sup_le Subgroup.le_normalizer hker_norm
    haveI hMnormal : M₀.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
    have hnc : Subgroup.normalClosure ((Subgroup.zpowers t : Subgroup X) : Set X) ≤ M₀ :=
      Subgroup.normalClosure_le_normal (Subgroup.zpowers_le.mpr
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers t)))))
    exact top_le_iff.mp (hgen ▸ hnc)
  · intro y hyT'
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hQchars, hQchars]
    have hTconj : π (y * x * y⁻¹) ∈ T' ↔ π x ∈ T' := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hyT' (π x)).symm
    have hpow : ∀ k, (y * x * y⁻¹) ^ (2 ^ k) = y * x ^ (2 ^ k) * y⁻¹ := by
      intro k
      rw [← MulAut.conj_apply y x, ← map_pow, MulAut.conj_apply]
    have hiff : (∃ k, (y * x * y⁻¹) ^ (2 ^ k) = 1) ↔ ∃ k, x ^ (2 ^ k) = 1 := by
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have hk' : y * x ^ (2 ^ k) * y⁻¹ = 1 := by rwa [hpow k] at hk
        have := congrArg (fun z => y⁻¹ * z * y) hk'
        simpa [mul_assoc] using this
      · rintro ⟨k, hk⟩
        exact ⟨k, by rw [hpow k, hk]; group⟩
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hTconj.mpr h1, hiff.mpr h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨hTconj.mp h1, hiff.mp h2⟩

theorem sevenTwelveConfig_lift (π : X →* X') (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center X) (hodd : Odd (Nat.card π.ker)) {t : X} (ht : t * t = 1)
    (hgen : Subgroup.normalClosure ((Subgroup.zpowers t : Subgroup X) : Set X) = ⊤)
    {g₂' g₃' y' : X'} {W' T' : Subgroup X'}
    (h : SevenTwelveConfig (Subgroup.zpowers (π t)) g₂' g₃' y' W' T') :
    ∃ (g₂ g₃ y : X) (W T : Subgroup X), SevenTwelveConfig (Subgroup.zpowers t) g₂ g₃ y W T := by
  obtain ⟨g₂, rfl⟩ := hπ g₂'
  obtain ⟨g₃, rfl⟩ := hπ g₃'
  obtain ⟨hne, hc₁₃, hc₂₃, hys⟩ := sevenTwelveConfig_lift_reflect π h
  have hperf := sevenTwelveConfig_lift_perfect π hcen hodd ht h.perfect
  obtain ⟨W, hW2, hS, hS₂, hWL, hWy⟩ :=
    sevenTwelveConfig_lift_w π hcen hodd ht h.w_two h.le_w h.le_w₂
  obtain ⟨T, hT2, hTn, hTgen, hTy⟩ :=
    sevenTwelveConfig_lift_t π hπ hcen hodd ht hgen h.t_two h.t_le h.gen
  have hy : y' ∈ (sevenTwelveGen (Subgroup.zpowers t) g₂ g₃).map π := by
    rw [map_sevenTwelveGen, MonoidHom.map_zpowers]
    exact h.y_mem
  obtain ⟨y, hyL, rfl⟩ := hy
  exact ⟨g₂, g₃, y, W, T, ⟨hne, hc₁₃, hc₂₃, hperf, hW2, hS, hS₂, hWL, hT2, hTn, hTgen, hyL,
    hTy y h.y_t, hWy y hyL h.y_w, fun hy => h.y_s (hys y hy)⟩⟩

end CFSG.LocalAnalysis.WeakClosure81

end
