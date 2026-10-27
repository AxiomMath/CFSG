module

public import CFSG.Quasithin.SteinbergCDOddPlaneDecomposition
public import CFSG.Quasithin.SteinbergCDOddPlaneTools

public noncomputable section

namespace CFSG.Quasithin.SteinbergCD

open Module CFSG.Quasithin.SteinbergBQ Subgroup

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {p : ℕ}

theorem finrank_sub_le_finrank_commSpan [FiniteDimensional (ZMod 2) V]
    {y : LinearMap.GeneralLinearGroup (ZMod 2) V} {U : Submodule (ZMod 2) V}
    (hU : ∀ u ∈ U, (y : V →ₗ[ZMod 2] V) u ∈ U) :
    finrank (ZMod 2) U - finrank (ZMod 2)
        (U ⊓ LinearMap.ker ((y : V →ₗ[ZMod 2] V) - 1) : Submodule (ZMod 2) V) ≤
      finrank (ZMod 2) (commSpan (zpowers y)) := by
  set T : Module.End (ZMod 2) V := (y : V →ₗ[ZMod 2] V) - 1 with hT
  have hTU : ∀ u ∈ U, T u ∈ U := fun u hu => by
    rw [hT, LinearMap.sub_apply, Module.End.one_apply]
    exact U.sub_mem (hU u hu) hu
  let TU : Module.End (ZMod 2) U := T.restrict hTU
  have h := LinearMap.finrank_range_add_finrank_ker TU
  have hker : (LinearMap.ker TU).map U.subtype = U ⊓ LinearMap.ker T := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, congrArg Subtype.val hw⟩
    · rintro ⟨hvU, hvT⟩
      exact ⟨⟨v, hvU⟩, Subtype.ext hvT, rfl⟩
  have hrange : (LinearMap.range TU).map U.subtype ≤ commSpan (zpowers y) := by
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    change T w ∈ commSpan (zpowers y)
    rw [hT, LinearMap.sub_apply, Module.End.one_apply]
    exact sub_mem_commSpan _ (mem_zpowers y) w
  have h1 := Submodule.finrank_map_subtype_eq U (LinearMap.ker TU)
  have h2 := Submodule.finrank_map_subtype_eq U (LinearMap.range TU)
  rw [hker] at h1
  have h3 := Submodule.finrank_mono hrange
  rw [h2] at h3
  omega

theorem exists_center_generator {G : Type*} [Group G] (hp : p.Prime) {P : Subgroup G}
    (hP : Nat.card P = p ^ 3) (hPab : ∃ x y : P, x * y ≠ y * x) :
    ∃ z ∈ P, z ≠ 1 ∧ (∀ x ∈ P, x * z = z * x) ∧ orderOf z = p ∧
      (∀ x ∈ P, (∀ w ∈ P, w * x = x * w) → x ∈ zpowers z) ∧
      ∀ x ∈ P, ∀ w ∈ P, w * x * w⁻¹ * x⁻¹ ∈ zpowers z := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero 3 hp.ne_zero)
  obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow hP (by norm_num)
  have hk3 : k ≤ 3 := by
    have h := card_subgroup_dvd_card (center P)
    rw [hk, hP] at h
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h
  have hquot : Nat.card (P ⧸ center P) * p ^ k = p ^ 3 := by
    rw [← hk, ← hP, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hk1 : k = 1 := by
    obtain ⟨x, y, hxy⟩ := hPab
    by_contra hne
    apply hxy
    rcases (show k = 2 ∨ k = 3 by omega) with h2 | h3
    ·
      have hq : Nat.card (P ⧸ center P) = p := by
        subst h2
        have : p ^ 3 = p * p ^ 2 := by ring
        rw [this] at hquot
        exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) hquot
      have : IsCyclic (P ⧸ center P) := isCyclic_of_prime_card hq
      exact ((QuotientGroup.mk' (center P)).isMulCommutative_of_isCyclic_of_ker_le_center
        (by rw [QuotientGroup.ker_mk'])).is_comm.comm x y
    · have hc : center P = ⊤ := by
        subst h3
        exact eq_top_of_card_eq _ (by rw [hk, hP])
      exact mem_center_iff.1 (hc ▸ mem_top y) x
  subst hk1
  rw [pow_one] at hk hquot
  have hq : Nat.card (P ⧸ center P) = p ^ 2 := by
    have : p ^ 3 = p ^ 2 * p := by ring
    rw [this] at hquot
    exact Nat.eq_of_mul_eq_mul_right hp.pos hquot
  have : IsCyclic (center P) := isCyclic_of_prime_card hk
  obtain ⟨z₀, hz₀⟩ := IsCyclic.exists_generator (α := center P)
  have hz₀1 : z₀ ≠ 1 := by
    intro h
    have : Nat.card (center P) = 1 := by
      have htop : (⊤ : Subgroup (center P)) = ⊥ := by
        rw [eq_bot_iff]
        intro x _
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 (hz₀ x)
        rw [h, one_zpow]
        exact one_mem _
      rw [← card_top, htop, card_bot]
    rw [hk] at this
    exact hp.one_lt.ne' this
  set z : G := ((z₀ : P) : G) with hz
  have hzP : z ∈ P := (z₀ : P).2
  have hz1 : z ≠ 1 := fun h => hz₀1 (Subtype.ext (Subtype.ext h))
  have hzc : ∀ x ∈ P, x * z = z * x := fun x hx =>
    congrArg Subtype.val ((mem_center_iff.1 z₀.2) ⟨x, hx⟩)
  have hzord : orderOf z = p := by
    have h1 : orderOf z = orderOf z₀ := by
      rw [hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    rw [h1, orderOf_eq_card_of_forall_mem_zpowers hz₀, hk]
  have hcent : ∀ x ∈ P, (∀ w ∈ P, w * x = x * w) → x ∈ zpowers z := by
    intro x hx hxc
    have hxZ : (⟨x, hx⟩ : P) ∈ center P := mem_center_iff.2 fun w =>
      Subtype.ext (hxc w w.2)
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 (hz₀ ⟨⟨x, hx⟩, hxZ⟩)
    refine mem_zpowers_iff.2 ⟨n, ?_⟩
    have := congrArg (fun c : center P => ((c : P) : G)) hn
    simpa using this
  refine ⟨z, hzP, hz1, hzc, hzord, hcent, fun x hx w hw => ?_⟩
  set a : P := ⟨w, hw⟩
  set b : P := ⟨x, hx⟩
  have hcomm : (a : P ⧸ center P) * (b : P ⧸ center P) = (b : P ⧸ center P) * (a : P ⧸ center P) :=
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq hq).is_comm.comm _ _
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ center P := by
    refine (QuotientGroup.eq_one_iff (a * b * a⁻¹ * b⁻¹)).1 ?_
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hcomm, mul_inv_cancel_right, mul_inv_cancel]
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 (hz₀ ⟨_, hmem⟩)
  refine mem_zpowers_iff.2 ⟨n, ?_⟩
  have := congrArg (fun c : center P => ((c : P) : G)) hn
  simpa using this

theorem twelve_le_finrank_commSpan_zpowers [FiniteDimensional (ZMod 2) V] (hp : p.Prime)
    (hp5 : 5 ≤ p) {P : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    (hP : Nat.card P = p ^ 3) (hPab : ∃ x y : P, x * y ≠ y * x) (hPexp : ∀ x ∈ P, x ^ p = 1)
    {y : LinearMap.GeneralLinearGroup (ZMod 2) V} (hyP : y ∈ P) (hy1 : y ≠ 1) :
    12 ≤ finrank (ZMod 2) (commSpan (zpowers y)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have := finite_generalLinearGroup (V := V)
  have : Finite V := Module.finite_of_finite (ZMod 2)
  obtain ⟨z, hzP, hz1, hzc, hzord, hcent, hcomm⟩ := exists_center_generator hp hP hPab
  have hz : z ^ p = 1 := hPexp z hzP
  set Z := zpowers z with hZ
  set U := commSpan Z with hU
  have : Fintype Z := Fintype.ofFinite Z
  have hZcard : Nat.card Z = p := by rw [hZ, Nat.card_zpowers, hzord]
  have hZP : Z ≤ P := zpowers_le.2 hzP
  have hval : ∀ (g h : LinearMap.GeneralLinearGroup (ZMod 2) V) (v : V),
      ((g * h : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v =
        (g : V →ₗ[ZMod 2] V) ((h : V →ₗ[ZMod 2] V) v) := fun g h v => by
    rw [Units.val_mul, Module.End.mul_apply]
  have hPZ : ∀ g ∈ P, ∀ c ∈ Z, g * c = c * g := fun g hg c hc => by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hc
    exact (Commute.zpow_right (hzc g hg) n).eq
  have hPN : ∀ g ∈ P, g ∈ normalizer (Z : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)) :=
    fun g hg => mem_normalizer_of_commute fun c hc => hPZ g hg c hc
  have hUP : ∀ g ∈ P, ∀ u ∈ U, (g : V →ₗ[ZMod 2] V) u ∈ U := fun g hg u hu =>
    map_mem_commSpan_of_mem_normalizer (hPN g hg) hu
  have hU0 : U ≠ ⊥ := by
    intro hbot
    apply hz1
    refine Units.ext (LinearMap.ext fun v => ?_)
    have h := sub_mem_commSpan Z (mem_zpowers z) v
    rw [← hU, hbot, Submodule.mem_bot, sub_eq_zero] at h
    exact h
  have hodd : Odd (Fintype.card Z) := by
    rw [← Nat.card_eq_fintype_card, hZcard]
    exact hp.odd_of_ne_two hp2
  have hUfix : U ⊓ glFixedSpace Z = ⊥ := by
    rw [inf_comm]
    exact glFixedSpace_inf_commSpan Z hodd
  have key : ∀ y' ∈ P, y' ∉ Z → finrank (ZMod 2) U = p * finrank (ZMod 2)
      (U ⊓ LinearMap.ker ((y' : V →ₗ[ZMod 2] V) - 1) : Submodule (ZMod 2) V) ∧
      3 ≤ finrank (ZMod 2) (U ⊓ LinearMap.ker ((y' : V →ₗ[ZMod 2] V) - 1) :
        Submodule (ZMod 2) V) := by
    intro y' hy'P hy'Z
    obtain ⟨w, hwP, hwy⟩ : ∃ w ∈ P, w * y' ≠ y' * w := by
      by_contra h
      push Not at h
      exact hy'Z (hcent y' hy'P h)
    set d := w * y' * w⁻¹ * y'⁻¹ with hd
    have hdZ : d ∈ Z := hcomm y' hy'P w hwP
    have hd1 : d ≠ 1 := fun h => hwy (by
      rw [hd, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
      exact h)
    have hdZ' : zpowers d = Z := by
      refine eq_of_le_of_card_ge (zpowers_le.2 hdZ) ?_
      rw [hZcard, Nat.card_zpowers, orderOf_eq_prime (hPexp d (hZP hdZ)) hd1]
    have hwy' : w * y' * w⁻¹ = d * y' := by rw [hd, inv_mul_cancel_right]
    have hconj : ∀ m : ℕ, w ^ m * y' * (w ^ m)⁻¹ = d ^ m * y' := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have hdw : w * d ^ m = d ^ m * w := (Commute.pow_right (hPZ w hwP d hdZ) m).eq
        calc w ^ (m + 1) * y' * (w ^ (m + 1))⁻¹ = w * (w ^ m * y' * (w ^ m)⁻¹) * w⁻¹ := by
              rw [pow_succ']
              group
          _ = w * (d ^ m * y') * w⁻¹ := by rw [ih]
          _ = d ^ m * (w * y' * w⁻¹) := by
              rw [← mul_assoc, hdw]
              group
          _ = d ^ (m + 1) * y' := by rw [hwy', ← mul_assoc, ← pow_succ]
    have hdecomp := finrank_eq_mul_of_conj hp hp2 hz hz1 (hzc y' hy'P)
      (fun c hc => hPexp _ (mul_mem hy'P (hZP hc))) fun c hc => by
        have hc' : c ∈ zpowers d := by
          rw [hdZ']
          exact hc
        obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hc')
        refine ⟨w ^ m, hPN _ (pow_mem hwP m), ?_⟩
        rw [hconj m]
        exact (hPZ y' hy'P _ (pow_mem hdZ m)).symm
    refine ⟨hdecomp, ?_⟩
    set W₀ : Submodule (ZMod 2) V := U ⊓ LinearMap.ker ((y' : V →ₗ[ZMod 2] V) - 1) with hW₀
    have hW₀ne : W₀ ≠ ⊥ := by
      intro h
      apply hU0
      rw [← Submodule.finrank_eq_zero, hdecomp, h, finrank_bot, mul_zero]
    have hW₀inv : ∀ x ∈ Z, ∀ u ∈ W₀, (x : V →ₗ[ZMod 2] V) u ∈ W₀ := by
      intro x hx u hu
      obtain ⟨huU, huk⟩ := Submodule.mem_inf.1 hu
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at huk
      refine Submodule.mem_inf.2 ⟨hUP x (hZP hx) u huU, ?_⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, ← hval,
        hPZ y' hy'P x hx, hval, huk]
    have hmod := two_pow_finrank_modEq_one Z (IsPGroup.of_card (n := 1)
      (by rw [hZcard, pow_one])) W₀ hW₀inv fun u hu hfix => by
        have hmem : u ∈ U ⊓ glFixedSpace Z := ⟨(Submodule.mem_inf.1 hu).1, hfix⟩
        rw [hUfix] at hmem
        exact hmem
    have hpos : 0 < finrank (ZMod 2) W₀ :=
      Nat.pos_of_ne_zero fun h => hW₀ne (Submodule.finrank_eq_zero.1 h)
    by_contra hlt
    push Not at hlt
    interval_cases h : finrank (ZMod 2) W₀
    · have hdvd : p ∣ 1 := (Nat.modEq_iff_dvd' (by norm_num)).1 hmod.symm
      exact hp.one_lt.ne' (Nat.dvd_one.1 hdvd)
    · have hdvd : p ∣ 3 := (Nat.modEq_iff_dvd' (by norm_num)).1 hmod.symm
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
  obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, hx⟩ := hPab
  have hx₁Z : x₁ ∉ Z := fun h => hx (Subtype.ext (by
    show x₁ * x₂ = x₂ * x₁
    exact (hPZ x₂ hx₂ x₁ h).symm))
  obtain ⟨hdim₁, hc₁⟩ := key x₁ hx₁ hx₁Z
  by_cases hyZ : y ∈ Z
  ·
    have hyZ' : zpowers y = Z := by
      refine eq_of_le_of_card_ge (zpowers_le.2 hyZ) ?_
      rw [hZcard, Nat.card_zpowers, orderOf_eq_prime (hPexp y hyP) hy1]
    rw [hyZ', ← hU, hdim₁]
    nlinarith
  · obtain ⟨hdim, hc⟩ := key y hyP hyZ
    have hle := finrank_sub_le_finrank_commSpan (y := y) (U := U) (hUP y hyP)
    rw [hdim] at hle
    have : 12 ≤ p * finrank (ZMod 2) (U ⊓ LinearMap.ker ((y : V →ₗ[ZMod 2] V) - 1) :
        Submodule (ZMod 2) V) - finrank (ZMod 2) (U ⊓ LinearMap.ker ((y : V →ₗ[ZMod 2] V) - 1) :
          Submodule (ZMod 2) V) := by
      have h4 : 4 ≤ p - 1 := by omega
      have e : p * finrank (ZMod 2) (U ⊓ LinearMap.ker ((y : V →ₗ[ZMod 2] V) - 1) :
          Submodule (ZMod 2) V) - finrank (ZMod 2) (U ⊓ LinearMap.ker
            ((y : V →ₗ[ZMod 2] V) - 1) : Submodule (ZMod 2) V) =
          (p - 1) * finrank (ZMod 2) (U ⊓ LinearMap.ker ((y : V →ₗ[ZMod 2] V) - 1) :
            Submodule (ZMod 2) V) := by
        rw [Nat.sub_mul, one_mul]
      rw [e]
      nlinarith
    omega

end CFSG.Quasithin.SteinbergCD
