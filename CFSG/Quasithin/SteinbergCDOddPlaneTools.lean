module

public import CFSG.Quasithin.SteinbergBQCyclicFiveSupport

public noncomputable section

namespace CFSG.Quasithin.SteinbergCD

open Module CFSG.Quasithin.SteinbergBQ

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

section Fixed

variable (H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))

@[expose] def glFixedSpace : Submodule (ZMod 2) V where
  carrier := {v | ∀ x ∈ H, (x : V →ₗ[ZMod 2] V) v = v}
  add_mem' {u v} hu hv x hx := by
    rw [map_add, hu x hx, hv x hx]
  zero_mem' x _ := map_zero _
  smul_mem' c v hv x hx := by
    rw [map_smul, hv x hx]

theorem mem_glFixedSpace {v : V} :
    v ∈ glFixedSpace H ↔ ∀ x ∈ H, (x : V →ₗ[ZMod 2] V) v = v :=
  Iff.rfl

@[expose] def avgOp [Fintype H] : Module.End (ZMod 2) V :=
  ∑ x : H, ((x : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)

theorem avgOp_apply [Fintype H] (v : V) :
    avgOp H v = ∑ x : H, ((x : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v := by
  rw [avgOp, LinearMap.sum_apply]

theorem avgOp_apply_mem [Fintype H] (v : V) : avgOp H v ∈ glFixedSpace H := by
  intro y hy
  rw [avgOp_apply, map_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft ⟨y, hy⟩) _ _ fun x => rfl

theorem avgOp_apply_of_mem [Fintype H] (hodd : Odd (Fintype.card H)) {c : V}
    (hc : c ∈ glFixedSpace H) : avgOp H c = c := by
  rw [avgOp_apply, Finset.sum_congr rfl fun (x : H) _ =>
    hc (x : LinearMap.GeneralLinearGroup (ZMod 2) V) x.2, Finset.sum_const, Finset.card_univ]
  obtain ⟨k, hk⟩ := hodd
  rw [hk, add_smul, mul_smul, one_smul]
  have h2 : (2 : ℕ) • c = 0 := by
    rw [two_nsmul]
    exact CFSG.LinearAlgebra.zmod2_vec_add_self c
  rw [smul_comm, h2, smul_zero, zero_add]

theorem avgOp_apply_eq_zero [Fintype H] {w : V} (hw : w ∈ commSpan H) : avgOp H w = 0 := by
  rw [avgOp_apply]
  exact sum_apply_eq_zero H hw

theorem sub_avgOp_mem [Fintype H] (hodd : Odd (Fintype.card H)) (v : V) :
    v - avgOp H v ∈ commSpan H := by
  have e : v - avgOp H v = ∑ x : H,
      (v - ((x : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, avgOp_apply]
    congr 1
    obtain ⟨k, hk⟩ := hodd
    rw [hk, add_smul, mul_smul, one_smul]
    have h2 : (2 : ℕ) • v = 0 := by
      rw [two_nsmul]
      exact CFSG.LinearAlgebra.zmod2_vec_add_self v
    rw [smul_comm, h2, smul_zero, zero_add]
  rw [e]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [← neg_sub]
  exact Submodule.neg_mem _ (sub_mem_commSpan H x.2 v)

theorem glFixedSpace_inf_commSpan [Fintype H] (hodd : Odd (Fintype.card H)) :
    glFixedSpace H ⊓ commSpan H = ⊥ := by
  refine eq_bot_iff.2 fun v hv => ?_
  obtain ⟨hvf, hvc⟩ := Submodule.mem_inf.1 hv
  rw [Submodule.mem_bot, ← avgOp_apply_of_mem H hodd hvf]
  exact avgOp_apply_eq_zero H hvc

theorem avgOp_apply_mem_of_invariant [Fintype H] {W : Submodule (ZMod 2) V}
    (hW : ∀ x ∈ H, ∀ w ∈ W, (x : V →ₗ[ZMod 2] V) w ∈ W) {w : V} (hw : w ∈ W) :
    avgOp H w ∈ W := by
  rw [avgOp_apply]
  exact Submodule.sum_mem _ fun x _ => hW x x.2 w hw

theorem avgOp_comm [Fintype H] {g : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hg : g ∈ Subgroup.normalizer (H : Set (LinearMap.GeneralLinearGroup (ZMod 2) V))) (v : V) :
    (g : V →ₗ[ZMod 2] V) (avgOp H v) = avgOp H ((g : V →ₗ[ZMod 2] V) v) := by
  rw [avgOp_apply, avgOp_apply, map_sum]
  let e : H ≃ H :=
    { toFun := fun x => ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg x).1 x.prop⟩
      invFun := fun x => ⟨g⁻¹ * x * g, by
        have h := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) x).1 x.prop
        rwa [inv_inv] at h⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun x => Subtype.ext (by simp only; group) }
  refine Fintype.sum_equiv e _ _ fun x => ?_
  change (g : V →ₗ[ZMod 2] V) (((x : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) v) =
    ((g * x * g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
      ((g : V →ₗ[ZMod 2] V) v)
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
    ← Module.End.mul_apply (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V)) :
      V →ₗ[ZMod 2] V), ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]

theorem finrank_eq_fixed_add_comm [FiniteDimensional (ZMod 2) V] [Fintype H]
    (hodd : Odd (Fintype.card H)) {W : Submodule (ZMod 2) V}
    (hW : ∀ x ∈ H, ∀ w ∈ W, (x : V →ₗ[ZMod 2] V) w ∈ W) :
    finrank (ZMod 2) W =
      finrank (ZMod 2) (W ⊓ glFixedSpace H : Submodule (ZMod 2) V) +
        finrank (ZMod 2) (W ⊓ commSpan H : Submodule (ZMod 2) V) := by
  have hsup : (W ⊓ glFixedSpace H) ⊔ (W ⊓ commSpan H) = W := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) fun w hw => ?_
    have h1 : avgOp H w ∈ W ⊓ glFixedSpace H :=
      ⟨avgOp_apply_mem_of_invariant H hW hw, avgOp_apply_mem H w⟩
    have h2 : w - avgOp H w ∈ W ⊓ commSpan H :=
      ⟨W.sub_mem hw (avgOp_apply_mem_of_invariant H hW hw), sub_avgOp_mem H hodd w⟩
    have e : w = avgOp H w + (w - avgOp H w) := by abel
    rw [e]
    exact Submodule.add_mem_sup h1 h2
  have hinf : (W ⊓ glFixedSpace H) ⊓ (W ⊓ commSpan H) = ⊥ := by
    refine eq_bot_iff.2 fun v hv => ?_
    rw [← glFixedSpace_inf_commSpan H hodd]
    exact ⟨hv.1.2, hv.2.2⟩
  have h := Submodule.finrank_sup_add_finrank_inf_eq (W ⊓ glFixedSpace H) (W ⊓ commSpan H)
  rw [hsup, hinf, finrank_bot, add_zero] at h
  exact h

end Fixed

section Inverting

variable {Q : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}

theorem exists_sub_eq_of_mem [Finite (LinearMap.GeneralLinearGroup (ZMod 2) V)] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) [IsElementaryAbelian p Q]
    {t : LinearMap.GeneralLinearGroup (ZMod 2) V} (htQ : ∀ x ∈ Q, t⁻¹ * x * t = x⁻¹)
    {W : Submodule (ZMod 2) V} (hWQ : ∀ x ∈ Q, ∀ w ∈ W, (x : V →ₗ[ZMod 2] V) w ∈ W)
    (hW0 : W ⊓ glFixedSpace Q = ⊥) {w : V} (hw : w ∈ W) (htw : (t : V →ₗ[ZMod 2] V) w = w) :
    ∃ u ∈ W, (t : V →ₗ[ZMod 2] V) u - u = w := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have hinv : ∀ x : Q, x⁻¹ = x → x = 1 := by
    intro x hx
    have h2 : x ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← hx]
      exact inv_mul_cancel x
    have hp : x ^ p = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian
      (x : LinearMap.GeneralLinearGroup (ZMod 2) V) x.2)
    have := pow_gcd_eq_one.2 ⟨h2, hp⟩
    rwa [Nat.Coprime.gcd_eq_one ((Nat.coprime_primes Nat.prime_two Fact.out).2 hp2.symm),
      pow_one] at this
  obtain ⟨ε, hε⟩ := exists_half_sign hinv
  set φ : Q → V := fun x => ((x : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w
    with hφ
  have hsum : ∑ x : Q, φ x = 0 := by
    have hmem : avgOp Q w ∈ W ⊓ glFixedSpace Q :=
      ⟨avgOp_apply_mem_of_invariant Q hWQ hw, avgOp_apply_mem Q w⟩
    rw [hW0, Submodule.mem_bot, avgOp_apply] at hmem
    exact hmem
  refine ⟨∑ x : Q, ε x • φ x, Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _
    (hWQ x x.2 w hw), ?_⟩
  have h1 : ∀ x : Q, (t : V →ₗ[ZMod 2] V) (ε x • φ x) = ε x • φ x⁻¹ := by
    intro x
    have htx := mul_eq_inv_mul_of_inverts (htQ _ (Q.inv_mem x.2))
    rw [map_smul, hφ]
    simp only
    rw [← Module.End.mul_apply, ← Units.val_mul, htx, Units.val_mul, Module.End.mul_apply, htw]
    rfl
  have htu : (t : V →ₗ[ZMod 2] V) (∑ x : Q, ε x • φ x) = ∑ x : Q, ε x⁻¹ • φ x := by
    rw [map_sum, Finset.sum_congr rfl fun x _ => h1 x]
    exact Fintype.sum_equiv (Equiv.inv Q) _ _ fun x => by simp
  have h2 : ∀ x : Q, ε x⁻¹ • φ x - ε x • φ x = φ x - if x = 1 then w else 0 := by
    intro x
    have hsub : ε x⁻¹ - ε x = ε x + ε x⁻¹ := by
      rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two, add_comm]
    rw [← sub_smul, hsub, hε]
    by_cases hx : x = 1
    · subst hx
      simp [hφ]
    · simp [hx]
  have h3 : ∑ x : Q, (if x = 1 then w else 0) = w := by simp
  rw [htu, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun x _ => h2 x, Finset.sum_sub_distrib,
    hsum, h3, zero_sub]
  exact neg_eq_of_add_eq_zero_left (CFSG.LinearAlgebra.zmod2_vec_add_self w)

theorem two_mul_finrank_inf_ker_eq [FiniteDimensional (ZMod 2) V] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) [IsElementaryAbelian p Q] {t : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (ht : t ^ 2 = 1) (htQ : ∀ x ∈ Q, t⁻¹ * x * t = x⁻¹) {W : Submodule (ZMod 2) V}
    (hWQ : ∀ x ∈ Q, ∀ w ∈ W, (x : V →ₗ[ZMod 2] V) w ∈ W)
    (hWt : ∀ w ∈ W, (t : V →ₗ[ZMod 2] V) w ∈ W) (hW0 : W ⊓ glFixedSpace Q = ⊥) :
    2 * finrank (ZMod 2)
        (W ⊓ LinearMap.ker ((t : V →ₗ[ZMod 2] V) - 1) : Submodule (ZMod 2) V) =
      finrank (ZMod 2) W := by
  have := finite_generalLinearGroup (V := V)
  set T : Module.End (ZMod 2) V := (t : V →ₗ[ZMod 2] V) - 1 with hT
  have hTW : ∀ w ∈ W, T w ∈ W := fun w hw => by
    rw [hT, LinearMap.sub_apply, Module.End.one_apply]
    exact W.sub_mem (hWt w hw) hw
  let TW : Module.End (ZMod 2) W := T.restrict hTW
  have htt : ∀ v, (t : V →ₗ[ZMod 2] V) ((t : V →ₗ[ZMod 2] V) v) = v := fun v => by
    rw [← Module.End.mul_apply, ← Units.val_mul, ← pow_two, ht, Units.val_one,
      Module.End.one_apply]
  have hTT : ∀ v, T (T v) = 0 := fun v => by
    rw [hT, LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
      map_sub, htt]
    have e : v - (t : V →ₗ[ZMod 2] V) v - ((t : V →ₗ[ZMod 2] V) v - v) =
        (v + v) - ((t : V →ₗ[ZMod 2] V) v + (t : V →ₗ[ZMod 2] V) v) := by abel
    rw [e, CFSG.LinearAlgebra.zmod2_vec_add_self, CFSG.LinearAlgebra.zmod2_vec_add_self, sub_self]
  have hker : LinearMap.ker TW = LinearMap.range TW := by
    refine le_antisymm (fun w hw => ?_) ?_
    · have h0 : T w = 0 := congrArg Subtype.val hw
      have htw : (t : V →ₗ[ZMod 2] V) w = w := by
        rw [hT, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h0
        exact h0
      obtain ⟨u, hu, hut⟩ := exists_sub_eq_of_mem hp2 htQ hWQ hW0 w.2 htw
      refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
      change T u = w
      rw [hT, LinearMap.sub_apply, Module.End.one_apply]
      exact hut
    · rintro _ ⟨w, rfl⟩
      exact Subtype.ext (hTT w)
  have h := LinearMap.finrank_range_add_finrank_ker TW
  rw [← hker] at h
  have hmap : (LinearMap.ker TW).map W.subtype = W ⊓ LinearMap.ker T := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, congrArg Subtype.val hw⟩
    · rintro ⟨hvW, hvT⟩
      exact ⟨⟨v, hvW⟩, Subtype.ext hvT, rfl⟩
  have h2 := Submodule.finrank_map_subtype_eq W (LinearMap.ker TW)
  rw [hmap] at h2
  omega

theorem four_le_finrank [FiniteDimensional (ZMod 2) V] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    [IsElementaryAbelian p Q] {t : LinearMap.GeneralLinearGroup (ZMod 2) V} (ht : t ^ 2 = 1)
    (htQ : ∀ x ∈ Q, t⁻¹ * x * t = x⁻¹) {W : Submodule (ZMod 2) V}
    (hWQ : ∀ x ∈ Q, ∀ w ∈ W, (x : V →ₗ[ZMod 2] V) w ∈ W)
    (hWt : ∀ w ∈ W, (t : V →ₗ[ZMod 2] V) w ∈ W) (hW0 : W ⊓ glFixedSpace Q = ⊥) (hW : W ≠ ⊥) :
    4 ≤ finrank (ZMod 2) W := by
  have hp2 : p ≠ 2 := by omega
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have h2 := two_mul_finrank_inf_ker_eq hp2 ht htQ hWQ hWt hW0
  have hmod := two_pow_finrank_modEq_one Q (isPGroup_of_isElementaryAbelian Q (p := p)) W hWQ
    fun u hu hfix => by
      have hmem : u ∈ W ⊓ glFixedSpace Q := ⟨hu, hfix⟩
      rw [hW0] at hmem
      exact hmem
  have hpos : 0 < finrank (ZMod 2) W :=
    Nat.pos_of_ne_zero fun h => hW (Submodule.finrank_eq_zero.1 h)
  by_contra hlt
  have h2' : finrank (ZMod 2) W = 2 := by omega
  rw [h2'] at hmod
  have hdvd : p ∣ 3 := (Nat.modEq_iff_dvd' (by norm_num)).1 hmod.symm
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem finrank_commSpan_le [FiniteDimensional (ZMod 2) V] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    [IsElementaryAbelian p Q] {t : LinearMap.GeneralLinearGroup (ZMod 2) V} (ht : t ^ 2 = 1)
    (htQ : ∀ x ∈ Q, t⁻¹ * x * t = x⁻¹) :
    finrank (ZMod 2) (commSpan Q) ≤
      2 * (finrank (ZMod 2) V - finrank (ZMod 2) (LinearMap.ker ((t : V →ₗ[ZMod 2] V) - 1))) := by
  rw [finrank_commSpan_eq_two_mul Q hp2 ht htQ]
  have h1 := LinearMap.finrank_range_add_finrank_ker ((t : V →ₗ[ZMod 2] V) - 1)
  have h2 : finrank (ZMod 2) ((commSpan Q).map ((t : V →ₗ[ZMod 2] V) - 1)) ≤
      finrank (ZMod 2) (LinearMap.range ((t : V →ₗ[ZMod 2] V) - 1)) :=
    Submodule.finrank_mono LinearMap.map_le_range
  omega

end Inverting

theorem exists_inverted {G : Type*} [Group G] {P : Subgroup G} {t : G} (ht : t ^ 2 = 1)
    (htP : t ∈ Subgroup.normalizer (P : Set G)) {x : G} (hx : x ∈ P) (htx : t * x * t⁻¹ ≠ x) :
    ∃ y ∈ P, y ≠ 1 ∧ t⁻¹ * y * t = y⁻¹ := by
  have htt : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by rw [← pow_two, ht])
  refine ⟨x⁻¹ * (t * x * t⁻¹), mul_mem (inv_mem hx) ((Subgroup.mem_normalizer_iff.1 htP x).1 hx),
    fun h => htx (by rw [inv_mul_eq_one] at h; exact h.symm), ?_⟩
  rw [htt]
  calc t * (x⁻¹ * (t * x * t)) * t = t * x⁻¹ * t * x * (t * t) := by group
    _ = t * x⁻¹ * t * x := by rw [← pow_two, ht, mul_one]
    _ = (x⁻¹ * (t * x * t))⁻¹ := by simp only [mul_inv_rev, inv_inv, htt]; group

end CFSG.Quasithin.SteinbergCD
