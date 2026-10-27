module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.Blueprint.FischerDefs

public noncomputable section

namespace CFSG.StandardType.ZS

open Subgroup
open Module

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  [Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}

omit [Module.Finite (ZMod p) U] in
@[expose] def reflImage (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (A : Subgroup (U ≃ₗ[ZMod p] U)) : Set (↥A ⧸ Subgroup.center ↥A) :=
  {x | ∃ t : ↥A, IsRefl p (t : U ≃ₗ[ZMod p] U) ∧
    (QuotientGroup.mk t : ↥A ⧸ Subgroup.center ↥A) = x}

local notation "mk" => (QuotientGroup.mk : A → A ⧸ Subgroup.center A)

omit [Module.Finite (ZMod p) U] in
private theorem zq_orderOf_refl {t : ↥A} (ht : IsRefl p (t : U ≃ₗ[ZMod p] U)) :
    orderOf t = 2 := by
  have ht2 : t ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    simpa [pow_two] using ht.1
  have hne : t ≠ 1 := by
    intro h1
    have hzero : (t : U →ₗ[ZMod p] U) - LinearMap.id = 0 := by
      ext x
      have hx : (t : U ≃ₗ[ZMod p] U) x = x := by
        simpa using congrArg (fun e : ↥A => (e : U ≃ₗ[ZMod p] U) x) h1
      simpa [sub_eq_zero] using hx
    have hrange := ht.2
    rw [hzero, LinearMap.range_zero, finrank_bot] at hrange
    exact zero_ne_one hrange
  exact orderOf_eq_prime ht2 hne

omit [Module.Finite (ZMod p) U] in
private theorem zq_exists_refl (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) :
    ∃ t ∈ A, IsRefl p (t : U ≃ₗ[ZMod p] U) := by
  by_contra h
  simp only [not_exists, not_and] at h
  have hset : {t : U ≃ₗ[ZMod p] U | t ∈ A ∧ IsRefl p t} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    exact h t
  have hbot : A = ⊥ := by
    rw [hgen, hset]
    exact Subgroup.closure_empty
  have hU : Nontrivial U :=
    Module.nontrivial_of_finrank_pos (R := ZMod p) (M := U) (by omega)
  obtain ⟨v, hv0⟩ := exists_ne (0 : U)
  let W : Submodule (ZMod p) U := Submodule.span (ZMod p) {v}
  have hW1 : finrank (ZMod p) W = 1 := by
    simpa only [W] using finrank_span_singleton (K := ZMod p) hv0
  have hinv : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W := by
    intro a ha w hw
    have ha1 : a = 1 := by
      have : a ∈ (⊥ : Subgroup (U ≃ₗ[ZMod p] U)) := by
        rw [← hbot]
        exact ha
      simpa using this
    simpa [ha1] using hw
  have hWne : W ≠ ⊥ := by
    intro hW
    have hvW : v ∈ W := by
      simp [W]
    rw [hW] at hvW
    exact hv0 (by simpa using hvW)
  have hWtop : W ≠ ⊤ := by
    intro hW
    rw [hW, finrank_top] at hW1
    omega
  rcases hirr.1 W hinv with hW | hW
  · exact hWne hW
  · exact hWtop hW

omit [Module.Finite (ZMod p) U] in
private theorem zq_closure_refl_eq_top (hgen : ReflGen p A) :
    Subgroup.closure {t : ↥A | IsRefl p (t : U ≃ₗ[ZMod p] U)} = ⊤ := by
  apply (Subgroup.map_subtype_inj (H := A)).mp
  rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
  have himg : A.subtype '' {t : ↥A | IsRefl p (t : U ≃ₗ[ZMod p] U)} =
      {t : U ≃ₗ[ZMod p] U | t ∈ A ∧ IsRefl p t} := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, hu⟩
    · rintro ⟨htA, ht⟩
      exact ⟨⟨t, htA⟩, ht, rfl⟩
  rw [himg]
  exact hgen.symm

omit [Module.Finite (ZMod p) U] in
theorem IsRefl.conj {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t)
    (g : U ≃ₗ[ZMod p] U) : IsRefl p (g * t * g⁻¹) := by
  constructor
  · calc
      (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht.1]; group
  · have hrange : LinearMap.range
        (((g * t * g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - LinearMap.id) =
        (LinearMap.range ((t : U →ₗ[ZMod p] U) - LinearMap.id)).map
          (g : U →ₗ[ZMod p] U) := by
      ext x
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨((t : U →ₗ[ZMod p] U) -
          (LinearMap.id : U →ₗ[ZMod p] U)) (g⁻¹ y), ⟨g⁻¹ y, rfl⟩, ?_⟩
        rw [← hy]
        simp
      · rintro ⟨y, ⟨z, hz⟩, hxy⟩
        refine ⟨g z, ?_⟩
        rw [← hxy, ← hz]
        simp
    rw [hrange, LinearEquiv.finrank_map_eq, ht.2]

theorem IsRefl.exists_ne_zero_fixed {s t : U ≃ₗ[ZMod p] U}
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hs : IsRefl p s) (ht : IsRefl p t) :
    ∃ v : U, v ≠ 0 ∧ s v = v ∧ t v = v := by
  let S : Submodule (ZMod p) U := LinearMap.ker ((s : U →ₗ[ZMod p] U) - LinearMap.id)
  let T : Submodule (ZMod p) U := LinearMap.ker ((t : U →ₗ[ZMod p] U) - LinearMap.id)
  have hS : finrank (ZMod p) S + 1 = Module.finrank (ZMod p) U := by
    have h := LinearMap.finrank_range_add_finrank_ker
      ((s : U →ₗ[ZMod p] U) - LinearMap.id)
    rw [hs.2] at h
    dsimp [S]
    omega
  have hT : finrank (ZMod p) T + 1 = Module.finrank (ZMod p) U := by
    have h := LinearMap.finrank_range_add_finrank_ker
      ((t : U →ₗ[ZMod p] U) - LinearMap.id)
    rw [ht.2] at h
    dsimp [T]
    omega
  have hsup : finrank (ZMod p) ↥(S ⊔ T) ≤ Module.finrank (ZMod p) U :=
    Submodule.finrank_le (S ⊔ T)
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq S T
  have hpos : 0 < finrank (ZMod p) ↥(S ⊓ T) := by omega
  have hne : S ⊓ T ≠ ⊥ := by
    intro hbot
    have hzero : finrank (ZMod p) ↥(S ⊓ T) = 0 := by rw [hbot, finrank_bot]
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨v, hv0, ?_, ?_⟩
  · have h : ((s : U →ₗ[ZMod p] U) -
        (LinearMap.id : U →ₗ[ZMod p] U)) v = 0 :=
      LinearMap.mem_ker.mp hv.1
    simpa [sub_eq_zero] using h
  · have h : ((t : U →ₗ[ZMod p] U) -
        (LinearMap.id : U →ₗ[ZMod p] U)) v = 0 :=
      LinearMap.mem_ker.mp hv.2
    simpa [sub_eq_zero] using h

omit [Module.Finite (ZMod p) U] in
theorem AbsIrred.exists_eq_smul_of_mem_center (hirr : AbsIrred p A) {z : ↥A}
    (hz : z ∈ Subgroup.center ↥A) :
    ∃ c : ZMod p, ((z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = c • LinearMap.id := by
  refine hirr.2 ((z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ?_
  intro a ha
  have hcomm : (⟨a, ha⟩ : ↥A) * z = z * ⟨a, ha⟩ :=
    Subgroup.mem_center_iff.mp hz ⟨a, ha⟩
  have hmap := congrArg
    (fun e : ↥A => ((e : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)) hcomm
  rw [Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.coe_toLinearMap_mul,
    LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp] at hmap
  simpa using hmap.symm

omit [Module.Finite (ZMod p) U] in
theorem AbsIrred.eq_one_of_mem_center (hirr : AbsIrred p A) {z : ↥A}
    (hz : z ∈ Subgroup.center ↥A) {v : U} (hv : v ≠ 0)
    (hzv : (z : U ≃ₗ[ZMod p] U) v = v) : z = 1 := by
  obtain ⟨c, hc⟩ := hirr.exists_eq_smul_of_mem_center hz
  have hcv : c • v = v := by
    have := congrArg (fun f : U →ₗ[ZMod p] U => f v) hc
    simpa [hzv] using this.symm
  have hc1 : c = 1 := by
    have h : (c - 1) • v = 0 := by
      rw [sub_smul, one_smul, hcv, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero_iff_left hv).mp h)
  have hz1 : ((z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = LinearMap.id := by
    rw [hc, hc1, one_smul]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have := congrArg (fun f : U →ₗ[ZMod p] U => f x) hz1
  simpa using this

omit [Module.Finite (ZMod p) U] in
theorem AbsIrred.orderOf_mk (hirr : AbsIrred p A) (g : ↥A) {v : U} (hv : v ≠ 0)
    (hgv : (g : U ≃ₗ[ZMod p] U) v = v) :
    orderOf (mk g) = orderOf g := by
  have hdiv : orderOf (mk g) ∣ orderOf g := by
    simpa only [QuotientGroup.coe_mk'] using
      orderOf_map_dvd (QuotientGroup.mk' (Subgroup.center A)) g
  have hpow : g ^ orderOf (mk g) = 1 := by
    refine hirr.eq_one_of_mem_center (z := g ^ orderOf (mk g)) (v := v) ?_ hv ?_
    · have h : mk (g ^ orderOf (mk g)) = 1 := by
        rw [QuotientGroup.mk_pow]
        exact pow_orderOf_eq_one (mk g)
      exact (QuotientGroup.eq_one_iff (N := Subgroup.center A)
        (g ^ orderOf (mk g))).mp h
    · rw [Subgroup.coe_pow, LinearEquiv.pow_apply]
      exact Function.IsFixedPt.iterate hgv (orderOf (mk g))
  exact Nat.dvd_antisymm hdiv (orderOf_dvd_of_pow_eq_one hpow)

theorem AbsIrred.mk_injOn_refl (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) {s t : ↥A}
    (hs : IsRefl p (s : U ≃ₗ[ZMod p] U))
    (ht : IsRefl p (t : U ≃ₗ[ZMod p] U)) (h : mk s = mk t) : s = t := by
  obtain ⟨v, hv0, hsv, htv⟩ := IsRefl.exists_ne_zero_fixed hn hs ht
  have hst_mem : s * t⁻¹ ∈ Subgroup.center ↥A := by
    apply (QuotientGroup.eq_one_iff (N := Subgroup.center A) (s * t⁻¹)).mp
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h]
    exact mul_inv_cancel _
  have hfix : ((s * t⁻¹ : ↥A) : U ≃ₗ[ZMod p] U) v = v := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply]
    have htinv : ((t : U ≃ₗ[ZMod p] U))⁻¹ v = v := by
      have h' := congrArg ((t : U ≃ₗ[ZMod p] U).symm) htv
      simp only [LinearEquiv.symm_apply_apply] at h'
      exact h'.symm
    rw [htinv, hsv]
  have hz1 : s * t⁻¹ = 1 := hirr.eq_one_of_mem_center hst_mem hv0 hfix
  calc
    s = s * t⁻¹ * t := by group
    _ = 1 * t := by rw [hz1]
    _ = t := one_mul t

theorem AbsIrred.orderOf_mk_mul_mk (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) {s t : ↥A}
    (hs : IsRefl p (s : U ≃ₗ[ZMod p] U))
    (ht : IsRefl p (t : U ≃ₗ[ZMod p] U)) :
    orderOf (mk s * mk t) = orderOf (s * t) := by
  obtain ⟨v, hv0, hsv, htv⟩ := IsRefl.exists_ne_zero_fixed hn hs ht
  rw [← QuotientGroup.mk_mul]
  exact hirr.orderOf_mk (s * t) hv0 (by
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, htv, hsv])

theorem AbsIrred.commute_mk_iff (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) {s t : ↥A}
    (ht : IsRefl p (t : U ≃ₗ[ZMod p] U)) :
    Commute (mk s) (mk t) ↔ Commute s t := by
  constructor
  · intro h
    have hconj : mk (s * t * s⁻¹) = mk t := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h.eq]
      group
    have hst : s * t * s⁻¹ = t :=
      hirr.mk_injOn_refl hn
        (by simpa [Subgroup.coe_mul, Subgroup.coe_inv] using
          ht.conj (s : U ≃ₗ[ZMod p] U)) ht hconj
    calc
      s * t = s * t * s⁻¹ * s := by group
      _ = t * s := by rw [hst]
  · intro h
    rw [commute_iff_eq, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h.eq]

theorem center_quotient_center_eq_bot (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) :
    Subgroup.center (↥A ⧸ Subgroup.center ↥A) = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hg : g ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro a
    have hcomm : ∀ t : ↥A, IsRefl p (t : U ≃ₗ[ZMod p] U) → g * t = t * g := by
      intro t ht
      have hcentral : ∀ y : ↥A ⧸ Subgroup.center ↥A, y * mk g = mk g * y :=
        Subgroup.mem_center_iff.mp hx
      have hgt : mk (g * t * g⁻¹) = mk t := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hcentral (mk t)]
        group
      have hrefl : IsRefl p ((g * t * g⁻¹ : ↥A) : U ≃ₗ[ZMod p] U) := by
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using
          ht.conj (g : U ≃ₗ[ZMod p] U)
      have hEq : g * t * g⁻¹ = t := hirr.mk_injOn_refl hn hrefl ht hgt
      calc
        g * t = g * t * g⁻¹ * g := by group
        _ = t * g := by rw [hEq]
    have hle : (⊤ : Subgroup ↥A) ≤ Subgroup.centralizer ({g} : Set ↥A) := by
      rw [← zq_closure_refl_eq_top hgen]
      apply (Subgroup.closure_le _).mpr
      intro t ht
      exact (Subgroup.mem_centralizer_singleton_iff).mpr (hcomm t ht).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top a))
  exact (QuotientGroup.eq_one_iff (N := Subgroup.center A) g).mpr hg

theorem exists_unique_refl_of_mem_reflImage (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) {x : ↥A ⧸ Subgroup.center ↥A}
    (hx : x ∈ reflImage p A) :
    ∃! t : ↥A, IsRefl p (t : U ≃ₗ[ZMod p] U) ∧ mk t = x := by
  obtain ⟨t, ht, rfl⟩ := hx
  refine ⟨t, ⟨ht, rfl⟩, ?_⟩
  intro t' ht'
  exact hirr.mk_injOn_refl hn ht'.1 ht ht'.2

omit [Module.Finite (ZMod p) U] in
private theorem zq_reflImage_eq_conj (hone : OneClass p A)
    {t₀ : U ≃ₗ[ZMod p] U} (ht₀A : t₀ ∈ A) (ht₀ : IsRefl p t₀) :
    reflImage p A = {x | IsConj (mk ⟨t₀, ht₀A⟩) x} := by
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨g, hgA, hgt⟩ := hone (t₀ : U ≃ₗ[ZMod p] U) ht₀A
      (t : U ≃ₗ[ZMod p] U) t.2 ht₀ ht
    rw [Set.mem_setOf_eq, isConj_iff]
    refine ⟨mk ⟨g, hgA⟩, ?_⟩
    calc
      mk ⟨g, hgA⟩ * mk ⟨t₀, ht₀A⟩ * (mk ⟨g, hgA⟩)⁻¹
          = mk (⟨g, hgA⟩ * ⟨t₀, ht₀A⟩ * ⟨g, hgA⟩⁻¹) := by
            rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      _ = mk ⟨t, t.2⟩ := by
        congr 1
        apply Subtype.ext
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hgt.symm
  · intro hx
    rw [Set.mem_setOf_eq, isConj_iff] at hx
    obtain ⟨c, hc⟩ := hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    refine ⟨g * ⟨t₀, ht₀A⟩ * g⁻¹, ?_, ?_⟩
    · simpa [Subgroup.coe_mul, Subgroup.coe_inv] using
        ht₀.conj (g : U ≃ₗ[ZMod p] U)
    · change mk (g * ⟨t₀, ht₀A⟩ * g⁻¹) = x
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact hc

omit [Module.Finite (ZMod p) U] in
private theorem zq_closure_reflImage_eq_top (hgen : ReflGen p A) :
    Subgroup.closure (reflImage p A) = ⊤ := by
  have hR : reflImage p A =
      QuotientGroup.mk '' {t : ↥A | IsRefl p (t : U ≃ₗ[ZMod p] U)} := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, rfl⟩
  rw [hR]
  have hmap := MonoidHom.map_closure (QuotientGroup.mk' (Subgroup.center A))
    {t : ↥A | IsRefl p (t : U ≃ₗ[ZMod p] U)}
  rw [zq_closure_refl_eq_top hgen] at hmap
  have himg : (QuotientGroup.mk' (Subgroup.center A)) ''
      {t : ↥A | IsRefl p (t : U ≃ₗ[ZMod p] U)} =
      QuotientGroup.mk '' {t : ↥A | IsRefl p (t : U ≃ₗ[ZMod p] U)} := by
    simp only [QuotientGroup.coe_mk']
  rw [himg] at hmap
  rw [← hmap]
  exact Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective (Subgroup.center A))

private theorem zq_refl_mem_closure (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hone : OneClass p A) {S : Set ↥A}
    (hS : ∀ s ∈ S, IsRefl p (s : U ≃ₗ[ZMod p] U)) (hSne : S.Nonempty)
    (hKmap : (Subgroup.closure S).map (QuotientGroup.mk' (Subgroup.center A)) = ⊤) :
    ∀ t : U ≃ₗ[ZMod p] U, ∀ htA : t ∈ A, IsRefl p t →
      (⟨t, htA⟩ : ↥A) ∈ Subgroup.closure S := by
  intro t htA ht
  obtain ⟨s₀, hs₀S⟩ := hSne
  have hs₀ : IsRefl p (s₀ : U ≃ₗ[ZMod p] U) := hS s₀ hs₀S
  obtain ⟨g, hgA, hgt⟩ := hone (s₀ : U ≃ₗ[ZMod p] U) s₀.2 t htA hs₀ ht
  let g' : ↥A := ⟨g, hgA⟩
  have hg'mem : (QuotientGroup.mk' (Subgroup.center A)) g' ∈
      (Subgroup.closure S).map (QuotientGroup.mk' (Subgroup.center A)) := by
    rw [hKmap]
    exact Subgroup.mem_top _
  obtain ⟨k, hkK, hk⟩ := Subgroup.mem_map.mp hg'mem
  have hk' : mk k = mk g' := by
    simpa only [QuotientGroup.coe_mk'] using hk
  have ht'eq : (⟨t, htA⟩ : ↥A) = g' * s₀ * g'⁻¹ := by
    apply Subtype.ext
    simpa [g', Subgroup.coe_mul, Subgroup.coe_inv] using hgt
  have hkconj : mk (k * s₀ * k⁻¹) = mk ⟨t, htA⟩ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hk', ht'eq]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hreflConj : IsRefl p ((k * s₀ * k⁻¹ : ↥A) : U ≃ₗ[ZMod p] U) := by
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using
      hs₀.conj (k : U ≃ₗ[ZMod p] U)
  have hkt : k * s₀ * k⁻¹ = ⟨t, htA⟩ :=
    hirr.mk_injOn_refl hn hreflConj ht hkconj
  rw [← hkt]
  exact Subgroup.mul_mem (Subgroup.closure S)
    (Subgroup.mul_mem (Subgroup.closure S) hkK (Subgroup.subset_closure hs₀S))
    (Subgroup.inv_mem (Subgroup.closure S) hkK)

theorem closure_eq_top_of_closure_mk_eq_top (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hone : OneClass p A) {S : Set ↥A}
    (hS : ∀ s ∈ S, IsRefl p (s : U ≃ₗ[ZMod p] U))
    (htop : Subgroup.closure (mk '' S) = ⊤) :
    Subgroup.closure S = ⊤ := by
  obtain ⟨t₀, ht₀A, ht₀⟩ := zq_exists_refl hgen hirr hn
  have hSne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hbot : Subgroup.closure (mk '' S) = ⊥ := by
      rw [h, Set.image_empty, Subgroup.closure_empty]
    have hbotTop : (⊥ : Subgroup (↥A ⧸ Subgroup.center ↥A)) = ⊤ := by
      rw [← hbot, htop]
    obtain ⟨v, hv0, hvv, _⟩ := IsRefl.exists_ne_zero_fixed hn ht₀ ht₀
    have hord : orderOf (mk ⟨t₀, ht₀A⟩) = 2 := by
      rw [hirr.orderOf_mk ⟨t₀, ht₀A⟩ hv0 (by simpa using hvv)]
      exact zq_orderOf_refl ht₀
    have htriv : (mk ⟨t₀, ht₀A⟩ : ↥A ⧸ Subgroup.center ↥A) = 1 := by
      have hmem : mk ⟨t₀, ht₀A⟩ ∈ (⊤ : Subgroup (↥A ⧸ Subgroup.center ↥A)) :=
        Subgroup.mem_top _
      rw [← hbotTop] at hmem
      exact Subgroup.mem_bot.mp hmem
    rw [htriv, orderOf_one] at hord
    omega
  have hKmap : (Subgroup.closure S).map (QuotientGroup.mk' (Subgroup.center A)) = ⊤ := by
    rw [MonoidHom.map_closure]
    have himg : (QuotientGroup.mk' (Subgroup.center A)) '' S = mk '' S := by
      simp only [QuotientGroup.coe_mk']
    rw [himg, htop]
  have hrefl_mem := zq_refl_mem_closure hirr hn hone hS hSne hKmap
  have htop_le : (⊤ : Subgroup ↥A) ≤ Subgroup.closure S := by
    rw [← zq_closure_refl_eq_top hgen]
    apply (Subgroup.closure_le _).mpr
    intro t ht
    simpa using hrefl_mem (t : U ≃ₗ[ZMod p] U) t.2 ht
  exact top_le_iff.mp htop_le

theorem pair_reflImage (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) (hone : OneClass p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3) :
    CFSG.Blueprint.Fischer.Pair (↥A ⧸ Subgroup.center ↥A) (reflImage p A) := by
  have hU : Finite U := Module.finite_of_finite (ZMod p)
  have hE : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      DFunLike.coe_injective
  have hA : Finite ↥A := inferInstance
  have hQ : Finite (↥A ⧸ Subgroup.center ↥A) := inferInstance
  obtain ⟨t₀, ht₀A, ht₀⟩ := zq_exists_refl hgen hirr hn
  refine ⟨hQ, ⟨mk ⟨t₀, ht₀A⟩, ?_⟩, ?_, ?_, ?_⟩
  · exact zq_reflImage_eq_conj hone ht₀A ht₀
  · intro e he
    obtain ⟨t, ht, rfl⟩ := he
    obtain ⟨v, hv0, hvv, _⟩ := IsRefl.exists_ne_zero_fixed hn ht ht
    have hord : orderOf (mk t) = 2 := by
      rw [hirr.orderOf_mk t hv0 hvv, zq_orderOf_refl ht]
    simpa using hord
  · intro e he f hf
    obtain ⟨s, hs, rfl⟩ := he
    obtain ⟨t, ht, rfl⟩ := hf
    have hpos : 0 < orderOf (mk s * mk t) :=
      IsOfFinOrder.orderOf_pos (isOfFinOrder_of_finite _)
    have hle : orderOf (mk s * mk t) ≤ 3 := by
      rw [hirr.orderOf_mk_mul_mk hn hs ht]
      have h := h3 (s : U ≃ₗ[ZMod p] U) s.2 (t : U ≃ₗ[ZMod p] U) t.2 hs ht
      rw [← Subgroup.coe_mul, Subgroup.orderOf_coe] at h
      exact h
    have hb : orderOf (mk s * mk t) = 1 ∨ orderOf (mk s * mk t) = 2 ∨
        orderOf (mk s * mk t) = 3 := by omega
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hb
  · exact zq_closure_reflImage_eq_top hgen

end CFSG.StandardType.ZS
