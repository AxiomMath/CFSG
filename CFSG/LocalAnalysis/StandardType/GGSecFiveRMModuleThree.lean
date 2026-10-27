module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section

namespace CFSG.StandardType

section Module

private lemma ggLinMove_smul_involution
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (r : V ≃ₗ[ZMod p] V) (hr : r * r = 1) :
    ∀ x ∈ ggLinMove r, r x = -x := by
  rintro x ⟨v, rfl⟩
  have hr' : r (r v) = v := by
    have h := congrArg (fun e : V ≃ₗ[ZMod p] V => e v) hr
    simpa [LinearEquiv.mul_apply] using h
  show r (r v - v) = -(r v - v)
  rw [map_sub, hr']
  abel

private lemma two_ne_zero_zmod
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) Nat.prime_two).mp hdvd)

private structure ReflData
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (r : V ≃ₗ[ZMod p] V) (hr : GGLinRefl r) where
  e : V
  he : e ∈ ggLinMove r
  he0 : e ≠ 0
  span_eq : ggLinMove r = Submodule.span (ZMod p) ({e} : Set V)
  φ : V →ₗ[ZMod p] ZMod p
  spec : ∀ v, r v = v - (φ v) • e

private noncomputable def reflData
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (r : V ≃ₗ[ZMod p] V) (hr : GGLinRefl r) :
    ReflData r hr := by
  haveI : Nontrivial (ggLinMove r) :=
    Module.nontrivial_of_finrank_eq_succ (R := ZMod p) (M := ggLinMove r) (n := 0) (by simpa using hr.2)
  let e : ggLinMove r := Classical.choose (exists_ne (0 : ggLinMove r))
  have he0 : e ≠ 0 := Classical.choose_spec (exists_ne (0 : ggLinMove r))
  have he0' : (e : V) ≠ 0 := by
    intro h
    exact he0 (Subtype.ext (by simpa using h))
  have hspan : ggLinMove r = ZMod p ∙ (e : V) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hr.2 e.2 he0'
  let f : V →ₗ[ZMod p] V := r.toLinearMap - LinearMap.id
  let g : V →ₗ[ZMod p] (ZMod p ∙ (e : V)) :=
    LinearMap.codRestrict (ZMod p ∙ (e : V)) (-f) (fun v => by
      rw [LinearMap.neg_apply, Submodule.neg_mem_iff, ← hspan]
      exact ⟨v, rfl⟩)
  let ψ : ZMod p ≃ₗ[ZMod p] (ZMod p ∙ (e : V)) :=
    LinearEquiv.toSpanNonzeroSingleton (ZMod p) V (e : V) he0'
  let φ : V →ₗ[ZMod p] ZMod p := ψ.symm.toLinearMap.comp g
  refine ⟨e, e.2, he0', hspan, φ, ?_⟩
  intro v
  have h1 : ψ (φ v) = g v := LinearEquiv.apply_symm_apply ψ (g v)
  have h2 : ((ψ (φ v) : ZMod p ∙ (e:V)) : V) = (φ v) • (e:V) := by
    rw [LinearEquiv.toSpanNonzeroSingleton_apply]
  have h3 : ((g v : ZMod p ∙ (e:V)) : V) = -f v := by
    rw [LinearMap.codRestrict_apply, LinearMap.neg_apply]
  have h4 : (φ v) • (e:V) = -f v := by rw [← h2, h1, h3]
  have h5 : (φ v) • (e:V) = v - r v := by
    rw [h4]; simp [f, LinearMap.sub_apply, LinearMap.id_apply]
  rw [h5]; abel

private lemma reflData_phi_self
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {r : V ≃ₗ[ZMod p] V} {hr : GGLinRefl r}
    (d : ReflData r hr) : d.φ d.e = 2 := by
  have h := d.spec d.e
  have hr1 : r d.e = -d.e := ggLinMove_smul_involution r hr.1 d.e d.he
  rw [hr1] at h
  have h2 : ((d.φ d.e) - 2) • d.e = 0 := by
    rw [sub_smul]
    have hh : (d.φ d.e) • d.e = (2 : ZMod p) • d.e := by
      rw [two_smul]
      have h1 : -d.e + (d.φ d.e) • d.e = d.e := by rw [h]; abel
      calc (d.φ d.e) • d.e = -d.e + (d.φ d.e) • d.e + d.e := by abel
        _ = d.e + d.e := by rw [h1]
    rw [hh, sub_self]
  rcases (smul_eq_zero.mp h2) with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 d.he0

private lemma eq_one_of_ggLinMove_eq_bot
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (g : V ≃ₗ[ZMod p] V)
    (h : ggLinMove g = ⊥) : g = 1 := by
  have hf : g.toLinearMap - LinearMap.id = 0 := LinearMap.range_eq_bot.mp h
  ext v
  change g v = v
  have hv := congrArg (fun (f : V →ₗ[ZMod p] V) => f v) hf
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply] at hv
  exact sub_eq_zero.mp hv

private lemma ggLinMove_ne_of_refl_ne
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (S : Set (V ≃ₗ[ZMod p] V))
    (hnotr : ∀ g ∈ Subgroup.closure S, g ≠ 1 →
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}))
    {a b : V ≃ₗ[ZMod p] V} (ha : GGLinRefl a) (hb : GGLinRefl b)
    (haS : a ∈ Subgroup.closure S) (hbS : b ∈ Subgroup.closure S) (hne : a ≠ b) :
    ggLinMove a ≠ ggLinMove b := by
  intro heq
  have hle : ggLinMove (a * b) ≤ ggLinMove a := by
    rintro x ⟨v, rfl⟩
    have hdecomp : ((a * b).toLinearMap - LinearMap.id : V →ₗ[ZMod p] V) v =
        ((a.toLinearMap - LinearMap.id : V →ₗ[ZMod p] V) (b v)) +
          ((b.toLinearMap - LinearMap.id : V →ₗ[ZMod p] V) v) := by
      show (a * b) v - v = (a (b v) - b v) + (b v - v)
      rw [LinearEquiv.mul_apply]
      abel
    rw [hdecomp]
    refine add_mem ⟨b v, rfl⟩ ?_
    rw [heq]
    exact ⟨v, rfl⟩
  have hfix : ggLinMove (a * b) ≤ ggLinFix ({a * b} : Set (V ≃ₗ[ZMod p] V)) := by
    intro x hx g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have hx_a : x ∈ ggLinMove a := hle hx
    rw [LinearEquiv.mul_apply]
    have hbx : b x = -x := ggLinMove_smul_involution b hb.1 x (heq ▸ hx_a)
    have hax : a x = -x := ggLinMove_smul_involution a ha.1 x hx_a
    rw [hbx, map_neg, hax, neg_neg]
  have hline : ggLinMove (a * b) = ggLinMove a := by
    refine le_antisymm hle ?_
    have hne_bot : ggLinMove (a * b) ≠ ⊥ := by
      intro hbot
      have hg1 : a * b = 1 := eq_one_of_ggLinMove_eq_bot (a * b) hbot
      have hab : a = b := by
        calc a = a * (b * b) := by rw [hb.1, mul_one]
          _ = (a * b) * b := by rw [mul_assoc]
          _ = b := by rw [hg1, one_mul]
      exact hne hab
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
    have hw_a : w ∈ ggLinMove a := hle hw
    have d_a := reflData a ha
    have hw_span : w ∈ Submodule.span (ZMod p) ({d_a.e} : Set V) := by
      rw [← d_a.span_eq]; exact hw_a
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw_span
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hw0 hc.symm
    have he_eq : d_a.e = c⁻¹ • w := by
      rw [← hc, inv_smul_smul₀ hc0]
    have he_mem : d_a.e ∈ ggLinMove (a * b) := by
      rw [he_eq]
      exact Submodule.smul_mem _ _ hw
    rw [d_a.span_eq]
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr he_mem
  by_cases hg1 : a * b = 1
  · have hab : a = b := by
      calc a = a * (b * b) := by rw [hb.1, mul_one]
        _ = (a * b) * b := by rw [mul_assoc]
        _ = b := by rw [hg1, one_mul]
    exact hne hab
  · have hgS : a * b ∈ Subgroup.closure S := Subgroup.mul_mem _ haS hbS
    have hfin : Module.finrank (ZMod p) (ggLinMove (a * b)) = 1 := by
      rw [hline]; exact ha.2
    exact (hnotr (a * b) hgS hg1) ⟨hfin, hfix⟩

private lemma linearIndependent_pair_of_span_ne
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : Submodule.span (ZMod p) ({x} : Set V) ≠ Submodule.span (ZMod p) ({y} : Set V)) :
    LinearIndependent (ZMod p) ![x, y] := by
  rw [linearIndependent_fin2]
  constructor
  · simpa using hy
  · intro a ha
    have ha' : a • y = x := by simpa using ha
    apply h
    have hxmem : x ∈ Submodule.span (ZMod p) ({y} : Set V) :=
      Submodule.mem_span_singleton.mpr ⟨a, ha'⟩
    have hle1 : Submodule.span (ZMod p) ({x} : Set V) ≤ Submodule.span (ZMod p) ({y} : Set V) :=
      Submodule.span_le.mpr (by rintro z rfl; exact hxmem)
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ha'
      exact hx ha'.symm
    have hle2 : Submodule.span (ZMod p) ({y} : Set V) ≤ Submodule.span (ZMod p) ({x} : Set V) := by
      rw [Submodule.span_singleton_le_iff_mem]
      have hy_eq : y = a⁻¹ • x := by rw [← ha', inv_smul_smul₀ ha0]
      rw [hy_eq]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
    exact le_antisymm hle1 hle2

private lemma op3
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {t : V ≃ₗ[ZMod p] V} {x : V} {c : ZMod p}
    (h2 : t (t x) = (c - 2) • t x - x) :
    t (t (t x)) = ((c - 1) * (c - 3)) • t x - (c - 2) • x := by
  rw [h2]
  rw [map_sub, map_smul, h2]
  module

private lemma op4
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {t : V ≃ₗ[ZMod p] V} {x : V} {c : ZMod p}
    (h2 : t (t x) = (c - 2) • t x - x) :
    t (t (t (t x))) = (c - 2)^2 • t (t x) - (2 * (c - 2)) • t x + x := by
  have h3 : t (t (t x)) = (c - 2) • t (t x) - t x := by
    rw [h2]; rw [map_sub, map_smul]; rw [h2]
  calc t (t (t (t x)))
      = t ((c - 2) • t (t x) - t x) := by rw [h3]
    _ = (c - 2) • t (t (t x)) - t (t x) := by rw [map_sub, map_smul]
    _ = (c - 2) • ((c - 2) • t (t x) - t x) - t (t x) := by rw [h3]
    _ = (c - 2)^2 • t (t x) - (2 * (c - 2)) • t x + x := by
          rw [h2]; module

private lemma op4_cancel
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {t : V ≃ₗ[ZMod p] V} {x : V} {c : ZMod p}
    (h2 : t (t x) = (c - 2) • t x - x) (h4x : t (t (t (t x))) = x)
    (hc2 : c - 2 ≠ 0) :
    (c - 2) • t x = (2 : ZMod p) • x := by
  have h4 := op4 h2
  rw [h4x] at h4
  have hA : (c - 2)^2 • t (t x) - (2 * (c - 2)) • t x = 0 := by
    have h := congrArg (fun w => w - x) h4.symm
    simpa using h
  have hZ : (c - 2) • ((c - 2) • t (t x) - (2 : ZMod p) • t x) = 0 := by
    rw [show (c - 2)^2 • t (t x) - (2 * (c - 2)) • t x =
        (c - 2) • ((c - 2) • t (t x) - (2 : ZMod p) • t x) from by module] at hA
    exact hA
  have hZ' : (c - 2) • t (t x) - (2 : ZMod p) • t x = 0 := by
    rcases smul_eq_zero.mp hZ with h | h
    · exact absurd h hc2
    · exact h
  have ht : t ((c - 2) • t x - (2 : ZMod p) • x) = 0 := by
    rw [map_sub, map_smul, map_smul]
    exact hZ'
  have ht0 : t ((c - 2) • t x - (2 : ZMod p) • x) = t 0 := by
    rw [ht, map_zero]
  have hZ0 := t.injective ht0
  rwa [sub_eq_zero] at hZ0

private lemma refl_commutator
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {r s : V ≃ₗ[ZMod p] V} {e e' : V}
    (φr φs : V →ₗ[ZMod p] ZMod p)
    (hspec_r : ∀ v, r v = v - (φr v) • e)
    (hspec_s : ∀ v, s v = v - (φs v) • e') :
    ∀ v, r (s v) - s (r v) = (φs v * φr e') • e - (φr v * φs e) • e' := by
  intro v
  rw [hspec_s v, hspec_r v]
  rw [map_sub, map_smul, hspec_r e', map_sub, map_smul, hspec_s e]
  rw [hspec_r v, hspec_s v]
  module

private lemma pair_relation_three
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {r s : V ≃ₗ[ZMod p] V} (hr : GGLinRefl r) (hs : GGLinRefl s)
    (d_r : ReflData r hr) (d_s : ReflData s hs)
    (hind : LinearIndependent (ZMod p) ![d_r.e, d_s.e])
    (hp2 : p ≠ 2) (ho : orderOf (r * s) = 3) :
    d_r.φ d_s.e * d_s.φ d_r.e = 1 := by
  have h2p : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  have hre : r d_r.e = -d_r.e := ggLinMove_smul_involution r hr.1 d_r.e d_r.he
  have hse : s d_s.e = -d_s.e := ggLinMove_smul_involution s hs.1 d_s.e d_s.he
  set a : ZMod p := d_r.φ d_s.e with ha
  set a' : ZMod p := d_s.φ d_r.e with ha'
  set c : ZMod p := a * a' with hc
  set t : V ≃ₗ[ZMod p] V := r * s with ht
  have h_te : t d_r.e = (c - 1) • d_r.e - a' • d_s.e := by
    rw [ht, LinearEquiv.mul_apply, d_s.spec d_r.e]
    rw [map_sub, map_smul, hre, d_r.spec d_s.e]
    rw [← ha, ← ha', hc]
    module
  have h_te' : t d_s.e = a • d_r.e - d_s.e := by
    rw [ht, LinearEquiv.mul_apply, hse]
    rw [map_neg, d_r.spec d_s.e]
    rw [← ha]
    module
  have ht2e : t (t d_r.e) = (c - 2) • t d_r.e - d_r.e := by
    rw [h_te]
    simp only [map_sub, map_smul]
    rw [h_te, h_te']
    rw [hc]
    module
  have ht2e' : t (t d_s.e) = (c - 2) • t d_s.e - d_s.e := by
    rw [h_te']
    simp only [map_sub, map_smul]
    rw [h_te, h_te']
    rw [hc]
    module
  have hot : orderOf t = 3 := by rw [ht]; exact ho
  have ho3 : t ^ 3 = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [hot] at h
  have ht3e' : t (t (t d_s.e)) = d_s.e := by
    have h := congrArg (fun (u : V ≃ₗ[ZMod p] V) => u d_s.e) ho3
    simpa [LinearEquiv.pow_apply, Function.iterate_succ_apply',
      Function.iterate_zero_apply] using h
  have hrel : ((c - 1) * (c - 3) * a) • d_r.e +
      (-((c - 1) * (c - 3)) - (c - 2) - 1) • d_s.e = 0 := by
    have h3 : t (t (t d_s.e)) = ((c - 1) * (c - 3)) • t d_s.e - (c - 2) • d_s.e :=
      op3 ht2e'
    rw [ht3e'] at h3
    rw [h_te'] at h3
    have h3' : ((c - 1) * (c - 3)) • (a • d_r.e - d_s.e) - (c - 2) • d_s.e = d_s.e := h3.symm
    have h4 := sub_eq_zero.mpr h3'
    have heq : ((c - 1) * (c - 3) * a) • d_r.e +
        (-((c - 1) * (c - 3)) - (c - 2) - 1) • d_s.e =
        ((c - 1) * (c - 3)) • (a • d_r.e - d_s.e) - (c - 2) • d_s.e - d_s.e := by
      module
    rw [heq]
    exact h4
  have hcoeff := (LinearIndependent.pair_iff.mp hind) ((c - 1) * (c - 3) * a)
      (-((c - 1) * (c - 3)) - (c - 2) - 1) hrel
  have hQ : -((c - 1) * (c - 3)) - (c - 2) - 1 = 0 := hcoeff.2
  have hP : (c - 1) * (c - 3) * a = 0 := hcoeff.1
  have hc12 : (c - 1) * (c - 2) = 0 := by
    have h := hQ
    rw [show -((c - 1) * (c - 3)) - (c - 2) - 1 = -((c - 1) * (c - 2)) from by ring] at h
    exact neg_eq_zero.mp h
  rcases mul_eq_zero.mp hc12 with h1 | h2
  · have hc1 : c = 1 := sub_eq_zero.mp h1
    have hres : a * a' = 1 := by rw [← hc]; exact hc1
    simpa [ha, ha'] using hres
  · exfalso
    have hc2 : c = 2 := sub_eq_zero.mp h2
    have ha0 : a = 0 := by
      have h := hP
      rw [hc2] at h
      have h' : (2 - 1 : ZMod p) * (2 - 3) * a = -a := by ring
      rw [h'] at h
      exact neg_eq_zero.mp h
    have hc0 : c = 0 := by rw [hc, ha0, zero_mul]
    rw [hc0] at hc2
    exact h2p hc2.symm

private lemma pair_relation_four
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {r s : V ≃ₗ[ZMod p] V} (hr : GGLinRefl r) (hs : GGLinRefl s)
    (d_r : ReflData r hr) (d_s : ReflData s hs)
    (hind : LinearIndependent (ZMod p) ![d_r.e, d_s.e])
    (hp2 : p ≠ 2) (ho : orderOf (r * s) = 4) :
    d_r.φ d_s.e * d_s.φ d_r.e = 2 := by
  have h2p : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  have hre : r d_r.e = -d_r.e := ggLinMove_smul_involution r hr.1 d_r.e d_r.he
  have hse : s d_s.e = -d_s.e := ggLinMove_smul_involution s hs.1 d_s.e d_s.he
  set a : ZMod p := d_r.φ d_s.e with ha
  set a' : ZMod p := d_s.φ d_r.e with ha'
  set c : ZMod p := a * a' with hc
  set t : V ≃ₗ[ZMod p] V := r * s with ht
  have h_te : t d_r.e = (c - 1) • d_r.e - a' • d_s.e := by
    rw [ht, LinearEquiv.mul_apply, d_s.spec d_r.e]
    rw [map_sub, map_smul, hre, d_r.spec d_s.e]
    rw [← ha, ← ha', hc]
    module
  have h_te' : t d_s.e = a • d_r.e - d_s.e := by
    rw [ht, LinearEquiv.mul_apply, hse]
    rw [map_neg, d_r.spec d_s.e]
    rw [← ha]
    module
  have ht2e : t (t d_r.e) = (c - 2) • t d_r.e - d_r.e := by
    rw [h_te]
    simp only [map_sub, map_smul]
    rw [h_te, h_te']
    rw [hc]
    module
  have ht2e' : t (t d_s.e) = (c - 2) • t d_s.e - d_s.e := by
    rw [h_te']
    simp only [map_sub, map_smul]
    rw [h_te, h_te']
    rw [hc]
    module
  have hot : orderOf t = 4 := by rw [ht]; exact ho
  have ho4 : t ^ 4 = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [hot] at h
  have ht4e' : t (t (t (t d_s.e))) = d_s.e := by
    have h := congrArg (fun (u : V ≃ₗ[ZMod p] V) => u d_s.e) ho4
    simpa [LinearEquiv.pow_apply, Function.iterate_succ_apply',
      Function.iterate_zero_apply] using h
  by_cases hc2 : c - 2 = 0
  · have hc_eq : c = 2 := sub_eq_zero.mp hc2
    have hres : a * a' = 2 := by rw [← hc]; exact hc_eq
    simpa [ha, ha'] using hres
  · exfalso
    have hcancel' : (c - 2) • t d_s.e = (2 : ZMod p) • d_s.e := op4_cancel ht2e' ht4e' hc2
    have hrel' : ((c - 2) * a) • d_r.e + (-(c - 2) - 2) • d_s.e = 0 := by
      have h := hcancel'
      rw [h_te'] at h
      have h0 : (c - 2) • (a • d_r.e - d_s.e) - (2 : ZMod p) • d_s.e = 0 := sub_eq_zero.mpr h
      have heq : ((c - 2) * a) • d_r.e + (-(c - 2) - 2) • d_s.e =
          (c - 2) • (a • d_r.e - d_s.e) - (2 : ZMod p) • d_s.e := by module
      rw [heq]; exact h0
    have hcoeff' := (LinearIndependent.pair_iff.mp hind) ((c - 2) * a) (-(c - 2) - 2) hrel'
    have hc0 : c = 0 := by
      have h := hcoeff'.2
      have h' : -(c - 2) - 2 = -c := by ring
      rw [h'] at h
      exact neg_eq_zero.mp h
    have ha0 : a = 0 := by
      have h := hcoeff'.1
      rw [hc0] at h
      have h' : (0 - 2 : ZMod p) * a = -((2 : ZMod p) * a) := by ring
      rw [h'] at h
      have h2 : (2 : ZMod p) * a = 0 := neg_eq_zero.mp h
      exact (mul_eq_zero.mp h2).resolve_left h2p
    have ht4e : t (t (t (t d_r.e))) = d_r.e := by
      have h := congrArg (fun (u : V ≃ₗ[ZMod p] V) => u d_r.e) ho4
      simpa [LinearEquiv.pow_apply, Function.iterate_succ_apply',
        Function.iterate_zero_apply] using h
    have hcancel : (c - 2) • t d_r.e = (2 : ZMod p) • d_r.e := op4_cancel ht2e ht4e hc2
    have hrel'' : ((c - 2) * (c - 1) - 2) • d_r.e + (-(c - 2) * a') • d_s.e = 0 := by
      have h := hcancel
      rw [h_te] at h
      have h0 : (c - 2) • ((c - 1) • d_r.e - a' • d_s.e) - (2 : ZMod p) • d_r.e = 0 := sub_eq_zero.mpr h
      have heq : ((c - 2) * (c - 1) - 2) • d_r.e + (-(c - 2) * a') • d_s.e =
          (c - 2) • ((c - 1) • d_r.e - a' • d_s.e) - (2 : ZMod p) • d_r.e := by module
      rw [heq]; exact h0
    have hcoeff'' := (LinearIndependent.pair_iff.mp hind) ((c - 2) * (c - 1) - 2) (-(c - 2) * a') hrel''
    have ha'0 : a' = 0 := by
      have h := hcoeff''.2
      rw [hc0] at h
      have h' : -((0 : ZMod p) - 2) * a' = (2 : ZMod p) * a' := by ring
      rw [h'] at h
      exact (mul_eq_zero.mp h).resolve_left h2p
    have hcomm : r * s = s * r := by
      ext v
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      have h := refl_commutator d_r.φ d_s.φ d_r.spec d_s.spec v
      rw [← ha, ha0, ← ha', ha'0] at h
      have h' : r (s v) - s (r v) = 0 := by simpa using h
      exact sub_eq_zero.mp h'
    have ht2 : t ^ 2 = 1 := by
      rw [ht, pow_two]
      calc (r * s) * (r * s) = r * (s * (r * s)) := by rw [mul_assoc]
        _ = r * ((s * r) * s) := by rw [← mul_assoc s r s]
        _ = r * ((r * s) * s) := by rw [← hcomm]
        _ = (r * r) * (s * s) := by rw [← mul_assoc r (r * s) s, ← mul_assoc r r s, mul_assoc]
        _ = 1 := by rw [hr.1, hs.1, one_mul]
    have hdvd : orderOf t ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr ht2
    have hle : orderOf t ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    rw [hot] at hle
    omega

private lemma phi_zero_of_commute
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {r s : V ≃ₗ[ZMod p] V} (hr : GGLinRefl r) (hs : GGLinRefl s)
    (d_r : ReflData r hr) (d_s : ReflData s hs)
    (hind : LinearIndependent (ZMod p) ![d_r.e, d_s.e])
    (hcomm : r * s = s * r) (hp2 : p ≠ 2) :
    d_r.φ d_s.e = 0 ∧ d_s.φ d_r.e = 0 := by
  have h2p : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  set a : ZMod p := d_r.φ d_s.e with ha
  set a' : ZMod p := d_s.φ d_r.e with ha'
  have hcomm_apply : ∀ v, r (s v) = s (r v) := by
    intro v
    have h := congrArg (fun (u : V ≃ₗ[ZMod p] V) => u v) hcomm
    simpa [LinearEquiv.mul_apply] using h
  have hlhs1 : r (s d_s.e) - s (r d_s.e) = 0 := by
    rw [← hcomm_apply d_s.e, sub_self]
  have h1 := refl_commutator d_r.φ d_s.φ d_r.spec d_s.spec d_s.e
  have hrel1 : (2 * a) • d_r.e + (-(a * a')) • d_s.e = 0 := by
    rw [hlhs1] at h1
    rw [← ha, ← ha', reflData_phi_self d_s] at h1
    have heq : (2 * a) • d_r.e + (-(a * a')) • d_s.e =
        (2 * a) • d_r.e - (a * a') • d_s.e := by module
    rw [heq]; exact h1.symm
  have hcoeff1 := (LinearIndependent.pair_iff.mp hind) (2 * a) (-(a * a')) hrel1
  have ha0 : a = 0 := (mul_eq_zero.mp hcoeff1.1).resolve_left h2p
  have hlhs2 : r (s d_r.e) - s (r d_r.e) = 0 := by
    rw [← hcomm_apply d_r.e, sub_self]
  have h2 := refl_commutator d_r.φ d_s.φ d_r.spec d_s.spec d_r.e
  have hrel2 : (a' * a) • d_r.e + (-(2 * a')) • d_s.e = 0 := by
    rw [hlhs2] at h2
    rw [← ha, ← ha', reflData_phi_self d_r] at h2
    have heq : (a' * a) • d_r.e + (-(2 * a')) • d_s.e =
        (a' * a) • d_r.e - (2 * a') • d_s.e := by module
    rw [heq]; exact h2.symm
  have hcoeff2 := (LinearIndependent.pair_iff.mp hind) (a' * a) (-(2 * a')) hrel2
  have ha'0 : a' = 0 := by
    have h2 : (2 : ZMod p) * a' = 0 := neg_eq_zero.mp hcoeff2.2
    exact (mul_eq_zero.mp h2).resolve_left h2p
  exact ⟨by simpa [ha] using ha0, by simpa [ha'] using ha'0⟩

private lemma four_sub_ne_zero
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {c1 c2 : ZMod p}
    (h1 : c1 = 1 ∨ c1 = 2) (h2 : c2 = 1 ∨ c2 = 2) (h : c1 = 1 ∨ c2 = 1) :
    (4 : ZMod p) - c1 - c2 ≠ 0 := by
  have h2p : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  rcases h with hc | hc
  · rcases h2 with h2 | h2
    · rw [hc, h2]
      have : (4 : ZMod p) - 1 - 1 = 2 := by ring
      rw [this]; exact h2p
    · rw [hc, h2]
      have : (4 : ZMod p) - 1 - 2 = 1 := by ring
      rw [this]; exact one_ne_zero
  · rcases h1 with h1 | h1
    · rw [h1, hc]
      have : (4 : ZMod p) - 1 - 1 = 2 := by ring
      rw [this]; exact h2p
    · rw [h1, hc]
      have : (4 : ZMod p) - 2 - 1 = 1 := by ring
      rw [this]; exact one_ne_zero

theorem ggLin_three_indep
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (hp2 : p ≠ 2) (r₁ r₂ r₃ : V ≃ₗ[ZMod p] V)
    (h₁ : GGLinRefl r₁) (h₂ : GGLinRefl r₂) (h₃ : GGLinRefl r₃)
    (h13 : r₁ * r₃ = r₃ * r₁) (hne : r₁ ≠ r₃)
    (m₁ m₂ : ℕ) (hm₁ : m₁ = 3 ∨ m₁ = 4) (hm₂ : m₂ = 3 ∨ m₂ = 4) (hm : m₁ = 3 ∨ m₂ = 3)
    (ho₁ : orderOf (r₁ * r₂) = m₁) (ho₂ : orderOf (r₂ * r₃) = m₂)
    (hnotr : ∀ g ∈ Subgroup.closure ({r₁, r₂, r₃} : Set (V ≃ₗ[ZMod p] V)), g ≠ 1 →
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g})) :
    3 ≤ Module.finrank (ZMod p) ↥(ggLinMove r₁ ⊔ ggLinMove r₂ ⊔ ggLinMove r₃) := by
  have h2p : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  let d₁ : ReflData r₁ h₁ := reflData r₁ h₁
  let d₂ : ReflData r₂ h₂ := reflData r₂ h₂
  let d₃ : ReflData r₃ h₃ := reflData r₃ h₃
  have hS1 : r₁ ∈ Subgroup.closure ({r₁, r₂, r₃} : Set (V ≃ₗ[ZMod p] V)) :=
    Subgroup.subset_closure (by simp)
  have hS2 : r₂ ∈ Subgroup.closure ({r₁, r₂, r₃} : Set (V ≃ₗ[ZMod p] V)) :=
    Subgroup.subset_closure (by simp)
  have hS3 : r₃ ∈ Subgroup.closure ({r₁, r₂, r₃} : Set (V ≃ₗ[ZMod p] V)) :=
    Subgroup.subset_closure (by simp)
  have hne12 : r₁ ≠ r₂ := by
    intro h
    have h1 : r₁ * r₂ = 1 := by rw [h]; exact h₂.1
    rw [h1, orderOf_one] at ho₁
    rcases hm₁ with h3 | h4 <;> omega
  have hne23 : r₂ ≠ r₃ := by
    intro h
    have h1 : r₂ * r₃ = 1 := by rw [h]; exact h₃.1
    rw [h1, orderOf_one] at ho₂
    rcases hm₂ with h3 | h4 <;> omega
  have hspan12 : Submodule.span (ZMod p) ({d₁.e} : Set V) ≠
      Submodule.span (ZMod p) ({d₂.e} : Set V) := by
    intro hspan
    exact (ggLinMove_ne_of_refl_ne ({r₁, r₂, r₃} : Set (V ≃ₗ[ZMod p] V)) hnotr h₁ h₂ hS1 hS2 hne12)
      (by rw [d₁.span_eq, d₂.span_eq]; exact hspan)
  have hspan23 : Submodule.span (ZMod p) ({d₂.e} : Set V) ≠
      Submodule.span (ZMod p) ({d₃.e} : Set V) := by
    intro hspan
    exact (ggLinMove_ne_of_refl_ne ({r₁, r₂, r₃} : Set (V ≃ₗ[ZMod p] V)) hnotr h₂ h₃ hS2 hS3 hne23)
      (by rw [d₂.span_eq, d₃.span_eq]; exact hspan)
  have hspan13 : Submodule.span (ZMod p) ({d₁.e} : Set V) ≠
      Submodule.span (ZMod p) ({d₃.e} : Set V) := by
    intro hspan
    exact (ggLinMove_ne_of_refl_ne ({r₁, r₂, r₃} : Set (V ≃ₗ[ZMod p] V)) hnotr h₁ h₃ hS1 hS3 hne)
      (by rw [d₁.span_eq, d₃.span_eq]; exact hspan)
  have hind12 : LinearIndependent (ZMod p) ![d₁.e, d₂.e] :=
    linearIndependent_pair_of_span_ne d₁.he0 d₂.he0 hspan12
  have hind23 : LinearIndependent (ZMod p) ![d₂.e, d₃.e] :=
    linearIndependent_pair_of_span_ne d₂.he0 d₃.he0 hspan23
  have hind13 : LinearIndependent (ZMod p) ![d₁.e, d₃.e] :=
    linearIndependent_pair_of_span_ne d₁.he0 d₃.he0 hspan13
  have h13zero := phi_zero_of_commute h₁ h₃ d₁ d₃ hind13 h13 hp2
  have hc1_three : m₁ = 3 → d₁.φ d₂.e * d₂.φ d₁.e = 1 :=
    fun h3 => pair_relation_three h₁ h₂ d₁ d₂ hind12 hp2 (by rw [ho₁, h3])
  have hc1_four : m₁ = 4 → d₁.φ d₂.e * d₂.φ d₁.e = 2 :=
    fun h4 => pair_relation_four h₁ h₂ d₁ d₂ hind12 hp2 (by rw [ho₁, h4])
  have hc2_three : m₂ = 3 → d₂.φ d₃.e * d₃.φ d₂.e = 1 :=
    fun h3 => pair_relation_three h₂ h₃ d₂ d₃ hind23 hp2 (by rw [ho₂, h3])
  have hc2_four : m₂ = 4 → d₂.φ d₃.e * d₃.φ d₂.e = 2 :=
    fun h4 => pair_relation_four h₂ h₃ d₂ d₃ hind23 hp2 (by rw [ho₂, h4])
  have hc1v : d₁.φ d₂.e * d₂.φ d₁.e = 1 ∨ d₁.φ d₂.e * d₂.φ d₁.e = 2 := by
    rcases hm₁ with h3 | h4
    · left; exact hc1_three h3
    · right; exact hc1_four h4
  have hc2v : d₂.φ d₃.e * d₃.φ d₂.e = 1 ∨ d₂.φ d₃.e * d₃.φ d₂.e = 2 := by
    rcases hm₂ with h3 | h4
    · left; exact hc2_three h3
    · right; exact hc2_four h4
  set a12 : ZMod p := d₁.φ d₂.e with ha12
  set a21 : ZMod p := d₂.φ d₁.e with ha21
  set a23 : ZMod p := d₂.φ d₃.e with ha23
  set a32 : ZMod p := d₃.φ d₂.e with ha32
  set c1 : ZMod p := a12 * a21 with hc1def
  set c2 : ZMod p := a23 * a32 with hc2def
  have hc1v' : c1 = 1 ∨ c1 = 2 := by
    rcases hc1v with h | h
    · left; rw [hc1def, ha12, ha21]; exact h
    · right; rw [hc1def, ha12, ha21]; exact h
  have hc2v' : c2 = 1 ∨ c2 = 2 := by
    rcases hc2v with h | h
    · left; rw [hc2def, ha23, ha32]; exact h
    · right; rw [hc2def, ha23, ha32]; exact h
  have hc1_three' : m₁ = 3 → c1 = 1 :=
    fun h3 => by rw [hc1def, ha12, ha21]; exact hc1_three h3
  have hc2_three' : m₂ = 3 → c2 = 1 :=
    fun h3 => by rw [hc2def, ha23, ha32]; exact hc2_three h3
  have hind3 : LinearIndependent (ZMod p) ![d₁.e, d₂.e, d₃.e] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    have hg' : g 0 • d₁.e + g 1 • d₂.e + g 2 • d₃.e = 0 := by simpa using hg
    have hE1 : (2 : ZMod p) * g 0 + a12 * g 1 = 0 := by
      have h := congrArg (fun w => d₁.φ w) hg'
      simp only [map_add, map_smul, map_zero, smul_eq_mul] at h
      rw [reflData_phi_self d₁, ← ha12, h13zero.1] at h
      ring_nf at h ⊢
      exact h
    have hE3 : a32 * g 1 + (2 : ZMod p) * g 2 = 0 := by
      have h := congrArg (fun w => d₃.φ w) hg'
      simp only [map_add, map_smul, map_zero, smul_eq_mul] at h
      rw [reflData_phi_self d₃, ← ha32, h13zero.2] at h
      ring_nf at h ⊢
      exact h
    have hE2 : a21 * g 0 + (2 : ZMod p) * g 1 + a23 * g 2 = 0 := by
      have h := congrArg (fun w => d₂.φ w) hg'
      simp only [map_add, map_smul, map_zero, smul_eq_mul] at h
      rw [reflData_phi_self d₂, ← ha21, ← ha23] at h
      ring_nf at h ⊢
      exact h
    have hg1 : g 1 = 0 := by
      have h2 : (2 : ZMod p) * (a21 * g 0 + 2 * g 1 + a23 * g 2) = 0 := by rw [hE2, mul_zero]
      have h2g0 : (2 : ZMod p) * g 0 = -(a12 * g 1) := add_eq_zero_iff_eq_neg.mp hE1
      have h2g2 : (2 : ZMod p) * g 2 = -(a32 * g 1) := by
        rw [add_comm] at hE3
        exact add_eq_zero_iff_eq_neg.mp hE3
      have h2' : a21 * (2 * g 0) + 4 * g 1 + a23 * (2 * g 2) = 0 := by
        have hh := h2; ring_nf at hh ⊢; exact hh
      have hcoef : g 1 * (4 - c1 - c2) = 0 := by
        rw [h2g0, h2g2] at h2'
        rw [hc1def, hc2def]
        ring_nf at h2' ⊢
        exact h2'
      exact (mul_eq_zero.mp hcoef).resolve_right
        (four_sub_ne_zero hp2 hc1v' hc2v' (hm.imp hc1_three' hc2_three'))
    have hg0 : g 0 = 0 := by
      have h := hE1
      rw [hg1, mul_zero, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_left h2p
    have hg2 : g 2 = 0 := by
      have h := hE3
      rw [hg1, mul_zero, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_left h2p
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  have hfg1 : (ggLinMove r₁).FG := by rw [d₁.span_eq]; exact Submodule.fg_span (Set.finite_singleton d₁.e)
  have hfg2 : (ggLinMove r₂).FG := by rw [d₂.span_eq]; exact Submodule.fg_span (Set.finite_singleton d₂.e)
  have hfg3 : (ggLinMove r₃).FG := by rw [d₃.span_eq]; exact Submodule.fg_span (Set.finite_singleton d₃.e)
  have : Module.Finite (ZMod p) ↥(ggLinMove r₁ ⊔ ggLinMove r₂ ⊔ ggLinMove r₃) :=
    Module.Finite.iff_fg.mpr ((hfg1.sup hfg2).sup hfg3)
  have hspan_le : Submodule.span (ZMod p) (Set.range ![d₁.e, d₂.e, d₃.e]) ≤
      ggLinMove r₁ ⊔ ggLinMove r₂ ⊔ ggLinMove r₃ := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · simpa using Submodule.mem_sup_left (Submodule.mem_sup_left d₁.he)
    · simpa using Submodule.mem_sup_left (Submodule.mem_sup_right d₂.he)
    · simpa using Submodule.mem_sup_right d₃.he
  have h3fin : Module.finrank (ZMod p)
      ↥(Submodule.span (ZMod p) (Set.range ![d₁.e, d₂.e, d₃.e])) = 3 := by
    rw [finrank_span_eq_card hind3]
    simp
  have hle := Submodule.finrank_mono hspan_le
  omega

end Module

end CFSG.StandardType

end
