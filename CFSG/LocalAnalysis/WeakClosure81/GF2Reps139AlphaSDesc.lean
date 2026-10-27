module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.Trace.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open Algebra

open scoped commutatorElement

local notation "K4" => GaloisField 2 2

variable {V : Type} [AddCommGroup V] [Module K4 V]

private theorem w1369_trace_mul_ne_zero {γ : K4} (hγ : γ ≠ 0) :
    ∃ y : K4, Algebra.trace (ZMod 2) K4 (γ * y) ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := Algebra.trace_surjective (ZMod 2) K4 1
  exact ⟨y₀ / γ, by rw [mul_div_cancel₀ _ hγ, hy₀]; exact one_ne_zero⟩

private theorem w1369_trace_eq_of_forall {a b : K4}
    (h : ∀ x : K4, Algebra.trace (ZMod 2) K4 (x * a) = Algebra.trace (ZMod 2) K4 (x * b)) :
    a = b := by
  by_contra hne
  have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨y, hy⟩ := w1369_trace_mul_ne_zero hne'
  refine hy ?_
  have h0 : Algebra.trace (ZMod 2) K4 (y * (a - b)) = 0 := by
    rw [mul_sub, map_sub, h y, sub_self]
  rwa [mul_comm] at h0

private theorem w1369_zmod2_add_eq_zero {x y : ZMod 2} (h : x + y = 0) : x = y := by
  have hchar : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  exact hchar x y h

private theorem w1369_form_symm (B : V →+ V →+ ZMod 2) (halt : ∀ u, B u u = 0) (u v : V) :
    B u v = B v u := by
  have hcalc : B (u + v) (u + v) = B u v + B v u := by
    rw [map_add B u v, AddMonoidHom.add_apply, map_add (B u) u v, map_add (B v) u v,
      halt u, halt v]
    abel
  have h0 : B u v + B v u = 0 := by
    rw [← hcalc]
    exact halt (u + v)
  exact w1369_zmod2_add_eq_zero h0

private theorem w1369_adj_unique (B : V →+ V →+ ZMod 2)
    (hnd : ∀ u, (∀ v, B u v = 0) → u = 0) (halt : ∀ u, B u u = 0)
    {v₀ : V} (hv₀ : v₀ ≠ 0) {μ a b : K4}
    (ha : ∀ u v, B (μ • u) v = B u (a • v))
    (hb : ∀ u v, B (μ • u) v = B u (b • v)) : a = b := by
  have hsymm := w1369_form_symm B halt
  have hzero : ∀ u, B u ((a - b) • v₀) = 0 := by
    intro u
    rw [sub_smul, map_sub, ← ha u v₀, ← hb u v₀, sub_self]
  have hz : (a - b) • v₀ = 0 :=
    hnd ((a - b) • v₀) fun v => (hsymm ((a - b) • v₀) v).trans (hzero v)
  have hδ0 : a - b = 0 := by
    rcases smul_eq_zero.1 hz with h | h
    · exact h
    · exact absurd h hv₀
  exact sub_eq_zero.1 hδ0

private noncomputable def w1369_phi (B : V →+ V →+ ZMod 2) (u v : V) :
    K4 →ₗ[ZMod 2] ZMod 2 where
  toFun := fun r => B (r • u) v
  map_add' := by intro r μ; simp only [add_smul, map_add, AddMonoidHom.add_apply]
  map_smul' := by
    intro a r
    have ha : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    rcases ha a with h | h <;> rw [h] <;> simp

private noncomputable def w1369_form (B : V →+ V →+ ZMod 2) (u v : V) : K4 :=
  ((Algebra.traceForm (ZMod 2) K4).toDual (traceForm_nondegenerate (ZMod 2) K4)).symm
    (w1369_phi B u v)

private theorem w1369_form_spec (B : V →+ V →+ ZMod 2) (u v : V) (r : K4) :
    Algebra.trace (ZMod 2) K4 (r * w1369_form B u v) = B (r • u) v := by
  have h := LinearMap.BilinForm.apply_toDual_symm_apply
    (B := Algebra.traceForm (ZMod 2) K4)
    (hB := traceForm_nondegenerate (ZMod 2) K4)
    (w1369_phi B u v) r
  simp only [Algebra.traceForm_apply] at h
  rw [mul_comm]
  exact h

private theorem w1369_form_add_left (B : V →+ V →+ ZMod 2) (u₁ u₂ v : V) :
    w1369_form B (u₁ + u₂) v = w1369_form B u₁ v + w1369_form B u₂ v := by
  apply w1369_trace_eq_of_forall
  intro r
  rw [w1369_form_spec B (u₁ + u₂) v r,
      mul_add, map_add (Algebra.trace (ZMod 2) K4) (r * w1369_form B u₁ v)
        (r * w1369_form B u₂ v),
      w1369_form_spec B u₁ v r, w1369_form_spec B u₂ v r,
      smul_add, map_add B (r • u₁) (r • u₂), AddMonoidHom.add_apply]

private theorem w1369_form_smul_left (B : V →+ V →+ ZMod 2) (c : K4) (u v : V) :
    w1369_form B (c • u) v = c * w1369_form B u v := by
  apply w1369_trace_eq_of_forall
  intro r
  rw [w1369_form_spec B (c • u) v r, ← mul_assoc, w1369_form_spec B u v (r * c), mul_smul]

private theorem w1369_form_add_right (B : V →+ V →+ ZMod 2) (u v₁ v₂ : V) :
    w1369_form B u (v₁ + v₂) = w1369_form B u v₁ + w1369_form B u v₂ := by
  apply w1369_trace_eq_of_forall
  intro r
  rw [w1369_form_spec B u (v₁ + v₂) r,
      mul_add, map_add (Algebra.trace (ZMod 2) K4) (r * w1369_form B u v₁)
        (r * w1369_form B u v₂),
      w1369_form_spec B u v₁ r, w1369_form_spec B u v₂ r,
      ← map_add (B (r • u))]

private theorem w1369_form_smul_right (B : V →+ V →+ ZMod 2) (θ' : K4 →+* K4)
    (hrel : ∀ u v ν, B u (ν • v) = B ((θ' ν) • u) v)
    (c : K4) (u v : V) :
    w1369_form B u (c • v) = θ' c * w1369_form B u v := by
  apply w1369_trace_eq_of_forall
  intro r
  rw [w1369_form_spec B u (c • v) r, hrel (r • u) v c, ← mul_smul]
  rw [← mul_assoc, mul_comm r (θ' c), w1369_form_spec B u v (θ' c * r)]

theorem trace_descent_f4 {V : Type} [AddCommGroup V] [Module (GaloisField 2 2) V] [Finite V]
    (B : V →+ V →+ ZMod 2) (hnd : ∀ u, (∀ v, B u v = 0) → u = 0) (halt : ∀ u, B u u = 0)
    (hadj : ∀ μ : GaloisField 2 2, ∃ μ' : GaloisField 2 2, ∀ u v, B (μ • u) v = B u (μ' • v)) :
    ∃ (θ : GaloisField 2 2 →+* GaloisField 2 2)
      (b : V →ₗ[GaloisField 2 2] V →ₛₗ[θ] GaloisField 2 2),
      (∀ u v, B u v = Algebra.trace (ZMod 2) (GaloisField 2 2) (b u v)) ∧
      (∀ u, (∀ v, b u v = 0) → u = 0) ∧ (∀ c, θ (θ c) = c) ∧ (∀ u v, b v u = θ (b u v)) ∧
      (θ = RingHom.id _ → ∀ u, b u u = 0) := by
  classical
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite (GaloisField 2 2)
  by_cases htriv : Subsingleton V
  · haveI := htriv
    refine ⟨RingHom.id (GaloisField 2 2), 0, ?_, ?_, ?_, ?_, ?_⟩
    · intro u v
      rw [Subsingleton.elim u 0]
      simp
    · intro u _
      exact Subsingleton.elim u 0
    · intro c; rfl
    · intro u v; rfl
    · intro _ u; rfl
  · haveI : Nontrivial V := not_subsingleton_iff_nontrivial.mp htriv
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
    have hsymm : ∀ u v, B u v = B v u := w1369_form_symm B halt
    have hunique : ∀ {μ a b : K4}, (∀ u v, B (μ • u) v = B u (a • v)) →
        (∀ u v, B (μ • u) v = B u (b • v)) → a = b :=
      fun ha hb => w1369_adj_unique B hnd halt hv₀ ha hb
    let θ' : K4 →+* K4 :=
      { toFun := fun μ => Classical.choose (hadj μ)
        map_one' := hunique (Classical.choose_spec (hadj 1)) (by intro u v; simp)
        map_mul' := fun μ ν => hunique (Classical.choose_spec (hadj (μ * ν))) (by
          intro u v
          rw [mul_smul, Classical.choose_spec (hadj μ) (ν • u) v,
              Classical.choose_spec (hadj ν) u (Classical.choose (hadj μ) • v),
              ← mul_smul, mul_comm (Classical.choose (hadj ν)) (Classical.choose (hadj μ))])
        map_zero' := hunique (Classical.choose_spec (hadj 0)) (by intro u v; simp)
        map_add' := fun μ ν => hunique (Classical.choose_spec (hadj (μ + ν))) (by
          intro u v
          rw [add_smul, map_add B (μ • u) (ν • u), AddMonoidHom.add_apply,
              Classical.choose_spec (hadj μ) u v,
              Classical.choose_spec (hadj ν) u v, ← map_add (B u), ← add_smul]) }
    have hθ'spec : ∀ μ u v, B (μ • u) v = B u (θ' μ • v) :=
      fun μ => Classical.choose_spec (hadj μ)
    have hθ'inj : Function.Injective θ' := RingHom.injective θ'
    have hθ'bij : Function.Bijective θ' :=
      ⟨hθ'inj, (Finite.injective_iff_surjective).1 hθ'inj⟩
    let e' : K4 ≃+* K4 := RingEquiv.ofBijective θ' hθ'bij
    have he'_apply : ∀ x, e' x = θ' x := fun x => RingEquiv.ofBijective_apply θ' hθ'bij x
    have hcomm : ∀ x : ZMod 2, e' (algebraMap (ZMod 2) K4 x) = algebraMap (ZMod 2) K4 x := by
      intro x
      have hcomp : θ'.comp (algebraMap (ZMod 2) K4) = algebraMap (ZMod 2) K4 :=
        Subsingleton.elim _ _
      have h : θ' (algebraMap (ZMod 2) K4 x) = algebraMap (ZMod 2) K4 x := by
        have := DFunLike.congr_fun hcomp x
        rwa [RingHom.comp_apply] at this
      rw [he'_apply]
      exact h
    let e : K4 ≃ₐ[ZMod 2] K4 := AlgEquiv.ofRingEquiv (f := e') hcomm
    have he_apply : ∀ x, e x = θ' x := by
      intro x
      rw [AlgEquiv.ofRingEquiv_apply, he'_apply]
    have htrace_inv : ∀ x : K4,
        Algebra.trace (ZMod 2) K4 (θ' x) = Algebra.trace (ZMod 2) K4 x := by
      intro x
      have h := Algebra.trace_eq_of_algEquiv e x
      rwa [he_apply x] at h
    have hcard : Nat.card (K4 ≃ₐ[ZMod 2] K4) = 2 := by
      rw [IsGalois.card_aut_eq_finrank, GaloisField.finrank 2 (by norm_num)]
    have hsquare : e ^ 2 = 1 := by
      have h := pow_card_eq_one' (x := e)
      rwa [hcard] at h
    have hθ'2 : ∀ c, θ' (θ' c) = c := by
      intro c
      have h := congrArg (fun f : K4 ≃ₐ[ZMod 2] K4 => f c) hsquare
      have hee : e (e c) = c := by
        simpa [pow_two, AlgEquiv.mul_apply] using h
      simpa only [he_apply] using hee
    have hrel : ∀ (u v : V) (ν : K4), B u (ν • v) = B ((θ' ν) • u) v := by
      intro u v ν
      have h := hθ'spec (θ' ν) u v
      rw [hθ'2 ν] at h
      exact h.symm
    have hgal : ∀ r w : K4, Algebra.trace (ZMod 2) K4 (θ' r * w) =
        Algebra.trace (ZMod 2) K4 (r * θ' w) := by
      intro r w
      have h1 : θ' (r * θ' w) = θ' r * w := by
        rw [map_mul, hθ'2]
      calc Algebra.trace (ZMod 2) K4 (θ' r * w)
          = Algebra.trace (ZMod 2) K4 (θ' (r * θ' w)) := by rw [h1]
        _ = Algebra.trace (ZMod 2) K4 (r * θ' w) := htrace_inv _
    have H1 : ∀ (u₁ u₂ v : V),
        w1369_form B (u₁ + u₂) v = w1369_form B u₁ v + w1369_form B u₂ v :=
      fun u₁ u₂ v => w1369_form_add_left B u₁ u₂ v
    have H2 : ∀ (c : K4) (u v : V),
        w1369_form B (c • u) v = (RingHom.id K4) c • w1369_form B u v := by
      intro c u v
      simpa [smul_eq_mul] using w1369_form_smul_left B c u v
    have H3 : ∀ (u v₁ v₂ : V),
        w1369_form B u (v₁ + v₂) = w1369_form B u v₁ + w1369_form B u v₂ :=
      fun u v₁ v₂ => w1369_form_add_right B u v₁ v₂
    have H4 : ∀ (c : K4) (u v : V),
        w1369_form B u (c • v) = θ' c • w1369_form B u v := by
      intro c u v
      simpa [smul_eq_mul] using w1369_form_smul_right B θ' hrel c u v
    let b : V →ₗ[K4] V →ₛₗ[θ'] K4 :=
      LinearMap.mk₂'ₛₗ (RingHom.id K4) θ' (fun u v => w1369_form B u v) H1 H2 H3 H4
    have hbval : ∀ u v, b u v = w1369_form B u v := fun u v => rfl
    refine ⟨θ', b, ?_, ?_, ?_, ?_, ?_⟩
    · intro u v
      have h := w1369_form_spec B u v (1 : K4)
      simpa [hbval] using h.symm
    · intro u hu
      refine hnd u fun v => ?_
      have hv : w1369_form B u v = 0 := by
        have := hu v
        simpa [hbval] using this
      have h2 := w1369_form_spec B u v (1 : K4)
      simpa [hv] using h2.symm
    · exact hθ'2
    · intro u v
      apply w1369_trace_eq_of_forall
      intro r
      calc Algebra.trace (ZMod 2) K4 (r * b v u)
          = B (r • v) u := by simpa [hbval] using w1369_form_spec B v u r
        _ = B u (r • v) := hsymm (r • v) u
        _ = B ((θ' r) • u) v := hrel u v r
        _ = Algebra.trace (ZMod 2) K4 ((θ' r) * b u v) := by
              simpa [hbval] using (w1369_form_spec B u v (θ' r)).symm
        _ = Algebra.trace (ZMod 2) K4 (r * θ' (b u v)) := hgal r (b u v)
    · intro hθid u
      have hpow4 : ∀ x : K4, x ^ 4 = x := by
        intro x
        have hcard4 : Fintype.card K4 = 4 := by
          rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]; norm_num
        have h := FiniteField.pow_card x
        rwa [hcard4] at h
      have hsurj : Function.Surjective (fun r : K4 => r ^ 2) := fun μ => by
        refine ⟨μ ^ 2, ?_⟩
        show (μ ^ 2) ^ 2 = μ
        rw [show (μ ^ 2) ^ 2 = μ ^ 4 by ring, hpow4 μ]
      have hzero : ∀ r : K4,
          Algebra.trace (ZMod 2) K4 (r ^ 2 * w1369_form B u u) = 0 := by
        intro r
        have h1 : w1369_form B (r • u) (r • u) = r ^ 2 * w1369_form B u u := by
          rw [w1369_form_smul_left B r u (r • u),
              w1369_form_smul_right B θ' hrel r u u, hθid]
          simp only [RingHom.id_apply]
          ring
        rw [← h1]
        have hspec := w1369_form_spec B (r • u) (r • u) (1 : K4)
        simp only [one_mul, one_smul] at hspec
        exact hspec.trans (halt (r • u))
      have hfuu : w1369_form B u u = 0 := by
        apply w1369_trace_eq_of_forall
        intro μ
        obtain ⟨r, hr⟩ := hsurj μ
        rw [← hr, mul_zero, map_zero]
        exact hzero r
      simpa [hbval] using hfuu

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
