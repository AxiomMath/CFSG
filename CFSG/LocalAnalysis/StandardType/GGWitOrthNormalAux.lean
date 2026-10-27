module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQ1
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderTransitive

public section

namespace CFSG.StandardType.ZS

open Subgroup
open CFSG.QuasithinUnique.Setup.Layer

section Transport

private lemma owNm_conj_mem_classRefl {p : ℕ} (hp : p.Prime) {U V : Type} [AddCommGroup U]
    [Module (ZMod p) U] [AddCommGroup V] [Module (ZMod p) V] {Q : QuadraticForm (ZMod p) U}
    {Q' : QuadraticForm (ZMod p) V} (e : U ≃ₗ[ZMod p] V) (he : ∀ v, Q' (e v) = Q v)
    {c : ZMod p} {t : U ≃ₗ[ZMod p] U} (ht : t ∈ ClassRefl p Q c) :
    e.symm.trans (t.trans e) ∈ ClassRefl p Q' c := by
  haveI : Fact p.Prime := ⟨hp⟩
  change autConj e t ∈ ClassRefl p Q' c
  rcases ht with ⟨hr, hiso, a, hQa, hta⟩
  refine ⟨⟨?_, ?_⟩, ?_, e a, ?_, ?_⟩
  · rw [← map_mul, hr.1, map_one]
  · have hrange : LinearMap.range
        (((autConj e t : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) - LinearMap.id) =
        Submodule.map ((e : U ≃ₗ[ZMod p] V) : U →ₗ[ZMod p] V)
          (LinearMap.range (((t : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - LinearMap.id)) := by
      ext y
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨t (e.symm x) - e.symm x, ⟨e.symm x, rfl⟩, ?_⟩
        rw [← hx]
        simp [autConj_apply, sub_eq_add_neg]
      · rintro ⟨w, ⟨u, hu⟩, hw⟩
        refine ⟨e u, ?_⟩
        rw [← hw, ← hu]
        simp [autConj_apply, sub_eq_add_neg]
    rw [hrange, LinearEquiv.finrank_map_eq, hr.2]
  · intro v
    calc Q' (autConj e t v) = Q (t (e.symm v)) := by rw [autConj_apply, he]
      _ = Q (e.symm v) := hiso _
      _ = Q' v := by rw [← he (e.symm v), e.apply_symm_apply]
  · rw [he, hQa]
  · rw [autConj_apply, e.symm_apply_apply, hta, map_neg]

theorem owNm_classRefl_transport_aux {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U V : Type}
    [AddCommGroup U] [Module (ZMod p) U] [AddCommGroup V] [Module (ZMod p) V]
    (Q : QuadraticForm (ZMod p) U) (Q' : QuadraticForm (ZMod p) V) (e : U ≃ₗ[ZMod p] V)
    (he : ∀ v, Q' (e v) = Q v) (c : ZMod p)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {A' : Subgroup (V ≃ₗ[ZMod p] V)}
    (hA : A = closure (ClassRefl p Q c)) (hA' : A' = closure (ClassRefl p Q' c)) :
    ∃ φ : ↥A ≃* ↥A', ∀ g : ↥A,
      ((φ g : ↥A') : V ≃ₗ[ZMod p] V) = e.symm.trans (((g : ↥A) : U ≃ₗ[ZMod p] U).trans e) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have he' : ∀ w, Q (e.symm w) = Q' w := fun w => by
    simpa using (he (e.symm w)).symm
  have himage : (⇑(autConj e).toMonoidHom) '' ClassRefl p Q c = ClassRefl p Q' c := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact owNm_conj_mem_classRefl hp e he hs
    · intro ht
      refine ⟨autConj e.symm t, owNm_conj_mem_classRefl hp e.symm he' ht, ?_⟩
      ext x
      simp [autConj_apply]
  have himage' : (⇑(autConj e.symm).toMonoidHom) '' ClassRefl p Q' c = ClassRefl p Q c := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact owNm_conj_mem_classRefl hp e.symm he' hs
    · intro ht
      refine ⟨autConj e t, owNm_conj_mem_classRefl hp e he ht, ?_⟩
      ext x
      simp [autConj_apply]
  have hmapA : Subgroup.map (autConj e).toMonoidHom A = A' := by
    rw [hA, MonoidHom.map_closure, himage, hA']
  have hmapA' : Subgroup.map (autConj e.symm).toMonoidHom A' = A := by
    rw [hA', MonoidHom.map_closure, himage', hA]
  let φ : ↥A ≃* ↥A' :=
    { toFun := fun g =>
        ⟨autConj e (g : U ≃ₗ[ZMod p] U), by
          have hmem : autConj e (g : U ≃ₗ[ZMod p] U) ∈
              Subgroup.map (autConj e).toMonoidHom A :=
            Subgroup.mem_map.mpr ⟨(g : U ≃ₗ[ZMod p] U), g.2, rfl⟩
          rwa [hmapA] at hmem⟩
      invFun := fun g =>
        ⟨autConj e.symm (g : V ≃ₗ[ZMod p] V), by
          have hmem : autConj e.symm (g : V ≃ₗ[ZMod p] V) ∈
              Subgroup.map (autConj e.symm).toMonoidHom A' :=
            Subgroup.mem_map.mpr ⟨(g : V ≃ₗ[ZMod p] V), g.2, rfl⟩
          rwa [hmapA'] at hmem⟩
      left_inv := fun g => by
        apply Subtype.ext
        show autConj e.symm (autConj e (g : U ≃ₗ[ZMod p] U)) = (g : U ≃ₗ[ZMod p] U)
        ext x
        simp [autConj_apply]
      right_inv := fun g => by
        apply Subtype.ext
        show autConj e (autConj e.symm (g : V ≃ₗ[ZMod p] V)) = (g : V ≃ₗ[ZMod p] V)
        ext x
        simp [autConj_apply]
      map_mul' := fun g h => by
        apply Subtype.ext
        show autConj e ((g : U ≃ₗ[ZMod p] U) * (h : U ≃ₗ[ZMod p] U)) =
          autConj e g * autConj e h
        exact map_mul (autConj e) (g : U ≃ₗ[ZMod p] U) (h : U ≃ₗ[ZMod p] U) }
  refine ⟨φ, fun g => ?_⟩
  rfl

theorem owNm_absIrred_transport_aux {p : ℕ} (hp : p.Prime) {U V : Type}
    [AddCommGroup U] [Module (ZMod p) U] [AddCommGroup V] [Module (ZMod p) V]
    (e : U ≃ₗ[ZMod p] V) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {A' : Subgroup (V ≃ₗ[ZMod p] V)} (φ : ↥A ≃* ↥A')
    (hφ : ∀ g : ↥A,
      ((φ g : ↥A') : V ≃ₗ[ZMod p] V) = e.symm.trans (((g : ↥A) : U ≃ₗ[ZMod p] U).trans e))
    (h : AbsIrred p A) : AbsIrred p A' := by
  classical
  constructor
  · intro W' hW'
    let W : Submodule (ZMod p) U := W'.comap (e : U →ₗ[ZMod p] V)
    have hW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W := by
      intro a ha w hw
      change e (a w) ∈ W'
      have hthis := hW' (φ ⟨a, ha⟩) (φ ⟨a, ha⟩).2 (e w) hw
      rw [hφ ⟨a, ha⟩] at hthis
      simpa [LinearEquiv.trans_apply] using hthis
    rcases h.1 W hW with hbot | htop
    · left
      rw [Submodule.eq_bot_iff] at hbot ⊢
      intro x hx
      have hxW : e.symm x ∈ W := by
        change e (e.symm x) ∈ W'
        simpa using hx
      have hx0 : e.symm x = 0 := hbot (e.symm x) hxW
      simpa using congrArg e hx0
    · right
      rw [Submodule.eq_top_iff'] at htop ⊢
      intro x
      have hxW : e.symm x ∈ W := htop (e.symm x)
      change e (e.symm x) ∈ W' at hxW
      simpa using hxW
  · intro T' hT'
    let T : Module.End (ZMod p) U :=
      (e.symm : V →ₗ[ZMod p] U).comp (T'.comp (e : U →ₗ[ZMod p] V))
    have hT : ∀ a ∈ A,
        T ∘ₗ (a : U →ₗ[ZMod p] U) = (a : U →ₗ[ZMod p] U) ∘ₗ T := by
      intro a ha
      ext u
      have hcomm := hT' (φ ⟨a, ha⟩) (φ ⟨a, ha⟩).2
      have hcomm' := congrArg (fun f : Module.End (ZMod p) V => f (e u)) hcomm
      simp only [LinearMap.comp_apply] at hcomm'
      rw [hφ ⟨a, ha⟩] at hcomm'
      have hcomm'' : T' (e (a u)) = e (a (e.symm (T' (e u)))) := by
        simpa [LinearEquiv.trans_apply] using hcomm'
      change e.symm (T' (e (a u))) = a (e.symm (T' (e u)))
      rw [hcomm'']
      simp
    obtain ⟨c, hc⟩ := h.2 T hT
    refine ⟨c, ?_⟩
    ext v
    have hTv : T' v = e (T (e.symm v)) := by
      simp [T]
    rw [hTv, hc]
    simp


private theorem owNm_orth_normal_field (K : Type) [Field K] [Invertible (2 : K)]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : LinearMap.Nondegenerate (QuadraticMap.polarBilin Q)) :
    ∃ (e : V ≃ₗ[K] (Fin (Module.finrank K V) → K)) (w : Fin (Module.finrank K V) → K),
      (∀ i, w i ≠ 0) ∧ ∀ v, Q v = ∑ i, w i * (e v i) ^ 2 := by
  have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  have hSep : LinearMap.SeparatingLeft (QuadraticMap.associated Q) := by
    intro x hx
    apply hQ.1 x
    intro y
    have hxy := hx y
    have hassoc : (QuadraticMap.associated Q x) y =
        (⅟(2 : K)) • ((QuadraticMap.polarBilin Q x) y) := by
      rw [QuadraticMap.associated_apply K, QuadraticMap.polarBilin_apply_apply]
      simp [QuadraticMap.polar]
    rw [hassoc] at hxy
    exact (smul_eq_zero.mp hxy).resolve_left (by
      rw [invOf_eq_inv]
      exact inv_ne_zero h2)
  obtain ⟨w, ⟨iso⟩⟩ :=
    QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q hSep
  refine ⟨iso.toLinearEquiv, fun i => (w i : K), fun i => (w i).ne_zero, fun v => ?_⟩
  have h1 : (QuadraticMap.weightedSumSquares K w) (iso v) = Q v := iso.map_app v
  rw [← h1, QuadraticMap.weightedSumSquares_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Units.smul_def, sq, smul_eq_mul]

theorem owNm_orth_normal_aux {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    ∃ (e : U ≃ₗ[ZMod p] (Fin (Module.finrank (ZMod p) U) → ZMod p))
      (w : Fin (Module.finrank (ZMod p) U) → ZMod p),
      (∀ i, w i ≠ 0) ∧ ∀ v, Q v = ∑ i, w i * (e v i) ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hzero)
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have hge : 2 ≤ p := hp.two_le
    have hp2' : p = 2 := by omega
    exact hp2 hp2'
  haveI : Invertible (2 : ZMod p) := invertibleOfNonzero h2
  exact owNm_orth_normal_field (ZMod p) Q hQ

end Transport

end CFSG.StandardType.ZS

end
