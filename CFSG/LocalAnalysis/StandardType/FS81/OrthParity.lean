module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusCore
public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarElementary
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.RankThree.Literature.FSmithOrthogonal

public section

namespace CFSG.StandardType.FrameRoute.FS81

open Module QuadraticMap CFSG.StandardType CFSG.StandardType.SpCoord
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ClassicalGroups.Orthogonal
open Multiplicative

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem neg_eq_self_zmod_two (v : V) : -v = v := by
  have hvv : v + v = 0 := by
    have h2v : (2 : ZMod 2) • v = 0 := by
      rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
    rwa [two_smul] at h2v
  exact neg_eq_of_add_eq_zero_right hvv

private theorem zmod_two_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 :=
  (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c

private def coordOne {r : ℕ} (i : Fin r) : Fin r → Multiplicative (ZMod 3) :=
  Pi.mulSingle (M := fun _ : Fin r => Multiplicative (ZMod 3)) i (ofAdd (1 : ZMod 3))

private def singleVal {r : ℕ} (i : Fin r) (x : Multiplicative (ZMod 3)) :
    Fin r → Multiplicative (ZMod 3) :=
  Pi.mulSingle (M := fun _ : Fin r => Multiplicative (ZMod 3)) i x

private noncomputable def frameS {Q : QuadraticForm (ZMod 2) V}
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ} (_F : SevOm.Frame Q 3 A r) (i : Fin r) :
    Multiplicative (Fin r → ZMod 3) :=
  OrthTorus.piMul r 3 (coordOne i)

private noncomputable def frameA {Q : QuadraticForm (ZMod 2) V}
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ} (F : SevOm.Frame Q 3 A r) (i : Fin r) :
    V ≃ₗ[ZMod 2] V :=
  F.ι (frameS F i)

private theorem toAdd_piMul_apply {p r : ℕ} (f : Fin r → Multiplicative (ZMod p)) (j : Fin r) :
    toAdd (OrthTorus.piMul r p f) j = toAdd (f j) := by
  rw [OrthTorus.piMul_apply, toAdd_ofAdd]

private theorem toAdd_frameS {Q : QuadraticForm (ZMod 2) V}
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ} (F : SevOm.Frame Q 3 A r) (i j : Fin r) :
    toAdd (frameS F i) j = if j = i then (1 : ZMod 3) else 0 := by
  rw [frameS, toAdd_piMul_apply]
  by_cases h : j = i
  · subst h
    simp [coordOne, Pi.mulSingle_eq_same]
  · simp [coordOne, h]

private theorem frameA_mapsTo {Q : QuadraticForm (ZMod 2) V}
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ} (F : SevOm.Frame Q 3 A r) (i : Fin r) {u : V}
    (hu : u ∈ F.U i) : frameA F i u ∈ F.U i :=
  F.mapsTo (frameS F i) i u hu

private theorem frameA_fpf {Q : QuadraticForm (ZMod 2) V}
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ} (F : SevOm.Frame Q 3 A r) (i : Fin r) {u : V}
    (hu : u ∈ F.U i) (h : frameA F i u = u) : u = 0 :=
  F.fpf (frameS F i) i (by rw [toAdd_frameS]; simp) u hu h

private theorem frameA_pow_three {Q : QuadraticForm (ZMod 2) V}
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ} (F : SevOm.Frame Q 3 A r) (i : Fin r) :
    frameA F i ^ 3 = 1 :=
  F.pow_p (frameS F i)

private theorem frameA_fix_iff {Q : QuadraticForm (ZMod 2) V}
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ} (F : SevOm.Frame Q 3 A r) (i : Fin r) (v : V) :
    frameA F i v = v ↔ ∀ u ∈ F.U i, polar Q u v = 0 := by
  rw [frameA, F.fix (frameS F i) v]
  constructor
  · intro h u hu
    exact h i (by rw [toAdd_frameS]; simp) u hu
  · intro h j hj u hu
    by_cases hji : j = i
    · subst hji; exact h u hu
    · rw [toAdd_frameS, if_neg hji] at hj
      exact absurd rfl hj

private theorem frameA_sq_apply {Q : QuadraticForm (ZMod 2) V}
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ} (F : SevOm.Frame Q 3 A r) (i : Fin r) {w : V}
    (hw : w ∈ F.U i) : frameA F i (frameA F i w) = w + frameA F i w := by
  have ha3 : frameA F i ^ 3 = 1 := frameA_pow_three F i
  have hxmem : frameA F i (frameA F i w) + frameA F i w + w ∈ F.U i :=
    (F.U i).add_mem ((F.U i).add_mem (frameA_mapsTo F i (frameA_mapsTo F i hw))
      (frameA_mapsTo F i hw)) hw
  have hfix : frameA F i (frameA F i (frameA F i w) + frameA F i w + w) =
      frameA F i (frameA F i w) + frameA F i w + w := by
    simp only [map_add]
    have ha3w : frameA F i (frameA F i (frameA F i w)) = w := by
      have h := congrArg (fun g : V ≃ₗ[ZMod 2] V => g w) ha3
      simpa [pow_succ, LinearEquiv.mul_apply] using h
    rw [ha3w]
    abel
  have hx0 : frameA F i (frameA F i w) + frameA F i w + w = 0 :=
    frameA_fpf F i hxmem hfix
  have h1 : frameA F i (frameA F i w) + (frameA F i w + w) = 0 := by
    rw [← add_assoc]; exact hx0
  have h2 : frameA F i (frameA F i w) = -(frameA F i w + w) :=
    eq_neg_of_add_eq_zero_left h1
  rw [neg_add, neg_eq_self_zmod_two, neg_eq_self_zmod_two] at h2
  exact h2.trans (add_comm _ _)

private theorem frameA_span [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V}
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ} (F : SevOm.Frame Q 3 A r) (i : Fin r) {w : V}
    (hw : w ∈ F.U i) (hw0 : w ≠ 0) (hU : finrank (ZMod 2) (F.U i) = 2) :
    F.U i = Submodule.span (ZMod 2) {w, frameA F i w} := by
  have haw0 : frameA F i w ≠ 0 := fun h => hw0 ((frameA F i).map_eq_zero_iff.mp h)
  have haw_ne : frameA F i w ≠ w := fun h => hw0 (frameA_fpf F i hw h)
  have hle : Submodule.span (ZMod 2) {w, frameA F i w} ≤ F.U i := by
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hw
    · exact frameA_mapsTo F i hw
  have hnotmem : frameA F i w ∉ Submodule.span (ZMod 2) {w} := by
    intro h
    rw [Submodule.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    rcases zmod_two_eq_zero_or_one c with rfl | rfl
    · rw [zero_smul] at hc; exact haw0 hc.symm
    · rw [one_smul] at hc; exact haw_ne hc.symm
  have hlt : Submodule.span (ZMod 2) {w} < Submodule.span (ZMod 2) {w, frameA F i w} := by
    refine lt_of_le_of_ne (Submodule.span_mono ?_) ?_
    · intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact Set.mem_insert _ _
    · intro heq
      apply hnotmem
      rw [heq]
      exact Submodule.subset_span (by simp)
  have hfin1 : finrank (ZMod 2) (Submodule.span (ZMod 2) {w}) = 1 :=
    finrank_span_singleton hw0
  have hltfin : finrank (ZMod 2) (Submodule.span (ZMod 2) {w}) <
      finrank (ZMod 2) (Submodule.span (ZMod 2) {w, frameA F i w}) :=
    Submodule.finrank_lt_finrank_of_lt hlt
  rw [hfin1] at hltfin
  have hlefin : finrank (ZMod 2) (Submodule.span (ZMod 2) {w, frameA F i w}) ≤ 2 := by
    calc finrank (ZMod 2) (Submodule.span (ZMod 2) {w, frameA F i w})
        ≤ finrank (ZMod 2) (F.U i) := Submodule.finrank_mono hle
      _ = 2 := hU
  have hfin2 : finrank (ZMod 2) (Submodule.span (ZMod 2) {w, frameA F i w}) = 2 := by
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle (hfin2.trans hU.symm)).symm

private theorem frameA_orthogonal {Q : QuadraticForm (ZMod 2) V}
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (F : SevOm.Frame Q 3 A r) (i : Fin r) :
    frameA F i ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  hAO (F.mem (frameS F i))

private theorem frameA_map_Q {Q : QuadraticForm (ZMod 2) V}
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (F : SevOm.Frame Q 3 A r) (i : Fin r)
    (v : V) : Q (frameA F i v) = Q v :=
  TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (frameA_orthogonal hAO F i) v

private theorem polar_w_frameAv {Q : QuadraticForm (ZMod 2) V}
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (F : SevOm.Frame Q 3 A r) (i : Fin r)
    {w : V} (hw : w ∈ F.U i) : polar Q w (frameA F i w) = Q w := by
  have hq : Q (frameA F i w) = Q w := frameA_map_Q hAO F i w
  have hq2 : Q (frameA F i (frameA F i w)) = Q w :=
    (frameA_map_Q hAO F i (frameA F i w)).trans hq
  have hsum : w + frameA F i w = frameA F i (frameA F i w) :=
    (frameA_sq_apply F i hw).symm
  change Q (w + frameA F i w) - Q w - Q (frameA F i w) = Q w
  rw [hsum, hq2, hq]
  rw [sub_self, zero_sub, CharTwo.neg_eq]

private theorem frameA_Q_eq_one [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V}
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (F : SevOm.Frame Q 3 A r) (i : Fin r) {w : V} (hw : w ∈ F.U i) (hw0 : w ≠ 0)
    (hU : finrank (ZMod 2) (F.U i) = 2) : Q w = 1 := by
  by_contra h1
  have hQw : Q w = 0 := by
    rcases zmod_two_eq_zero_or_one (Q w) with h | h
    · exact h
    · exact absurd h h1
  have hpw : polar Q w w = 0 := by
    rw [QuadraticMap.polar_self, hQw, smul_zero]
  have hpaw : polar Q (frameA F i w) w = 0 := by
    rw [QuadraticMap.polar_comm, polar_w_frameAv hAO F i hw, hQw]
  have hspan := frameA_span F i hw hw0 hU
  have hvan : ∀ v ∈ F.U i, polar Q v w = 0 := by
    intro v hv
    rw [hspan] at hv
    obtain ⟨c1, c2, hc⟩ := Submodule.mem_span_pair.mp hv
    rw [← hc]
    change polar Q (c1 • w + c2 • frameA F i w) w = 0
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_left, hpw, hpaw]
    simp
  exact hw0 (F.nondeg i w hw hvan)

private theorem reflect_not_mem_orthDerived [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V}
    (hQ : (polarBilin Q).Nondegenerate) {w : V} (hQw : Q w = 1) :
    reflect Q w ∉ orthDerived Q := by
  intro hmem
  have h1 := CFSG.RankThree.PartOne.KCOrthogonal.dicksonHom_eq_one_of_mem_orthDerived hQ hmem
  have h2 : CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ
      ⟨reflect Q w, reflect_mem_orthogonalGroup Q w⟩ =
      Multiplicative.ofAdd (1 : ZMod 2) :=
    CFSG.RankThree.PartOne.KCOrthogonal.dicksonHom_reflect hQ (by rw [hQw]; exact one_ne_zero)
  have h1' : CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ
      (⟨reflect Q w, reflect_mem_orthogonalGroup Q w⟩ :
        TauCeti.QuadraticMap.orthogonalGroup Q) = 1 := by
    convert h1 using 1
  rw [h1'] at h2
  have h3 : (0 : ZMod 2) = 1 := Multiplicative.ofAdd.injective (by simpa using h2)
  exact zero_ne_one h3

private theorem reflect_commute_of_fix {Q : QuadraticForm (ZMod 2) V} {w : V} (hQw : Q w = 1)
    {b : V ≃ₗ[ZMod 2] V} (hb : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hbw : b w = w) :
    reflect Q w * b = b * reflect Q w := by
  have hQw_ne : Q w ≠ 0 := by rw [hQw]; exact one_ne_zero
  refine LinearEquiv.ext fun v => ?_
  have hpolar : polar Q w (b v) = polar Q w v := by
    have h1 : polar Q w (b v) = polar Q (b w) (b v) := by rw [hbw]
    calc polar Q w (b v) = polar Q (b w) (b v) := h1
      _ = polar Q w v := polar_map_of_mem hb w v
  simp only [LinearEquiv.mul_apply, reflect_apply hQw_ne, map_sub, map_smul, hbw, hpolar]

private theorem reflect_conj_frameA [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V}
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (F : SevOm.Frame Q 3 A r) (i : Fin r)
    {w : V} (hw : w ∈ F.U i) (hw0 : w ≠ 0) (hU : finrank (ZMod 2) (F.U i) = 2)
    (hQw : Q w = 1) :
    reflect Q w * frameA F i * reflect Q w = frameA F i ^ 2 := by
  have hQw_ne : Q w ≠ 0 := by rw [hQw]; exact one_ne_zero
  have hpw : polar Q w w = 0 := by
    rw [QuadraticMap.polar_self, hQw]
    decide
  have hpolar_aw : polar Q w (frameA F i w) = 1 := by
    rw [polar_w_frameAv hAO F i hw, hQw]
  have hpow2 : ∀ x : V, (frameA F i ^ 2) x = frameA F i (frameA F i x) := by
    intro x
    rw [pow_two, LinearEquiv.mul_apply]
  have ha3w : frameA F i (frameA F i (frameA F i w)) = w := by
    have h := congrArg (fun g : V ≃ₗ[ZMod 2] V => g w) (frameA_pow_three F i)
    simpa [pow_succ, LinearEquiv.mul_apply] using h
  have hρw : reflect Q w w = w := by
    rw [reflect_apply hQw_ne, hpw, zero_div, zero_smul, sub_zero]
  have hρaw : reflect Q w (frameA F i w) = (frameA F i ^ 2) w := by
    rw [reflect_apply hQw_ne, hpolar_aw, hQw, div_one, one_smul, hpow2,
      frameA_sq_apply F i hw, sub_eq_add_neg, neg_eq_self_zmod_two]
    abel
  have hpolar_a2 : polar Q w (frameA F i (frameA F i w)) = 1 := by
    rw [frameA_sq_apply F i hw, QuadraticMap.polar_add_right, hpw, hpolar_aw]
    simp
  have hρa2w : reflect Q w (frameA F i (frameA F i w)) = frameA F i w := by
    rw [reflect_apply hQw_ne, hpolar_a2, hQw, div_one, one_smul, frameA_sq_apply F i hw,
      add_sub_cancel_left]
  have hmain : ∀ v : V, (reflect Q w * frameA F i * reflect Q w) v = (frameA F i ^ 2) v := by
    intro v
    set u : V := polar Q (frameA F i w) v • w + polar Q w v • frameA F i w with hu
    have hu_mem : u ∈ F.U i := by
      rw [hu]
      exact (F.U i).add_mem ((F.U i).smul_mem _ hw)
        ((F.U i).smul_mem _ (frameA_mapsTo F i hw))
    have h2Q : (2 : ℕ) • Q (frameA F i w) = 0 := CharTwo.two_nsmul _
    have hvu_w : polar Q w (v - u) = 0 := by
      rw [hu, QuadraticMap.polar_sub_right, QuadraticMap.polar_add_right,
        QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, hpw, hpolar_aw]
      ring
    have hvu_aw : polar Q (frameA F i w) (v - u) = 0 := by
      rw [hu, QuadraticMap.polar_sub_right, QuadraticMap.polar_add_right,
        QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right,
        QuadraticMap.polar_comm (⇑Q) (frameA F i w) w, hpolar_aw, QuadraticMap.polar_self,
        h2Q]
      ring
    have hvan : ∀ x ∈ F.U i, polar Q x (v - u) = 0 := by
      intro x hx
      have hxspan : x ∈ Submodule.span (ZMod 2) {w, frameA F i w} := by
        rw [← frameA_span F i hw hw0 hU]; exact hx
      obtain ⟨c1, c2, hc⟩ := Submodule.mem_span_pair.mp hxspan
      rw [← hc, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
        QuadraticMap.polar_smul_left, hvu_w, hvu_aw]
      simp
    have hvu_a : frameA F i (v - u) = v - u := (frameA_fix_iff F i (v - u)).mpr hvan
    have hvu_ρ : reflect Q w (v - u) = v - u := by
      rw [reflect_apply hQw_ne, hvu_w, zero_div, zero_smul, sub_zero]
    have hvu_a2 : (frameA F i ^ 2) (v - u) = v - u := by
      rw [hpow2, hvu_a, hvu_a]
    have hρaρ_vu : (reflect Q w * frameA F i * reflect Q w) (v - u) = (frameA F i ^ 2) (v - u) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hvu_ρ, hvu_a, hvu_ρ, hvu_a2]
    have hρaρ_w : (reflect Q w * frameA F i * reflect Q w) w = (frameA F i ^ 2) w := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hρw, hρaw]
    have hρaρ_aw : (reflect Q w * frameA F i * reflect Q w) (frameA F i w) =
        (frameA F i ^ 2) (frameA F i w) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hρaw]
      rw [hpow2 w, hpow2 (frameA F i w), ha3w, hρw]
    have hspan_u : u ∈ Submodule.span (ZMod 2) {w, frameA F i w} := by
      rw [← frameA_span F i hw hw0 hU]; exact hu_mem
    obtain ⟨c1, c2, hc⟩ := Submodule.mem_span_pair.mp hspan_u
    have hρaρ_u : (reflect Q w * frameA F i * reflect Q w) u = (frameA F i ^ 2) u := by
      rw [← hc, map_add, map_smul, map_smul, hρaρ_w, hρaρ_aw, map_add, map_smul, map_smul]
    calc (reflect Q w * frameA F i * reflect Q w) v
        = (reflect Q w * frameA F i * reflect Q w) (u + (v - u)) := by
          rw [show u + (v - u) = v by abel]
      _ = (reflect Q w * frameA F i * reflect Q w) u +
          (reflect Q w * frameA F i * reflect Q w) (v - u) := map_add _ _ _
      _ = (frameA F i ^ 2) u + (frameA F i ^ 2) (v - u) := by rw [hρaρ_u, hρaρ_vu]
      _ = (frameA F i ^ 2) (u + (v - u)) := (map_add _ _ _).symm
      _ = (frameA F i ^ 2) v := by rw [show u + (v - u) = v by abel]
  exact LinearEquiv.ext hmain

theorem exists_reflection_conj_torus_sgnAut [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : (polarBilin Q).Nondegenerate) {r : ℕ}
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (F : SevOm.Frame Q 3 A r) {τ : (Fin r → Multiplicative (ZMod 3)) →* (V ≃ₗ[ZMod 2] V)}
    (hτF : ∀ f, τ f = F.ι (OrthTorus.piMul r 3 f)) (hU : ∀ j, finrank (ZMod 2) (F.U j) = 2)
    (i : Fin r) :
    ∃ ρ ∈ TauCeti.QuadraticMap.orthogonalGroup Q, ρ ∉ orthDerived Q ∧
      ∀ f, ρ * τ f * ρ⁻¹ = τ (sgnAut i f) := by
  classical
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff (F.U i)).mp (F.ne_bot i)
  have hQw : Q w = 1 := frameA_Q_eq_one hAO F i hw hw0 (hU i)
  refine ⟨reflect Q w, reflect_mem_orthogonalGroup Q w,
    reflect_not_mem_orthDerived hQ hQw, ?_⟩
  intro f
  set f' : Fin r → Multiplicative (ZMod 3) := singleVal i ((f i)⁻¹) * f with hf'
  have hf'_i : f' i = 1 := by
    simp [hf', singleVal, Pi.mulSingle_eq_same]
  have hf_decomp : f = singleVal i (f i) * f' := by
    funext j
    rw [hf']
    by_cases hji : j = i
    · subst hji
      simp [singleVal, Pi.mulSingle_eq_same]
    · simp [singleVal, Pi.mulSingle_eq_of_ne hji]
  have hτf' : ∀ u ∈ F.U i, τ f' u = u := by
    intro u hu
    rw [hτF f']
    exact F.triv (OrthTorus.piMul r 3 f') i
      (by rw [toAdd_piMul_apply, hf'_i]; rfl) u hu
  have hτf'_mem : τ f' ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [hτF f']
    exact hAO (F.mem (OrthTorus.piMul r 3 f'))
  have hτf'_w : τ f' w = w := hτf' w hw
  have hcomm : reflect Q w * τ f' = τ f' * reflect Q w :=
    reflect_commute_of_fix hQw hτf'_mem hτf'_w
  have hconj_f' : reflect Q w * τ f' * (reflect Q w)⁻¹ = τ f' := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  set k : ℕ := (toAdd (f i)).val with hk
  have hfi : ofAdd (k : ZMod 3) = f i := by
    rw [hk, ZMod.natCast_zmod_val, ofAdd_toAdd]
  have hfi_pow : f i = (ofAdd (1 : ZMod 3)) ^ k := by
    rw [← hfi, ← ofAdd_nsmul, nsmul_eq_mul, mul_one]
  have hsingle : singleVal i (f i) = (coordOne i) ^ k := by
    funext j
    rw [hfi_pow]
    by_cases hji : j = i
    · subst hji
      simp only [Pi.pow_apply, singleVal, coordOne, Pi.mulSingle_eq_same]
    · simp only [Pi.pow_apply, singleVal, coordOne, Pi.mulSingle_eq_of_ne hji, one_pow]
  have hpow : τ (singleVal i (f i)) = frameA F i ^ k := by
    rw [hsingle, map_pow]
    congr 1
    exact hτF (coordOne i)
  have hconj_pow : reflect Q w * frameA F i ^ k * (reflect Q w)⁻¹ = (frameA F i ^ k)⁻¹ := by
    have ha_inv : (frameA F i)⁻¹ = frameA F i ^ 2 :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact frameA_pow_three F i)
    have hconj_a : reflect Q w * frameA F i * (reflect Q w)⁻¹ = (frameA F i)⁻¹ := by
      rw [reflect_inv, reflect_conj_frameA hAO F i hw hw0 (hU i) hQw, ha_inv]
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hconj_a, inv_pow]
  have hτinv : τ (singleVal i ((f i)⁻¹)) = (frameA F i ^ k)⁻¹ := by
    have h : singleVal i ((f i)⁻¹) = (singleVal i (f i))⁻¹ := by
      funext j
      by_cases hji : j = i
      · subst hji; simp [singleVal, Pi.mulSingle_eq_same]
      · simp [singleVal, Pi.mulSingle_eq_of_ne hji]
    rw [h, map_inv, hpow]
  have hsgn : sgnAut i f = singleVal i ((f i)⁻¹) * f' := by
    funext j
    rw [sgnAut_apply, hf']
    by_cases hji : j = i
    · subst hji; simp [singleVal, Pi.mulSingle_eq_same]
    · simp [Function.update_of_ne hji, singleVal, Pi.mulSingle_eq_of_ne hji]
  have hτf : τ f = τ (singleVal i (f i)) * τ f' := by
    conv_lhs => rw [hf_decomp]
    rw [map_mul]
  have hsplit : reflect Q w * τ f * (reflect Q w)⁻¹ =
      (reflect Q w * τ (singleVal i (f i)) * (reflect Q w)⁻¹) *
        (reflect Q w * τ f' * (reflect Q w)⁻¹) := by
    rw [hτf]; group
  have hL : reflect Q w * τ f * (reflect Q w)⁻¹ = (frameA F i ^ k)⁻¹ * τ f' := by
    rw [hsplit, hpow, hconj_pow, hconj_f']
  have hR : τ (sgnAut i f) = (frameA F i ^ k)⁻¹ * τ f' := by
    rw [hsgn, map_mul, hτinv]
  rw [hL, hR]

theorem mul_inv_mem_orthDerived_of_not_mem [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : (polarBilin Q).Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) {g h : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgΩ : g ∉ orthDerived Q) (hhΩ : h ∉ orthDerived Q) : g * h⁻¹ ∈ orthDerived Q := by
  have hΩ : orthDerived Q = CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ :=
    CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hQ h6
  let g' : TauCeti.QuadraticMap.orthogonalGroup Q := ⟨g, hg⟩
  let h' : TauCeti.QuadraticMap.orthogonalGroup Q := ⟨h, hh⟩
  have key : ∀ x : TauCeti.QuadraticMap.orthogonalGroup Q,
      x ∉ (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ).ker →
        CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ x = Multiplicative.ofAdd 1 := by
    intro x hx
    have hx0 : (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ x).toAdd ≠ 0 := by
      intro h0
      exact hx (by
        rw [MonoidHom.mem_ker, ← ofAdd_toAdd
          (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ x), h0,
          ofAdd_zero])
    have h1 : (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ x).toAdd = 1 :=
      CFSG.RankThree.Literature.FSmith.zmod2_eq_one_of_ne_zero hx0
    rw [← ofAdd_toAdd
      (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ x), h1]
  have hg' : g' ∉ (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ).ker := by
    intro hker
    apply hgΩ
    rw [hΩ]
    rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_ker Q hQ,
      Subgroup.mem_subgroupOf] at hker
    exact hker
  have hh' : h' ∉ (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ).ker := by
    intro hker
    apply hhΩ
    rw [hΩ]
    rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_ker Q hQ,
      Subgroup.mem_subgroupOf] at hker
    exact hker
  have hmem : g' * h'⁻¹ ∈ (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, key g' hg', key h' hh']
    simp
  rw [hΩ]
  rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_ker Q hQ,
    Subgroup.mem_subgroupOf] at hmem
  exact hmem

end CFSG.StandardType.FrameRoute.FS81
