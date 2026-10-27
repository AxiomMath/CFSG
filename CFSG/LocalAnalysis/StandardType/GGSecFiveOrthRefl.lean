module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.Orbit

public section

namespace CFSG.StandardType.OrthF3

open TauCeti

@[expose] def OrthReflOfNorm {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (Q : QuadraticForm (ZMod 3) V)
    (c : ZMod 3) (g : V ≃ₗ[ZMod 3] V) : Prop :=
  ∃ (v : V) (_ : Invertible (Q v)), Q v = c ∧
    ((QuadraticMap.reflectionOrthogonal Q v : QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ZMod 3] V) = g

private lemma ct_oa_zmod3_sq_eq_one (a : ZMod 3) (ha : a ≠ 0) : a * a = 1 := by
  fin_cases a
  · exact (ha rfl).elim
  · decide
  · decide

private lemma ct_oa_zmod3_represent :
    ∀ A B c : ZMod 3, A ≠ 0 → B ≠ 0 → c ≠ 0 →
      ∃ x y : ZMod 3, x * x * A + y * y * B = c := by
  decide

theorem OrthReflOfNorm.mem_orthogonalGroup_and_ne_zero {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {c : ZMod 3} {g : V ≃ₗ[ZMod 3] V} (h : OrthReflOfNorm Q c g) :
    g ∈ QuadraticMap.orthogonalGroup Q ∧ c ≠ 0 := by
  obtain ⟨v, hv, hQv, hg⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← hg]
    exact (QuadraticMap.reflectionOrthogonal Q v).2
  · rw [← hQv]
    exact IsUnit.ne_zero (isUnit_of_invertible (Q v))

theorem orthReflOfNorm_unique {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {c c' : ZMod 3} {g : V ≃ₗ[ZMod 3] V}
    (h : OrthReflOfNorm Q c g) (h' : OrthReflOfNorm Q c' g) : c = c' := by
  have hc : c ≠ 0 := (OrthReflOfNorm.mem_orthogonalGroup_and_ne_zero h).2
  obtain ⟨v, hv, hQv, hgv⟩ := h
  obtain ⟨w, hw, hQw, hgw⟩ := h'
  have : Invertible (Q v) := hv
  have : Invertible (Q w) := hw
  have hrefl : QuadraticMap.reflection Q v = QuadraticMap.reflection Q w := by
    have hcoe :
        ((QuadraticMap.reflectionOrthogonal Q v : QuadraticMap.orthogonalGroup Q) :
            V ≃ₗ[ZMod 3] V) =
          ((QuadraticMap.reflectionOrthogonal Q w : QuadraticMap.orthogonalGroup Q) :
            V ≃ₗ[ZMod 3] V) := by
      rw [show hv = (inferInstance : Invertible (Q v)) from Subsingleton.elim _ _] at hgv
      rw [show hw = (inferInstance : Invertible (Q w)) from Subsingleton.elim _ _] at hgw
      exact hgv.trans hgw.symm
    simpa only [QuadraticMap.coe_reflectionOrthogonal] using hcoe
  have happ : QuadraticMap.reflection Q v v = QuadraticMap.reflection Q w v :=
    congrArg (fun f : V ≃ₗ[ZMod 3] V => f v) hrefl
  rw [QuadraticMap.reflection_apply_self, QuadraticMap.reflection_apply_eq_sub_div] at happ
  set a : ZMod 3 := QuadraticMap.polar Q w v / Q w with ha_def
  have ha_w : a • w = (2 : ZMod 3) • v := by
    have h1 : a • w = v - (-v) :=
      (eq_sub_iff_add_eq).mpr (by rw [add_comm]; exact (eq_sub_iff_add_eq).mp happ)
    rw [h1, sub_neg_eq_add, ← two_smul (ZMod 3) v]
  have hv_ne : v ≠ 0 := fun h0 => hc (by rw [← hQv, h0, map_zero])
  have ha : a ≠ 0 := by
    intro ha0
    have h2v : (2 : ZMod 3) • v = 0 := by rw [← ha_w, ha0, zero_smul]
    rcases smul_eq_zero.mp h2v with h2 | hv0
    · exact (by decide : (2 : ZMod 3) ≠ 0) h2
    · exact hv_ne hv0
  have hQeq : Q w = Q v := by
    have h := congrArg Q ha_w
    rw [QuadraticMap.map_smul, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul] at h
    have ha2 : a * a = 1 := ct_oa_zmod3_sq_eq_one a ha
    have h22 : (2 : ZMod 3) * 2 = 1 := by decide
    rw [ha2, h22, one_mul, one_mul] at h
    exact h
  exact hQv.symm.trans (hQeq.symm.trans hQw)

theorem OrthReflOfNorm.conj {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {c : ZMod 3} {g : V ≃ₗ[ZMod 3] V} (h : OrthReflOfNorm Q c g)
    (e : V ≃ₗ[ZMod 3] V) (he : e ∈ QuadraticMap.orthogonalGroup Q) :
    OrthReflOfNorm Q c (e * g * e⁻¹) := by
  obtain ⟨v, hv, hQv, hg⟩ := h
  have : Invertible (Q v) := hv
  rw [show hv = (inferInstance : Invertible (Q v)) from Subsingleton.elim _ _] at hg
  have hev : Q (e v) = Q v := (QuadraticMap.mem_orthogonalGroup_iff.mp he) v
  let : Invertible (Q (e v)) := (inferInstance : Invertible (Q v)).copy (Q (e v)) hev
  refine ⟨e v, inferInstance, ?_, ?_⟩
  · rw [hev, hQv]
  · rw [← hg]
    simpa using
      congrArg Subtype.val (QuadraticMap.mul_reflectionOrthogonal_mul_inv Q ⟨e, he⟩ v).symm

theorem orthReflOfNorm_conjugate {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : 2 ≤ Module.finrank (ZMod 3) V)
    {c : ZMod 3} {g g' : V ≃ₗ[ZMod 3] V} (h : OrthReflOfNorm Q c g) (h' : OrthReflOfNorm Q c g') :
    ∃ e ∈ QuadraticMap.orthogonalGroup Q, g' = e * g * e⁻¹ := by
  have hc : c ≠ 0 := (OrthReflOfNorm.mem_orthogonalGroup_and_ne_zero h).2
  obtain ⟨v, hv, hQv, hg⟩ := h
  obtain ⟨w, hw, hQw, hgw⟩ := h'
  have hQvw : Q v = Q w := hQv.trans hQw.symm
  have hw0 : Q w ≠ 0 := by rw [hQw]; exact hc
  have : NeZero (2 : ZMod 3) := ⟨by decide⟩
  have : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  obtain ⟨e, hev⟩ :=
    QuadraticMap.exists_specialOrthogonal_map_eq_of_nondegenerate Q hQnd hd hQvw hw0
  have he : (e : V ≃ₗ[ZMod 3] V) ∈ QuadraticMap.orthogonalGroup Q :=
    QuadraticMap.specialOrthogonalGroup_le_orthogonalGroup Q e.property
  subst w
  have : Invertible (Q v) := hv
  have : Invertible (Q ((e : V ≃ₗ[ZMod 3] V) v)) := hw
  rw [show hv = (inferInstance : Invertible (Q v)) from Subsingleton.elim _ _] at hg
  rw [show hw = (inferInstance : Invertible (Q ((e : V ≃ₗ[ZMod 3] V) v)))
        from Subsingleton.elim _ _] at hgw
  refine ⟨(e : V ≃ₗ[ZMod 3] V), he, ?_⟩
  have hconj := congrArg Subtype.val
    (QuadraticMap.mul_reflectionOrthogonal_mul_inv Q ⟨(e : V ≃ₗ[ZMod 3] V), he⟩ v)
  rw [← hgw, ← hg]
  exact hconj.symm

theorem exists_orthReflOfNorm {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : 2 ≤ Module.finrank (ZMod 3) V) {c : ZMod 3} (hc : c ≠ 0) : ∃ g, OrthReflOfNorm Q c g := by
  have : NeZero (2 : ZMod 3) := ⟨by decide⟩
  have : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  obtain ⟨l, horth, hlen, _hspan, haniso⟩ := hQnd.exists_list_pairwise_isOrtho
  have hlen2 : 2 ≤ l.length := by rw [hlen]; exact hd
  obtain ⟨a, b, rest, hl⟩ : ∃ a b rest, l = a :: b :: rest := by
    cases l with
    | nil => simp at hlen2
    | cons a t =>
      cases t with
      | nil => simp at hlen2
      | cons b rest => exact ⟨a, b, rest, rfl⟩
  subst l
  have hortho : Q.IsOrtho a b := (List.pairwise_cons.mp horth).1 b (by simp)
  have ha0 : Q a ≠ 0 := haniso a (by simp)
  have hb0 : Q b ≠ 0 := haniso b (by simp)
  obtain ⟨x, y, hxy⟩ := ct_oa_zmod3_represent (Q a) (Q b) c ha0 hb0 hc
  have hQv : Q (x • a + y • b) = c := by
    have hpolar : QuadraticMap.polar Q a b = 0 := hortho.polar_eq_zero
    calc Q (x • a + y • b)
        = Q (x • a) + Q (y • b) + QuadraticMap.polar Q (x • a) (y • b) :=
          QuadraticMap.map_add Q (x • a) (y • b)
      _ = x * x * Q a + y * y * Q b + x * y * QuadraticMap.polar Q a b := by
          rw [QuadraticMap.map_smul, QuadraticMap.map_smul, QuadraticMap.polar_smul_left,
            QuadraticMap.polar_smul_right]
          simp only [smul_eq_mul]
          ring
      _ = x * x * Q a + y * y * Q b := by rw [hpolar, mul_zero, add_zero]
      _ = c := hxy
  let : Invertible (Q (x • a + y • b)) := invertibleOfNonzero (by rw [hQv]; exact hc)
  refine ⟨(QuadraticMap.reflectionOrthogonal Q (x • a + y • b) : V ≃ₗ[ZMod 3] V), ?_⟩
  exact ⟨x • a + y • b, inferInstance, hQv, rfl⟩

private lemma ct_oa_neg_two_smul {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (v : V) :
    (-2 : ZMod 3) • v = v := by
  rw [show (-2 : ZMod 3) = 1 by decide, one_smul]

theorem linRefl_iff_orthRefl {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {g : V ≃ₗ[ZMod 3] V} (hg : g ∈ QuadraticMap.orthogonalGroup Q) :
    (g * g = 1 ∧ Module.finrank (ZMod 3) (LinearMap.range (g.toLinearMap - LinearMap.id)) = 1) ↔
      ∃ c : ZMod 3, c ≠ 0 ∧ OrthReflOfNorm Q c g := by
  constructor
  · intro h
    obtain ⟨hgg, hrank⟩ := h
    set f : V →ₗ[ZMod 3] V := g.toLinearMap - LinearMap.id with hf
    have hbot : f.range ≠ ⊥ := by
      intro hbot
      rw [hbot] at hrank
      simp at hrank
    obtain ⟨u, hu_mem, hu_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hgQ : ∀ m : V, Q (g m) = Q m := QuadraticMap.mem_orthogonalGroup_iff.mp hg
    have hrange : f.range = ZMod 3 ∙ u := by
      refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
      · exact (Submodule.span_singleton_le_iff_mem u f.range).mpr hu_mem
      · rw [finrank_span_singleton hu_ne, hrank]
    have hpol : ∀ x y : V, QuadraticMap.polar Q (g x) (g y) = QuadraticMap.polar Q x y := by
      intro x y
      simp only [QuadraticMap.polar]
      rw [← g.map_add, hgQ (x + y), hgQ x, hgQ y]
    have hgu : g u = -u := by
      obtain ⟨y, hy⟩ := hu_mem
      have hu_eq : u = g y - y := by rw [hy.symm]; rfl
      calc g u = g (g y - y) := by rw [← hu_eq]
        _ = g (g y) - g y := by rw [map_sub]
        _ = (g * g) y - g y := rfl
        _ = y - g y := by rw [hgg]; rfl
        _ = -(g y - y) := by abel
        _ = -u := by rw [← hu_eq]
    have hker_polar : ∀ x, g x = x → QuadraticMap.polar Q x u = 0 := by
      intro x hx
      obtain ⟨y, hy⟩ := hu_mem
      have hu_eq : u = g y - y := by rw [hy.symm]; rfl
      have hpolx : QuadraticMap.polar Q x (g y) = QuadraticMap.polar Q x y := by
        calc QuadraticMap.polar Q x (g y) = QuadraticMap.polar Q (g x) (g y) := by rw [hx]
          _ = QuadraticMap.polar Q x y := hpol x y
      rw [hu_eq, QuadraticMap.polar_sub_right, hpolx, sub_self]
    have hQu_ne : Q u ≠ 0 := by
      intro hQu0
      have hv : ∃ v, QuadraticMap.polar Q u v ≠ 0 := by
        by_contra h
        have h' : ∀ v, QuadraticMap.polar Q u v = 0 :=
          fun v => not_not.mp (not_exists.mp h v)
        exact hu_ne (hQ.1 u (fun y => by rw [QuadraticMap.polarBilin_apply_apply]; exact h' y))
      obtain ⟨v, hv⟩ := hv
      have hmem : g v - v ∈ ZMod 3 ∙ u := by
        rw [← hrange]
        exact ⟨v, rfl⟩
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      have hgv : g v = v + c • u := by rw [hc]; abel
      have hp1 : QuadraticMap.polar Q u (g v) = QuadraticMap.polar Q u v := by
        rw [hgv, QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
          QuadraticMap.polar_self]
        simp [hQu0]
      have hp2 : QuadraticMap.polar Q u (g v) = -QuadraticMap.polar Q u v := by
        have hh := hpol u v
        rw [hgu] at hh
        rw [QuadraticMap.polar_neg_left] at hh
        exact (neg_eq_iff_eq_neg).mp hh
      have hzero : QuadraticMap.polar Q u v = 0 := by
        have h2 : (2 : ZMod 3) • QuadraticMap.polar Q u v = 0 := by
          rw [two_smul]
          nth_rewrite 1 [hp1.symm.trans hp2]
          rw [neg_add_cancel]
        exact (smul_eq_zero.mp h2).resolve_left (by decide)
      exact hv hzero
    let : Invertible (Q u) := invertibleOfNonzero hQu_ne
    have hgx_refl : ∀ x : V, g x = QuadraticMap.reflection Q u x := by
      intro x
      have hmem : g x - x ∈ ZMod 3 ∙ u := by
        rw [← hrange]
        exact ⟨x, rfl⟩
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      have hgx : g x = x + c • u := by rw [hc]; abel
      have hrel : c * (c * Q u + QuadraticMap.polar Q x u) = 0 := by
        have hQgx : Q (g x) = Q x := hgQ x
        have hexp : Q (g x) = Q x + (c * c) * Q u + c * QuadraticMap.polar Q x u := by
          have h1 : Q (x + c • u) = Q x + Q (c • u) + QuadraticMap.polar Q x (c • u) := by
            rw [QuadraticMap.polar]
            abel
          rw [hgx, h1, QuadraticMap.map_smul, QuadraticMap.polar_smul_right]
          simp only [smul_eq_mul]
        rw [hQgx] at hexp
        have hAB : (c * c) * Q u + c * QuadraticMap.polar Q x u = 0 := by
          have h' : Q x + ((c * c) * Q u + c * QuadraticMap.polar Q x u) = Q x + 0 := by
            rw [add_zero, ← add_assoc]
            exact hexp.symm
          exact add_left_cancel h'
        have : c * (c * Q u + QuadraticMap.polar Q x u) =
            (c * c) * Q u + c * QuadraticMap.polar Q x u := by ring
        rw [this]
        exact hAB
      have hcval : c = -(QuadraticMap.polar Q x u) / Q u := by
        rcases mul_eq_zero.mp hrel with hc0 | hc1
        · have hgxx : g x = x := by rw [hgx, hc0, zero_smul, add_zero]
          have hp : QuadraticMap.polar Q x u = 0 := hker_polar x hgxx
          rw [hc0, hp, neg_zero, zero_div]
        · rw [eq_div_iff hQu_ne, eq_neg_iff_add_eq_zero]
          exact hc1
      have hpcomm : QuadraticMap.polar Q u x = QuadraticMap.polar Q x u :=
        QuadraticMap.polar_comm Q u x
      rw [hgx, hcval, QuadraticMap.reflection_apply_eq_sub_div, hpcomm]
      simp only [div_eq_mul_inv, neg_mul, neg_smul, sub_eq_add_neg]
    have hg_eq_refl : g = QuadraticMap.reflection Q u := LinearEquiv.ext hgx_refl
    exact ⟨Q u, hQu_ne, u, inferInstance, rfl, by
      rw [hg_eq_refl, QuadraticMap.coe_reflectionOrthogonal]⟩
  · rintro ⟨c, _hc, hrefl⟩
    obtain ⟨v, hv, _hQv, hgv⟩ := hrefl
    have : Invertible (Q v) := hv
    rw [show hv = (inferInstance : Invertible (Q v)) from Subsingleton.elim _ _] at hgv
    have hg_eq : g = QuadraticMap.reflection Q v := by
      rw [← hgv, QuadraticMap.coe_reflectionOrthogonal]
    have hv0 : v ≠ 0 := by
      intro h0
      exact (isUnit_of_invertible (Q v)).ne_zero (by rw [h0, map_zero])
    constructor
    · rw [hg_eq, QuadraticMap.reflection_mul_self]
    · rw [hg_eq]
      have hrange :
          LinearMap.range ((QuadraticMap.reflection Q v).toLinearMap - LinearMap.id) =
            ZMod 3 ∙ v := by
        apply le_antisymm
        · rintro y ⟨x, rfl⟩
          rw [LinearMap.sub_apply, LinearMap.id_apply]
          change QuadraticMap.reflection Q v x - x ∈ ZMod 3 ∙ v
          rw [QuadraticMap.reflection_apply_eq_sub_div]
          have hx : x - (QuadraticMap.polar Q v x / Q v) • v - x =
              -((QuadraticMap.polar Q v x / Q v) • v) := by abel
          rw [hx, Submodule.mem_span_singleton]
          exact ⟨-(QuadraticMap.polar Q v x / Q v), neg_smul _ _⟩
        · rw [Submodule.span_singleton_le_iff_mem]
          refine ⟨v, ?_⟩
          rw [LinearMap.sub_apply, LinearMap.id_apply]
          change QuadraticMap.reflection Q v v - v = v
          rw [QuadraticMap.reflection_apply_self]
          rw [sub_eq_add_neg, ← neg_add, ← two_smul (ZMod 3) v, ← neg_smul, ct_oa_neg_two_smul]
      rw [hrange, finrank_span_singleton hv0]

end CFSG.StandardType.OrthF3

end
