module

public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.ASVolI

open Module Submodule CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def burnsideB49x_gl_fix (E : Subgroup (W ≃ₗ[ZMod 2] W)) : Submodule (ZMod 2) W where
  carrier := {x | ∀ e ∈ E, e x = x}
  add_mem' {x y} hx hy e he := by rw [map_add, hx e he, hy e he]
  zero_mem' e _ := map_zero e
  smul_mem' a x hx e he := by rw [map_smul, hx e he]

@[expose] def burnsideB49x_gl_comm (E : Subgroup (W ≃ₗ[ZMod 2] W)) : Submodule (ZMod 2) W :=
  Submodule.span (ZMod 2) {y | ∃ e ∈ E, ∃ x, e x - x = y}

@[expose] def burnsideB49x_gl_Q (X : Submodule (ZMod 2) W) : Subgroup (W ≃ₗ[ZMod 2] W) where
  carrier := {g | (∀ x, g x - x ∈ X) ∧ ∀ y ∈ X, g y = y}
  mul_mem' {g h} hg hh := by
    refine ⟨fun x => ?_, fun y hy => ?_⟩
    · rw [LinearEquiv.mul_apply, ← sub_add_sub_cancel (g (h x)) (h x) x]
      exact add_mem (hg.1 (h x)) (hh.1 x)
    · rw [LinearEquiv.mul_apply, hh.2 y hy, hg.2 y hy]
  one_mem' := ⟨fun x => by simp, fun y _ => rfl⟩
  inv_mem' {g} hg := by
    refine ⟨fun x => ?_, fun y hy => ?_⟩
    · rw [LinearEquiv.coe_inv]
      have h := hg.1 (g.symm x)
      rw [LinearEquiv.apply_symm_apply] at h
      rw [← neg_sub]
      exact neg_mem h
    · rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_eq, hg.2 y hy]

theorem burnsideB49x_gl_mem_fix {E : Subgroup (W ≃ₗ[ZMod 2] W)} {x : W} :
    x ∈ burnsideB49x_gl_fix E ↔ ∀ e ∈ E, e x = x :=
  Iff.rfl

theorem burnsideB49x_gl_sub_mem_comm {E : Subgroup (W ≃ₗ[ZMod 2] W)} {e : W ≃ₗ[ZMod 2] W}
    (he : e ∈ E) (x : W) : e x - x ∈ burnsideB49x_gl_comm E :=
  Submodule.subset_span ⟨e, he, x, rfl⟩

theorem burnsideB49x_gl_mem_Q {X : Submodule (ZMod 2) W} {g : W ≃ₗ[ZMod 2] W} :
    g ∈ burnsideB49x_gl_Q X ↔ (∀ x, g x - x ∈ X) ∧ ∀ y ∈ X, g y = y :=
  Iff.rfl

theorem burnsideB49x_gl_comm_le_fix_iff {E : Subgroup (W ≃ₗ[ZMod 2] W)} :
    burnsideB49x_gl_comm E ≤ burnsideB49x_gl_fix E ↔
      ∀ e ∈ E, ∀ e' ∈ E, ∀ x, e' (e x - x) = e x - x := by
  rw [burnsideB49x_gl_comm, Submodule.span_le]
  constructor
  · intro h e he e' he' x
    exact h ⟨e, he, x, rfl⟩ e' he'
  · rintro h _ ⟨e, he, x, rfl⟩ e' he'
    exact h e he e' he' x

theorem burnsideB49x_gl_apply_apply {e : W ≃ₗ[ZMod 2] W} (h : e * e = 1) (x : W) :
    e (e x) = x := by
  rw [← LinearEquiv.mul_apply, h]
  rfl

theorem burnsideB49x_gl_apply_comm {e e' : W ≃ₗ[ZMod 2] W} (h : e * e' = e' * e) (x : W) :
    e (e' x) = e' (e x) := by
  rw [← LinearEquiv.mul_apply, h, LinearEquiv.mul_apply]

theorem burnsideB49x_gl_apply_sub {e : W ≃ₗ[ZMod 2] W} (h : e * e = 1) (x : W) :
    e (e x - x) = e x - x := by
  rw [map_sub, burnsideB49x_gl_apply_apply h, two_sub, two_sub, add_comm]

theorem burnsideB49x_gl_finrank_lt [FiniteDimensional (ZMod 2) W] {S T : Submodule (ZMod 2) W}
    (hST : S ≤ T) {x : W} (hxT : x ∈ T) (hxS : x ∉ S) :
    finrank (ZMod 2) S < finrank (ZMod 2) T :=
  Submodule.finrank_lt_finrank_of_lt (SetLike.lt_iff_le_and_exists.2 ⟨hST, x, hxT, hxS⟩)

theorem burnsideB49x_gl_mem_or_add_mem [FiniteDimensional (ZMod 2) W]
    {D : Submodule (ZMod 2) W} {x : W} (hx : x ∉ D)
    (hD : finrank (ZMod 2) W ≤ finrank (ZMod 2) D + 1) (w : W) : w ∈ D ∨ w + x ∈ D := by
  have h1 := burnsideB49x_gl_finrank_lt (le_sup_left : D ≤ D ⊔ (ZMod 2) ∙ x)
    (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)) hx
  have htop : D ⊔ (ZMod 2) ∙ x = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (by omega))
  have hw : w ∈ D ⊔ (ZMod 2) ∙ x := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨d, hd, z, hz, rfl⟩ := Submodule.mem_sup.1 hw
  rcases mem_span_singleton_iff_two.1 hz with rfl | rfl
  · left
    rwa [add_zero]
  · right
    rwa [add_assoc, two_add_self, add_zero]

theorem burnsideB49x_gl_quad_of_codim [FiniteDimensional (ZMod 2) W]
    {E : Subgroup (W ≃ₗ[ZMod 2] W)} (hc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e)
    (h2 : ∀ e ∈ E, e * e = 1)
    (hdim : finrank (ZMod 2) W ≤ finrank (ZMod 2) (burnsideB49x_gl_fix E) + 2) :
    burnsideB49x_gl_comm E ≤ burnsideB49x_gl_fix E := by
  rw [burnsideB49x_gl_comm, Submodule.span_le]
  rintro _ ⟨e, he, x, rfl⟩
  by_contra hy
  change e x - x ∉ burnsideB49x_gl_fix E at hy
  have hey : e (e x - x) = e x - x := burnsideB49x_gl_apply_sub (h2 e he) x
  set y := e x - x with hy_def
  set D := burnsideB49x_gl_fix E ⊔ (ZMod 2) ∙ y with hD_def
  have hDe : ∀ d ∈ D, e d = d := by
    intro d hd
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hd
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hb
    rw [map_add, map_smul, ha e he, hey]
  have hD : finrank (ZMod 2) (burnsideB49x_gl_fix E) < finrank (ZMod 2) D :=
    burnsideB49x_gl_finrank_lt le_sup_left
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)) hy
  have hxD : x ∉ D := by
    intro hx
    apply hy
    rw [hy_def, hDe x hx, sub_self]
    exact zero_mem _
  have hw : ∀ w, e w - w = 0 ∨ e w - w = y := by
    intro w
    rcases burnsideB49x_gl_mem_or_add_mem hxD (by omega) w with hwD | hwD
    · left
      rw [hDe w hwD, sub_self]
    · right
      have h := hDe _ hwD
      rw [map_add] at h
      rw [hy_def, two_sub, two_sub]
      calc e w + w = e w + w + (e x + x) + (e x + x) := by
            rw [add_assoc (e w + w), two_add_self, add_zero]
        _ = (e w + e x) + (w + x) + (e x + x) := by abel
        _ = e x + x := by rw [h, two_add_self, zero_add]
  apply hy
  intro e' he'
  have hz : e' y - y = e (e' x - x) - (e' x - x) := by
    rw [hy_def, map_sub, ← burnsideB49x_gl_apply_comm (hc e he e' he'), map_sub]
    abel
  rcases hw (e' x - x) with h0 | h1
  · rw [← hz, sub_eq_zero] at h0
    exact h0
  · exfalso
    rw [← hz, sub_eq_iff_eq_add, two_add_self] at h1
    have hy0 : y = 0 := e'.injective (by rw [h1, map_zero])
    exact hy (hy0 ▸ zero_mem _)

theorem burnsideB49x_gl_quad_of_comm_le [FiniteDimensional (ZMod 2) W]
    {E : Subgroup (W ≃ₗ[ZMod 2] W)} (hc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e)
    (h2 : ∀ e ∈ E, e * e = 1)
    (hdim : finrank (ZMod 2) (burnsideB49x_gl_comm E) ≤ 2) :
    burnsideB49x_gl_comm E ≤ burnsideB49x_gl_fix E := by
  rw [burnsideB49x_gl_comm_le_fix_iff]
  intro e he e' he' x
  by_contra hne
  have hyB : e x - x ∈ burnsideB49x_gl_comm E := burnsideB49x_gl_sub_mem_comm he x
  have hwB : e' x - x ∈ burnsideB49x_gl_comm E := burnsideB49x_gl_sub_mem_comm he' x
  have hzB : e' (e x - x) - (e x - x) ∈ burnsideB49x_gl_comm E :=
    burnsideB49x_gl_sub_mem_comm he' _
  have hey : e (e x - x) = e x - x := burnsideB49x_gl_apply_sub (h2 e he) x
  have hzw : e' (e x - x) - (e x - x) = e (e' x - x) - (e' x - x) := by
    rw [map_sub, ← burnsideB49x_gl_apply_comm (hc e he e' he'), map_sub]
    abel
  have hez : e (e (e' x - x) - (e' x - x)) = e (e' x - x) - (e' x - x) :=
    burnsideB49x_gl_apply_sub (h2 e he) _
  set y := e x - x with hy_def
  set w := e' x - x with hw_def
  set z := e' y - y with hz_def
  have hz0 : z ≠ 0 := sub_ne_zero.2 hne
  have hy0 : y ≠ 0 := by
    intro h
    apply hz0
    rw [hz_def, h, map_zero, sub_zero]
  have hzy : z ∉ (ZMod 2) ∙ y := by
    rw [mem_span_singleton_iff_two]
    rintro (h | h)
    · exact hz0 h
    · apply hy0
      rw [hz_def, sub_eq_iff_eq_add, two_add_self] at h
      exact e'.injective (by rw [h, map_zero])
  have hS₂B : (ZMod 2) ∙ y ⊔ (ZMod 2) ∙ z ≤ burnsideB49x_gl_comm E :=
    sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hyB)
      ((Submodule.span_singleton_le_iff_mem _ _).2 hzB)
  have hwS₂ : w ∈ (ZMod 2) ∙ y ⊔ (ZMod 2) ∙ z := by
    by_contra hwS
    have h1 : finrank (ZMod 2) (⊥ : Submodule (ZMod 2) W) < finrank (ZMod 2) ((ZMod 2) ∙ y) :=
      burnsideB49x_gl_finrank_lt bot_le (Submodule.mem_span_singleton_self y)
        (by rwa [Submodule.mem_bot])
    have h2' := burnsideB49x_gl_finrank_lt (le_sup_left : (ZMod 2) ∙ y ≤ _ ⊔ (ZMod 2) ∙ z)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)) hzy
    have h3 := burnsideB49x_gl_finrank_lt
      (le_sup_left : (ZMod 2) ∙ y ⊔ (ZMod 2) ∙ z ≤ _ ⊔ (ZMod 2) ∙ w)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w)) hwS
    have h4 := Submodule.finrank_mono
      (sup_le hS₂B ((Submodule.span_singleton_le_iff_mem _ _).2 hwB))
    rw [finrank_bot] at h1
    omega
  have hS₂e : ∀ v ∈ (ZMod 2) ∙ y ⊔ (ZMod 2) ∙ z, e v = v := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 ha
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hb
    rw [map_add, map_smul, map_smul, hey, hzw, hez]
  exact hz0 (hzw.trans (by rw [hS₂e w hwS₂, sub_self]))

@[expose] def burnsideB49x_gl_hom (C B : Submodule (ZMod 2) W) (g : W ≃ₗ[ZMod 2] W)
    (hC : ∀ x ∈ C, g x = x) (hB : ∀ x, g x - x ∈ B) : (W ⧸ C) →ₗ[ZMod 2] B :=
  C.liftQ (LinearMap.codRestrict B ((g : W →ₗ[ZMod 2] W) - LinearMap.id) hB) fun x hx => by
    rw [LinearMap.mem_ker]
    ext
    simp [hC x hx]

theorem burnsideB49x_gl_hom_mk (C B : Submodule (ZMod 2) W) (g : W ≃ₗ[ZMod 2] W)
    (hC : ∀ x ∈ C, g x = x) (hB : ∀ x, g x - x ∈ B) (x : W) :
    ((burnsideB49x_gl_hom C B g hC hB (Submodule.Quotient.mk x) : B) : W) = g x - x :=
  rfl

theorem burnsideB49x_gl_hom_inj {C B : Submodule (ZMod 2) W} {g g' : W ≃ₗ[ZMod 2] W}
    {hC : ∀ x ∈ C, g x = x} {hB : ∀ x, g x - x ∈ B} {hC' : ∀ x ∈ C, g' x = x}
    {hB' : ∀ x, g' x - x ∈ B}
    (h : burnsideB49x_gl_hom C B g hC hB = burnsideB49x_gl_hom C B g' hC' hB') : g = g' := by
  ext x
  have hx := congrArg (fun φ : (W ⧸ C) →ₗ[ZMod 2] B => ((φ (Submodule.Quotient.mk x) : B) : W)) h
  simp only [burnsideB49x_gl_hom_mk] at hx
  exact sub_left_injective hx

theorem burnsideB49x_gl_card_hom [FiniteDimensional (ZMod 2) W] (C B : Submodule (ZMod 2) W) :
    Nat.card ((W ⧸ C) →ₗ[ZMod 2] B) =
      2 ^ ((finrank (ZMod 2) W - finrank (ZMod 2) C) * finrank (ZMod 2) B) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, Module.finrank_linearMap,
    Submodule.finrank_quotient]

theorem burnsideB49x_gl_card_le [FiniteDimensional (ZMod 2) W] {ι : Type*}
    (f : ι → (W ≃ₗ[ZMod 2] W)) (hf : Function.Injective f) (C B : Submodule (ZMod 2) W)
    (hC : ∀ i, ∀ x ∈ C, f i x = x) (hB : ∀ i x, f i x - x ∈ B) :
    Nat.card ι ≤ 2 ^ ((finrank (ZMod 2) W - finrank (ZMod 2) C) * finrank (ZMod 2) B) := by
  haveI : Finite ((W ⧸ C) →ₗ[ZMod 2] B) := Module.finite_of_finite (ZMod 2)
  rw [← burnsideB49x_gl_card_hom C B]
  exact Nat.card_le_card_of_injective (fun i => burnsideB49x_gl_hom C B (f i) (hC i) (hB i))
    fun i j hij => hf (burnsideB49x_gl_hom_inj hij)

theorem burnsideB49x_gl_card_le_fix_comm [FiniteDimensional (ZMod 2) W]
    (E : Subgroup (W ≃ₗ[ZMod 2] W)) :
    Nat.card E ≤ 2 ^ ((finrank (ZMod 2) W - finrank (ZMod 2) (burnsideB49x_gl_fix E)) *
      finrank (ZMod 2) (burnsideB49x_gl_comm E)) :=
  burnsideB49x_gl_card_le (fun e : E => (e : W ≃ₗ[ZMod 2] W)) Subtype.val_injective _ _
    (fun e _ hx => hx e e.2) (fun e x => burnsideB49x_gl_sub_mem_comm e.2 x)

theorem burnsideB49x_gl_one_le_finrank_fix [FiniteDimensional (ZMod 2) W]
    (hW : 0 < finrank (ZMod 2) W) {E : Subgroup (W ≃ₗ[ZMod 2] W)} (h2 : ∀ e ∈ E, e * e = 1) :
    1 ≤ finrank (ZMod 2) (burnsideB49x_gl_fix E) := by
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  have hp : IsPGroup 2 E := fun g => ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, pow_one, sq]
    exact h2 _ g.2)⟩
  have hdvd : 2 ∣ Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self 2 hW.ne'
  obtain ⟨b, hb, hb0⟩ := hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point W hdvd
    (a := 0) (MulAction.mem_fixedPoints.2 fun g => show (g : W ≃ₗ[ZMod 2] W) 0 = 0 from map_zero _)
  have hbfix : b ∈ burnsideB49x_gl_fix E := fun e he => MulAction.mem_fixedPoints.1 hb ⟨e, he⟩
  rw [Submodule.one_le_finrank_iff]
  intro hbot
  rw [hbot, Submodule.mem_bot] at hbfix
  exact hb0 hbfix.symm

theorem burnsideB49x_gl_Q_quad {X : Submodule (ZMod 2) W} {g g' : W ≃ₗ[ZMod 2] W}
    (hg : g ∈ burnsideB49x_gl_Q X) (hg' : g' ∈ burnsideB49x_gl_Q X) (x : W) :
    g (g' x - x) = g' x - x :=
  hg.2 _ (hg'.1 x)

theorem burnsideB49x_gl_Q_apply_apply {X : Submodule (ZMod 2) W} {g g' : W ≃ₗ[ZMod 2] W}
    (hg : g ∈ burnsideB49x_gl_Q X) (hg' : g' ∈ burnsideB49x_gl_Q X) (x : W) :
    g (g' x) = g x + (g' x - x) := by
  have h : g' x = x + (g' x - x) := by abel
  calc g (g' x) = g (x + (g' x - x)) := congrArg g h
    _ = g x + (g' x - x) := by rw [map_add, burnsideB49x_gl_Q_quad hg hg' x]

theorem burnsideB49x_gl_Q_mul_comm {X : Submodule (ZMod 2) W} {g g' : W ≃ₗ[ZMod 2] W}
    (hg : g ∈ burnsideB49x_gl_Q X) (hg' : g' ∈ burnsideB49x_gl_Q X) : g * g' = g' * g := by
  ext x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, burnsideB49x_gl_Q_apply_apply hg hg',
    burnsideB49x_gl_Q_apply_apply hg' hg]
  abel

theorem burnsideB49x_gl_Q_mul_self {X : Submodule (ZMod 2) W} {g : W ≃ₗ[ZMod 2] W}
    (hg : g ∈ burnsideB49x_gl_Q X) : g * g = 1 := by
  ext x
  rw [LinearEquiv.mul_apply, burnsideB49x_gl_Q_apply_apply hg hg, two_sub, ← add_assoc,
    two_add_self, zero_add]
  rfl

@[expose] def burnsideB49x_gl_ofHom (X : Submodule (ZMod 2) W) (φ : (W ⧸ X) →ₗ[ZMod 2] X) :
    W ≃ₗ[ZMod 2] W :=
  LinearEquiv.ofInvolutive (LinearMap.id + X.subtype ∘ₗ φ ∘ₗ X.mkQ) fun x => by
    simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.subtype_apply]
    rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero X).2 (φ _).2, add_zero,
      add_assoc, two_add_self, add_zero]

theorem burnsideB49x_gl_ofHom_apply (X : Submodule (ZMod 2) W) (φ : (W ⧸ X) →ₗ[ZMod 2] X)
    (x : W) : burnsideB49x_gl_ofHom X φ x = x + (φ (Submodule.Quotient.mk x) : W) :=
  rfl

theorem burnsideB49x_gl_ofHom_mem (X : Submodule (ZMod 2) W) (φ : (W ⧸ X) →ₗ[ZMod 2] X) :
    burnsideB49x_gl_ofHom X φ ∈ burnsideB49x_gl_Q X := by
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · rw [burnsideB49x_gl_ofHom_apply, add_sub_cancel_left]
    exact (φ _).2
  · rw [burnsideB49x_gl_ofHom_apply, (Submodule.Quotient.mk_eq_zero X).2 hy, map_zero,
      Submodule.coe_zero, add_zero]

theorem burnsideB49x_gl_card_Q_eq [FiniteDimensional (ZMod 2) W] (X : Submodule (ZMod 2) W) :
    Nat.card (burnsideB49x_gl_Q X) =
      2 ^ ((finrank (ZMod 2) W - finrank (ZMod 2) X) * finrank (ZMod 2) X) := by
  rw [← burnsideB49x_gl_card_hom X X]
  refine Nat.card_eq_of_bijective
    (fun g : burnsideB49x_gl_Q X => burnsideB49x_gl_hom X X g g.2.2 g.2.1) ⟨fun g g' h =>
      Subtype.ext (burnsideB49x_gl_hom_inj h), fun φ => ⟨⟨_, burnsideB49x_gl_ofHom_mem X φ⟩, ?_⟩⟩
  refine LinearMap.ext fun q => ?_
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    apply Subtype.ext
    change burnsideB49x_gl_ofHom X φ x - x = _
    rw [burnsideB49x_gl_ofHom_apply, add_sub_cancel_left]

theorem burnsideB49x_gl_card_Q [FiniteDimensional (ZMod 2) W] {X : Submodule (ZMod 2) W}
    {k n : ℕ} (hk : finrank (ZMod 2) X = k) (hn : finrank (ZMod 2) W = n) :
    Nat.card (burnsideB49x_gl_Q X) = 2 ^ (k * (n - k)) := by
  rw [burnsideB49x_gl_card_Q_eq, hk, hn, mul_comm]

theorem burnsideB49x_gl_three [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W = 3)
    {E : Subgroup (W ≃ₗ[ZMod 2] W)} (hc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e)
    (h2 : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 4 := by
  have hc1 := burnsideB49x_gl_one_le_finrank_fix (by omega) h2
  have hbc := Submodule.finrank_mono (burnsideB49x_gl_quad_of_codim hc h2 (by omega))
  have hc3 := Submodule.finrank_le (burnsideB49x_gl_fix E)
  have hcard := burnsideB49x_gl_card_le_fix_comm E
  rw [hW] at hcard hc3
  have hexp : (3 - finrank (ZMod 2) (burnsideB49x_gl_fix E)) *
      finrank (ZMod 2) (burnsideB49x_gl_comm E) ≤ 2 := by
    generalize finrank (ZMod 2) (burnsideB49x_gl_fix E) = c at hc1 hbc hc3 ⊢
    generalize finrank (ZMod 2) (burnsideB49x_gl_comm E) = b at hbc ⊢
    interval_cases c <;> omega
  calc Nat.card E ≤ 2 ^ ((3 - finrank (ZMod 2) (burnsideB49x_gl_fix E)) *
        finrank (ZMod 2) (burnsideB49x_gl_comm E)) := hcard
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hexp
    _ = 4 := by norm_num

theorem burnsideB49x_gl_map_fix {E : Subgroup (W ≃ₗ[ZMod 2] W)} {e : W ≃ₗ[ZMod 2] W}
    (he : e ∈ E) :
    (burnsideB49x_gl_fix E).map (e : W →ₗ[ZMod 2] W) = burnsideB49x_gl_fix E := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change e y ∈ burnsideB49x_gl_fix E
    rw [hy e he]
    exact hy
  · intro hx
    exact ⟨x, hx, hx e he⟩

@[expose] def burnsideB49x_gl_quotHom (E : Subgroup (W ≃ₗ[ZMod 2] W)) :
    E →* ((W ⧸ burnsideB49x_gl_fix E) ≃ₗ[ZMod 2] (W ⧸ burnsideB49x_gl_fix E)) where
  toFun e := Submodule.Quotient.equiv _ _ (e : W ≃ₗ[ZMod 2] W) (burnsideB49x_gl_map_fix e.2)
  map_one' := by
    ext q
    induction q using Submodule.Quotient.induction_on with
    | H x => rfl
  map_mul' e e' := by
    ext q
    induction q using Submodule.Quotient.induction_on with
    | H x => rfl

theorem burnsideB49x_gl_sub_mem_fix_of_mem_ker {E : Subgroup (W ≃ₗ[ZMod 2] W)} {k : E}
    (hk : k ∈ (burnsideB49x_gl_quotHom E).ker) (x : W) :
    (k : W ≃ₗ[ZMod 2] W) x - x ∈ burnsideB49x_gl_fix E := by
  have h := congrArg (fun φ : (W ⧸ burnsideB49x_gl_fix E) ≃ₗ[ZMod 2] (W ⧸ burnsideB49x_gl_fix E) =>
    φ (Submodule.Quotient.mk x)) (MonoidHom.mem_ker.1 hk)
  change Submodule.Quotient.mk ((k : W ≃ₗ[ZMod 2] W) x) = Submodule.Quotient.mk x at h
  exact (Submodule.Quotient.eq _).1 h

theorem burnsideB49x_gl_fix_sup_of_sub_mem_fix {E : Subgroup (W ≃ₗ[ZMod 2] W)}
    (hc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) {k : W ≃ₗ[ZMod 2] W} (hkE : k ∈ E)
    (hk : ∀ x, k x - x ∈ burnsideB49x_gl_fix E) :
    ∀ x ∈ burnsideB49x_gl_comm E ⊔ burnsideB49x_gl_fix E, k x = x := by
  have hle : burnsideB49x_gl_comm E ⊔ burnsideB49x_gl_fix E ≤
      LinearMap.fixedSubmodule (k : W →ₗ[ZMod 2] W) := by
    refine sup_le ?_ fun x hx => hx k hkE
    rw [burnsideB49x_gl_comm, Submodule.span_le]
    rintro _ ⟨e, he, w, rfl⟩
    change k (e w - w) = e w - w
    have hcE : e (k w - w) = k w - w := hk w e he
    rw [map_sub] at hcE
    rw [map_sub, burnsideB49x_gl_apply_comm (hc k hkE e he)]
    calc e (k w) - k w = (e (k w) - e w) + e w - k w := by abel
      _ = (k w - w) + e w - k w := by rw [hcE]
      _ = e w - w := by abel
  exact fun x hx => LinearMap.mem_fixedSubmodule_iff.1 (hle hx)

theorem burnsideB49x_gl_card_le_eight [FiniteDimensional (ZMod 2) W]
    (hW : finrank (ZMod 2) W = 4) {E : Subgroup (W ≃ₗ[ZMod 2] W)}
    (hc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) (h2 : ∀ e ∈ E, e * e = 1)
    (hC : finrank (ZMod 2) (burnsideB49x_gl_fix E) = 1)
    (hB : 3 ≤ finrank (ZMod 2) (burnsideB49x_gl_comm E)) : Nat.card E ≤ 8 := by
  have hQ : finrank (ZMod 2) (W ⧸ burnsideB49x_gl_fix E) = 3 := by
    have := Submodule.finrank_quotient_add_finrank (burnsideB49x_gl_fix E)
    omega
  have hcE : ∀ a b : E, a * b = b * a := fun a b => Subtype.ext (hc a a.2 b b.2)
  have h2E : ∀ a : E, a * a = 1 := fun a => Subtype.ext (h2 a a.2)
  have hrange : Nat.card (burnsideB49x_gl_quotHom E).range ≤ 4 := by
    refine burnsideB49x_gl_three hQ ?_ ?_
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul, hcE a b]
    · rintro _ ⟨a, rfl⟩
      rw [← map_mul, h2E a, map_one]
  have hker : Nat.card (burnsideB49x_gl_quotHom E).ker ≤ 2 := by
    have h := burnsideB49x_gl_card_le
      (fun k : (burnsideB49x_gl_quotHom E).ker => ((k : E) : W ≃ₗ[ZMod 2] W))
      (fun k k' h => Subtype.ext (Subtype.ext h))
      (burnsideB49x_gl_comm E ⊔ burnsideB49x_gl_fix E) (burnsideB49x_gl_fix E)
      (fun k => burnsideB49x_gl_fix_sup_of_sub_mem_fix hc (k : E).2
        (burnsideB49x_gl_sub_mem_fix_of_mem_ker k.2))
      (fun k => burnsideB49x_gl_sub_mem_fix_of_mem_ker k.2)
    have hd : 3 ≤ finrank (ZMod 2) ↥(burnsideB49x_gl_comm E ⊔ burnsideB49x_gl_fix E) :=
      hB.trans (Submodule.finrank_mono le_sup_left)
    rw [hW, hC] at h
    calc Nat.card (burnsideB49x_gl_quotHom E).ker
        ≤ 2 ^ ((4 - finrank (ZMod 2) ↥(burnsideB49x_gl_comm E ⊔ burnsideB49x_gl_fix E)) * 1) := h
      _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 := by norm_num
  rw [← Subgroup.card_ker_mul_card_range (burnsideB49x_gl_quotHom E)]
  calc Nat.card (burnsideB49x_gl_quotHom E).ker * Nat.card (burnsideB49x_gl_quotHom E).range
      ≤ 2 * 4 := Nat.mul_le_mul hker hrange
    _ = 8 := by norm_num

theorem burnsideB49x_gl_four_card_le [FiniteDimensional (ZMod 2) W]
    (hW : finrank (ZMod 2) W = 4) {E : Subgroup (W ≃ₗ[ZMod 2] W)}
    (hc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) (h2 : ∀ e ∈ E, e * e = 1) : Nat.card E ≤ 16 := by
  have hc1 := burnsideB49x_gl_one_le_finrank_fix (by omega) h2
  have hc4 := Submodule.finrank_le (burnsideB49x_gl_fix E)
  have hcard := burnsideB49x_gl_card_le_fix_comm E
  rw [hW] at hcard hc4
  by_cases hc2 : 2 ≤ finrank (ZMod 2) (burnsideB49x_gl_fix E)
  · have hbc := Submodule.finrank_mono (burnsideB49x_gl_quad_of_codim hc h2 (by omega))
    have hexp : (4 - finrank (ZMod 2) (burnsideB49x_gl_fix E)) *
        finrank (ZMod 2) (burnsideB49x_gl_comm E) ≤ 4 := by
      generalize finrank (ZMod 2) (burnsideB49x_gl_fix E) = c at hc2 hc4 hbc ⊢
      generalize finrank (ZMod 2) (burnsideB49x_gl_comm E) = b at hbc ⊢
      interval_cases c <;> omega
    calc Nat.card E ≤ 2 ^ ((4 - finrank (ZMod 2) (burnsideB49x_gl_fix E)) *
          finrank (ZMod 2) (burnsideB49x_gl_comm E)) := hcard
      _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hexp
      _ = 16 := by norm_num
  · have hc1' : finrank (ZMod 2) (burnsideB49x_gl_fix E) = 1 := by omega
    by_cases hb2 : finrank (ZMod 2) (burnsideB49x_gl_comm E) ≤ 2
    · have hbc := Submodule.finrank_mono (burnsideB49x_gl_quad_of_comm_le hc h2 hb2)
      rw [hc1'] at hcard hbc
      calc Nat.card E ≤ 2 ^ ((4 - 1) * finrank (ZMod 2) (burnsideB49x_gl_comm E)) := hcard
        _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ 16 := by norm_num
    · exact (burnsideB49x_gl_card_le_eight hW hc h2 hc1' (by omega)).trans (by norm_num)

theorem burnsideB49x_gl_four_fix [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W = 4)
    {E : Subgroup (W ≃ₗ[ZMod 2] W)} (hc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e)
    (h2 : ∀ e ∈ E, e * e = 1) (hE : 16 ≤ Nat.card E) :
    finrank (ZMod 2) (burnsideB49x_gl_fix E) = 2 ∧
      E = burnsideB49x_gl_Q (burnsideB49x_gl_fix E) := by
  have hc1 := burnsideB49x_gl_one_le_finrank_fix (by omega) h2
  have hc4 := Submodule.finrank_le (burnsideB49x_gl_fix E)
  have hcard := burnsideB49x_gl_card_le_fix_comm E
  rw [hW] at hcard hc4
  have hexp : 4 ≤ (4 - finrank (ZMod 2) (burnsideB49x_gl_fix E)) *
      finrank (ZMod 2) (burnsideB49x_gl_comm E) := by
    by_contra h
    have : Nat.card E ≤ 2 ^ 3 := hcard.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  have key : burnsideB49x_gl_comm E ≤ burnsideB49x_gl_fix E ∧
      finrank (ZMod 2) (burnsideB49x_gl_fix E) = 2 := by
    by_cases hc2 : 2 ≤ finrank (ZMod 2) (burnsideB49x_gl_fix E)
    · have hq := burnsideB49x_gl_quad_of_codim hc h2 (by omega)
      refine ⟨hq, ?_⟩
      have hbc := Submodule.finrank_mono hq
      generalize finrank (ZMod 2) (burnsideB49x_gl_fix E) = c at hc2 hc4 hbc hexp ⊢
      generalize finrank (ZMod 2) (burnsideB49x_gl_comm E) = b at hbc hexp ⊢
      interval_cases c <;> omega
    · exfalso
      have hc1' : finrank (ZMod 2) (burnsideB49x_gl_fix E) = 1 := by omega
      by_cases hb2 : finrank (ZMod 2) (burnsideB49x_gl_comm E) ≤ 2
      · have hbc := Submodule.finrank_mono (burnsideB49x_gl_quad_of_comm_le hc h2 hb2)
        rw [hc1'] at hexp hbc
        omega
      · have := burnsideB49x_gl_card_le_eight hW hc h2 hc1' (by omega)
        omega
  obtain ⟨hBC, hC2⟩ := key
  refine ⟨hC2, ?_⟩
  have hle : E ≤ burnsideB49x_gl_Q (burnsideB49x_gl_fix E) := fun e he =>
    ⟨fun x => hBC (burnsideB49x_gl_sub_mem_comm he x), fun y hy => hy e he⟩
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  haveI : Finite (W ≃ₗ[ZMod 2] W) :=
    Finite.of_injective (fun e : W ≃ₗ[ZMod 2] W => (e : W → W)) fun a b h =>
      LinearEquiv.ext (congrFun h)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [burnsideB49x_gl_card_Q hC2 hW]
  exact hE

theorem burnsideB49x_gl_four [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W = 4)
    {E : Subgroup (W ≃ₗ[ZMod 2] W)} (hc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e)
    (h2 : ∀ e ∈ E, e * e = 1) (hE : 16 ≤ Nat.card E) :
    ∃ X : Submodule (ZMod 2) W, finrank (ZMod 2) X = 2 ∧ E = burnsideB49x_gl_Q X :=
  ⟨_, burnsideB49x_gl_four_fix hW hc h2 hE⟩

theorem burnsideB49x_gl_transvection_mem_Q {X : Submodule (ZMod 2) W}
    {f : Module.Dual (ZMod 2) W} (hf : ∀ x ∈ X, f x = 0) {y : W} (hy : y ∈ X) :
    LinearEquiv.transvection (hf y hy) ∈ burnsideB49x_gl_Q X := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · rw [transvection_apply, add_sub_cancel_left]
    exact X.smul_mem _ hy
  · rw [transvection_apply, hf x hx, zero_smul, add_zero]

theorem burnsideB49x_gl_fix_Q {X : Submodule (ZMod 2) W} (hX0 : X ≠ ⊥) :
    burnsideB49x_gl_fix (burnsideB49x_gl_Q X) = X := by
  refine le_antisymm (fun w hw => ?_) fun y hy g hg => hg.2 y hy
  by_contra hwX
  obtain ⟨f, hf, hfw⟩ := exists_dual_eq_one_of_notMem hwX
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX0
  have h := hw _ (burnsideB49x_gl_transvection_mem_Q hf hy)
  rw [transvection_apply, hfw, one_smul] at h
  exact hy0 (add_left_cancel (h.trans (add_zero w).symm))

theorem burnsideB49x_gl_comm_Q {X : Submodule (ZMod 2) W} (hXT : X ≠ ⊤) :
    burnsideB49x_gl_comm (burnsideB49x_gl_Q X) = X := by
  refine le_antisymm ?_ fun y hy => ?_
  · rw [burnsideB49x_gl_comm, Submodule.span_le]
    rintro _ ⟨g, hg, x, rfl⟩
    exact hg.1 x
  · obtain ⟨w, -, hwX⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hXT)
    obtain ⟨f, hf, hfw⟩ := exists_dual_eq_one_of_notMem hwX
    have h := burnsideB49x_gl_sub_mem_comm (burnsideB49x_gl_transvection_mem_Q hf hy) w
    rwa [transvection_apply, hfw, one_smul, add_sub_cancel_left] at h

theorem burnsideB49x_gl_Q_stab_of_finrank_eq [FiniteDimensional (ZMod 2) W]
    {X Y : Submodule (ZMod 2) W} (hXY : finrank (ZMod 2) X = finrank (ZMod 2) Y)
    (h : ∀ q ∈ burnsideB49x_gl_Q X, ∀ y ∈ Y, q y ∈ Y) : X = Y := by
  by_cases hYX : Y ≤ X
  · exact (Submodule.eq_of_le_of_finrank_eq hYX hXY.symm).symm
  obtain ⟨y, hyY, hyX⟩ := SetLike.not_le_iff_exists.1 hYX
  obtain ⟨f, hf, hfy⟩ := exists_dual_eq_one_of_notMem hyX
  refine Submodule.eq_of_le_of_finrank_eq (fun x hx => ?_) hXY
  have h' := h _ (burnsideB49x_gl_transvection_mem_Q hf hx) y hyY
  rw [transvection_apply, hfy, one_smul] at h'
  have h'' := Y.sub_mem h' hyY
  rwa [add_sub_cancel_left] at h''

theorem burnsideB49x_gl_Q_stab [FiniteDimensional (ZMod 2) W] {X Y : Submodule (ZMod 2) W}
    (hX : finrank (ZMod 2) X = 2) (hY : finrank (ZMod 2) Y = 2)
    (h : ∀ q ∈ burnsideB49x_gl_Q X, ∀ y ∈ Y, q y ∈ Y) : X = Y :=
  burnsideB49x_gl_Q_stab_of_finrank_eq (hX.trans hY.symm) h

end CFSG.ASVolI
