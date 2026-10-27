module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderField

public section

namespace CFSG.Quasithin.SmithD37

open Module CFSG.QuasithinUnique.Setup.Offender

namespace SubForm

section Lin

variable {F : Type*} [Field F] {P : Type*} [AddCommGroup P] [Module F P]

theorem eq_top_of_forall_end_mem {U : Submodule F P} (hU : U ≠ ⊥)
    (h : ∀ f : Module.End F P, ∀ u ∈ U, f u ∈ U) : U = ⊤ := by
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one F hu0
  refine eq_top_iff.2 fun v _ => ?_
  simpa [hℓ] using h (ℓ.smulRight v) u huU

theorem exists_eq_smul_of_forall_commute {T : Module.End F P}
    (h : ∀ f : Module.End F P, f * T = T * f) : ∃ c : F, ∀ x, T x = c • x := by
  obtain ⟨α, hα, hT⟩ := Module.End.mem_center_iff.1 (Semigroup.mem_center_iff.2 h)
  exact ⟨α, fun x => by rw [hT]; rfl⟩

variable {G : Type*} [Group G] {ρ : G →* (P ≃ₗ[F] P)}

theorem forall_end_mem_of_span_eq_top
    (hspan : Submodule.span F (Set.range fun g => ((ρ g : P ≃ₗ[F] P) : Module.End F P)) = ⊤)
    {U : Submodule F P} (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) (f : Module.End F P) :
    ∀ u ∈ U, f u ∈ U := by
  have hf : f ∈ Submodule.span F (Set.range fun g => ((ρ g : P ≃ₗ[F] P) : Module.End F P)) := by
    rw [hspan]; exact Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact hU g
  | zero => intro u _; simp
  | add x y _ _ hx hy => intro u hu; exact U.add_mem (hx u hu) (hy u hu)
  | smul c x _ hx => intro u hu; exact U.smul_mem c (hx u hu)

theorem exists_eq_smul_of_span_eq_top
    (hspan : Submodule.span F (Set.range fun g => ((ρ g : P ≃ₗ[F] P) : Module.End F P)) = ⊤)
    {T : Module.End F P} (hT : ∀ g x, T (ρ g x) = ρ g (T x)) : ∃ c : F, ∀ x, T x = c • x := by
  refine exists_eq_smul_of_forall_commute fun f => ?_
  have hf : f ∈ Submodule.span F (Set.range fun g => ((ρ g : P ≃ₗ[F] P) : Module.End F P)) := by
    rw [hspan]; exact Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact LinearMap.ext fun x => (hT g x).symm
  | zero => rw [zero_mul, mul_zero]
  | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
  | smul c x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem span_eq_top_of_invariant
    (hspan : Submodule.span F (Set.range fun g => ((ρ g : P ≃ₗ[F] P) : Module.End F P)) = ⊤)
    {S : Set P} {y : P} (hy : y ∈ S) (hy0 : y ≠ 0) (hS : ∀ g, ∀ x ∈ S, ρ g x ∈ S) :
    Submodule.span F S = ⊤ := by
  refine eq_top_of_forall_end_mem ?_ (forall_end_mem_of_span_eq_top hspan fun g u hu => ?_)
  · exact fun h => hy0 (by simpa [h] using Submodule.subset_span (R := F) hy)
  · have hle : Submodule.span F S ≤ (Submodule.span F S).comap (ρ g : P →ₗ[F] P) :=
      Submodule.span_le.2 fun x hx => Submodule.subset_span (hS g x hx)
    exact hle hu

end Lin

section Res

variable {F : Type*} [Field F] {P : Type*} [AddCommGroup P] [Module F P]
  {G : Type*} [Group G] (ρ : G →* (P ≃ₗ[F] P)) {p : ℕ} [Module (ZMod p) P]

@[expose] def resRep (Y : Submodule (ZMod p) P) (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) :
    G →* (Y ≃ₗ[ZMod p] Y) where
  toFun g :=
    { toFun := fun y => ⟨ρ g (y : P), hY g y y.2⟩
      invFun := fun y => ⟨ρ g⁻¹ (y : P), hY g⁻¹ y y.2⟩
      map_add' := fun x y => Subtype.ext (map_add (ρ g) (x : P) (y : P))
      map_smul' := fun a y => Subtype.ext (ZMod.map_smul (ρ g) a (y : P))
      left_inv := fun y => Subtype.ext (by
        show ρ g⁻¹ (ρ g (y : P)) = y
        rw [map_inv]; exact gl_inv_apply_apply _ _)
      right_inv := fun y => Subtype.ext (by
        show ρ g (ρ g⁻¹ (y : P)) = y
        rw [map_inv]; exact gl_apply_inv_apply _ _) }
  map_one' := by
    ext y
    show ρ 1 (y : P) = y
    rw [map_one]; rfl
  map_mul' g h := by
    ext y
    show ρ (g * h) (y : P) = ρ g (ρ h (y : P))
    rw [map_mul]; rfl

variable [Fact p.Prime]

theorem isIrrAct_range_resRep (Y : Submodule (ZMod p) P) (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y)
    (hmin : ∀ Y' : Submodule (ZMod p) P, Y' ≤ Y → (∀ g, ∀ y ∈ Y', ρ g y ∈ Y') →
      Y' = ⊥ ∨ Y' = Y) :
    IsIrrAct (resRep ρ Y hY).range := by
  intro U hU
  have hinv : ∀ g, ∀ y ∈ U.map Y.subtype, ρ g y ∈ U.map Y.subtype := by
    intro g y hy
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hy
    exact Submodule.mem_map.2 ⟨resRep ρ Y hY g u, hU _ ⟨g, rfl⟩ u hu, rfl⟩
  have hinj := Submodule.map_injective_of_injective Y.injective_subtype
  rcases hmin _ (Submodule.map_subtype_le Y U) hinv with h | h
  · exact Or.inl (hinj (h.trans (Submodule.map_bot _).symm))
  · exact Or.inr (hinj (h.trans (Submodule.map_subtype_top Y).symm))

theorem exists_lift_of_mem_span (Y : Submodule (ZMod p) P) (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y)
    {f : Module.End (ZMod p) Y}
    (hf : f ∈ Submodule.span (ZMod p) (Set.range (toEnd (resRep ρ Y hY).range))) :
    ∃ T : Module.End F P, ∀ y : Y, T y = f y := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨h, g, rfl⟩, rfl⟩ := hx
    exact ⟨ρ g, fun y => rfl⟩
  | zero => exact ⟨0, fun y => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨T₁, h₁⟩ := hx
    obtain ⟨T₂, h₂⟩ := hy
    exact ⟨T₁ + T₂, fun w => by simp [h₁, h₂]⟩
  | smul a x _ hx =>
    obtain ⟨T, hT⟩ := hx
    refine ⟨(a.val : F) • T, fun w => ?_⟩
    rw [LinearMap.smul_apply, hT, LinearMap.smul_apply, Submodule.coe_smul,
      Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]

end Res

section Form

variable {F : Type*} [Field F] {P : Type*} [AddCommGroup P] [Module F P]
  {G : Type*} [Group G] {ρ : G →* (P ≃ₗ[F] P)} {p : ℕ} [Fact p.Prime] [Module (ZMod p) P]

theorem exists_subfield_form_zmod [Finite P]
    (hspan : Submodule.span F (Set.range fun g => ((ρ g : P ≃ₗ[F] P) : Module.End F P)) = ⊤)
    (Y : Submodule (ZMod p) P) (hY0 : Y ≠ ⊥) (hYinv : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y)
    (hYmin : ∀ Y' : Submodule (ZMod p) P, Y' ≤ Y → (∀ g, ∀ y ∈ Y', ρ g y ∈ Y') →
      Y' = ⊥ ∨ Y' = Y) :
    ∃ (D : Subfield F) (k : ℕ) (b : Fin k → P),
      (∀ j, b j ∈ Y) ∧ LinearIndependent F b ∧ Submodule.span F (Set.range b) = ⊤ ∧
      (∀ c ∈ D, ∀ y ∈ Y, c • y ∈ Y) ∧
      (∀ y ∈ Y, ∃ a : Fin k → F, (∀ j, a j ∈ D) ∧ y = ∑ j, a j • b j) ∧
      (∀ φ : P →+ P, (∀ y ∈ Y, φ y ∈ Y) → (∀ g, ∀ y ∈ Y, φ (ρ g y) = ρ g (φ y)) →
        ∃ c ∈ D, ∀ y ∈ Y, φ y = c • y) := by
  have : Nontrivial Y := Submodule.nontrivial_iff_ne_bot.2 hY0
  obtain ⟨D, _, _, _, _, _, hcomm, _, hspanD, -⟩ :=
    finite_irreducible_endomorphism_field_core (resRep ρ Y hYinv).range
      (isIrrAct_range_resRep ρ Y hYinv hYmin)
  have hlift : ∀ f : Y →ₗ[D] Y, ∃ T : Module.End F P, ∀ y : Y, T y = f y := fun f =>
    exists_lift_of_mem_span ρ Y hYinv
      ((hspanD (f.restrictScalars (ZMod p))).2 fun c w => f.map_smul c w)
  have hDlin : ∀ g (c : D) (y : Y), resRep ρ Y hYinv g (c • y) = c • resRep ρ Y hYinv g y :=
    fun g c y => (hspanD (toEnd _ ⟨resRep ρ Y hYinv g, MonoidHom.mem_range.2 ⟨g, rfl⟩⟩)).1
      (Submodule.subset_span ⟨_, rfl⟩) c y
  obtain ⟨y₀, hy₀Y, hy₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY0
  have hFY : Submodule.span F (Y : Set P) = ⊤ :=
    span_eq_top_of_invariant hspan hy₀Y hy₀ hYinv
  have hscal : ∀ δ : D, ∃ c : F, ∀ y : Y, ((δ • y : Y) : P) = c • (y : P) := by
    intro δ
    obtain ⟨T, hT⟩ := hlift (δ • LinearMap.id)
    have hTρ : ∀ g x, T (ρ g x) = ρ g (T x) := by
      intro g
      have : T ∘ₗ (ρ g : P →ₗ[F] P) = (ρ g : P →ₗ[F] P) ∘ₗ T := by
        refine LinearMap.ext_on hFY fun y hy => ?_
        show T (ρ g y) = ρ g (T y)
        have h1 : T (ρ g y) = ((δ • resRep ρ Y hYinv g ⟨y, hy⟩ : Y) : P) :=
          hT (resRep ρ Y hYinv g ⟨y, hy⟩)
        have h2 : T y = ((δ • (⟨y, hy⟩ : Y) : Y) : P) := hT ⟨y, hy⟩
        rw [h1, h2, ← hDlin]; rfl
      exact fun x => LinearMap.congr_fun this x
    obtain ⟨c, hc⟩ := exists_eq_smul_of_span_eq_top hspan hTρ
    exact ⟨c, fun y => by rw [← hc, hT]; rfl⟩
  choose ιf hι using hscal
  have huniq : ∀ c c' : F, (∀ y : Y, c • (y : P) = c' • (y : P)) → c = c' :=
    fun c c' h => smul_left_injective F hy₀ (h ⟨y₀, hy₀Y⟩)
  let ι : D →+* F :=
    { toFun := ιf
      map_one' := huniq _ _ fun y => by rw [← hι, one_smul, one_smul]
      map_mul' := fun a b => huniq _ _ fun y => by
        rw [← hι, mul_smul a b y, hι, hι, mul_smul]
      map_zero' := huniq _ _ fun y => by rw [← hι, zero_smul, zero_smul, Submodule.coe_zero]
      map_add' := fun a b => huniq _ _ fun y => by
        rw [← hι, add_smul a b y, Submodule.coe_add, hι, hι, add_smul] }
  have hιapp : ∀ (δ : D) (y : Y), ((δ • y : Y) : P) = ι δ • (y : P) := hι
  let B := Module.finBasis D Y
  have hcoef : ∀ w : Y, (w : P) = ∑ j, ι (B.repr w j) • (B j : P) := by
    intro w
    conv_lhs => rw [← B.sum_repr w]
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun j _ => hιapp _ _
  refine ⟨ι.fieldRange, finrank D Y, fun j => (B j : P), fun j => (B j).2, ?_, ?_, ?_, ?_, ?_⟩
  · refine Fintype.linearIndependent_iff.2 fun c hc j₀ => ?_
    obtain ⟨T, hT⟩ := hlift ((B.coord j₀).smulRight (B j₀))
    have hTj : ∀ j, T (B j : P) = if j = j₀ then (B j₀ : P) else 0 := by
      intro j
      rw [hT]
      by_cases hj : j = j₀
      · subst hj; simp
      · simp [hj]
    have h0 := congrArg T hc
    simp only [map_sum, map_smul, hTj, map_zero, smul_ite, smul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h0
    refine (smul_eq_zero.1 h0).resolve_right fun h => B.ne_zero j₀ ?_
    exact Subtype.ext h
  · rw [eq_top_iff, ← hFY, Submodule.span_le]
    intro y hy
    have h : y = ∑ j, ι (B.repr ⟨y, hy⟩ j) • (B j : P) := hcoef ⟨y, hy⟩
    rw [h]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · intro c hc y hy
    obtain ⟨δ, rfl⟩ := RingHom.mem_fieldRange.1 hc
    have h : ι δ • y = ((δ • (⟨y, hy⟩ : Y) : Y) : P) := (hιapp δ ⟨y, hy⟩).symm
    rw [h]
    exact (δ • (⟨y, hy⟩ : Y)).2
  · intro y hy
    exact ⟨fun j => ι (B.repr ⟨y, hy⟩ j), fun j => RingHom.mem_fieldRange.2 ⟨_, rfl⟩,
      hcoef ⟨y, hy⟩⟩
  · intro φ hφY hφρ
    let f : Module.End (ZMod p) Y := LinearMap.restrict (φ.toZModLinearMap p) hφY
    obtain ⟨δ, hδ⟩ := (hcomm f).1 (by
      rintro _ ⟨g, rfl⟩ w
      exact Subtype.ext (hφρ g w w.2))
    refine ⟨ι δ, RingHom.mem_fieldRange.2 ⟨δ, rfl⟩, fun y hy => ?_⟩
    have h1 : φ y = (f ⟨y, hy⟩ : P) := rfl
    rw [h1, hδ, hιapp]

end Form

end SubForm

theorem exists_subfield_form {F : Type} [Field F] [Fintype F] {P : Type} [AddCommGroup P]
    [Module F P] [Module.Finite F P] [Nontrivial P] {G : Type*} [Group G]
    (ρ : G →* (P ≃ₗ[F] P))
    (hspan : Submodule.span F (Set.range fun g => ((ρ g : P ≃ₗ[F] P) : Module.End F P)) = ⊤)
    (Y : AddSubgroup P) (hY0 : Y ≠ ⊥) (hYinv : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y)
    (hYmin : ∀ Y' : AddSubgroup P, Y' ≤ Y → (∀ g, ∀ y ∈ Y', ρ g y ∈ Y') → Y' = ⊥ ∨ Y' = Y) :
    ∃ (D : Subfield F) (k : ℕ) (b : Fin k → P),
      (∀ j, b j ∈ Y) ∧ LinearIndependent F b ∧ Submodule.span F (Set.range b) = ⊤ ∧
      (∀ c ∈ D, ∀ y ∈ Y, c • y ∈ Y) ∧
      (∀ y ∈ Y, ∃ a : Fin k → F, (∀ j, a j ∈ D) ∧ y = ∑ j, a j • b j) ∧
      (∀ φ : P →+ P, (∀ y ∈ Y, φ y ∈ Y) → (∀ g, ∀ y ∈ Y, φ (ρ g y) = ρ g (φ y)) →
        ∃ c ∈ D, ∀ y ∈ Y, φ y = c • y) := by
  obtain ⟨p, _⟩ := CharP.exists F
  have : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  let : Module (ZMod p) P := Module.compHom P (ZMod.castHom (dvd_refl p) F)
  have : Finite P := Module.finite_of_finite F
  have hY0' : AddSubgroup.toZModSubmodule p Y ≠ ⊥ := fun h => hY0 (by
    rw [← AddSubgroup.toZModSubmodule_toAddSubgroup p Y, h, Submodule.bot_toAddSubgroup])
  exact SubForm.exists_subfield_form_zmod hspan (AddSubgroup.toZModSubmodule p Y) hY0' hYinv
    fun Y' hle hinv => (hYmin Y'.toAddSubgroup (fun x hx => hle hx) hinv).imp
      (fun h => Submodule.toAddSubgroup_injective (h.trans Submodule.bot_toAddSubgroup.symm))
      (fun h => Submodule.toAddSubgroup_injective h)

end CFSG.Quasithin.SmithD37
