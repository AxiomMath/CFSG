module

public import CFSG.Sporadic.Schreier.RuElemAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

private abbrev s16t_gl_hypP (p : GL (Fin 2) (ZMod 3) × GL (Fin 2) (ZMod 3)) : Prop :=
  p.1 * p.1 = 1 ∧ p.2 * p.2 = 1 ∧ p.1 * p.2 = p.2 * p.1 ∧ p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ p.1 ≠ p.2
private abbrev s16t_gl_conclP (p : GL (Fin 2) (ZMod 3) × GL (Fin 2) (ZMod 3)) : Prop :=
  p.1 = -1 ∨ p.2 = -1 ∨ p.1 * p.2 = -1
private abbrev s16t_gl_pairP (p : GL (Fin 2) (ZMod 3) × GL (Fin 2) (ZMod 3)) : Prop :=
  s16t_gl_hypP p → s16t_gl_conclP p
private instance : DecidablePred s16t_gl_hypP := fun p => by unfold s16t_gl_hypP; infer_instance
private instance : DecidablePred s16t_gl_conclP := fun p => by unfold s16t_gl_conclP; infer_instance
private instance : DecidablePred s16t_gl_pairP := fun p => by unfold s16t_gl_pairP; infer_instance
private theorem s16t_gl_pair : ∀ p : GL (Fin 2) (ZMod 3) × GL (Fin 2) (ZMod 3),
    s16t_gl_pairP p := by
  decide +kernel
private abbrev s16t_gl_invP (g : GL (Fin 2) (ZMod 3)) : Prop := g * g = 1 ∧ g ≠ 1
private abbrev s16t_gl_cenP (g : GL (Fin 2) (ZMod 3)) : Prop :=
  ∀ x : GL (Fin 2) (ZMod 3), x * g = g * x
private instance : DecidablePred s16t_gl_invP := fun g => by unfold s16t_gl_invP; infer_instance
private instance : DecidablePred s16t_gl_cenP := fun g => by unfold s16t_gl_cenP; infer_instance
private theorem s16t_gl_central_eq_neg_one : ∀ g : GL (Fin 2) (ZMod 3),
    s16t_gl_invP g → s16t_gl_cenP g → g = -1 := by
  decide +kernel
private theorem s16t_gl_neg_one_ne_one : ((-(1 : ZMod 3)) : ZMod 3) ≠ 1 := by decide

theorem s16t_exists_inv_of_aut_E9 {E : Type} [Group E] [Finite E]
    (hc : ∀ a b : E, a * b = b * a) (h2 : ∀ a : E, a ^ 2 = 1)
    (φ : E →* MulAut (Multiplicative (Fin 2 → ZMod 3))) (hφ : Function.Injective φ)
    (h3 : 2 < Nat.card E) : ∃ z : E, ∀ a, φ z a = a⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let e : MulAut (Multiplicative (Fin 2 → ZMod 3)) ≃* GL (Fin 2) (ZMod 3) :=
    CFSG.Sporadic.RuSchreier.ruMulAutEquivGL (p := 3) 2
  let ι : MulAut (Multiplicative (Fin 2 → ZMod 3)) :=
    MulEquiv.inv (Multiplicative (Fin 2 → ZMod 3))
  have hι2 : ι * ι = 1 := by ext a; simp [ι, MulAut.mul_apply]
  have hιcen : ∀ α : MulAut (Multiplicative (Fin 2 → ZMod 3)), α * ι = ι * α := by
    intro α; ext a; simp [ι, MulAut.mul_apply]
  have hι1 : ι ≠ 1 := by
    intro h
    have h' := congrArg (fun f : MulAut (Multiplicative (Fin 2 → ZMod 3)) =>
      f (Multiplicative.ofAdd (Pi.single (0 : Fin 2) (1 : ZMod 3) : Fin 2 → ZMod 3))) h
    have happ : (Multiplicative.ofAdd (Pi.single (0 : Fin 2) (1 : ZMod 3) : Fin 2 → ZMod 3))⁻¹
        = Multiplicative.ofAdd (Pi.single (0 : Fin 2) (1 : ZMod 3) : Fin 2 → ZMod 3) := by
      simpa [ι] using h'
    have h0 := congrFun (congrArg Multiplicative.toAdd happ) (0 : Fin 2)
    simp only [toAdd_inv, toAdd_ofAdd, Pi.neg_apply, Pi.single_eq_same] at h0
    exact s16t_gl_neg_one_ne_one h0
  have heι_inv : s16t_gl_invP (e ι) :=
    ⟨by rw [← map_mul, hι2, map_one], fun h => hι1 (e.injective (by rw [h, map_one]))⟩
  have heι_cen : s16t_gl_cenP (e ι) := fun x => by
    obtain ⟨α, rfl⟩ := e.surjective x
    rw [← map_mul, ← map_mul, hιcen α]
  have heι : e ι = -1 := s16t_gl_central_eq_neg_one (e ι) heι_inv heι_cen
  haveI : Fintype E := Fintype.ofFinite E
  rw [Nat.card_eq_fintype_card] at h3
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h3
  set x : E := a⁻¹ * b with hxdef
  set y : E := a⁻¹ * c with hydef
  have hx1 : x ≠ 1 := fun h =>
    hab.symm (by simpa [hxdef] using congrArg (fun t : E => a * t) h)
  have hy1 : y ≠ 1 := fun h =>
    hac.symm (by simpa [hydef] using congrArg (fun t : E => a * t) h)
  have hxy : x ≠ y := fun h =>
    hbc (by simpa [hxdef, hydef] using congrArg (fun t : E => a * t) h)
  have hφx1 : φ x ≠ 1 := fun h => hx1 (hφ (by rw [h, map_one]))
  have hφy1 : φ y ≠ 1 := fun h => hy1 (hφ (by rw [h, map_one]))
  have hφxy : φ x ≠ φ y := fun h => hxy (hφ h)
  have hφx2 : φ x * φ x = 1 := by rw [← map_mul (f := φ), ← pow_two, h2 x, map_one]
  have hφy2 : φ y * φ y = 1 := by rw [← map_mul (f := φ), ← pow_two, h2 y, map_one]
  have hφcomm : φ x * φ y = φ y * φ x := by
    rw [← map_mul (f := φ), ← map_mul (f := φ), hc x y]
  have hX2 : e (φ x) * e (φ x) = 1 := by rw [← map_mul (f := e), hφx2, map_one]
  have hY2 : e (φ y) * e (φ y) = 1 := by rw [← map_mul (f := e), hφy2, map_one]
  have hcomm : e (φ x) * e (φ y) = e (φ y) * e (φ x) := by
    rw [← map_mul (f := e), ← map_mul (f := e), hφcomm]
  have hX1 : e (φ x) ≠ 1 := fun h => hφx1 (e.injective (by rw [h, map_one]))
  have hY1 : e (φ y) ≠ 1 := fun h => hφy1 (e.injective (by rw [h, map_one]))
  have hXY : e (φ x) ≠ e (φ y) := fun h => hφxy (e.injective h)
  have hpair : e (φ x) = -1 ∨ e (φ y) = -1 ∨ e (φ x) * e (φ y) = -1 :=
    s16t_gl_pair (e (φ x), e (φ y)) ⟨hX2, hY2, hcomm, hX1, hY1, hXY⟩
  obtain hX | hY | hXY' := hpair
  · refine ⟨x, fun a => ?_⟩
    have hz : φ x = ι := e.injective (by rw [heι]; exact hX)
    rw [hz]; rfl
  · refine ⟨y, fun a => ?_⟩
    have hz : φ y = ι := e.injective (by rw [heι]; exact hY)
    rw [hz]; rfl
  · refine ⟨x * y, fun a => ?_⟩
    have hz : φ (x * y) = ι := e.injective (by rw [heι, map_mul, map_mul]; exact hXY')
    rw [hz]; rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
