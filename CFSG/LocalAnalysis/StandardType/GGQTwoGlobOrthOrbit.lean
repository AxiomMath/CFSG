module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobFour
public import CFSG.Fischer.Classification.Recognition.R3Count
public import Mathlib.GroupTheory.GroupAction.Quotient
public import CFSG.Sporadic.Schreier.J4SProfileNode

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType

variable {W : Type} [AddCommGroup W] [Module (ZMod 3) W]

theorem qTwoGlobOrb_normCount_le
    {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)}
    (hf : CFSG.Fischer.Classification.IsF3Form f) (c : ZMod 3) :
    CFSG.Fischer.Classification.Recognition.R3.normCount f c ≤ 90 := by
  have htriple := CFSG.Fischer.Classification.Recognition.R3.normTriple_eq 4 f hf
  have key : ∀ t : ℕ × ℕ × ℕ,
      (t = CFSG.Fischer.Classification.Recognition.R3.T^[4] (1, 2, 0) ∨
        t = CFSG.Fischer.Classification.Recognition.R3.T^[4] (1, 0, 2)) →
      t.1 ≤ 90 ∧ t.2.1 ≤ 90 ∧ t.2.2 ≤ 90 := by
    rintro t (rfl | rfl) <;> decide
  obtain ⟨h0, h1, h2⟩ := key _ htriple
  fin_cases c
  · exact h0
  · exact h1
  · exact h2

theorem qTwoGlobOrb_class_card_le [Finite W]
    (Q : QuadraticForm (ZMod 3) W) (hQ : (qTwoPolar Q).Nondegenerate)
    (hdim : Module.finrank (ZMod 3) W = 5) (c : ZMod 3) :
    Nat.card {v : W // Q v = c} ≤ 90 := by
  classical
  have : FiniteDimensional (ZMod 3) W := Module.Finite.of_finite
  let e : W ≃ₗ[ZMod 3] (Fin 5 → ZMod 3) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hdim, Module.finrank_fin_fun])
  let f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3) :=
    (qTwoPolar Q).comp (e.symm : (Fin 5 → ZMod 3) →ₗ[ZMod 3] W)
      (e.symm : (Fin 5 → ZMod 3) →ₗ[ZMod 3] W)
  have hQ2 : ∀ v : W, Q v = 2 * f (e v) (e v) := by
    intro v
    have hp : f (e v) (e v) = qTwoPolar Q v v := by
      simp [f, LinearMap.BilinForm.comp_apply]
    have hq : qTwoPolar Q v v = 2 * Q v := by
      change QuadraticMap.polar Q v v = 2 * Q v
      rw [QuadraticMap.polar_self]
      simp
    rw [hp, hq, ← mul_assoc, show (2 : ZMod 3) * 2 = 1 by decide, one_mul]
  have hf : CFSG.Fischer.Classification.IsF3Form f := by
    constructor
    · intro x y
      simp only [f, LinearMap.BilinForm.comp_apply]
      exact QuadraticMap.polar_comm Q (e.symm x) (e.symm y)
    · intro x hx
      apply e.symm.injective
      rw [map_zero]
      apply hQ.1 (e.symm x)
      intro y
      have h := hx (e y)
      change qTwoPolar Q (e.symm x) (e.symm (e y)) = 0 at h
      rw [e.symm_apply_apply] at h
      exact h
  have hcount := qTwoGlobOrb_normCount_le hf (2 * c)
  let g : {v : W // Q v = c} → {x : Fin 5 → ZMod 3 // f x x = 2 * c} := fun v =>
    ⟨e v.1, by
      have hv := v.2
      rw [hQ2 v.1] at hv
      have h2 : (2 : ZMod 3) * f (e v.1) (e v.1) = (2 : ZMod 3) * (2 * c) := by
        rw [hv, ← mul_assoc, show (2 : ZMod 3) * 2 = 1 by decide, one_mul]
      exact mul_left_cancel₀ (by decide : (2 : ZMod 3) ≠ 0) h2⟩
  have hinj : Function.Injective g := by
    intro v1 v2 h
    exact Subtype.ext (e.injective (congrArg (fun z : {x : Fin 5 → ZMod 3 // f x x = 2 * c} =>
      (z : Fin 5 → ZMod 3)) h))
  exact (Nat.card_le_card_of_injective g hinj).trans hcount

theorem qTwoGlobOrb_orbit_card_le [Finite W]
    (Q : QuadraticForm (ZMod 3) W) (hQ : (qTwoPolar Q).Nondegenerate)
    (hdim : Module.finrank (ZMod 3) W = 5)
    {A : Subgroup (W ≃ₗ[ZMod 3] W)}
    (hA : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    {u : W} (hu : u ≠ 0) :
    Nat.card (MulAction.orbit A u) ≤ 90 := by
  classical
  let g : MulAction.orbit A u → {v : W // v ≠ 0 ∧ Q v = Q u} := fun y =>
    ⟨y.1, by
      obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp y.2
      refine ⟨?_, ?_⟩
      · rw [← ha]
        intro h0
        have h1 : (a : W ≃ₗ[ZMod 3] W) u = 0 := by
          simpa [Subgroup.smul_def, LinearEquiv.smul_def] using h0
        exact hu ((a : W ≃ₗ[ZMod 3] W).injective (by simpa using h1))
      · rw [← ha]
        have hmem : (a : W ≃ₗ[ZMod 3] W) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
          hA a.2
        simpa [Subgroup.smul_def, LinearEquiv.smul_def] using
          TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hmem u⟩
  have hinj : Function.Injective g := by
    intro y1 y2 h
    apply Subtype.ext
    have h' : (g y1).1 = (g y2).1 := congrArg Subtype.val h
    simpa using h'
  have hsub : Nat.card {v : W // v ≠ 0 ∧ Q v = Q u} ≤
      Nat.card {v : W // Q v = Q u} :=
    Nat.card_le_card_of_injective
      (fun v : {v : W // v ≠ 0 ∧ Q v = Q u} => ⟨v.1, v.2.2⟩) (by
        intro v1 v2 h
        apply Subtype.ext
        simpa using congrArg Subtype.val h)
  exact (Nat.card_le_card_of_injective g hinj).trans
    (hsub.trans (qTwoGlobOrb_class_card_le Q hQ hdim (Q u)))

theorem qTwoGlobOrb_stabilizer_card {A : Subgroup (W ≃ₗ[ZMod 3] W)} (u : W) :
    Nat.card {g : A // (g : W ≃ₗ[ZMod 3] W) u = u} =
      Nat.card (MulAction.stabilizer A u) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [MulAction.mem_stabilizer_iff]
  simp [Subgroup.smul_def, LinearEquiv.smul_def]

theorem qTwoGlobOrb_false_of_card_le [Finite W]
    (Q : QuadraticForm (ZMod 3) W) (hQ : (qTwoPolar Q).Nondegenerate)
    (hdim : Module.finrank (ZMod 3) W = 5)
    {A : Subgroup (W ≃ₗ[ZMod 3] W)}
    (hA : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ 2 * Nat.card A)
    (hfull : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 103680)
    {u : W} (hu : u ≠ 0)
    (hstab : Nat.card {g : A // (g : W ≃ₗ[ZMod 3] W) u = u} ≤ 240) :
    False := by
  classical
  have : Finite (W ≃ₗ[ZMod 3] W) :=
    Finite.of_injective (fun e : W ≃ₗ[ZMod 3] W => (e : W → W))
      (fun e₁ e₂ h => LinearEquiv.ext (congrFun h))
  have : Fintype A := Fintype.ofFinite A
  have : Fintype (MulAction.orbit A u) := Fintype.ofFinite _
  have : Fintype (MulAction.stabilizer A u) := Fintype.ofFinite _
  have horb : Nat.card (MulAction.orbit A u) ≤ 90 :=
    qTwoGlobOrb_orbit_card_le Q hQ hdim hA hu
  have hstab' : Nat.card (MulAction.stabilizer A u) ≤ 240 := by
    rw [← qTwoGlobOrb_stabilizer_card (A := A) u]
    exact hstab
  have hOS : Nat.card (MulAction.orbit A u) * Nat.card (MulAction.stabilizer A u) =
      Nat.card A := by
    rw [Nat.card_eq_fintype_card (α := MulAction.orbit A u),
      Nat.card_eq_fintype_card (α := MulAction.stabilizer A u),
      Nat.card_eq_fintype_card (α := A)]
    exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group A u
  have hAle : Nat.card A ≤ 90 * 240 := by
    rw [← hOS]
    exact Nat.mul_le_mul horb hstab'
  have hOle : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ 2 * (90 * 240) :=
    hO.trans (Nat.mul_le_mul_left 2 hAle)
  rw [hfull] at hOle
  norm_num at hOle

theorem qTwoGlobOrb_false [Finite W]
    (Q : QuadraticForm (ZMod 3) W) (hQ : (qTwoPolar Q).Nondegenerate)
    (hdim : Module.finrank (ZMod 3) W = 5)
    {A : Subgroup (W ≃ₗ[ZMod 3] W)}
    (hA : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ 2 * Nat.card A)
    {u : W} (hu : u ≠ 0)
    (hstab : Nat.card {g : A // (g : W ≃ₗ[ZMod 3] W) u = u} ≤ 240) :
    False := by
  have : Module.Finite (ZMod 3) W := Module.Finite.of_finite
  exact qTwoGlobOrb_false_of_card_le Q hQ hdim hA hO
    (qTwoGlobFour_orth_five_card Q hQ hdim) hu hstab

end CFSG.StandardType.QTwo

attribute [instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

end
