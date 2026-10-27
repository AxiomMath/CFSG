module

public import CFSG.Quasithin.Background.Harris.L2.Setup
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.SchurEnd

public section

namespace CFSG.Quasithin.G11.Harris.L2

open CFSG.Open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

section Form

variable (F : Type) [Field F] [Algebra (ZMod 2) F]

@[expose] noncomputable def traceDetForm : LinearMap.BilinForm (ZMod 2) (Fin 2 → F) :=
  LinearMap.mk₂ (ZMod 2) (fun x y => Algebra.trace (ZMod 2) F (x 0 * y 1 - x 1 * y 0))
    (fun x x' y => by
      rw [← map_add]; congr 1; simp only [Pi.add_apply]; ring)
    (fun c x y => by
      rw [← map_smul]; congr 1
      simp only [Pi.smul_apply, smul_mul_assoc, smul_sub])
    (fun x y y' => by
      rw [← map_add]; congr 1; simp only [Pi.add_apply]; ring)
    (fun c x y => by
      rw [← map_smul]; congr 1
      simp only [Pi.smul_apply, mul_smul_comm, smul_sub])

theorem traceDetForm_apply (x y : Fin 2 → F) :
    traceDetForm F x y = Algebra.trace (ZMod 2) F (x 0 * y 1 - x 1 * y 0) := rfl

variable [Finite F]

theorem traceDetForm_separatingLeft : ∀ x : Fin 2 → F, (∀ y, traceDetForm F x y = 0) → x = 0 := by
  intro x hx
  have key : ∀ a : F, Algebra.trace (ZMod 2) F (x 0 * a) = 0 ∧
      Algebra.trace (ZMod 2) F (x 1 * a) = 0 := by
    intro a
    have h1 := hx (Pi.single 1 a)
    have h2 := hx (Pi.single 0 a)
    simp [traceDetForm_apply] at h1 h2
    rw [map_neg] at h2
    refine ⟨h1, ?_⟩
    generalize Algebra.trace (ZMod 2) F (x 1 * a) = t at h2 ⊢
    revert t; decide
  have hnd := (traceForm_nondegenerate (ZMod 2) F).1
  funext i
  fin_cases i
  · exact hnd _ fun b => by simpa [Algebra.traceForm_apply] using (key b).1
  · exact hnd _ fun b => by simpa [Algebra.traceForm_apply] using (key b).2

omit [Finite F] in
theorem traceDetForm_swap (x y : Fin 2 → F) : traceDetForm F y x = - traceDetForm F x y := by
  rw [traceDetForm_apply, traceDetForm_apply, ← map_neg]
  congr 1; ring

theorem traceDetForm_nondegenerate : (traceDetForm F).Nondegenerate := by
  refine ⟨traceDetForm_separatingLeft F, fun y hy => traceDetForm_separatingLeft F y fun x => ?_⟩
  rw [traceDetForm_swap, hy x]; decide

omit [Finite F] in
theorem traceDetForm_mulVec (g : Matrix.SpecialLinearGroup (Fin 2) F) (x y : Fin 2 → F) :
    traceDetForm F ((g : Matrix (Fin 2) (Fin 2) F).mulVec x)
      ((g : Matrix (Fin 2) (Fin 2) F).mulVec y) = traceDetForm F x y := by
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  rw [traceDetForm_apply, traceDetForm_apply]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination (x 0 * y 1 - x 1 * y 0) * hdet

end Form

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem selfDual_of_natural {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F]
    {L : Subgroup (GLV V)} (φ : ↥L ≃* SL(2, F)) (ψ : V ≃ₗ[ZMod 2] (Fin 2 → F))
    (hψ : ∀ (h : ↥L) (v : V),
      ψ ((h : GLV V) v) = ((φ h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (ψ v)) :
    CFSG.Quasithin.G11.SelfDual L ⊤ := by
  let e : ↥(⊤ : Submodule (ZMod 2) V) ≃ₗ[ZMod 2] (Fin 2 → F) := Submodule.topEquiv.trans ψ
  refine ⟨(traceDetForm F).compl₁₂ e.toLinearMap e.toLinearMap, ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    apply e.injective
    rw [map_zero]
    apply traceDetForm_separatingLeft F
    intro y
    simpa using hi (e.symm y)
  · intro j hj
    apply e.injective
    rw [map_zero]
    have := (traceDetForm_nondegenerate F).2 (e j) fun x => by
      simpa using hj (e.symm x)
    exact this
  · intro k hk i j i' j' hi hj
    have hki : e i' = ((φ ⟨k, hk⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (e i) := by
      have h := hψ ⟨k, hk⟩ (i : V)
      show ψ (i' : V) = _
      rw [← hi]; exact h
    have hkj : e j' = ((φ ⟨k, hk⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec (e j) := by
      have h := hψ ⟨k, hk⟩ (j : V)
      show ψ (j' : V) = _
      rw [← hj]; exact h
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
    rw [hki, hkj, traceDetForm_mulVec]

theorem natCard_endCommutant_eq {F : Type} [Field F] (L : Subgroup (GLV V))
    (φ : ↥L ≃* SL(2, F)) :
    Nat.card (CFSG.Quasithin.G11.endCommutant L) = Nat.card (EndRing (repOf L φ)) := by
  have hmem : ∀ f : Module.End (ZMod 2) V,
      f ∈ CFSG.Quasithin.G11.endCommutant L ↔ ∀ g v, f (repOf L φ g v) = repOf L φ g (f v) := by
    intro f
    constructor
    · intro hf g v
      rw [repOf_apply, repOf_apply]
      exact CFSG.Quasithin.Background.Harris.OrdinaryProofs.endCommutant_apply_comm hf
        (φ.symm g).2 v
    · intro hf
      rw [CFSG.Quasithin.G11.endCommutant, Subalgebra.mem_centralizer_iff]
      rintro _ ⟨h, hh, rfl⟩
      ext v
      have := hf (φ ⟨h, hh⟩) v
      rw [repOf_apply, repOf_apply, MulEquiv.symm_apply_apply] at this
      simpa [Module.End.mul_apply] using this.symm
  have hmem' := mem_endRing_iff (repOf L φ)
  let toEnd : EndRing (repOf L φ) → CFSG.Quasithin.G11.endCommutant L := fun ψ =>
    ⟨ψ.restrictScalars (ZMod 2), (hmem _).2 ((hmem' _).1 ⟨ψ, rfl⟩)⟩
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective toEnd ⟨fun a b hab => ?_, fun f => ?_⟩
  · apply LinearMap.ext
    intro v
    exact congrArg (fun f : CFSG.Quasithin.G11.endCommutant L => (f : Module.End (ZMod 2) V) v) hab
  · obtain ⟨ψ, hψ⟩ := (hmem' f.1).2 ((hmem _).1 f.2)
    refine ⟨ψ, Subtype.ext (LinearMap.ext fun v => ?_)⟩
    exact congrFun hψ v

end CFSG.Quasithin.G11.Harris.L2
