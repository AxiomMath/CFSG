module

public import CFSG.Quasithin.SteinbergCBGDSchur
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin.SteinbergCB.GDescent

open Matrix

variable {F : Type*} [Field F] {X : Type*} [Group X] [Fintype X] {d : ℕ}

@[expose] noncomputable def sumRep (ρ : X →* GL (Fin d) F) :
    (X → F) →ₗ[F] Matrix (Fin d) (Fin d) F where
  toFun a := ∑ g, a g • (ρ g : Matrix (Fin d) (Fin d) F)
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]

theorem sumRep_apply (ρ : X →* GL (Fin d) F) (a : X → F) :
    sumRep ρ a = ∑ g, a g • (ρ g : Matrix (Fin d) (Fin d) F) := rfl

theorem sumRep_single [DecidableEq X] (ρ : X →* GL (Fin d) F) (g : X) :
    sumRep ρ (Pi.single g 1) = (ρ g : Matrix (Fin d) (Fin d) F) := by
  rw [sumRep_apply, Finset.sum_eq_single g]
  · simp
  · intro h _ hne
    simp [hne]
  · simp

theorem range_sumRep [IsAlgClosed F] (hd : 1 ≤ d) {ρ : X →* GL (Fin d) F} (hρ : IsIrredRep ρ) :
    LinearMap.range (sumRep ρ) = ⊤ := by
  classical
  rw [eq_top_iff, ← span_range_eq_top hd hρ, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  exact ⟨Pi.single g 1, sumRep_single ρ g⟩

theorem mul_sumRep (ρ : X →* GL (Fin d) F) (h : X) (a : X → F) :
    (ρ h : Matrix (Fin d) (Fin d) F) * sumRep ρ a = sumRep ρ (fun k => a (h⁻¹ * k)) := by
  rw [sumRep_apply, sumRep_apply, Finset.mul_sum]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft h)]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, Units.val_mul, mul_smul_comm]

theorem ker_sumRep_le [IsAlgClosed F] (hd : 1 ≤ d) {ρ ρ' : X →* GL (Fin d) F}
    (hρ' : IsIrredRep ρ')
    (htr : ∀ g, Matrix.trace (ρ g : Matrix (Fin d) (Fin d) F) =
      Matrix.trace (ρ' g : Matrix (Fin d) (Fin d) F)) :
    LinearMap.ker (sumRep ρ) ≤ LinearMap.ker (sumRep ρ') := by
  intro a ha
  rw [LinearMap.mem_ker] at ha ⊢
  set M := sumRep ρ' a with hM
  have h1 : ∀ h : X, Matrix.trace (M * (ρ' h : Matrix (Fin d) (Fin d) F)) = 0 := by
    intro h
    have : Matrix.trace (M * (ρ' h : Matrix (Fin d) (Fin d) F)) =
        Matrix.trace (sumRep ρ a * (ρ h : Matrix (Fin d) (Fin d) F)) := by
      rw [hM, sumRep_apply, sumRep_apply, Finset.sum_mul, Finset.sum_mul, Matrix.trace_sum,
        Matrix.trace_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [smul_mul_assoc, smul_mul_assoc, Matrix.trace_smul, Matrix.trace_smul, ← Units.val_mul,
        ← Units.val_mul, ← map_mul, ← map_mul, htr (g * h)]
    rw [this, ha, zero_mul, Matrix.trace_zero]
  have h2 : ∀ N, Matrix.trace (M * N) = 0 := by
    intro N
    have hN : N ∈ Submodule.span F (Set.range fun g => (ρ' g : Matrix (Fin d) (Fin d) F)) := by
      rw [span_range_eq_top hd hρ']
      exact Submodule.mem_top
    induction hN using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact h1 g
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, Matrix.trace_add, hx, hy, add_zero]
    | smul c x _ hx => rw [mul_smul_comm, Matrix.trace_smul, hx, smul_zero]
  rw [Matrix.ext_iff_trace_mul_left]
  intro N
  rw [mul_zero, Matrix.trace_zero, Matrix.trace_mul_comm, h2]

theorem repIso_of_trace_eq [IsAlgClosed F] (hd : 1 ≤ d) {ρ ρ' : X →* GL (Fin d) F}
    (hρ : IsIrredRep ρ) (hρ' : IsIrredRep ρ')
    (htr : ∀ g, Matrix.trace (ρ g : Matrix (Fin d) (Fin d) F) =
      Matrix.trace (ρ' g : Matrix (Fin d) (Fin d) F)) : RepIso ρ ρ' := by
  classical
  have hsurj : Function.Surjective (sumRep ρ) := LinearMap.range_eq_top.1 (range_sumRep hd hρ)
  have hker := ker_sumRep_le hd hρ' htr
  have hker' := ker_sumRep_le hd hρ (fun g => (htr g).symm)
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : Matrix (Fin d) (Fin d) F →ₗ[F] Matrix (Fin d) (Fin d) F,
      ∀ a, Λ (sumRep ρ a) = sumRep ρ' a := by
    refine ⟨((LinearMap.ker (sumRep ρ)).liftQ (sumRep ρ') hker).comp
      ((sumRep ρ).quotKerEquivOfSurjective hsurj).symm.toLinearMap, fun a => ?_⟩
    have : ((sumRep ρ).quotKerEquivOfSurjective hsurj).symm (sumRep ρ a) =
        Submodule.Quotient.mk a := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have hΛinj : ∀ M, Λ M = 0 → M = 0 := by
    intro M hM
    obtain ⟨a, rfl⟩ := hsurj M
    rw [hΛ] at hM
    exact hker' hM
  have hΛmul : ∀ h M, Λ ((ρ h : Matrix (Fin d) (Fin d) F) * M) =
      (ρ' h : Matrix (Fin d) (Fin d) F) * Λ M := by
    intro h M
    obtain ⟨a, rfl⟩ := hsurj M
    rw [mul_sumRep, hΛ, hΛ, mul_sumRep]
  set e0 : Fin d := ⟨0, by omega⟩
  set u : Fin d → F := Pi.single e0 1
  have hE : Λ (vecMulVec u u) ≠ 0 := by
    intro h0
    have := hΛinj _ h0
    have h1 := congrFun (congrFun this e0) e0
    simp [u, vecMulVec_apply] at h1
  obtain ⟨j, hj⟩ : ∃ j, Λ (vecMulVec u u) *ᵥ Pi.single j 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hE
    ext i k
    have := congrFun (hcon k) i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
    exact this
  set w : Fin d → F := Pi.single j 1
  let T : (Fin d → F) →ₗ[F] (Fin d → F) :=
    { toFun := fun x => Λ (vecMulVec x u) *ᵥ w
      map_add' := fun x y => by rw [Matrix.add_vecMulVec, map_add, Matrix.add_mulVec]
      map_smul' := fun c x => by
        rw [Matrix.smul_vecMulVec, map_smul, Matrix.smul_mulVec, RingHom.id_apply] }
  have hTapp : ∀ x, T x = Λ (vecMulVec x u) *ᵥ w := fun x => rfl
  set Tm := LinearMap.toMatrix' T with hTm
  have hint : ∀ h, Tm * (ρ h : Matrix (Fin d) (Fin d) F) =
      (ρ' h : Matrix (Fin d) (Fin d) F) * Tm := by
    intro h
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, hTm, Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      hTapp, hTapp, ← Matrix.mul_vecMulVec, hΛmul, Matrix.mulVec_mulVec]
  have hTm0 : Tm ≠ 0 := by
    intro h0
    apply hj
    have : T u = 0 := by
      rw [← Matrix.toLin'_toMatrix' T, ← hTm, h0, map_zero, LinearMap.zero_apply]
    rw [hTapp] at this
    exact this
  obtain ⟨U, hU⟩ := isUnit_of_intertw hρ hint hTm0
  refine ⟨U, fun g => Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, hU]
  calc (ρ' g : Matrix (Fin d) (Fin d) F) =
        (ρ' g : Matrix (Fin d) (Fin d) F) * (Tm * (U⁻¹ : GL (Fin d) F)) := by
        rw [← hU, Units.mul_inv, mul_one]
    _ = Tm * (ρ g : Matrix (Fin d) (Fin d) F) * (U⁻¹ : GL (Fin d) F) := by
        rw [← mul_assoc, hint]

end CFSG.Quasithin.SteinbergCB.GDescent
