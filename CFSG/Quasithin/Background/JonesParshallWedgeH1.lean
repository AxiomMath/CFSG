module

public import CFSG.Quasithin.Background.JonesParshallWedge
public import CFSG.Quasithin.Background.JonesParshallSmallSL

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.JonesParshall

open Matrix

section Action

variable (K : Type) [Field K]

@[expose] def muW : SpecialLinearGroup (Fin 5) K →* AddMonoid.End (Fin 10 → K) where
  toFun g := ((wedgeEquiv K).toLinearMap ∘ₗ
    exteriorPower.map 2 (Matrix.toLin' (g : Matrix (Fin 5) (Fin 5) K)) ∘ₗ
      (wedgeEquiv K).symm.toLinearMap).toAddMonoidHom
  map_one' := AddMonoidHom.ext fun w => by
    change (wedgeEquiv K) (exteriorPower.map 2 (Matrix.toLin' (1 : Matrix (Fin 5) (Fin 5) K))
        ((wedgeEquiv K).symm w)) = w
    rw [Matrix.toLin'_one, exteriorPower.map_id, LinearMap.id_apply,
      LinearEquiv.apply_symm_apply]
  map_mul' g h := AddMonoidHom.ext fun w => by
    change (wedgeEquiv K) (exteriorPower.map 2
      (Matrix.toLin' ((g : Matrix (Fin 5) (Fin 5) K) * (h : Matrix (Fin 5) (Fin 5) K)))
        ((wedgeEquiv K).symm w)) =
      (wedgeEquiv K) (exteriorPower.map 2 (Matrix.toLin' (g : Matrix (Fin 5) (Fin 5) K))
        ((wedgeEquiv K).symm ((wedgeEquiv K) (exteriorPower.map 2
          (Matrix.toLin' (h : Matrix (Fin 5) (Fin 5) K)) ((wedgeEquiv K).symm w)))))
    rw [LinearEquiv.symm_apply_apply, Matrix.toLin'_mul, exteriorPower.map_comp]
    rfl

theorem muW_apply (g : SpecialLinearGroup (Fin 5) K) (w : Fin 10 → K) :
    muW K g w = wedgeMat (g : Matrix (Fin 5) (Fin 5) K) *ᵥ w := by
  change (wedgeEquiv K) (exteriorPower.map 2 (Matrix.toLin' (g : Matrix (Fin 5) (Fin 5) K))
    ((wedgeEquiv K).symm w)) = _
  rw [wedgeEquiv_apply, wedgeCoord_map, ← wedgeEquiv_apply, LinearEquiv.apply_symm_apply]

end Action

section Fox

variable {n k m : ℕ} {R : Type*} [CommRing R]

@[expose] def foxDM (mats : Fin k → Matrix (Fin n) (Fin n) R) :
    List (Fin k) → Fin k → Matrix (Fin n) (Fin n) R
  | [] => fun _ => 0
  | i :: w => fun l => (if i = l then 1 else 0) + mats i * foxDM mats w l

theorem sum_ite_mulVec (vals : Fin k → Fin n → R) (i : Fin k) :
    ∑ l, (if i = l then (1 : Matrix (Fin n) (Fin n) R) else 0) *ᵥ vals l = vals i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem foxEvalM_eq_sum (mats : Fin k → Matrix (Fin n) (Fin n) R) (vals : Fin k → Fin n → R)
    (w : List (Fin k)) : foxEvalM mats vals w = ∑ l, foxDM mats w l *ᵥ vals l := by
  induction w with
  | nil => simp [foxEvalM, foxDM]
  | cons i w ih =>
    change vals i + mats i *ᵥ foxEvalM mats vals w =
      ∑ l, ((if i = l then 1 else 0) + mats i * foxDM mats w l) *ᵥ vals l
    rw [ih, mulVec_sum]
    simp only [add_mulVec, Finset.sum_add_distrib, ← mulVec_mulVec, sum_ite_mulVec]

theorem eq_cob_of_cert (A : Fin k → Matrix (Fin n) (Fin n) R)
    (D : Fin m → Fin k → Matrix (Fin n) (Fin n) R) (P : Fin k → Matrix (Fin n) (Fin n) R)
    (C : Fin k → Fin m → Matrix (Fin n) (Fin n) R)
    (hcert : ∀ j l, (if j = l then 1 else 0) - (A j - 1) * P l = ∑ r, C j r * D r l)
    {v : Fin k → Fin n → R} (hv : ∀ r, ∑ l, D r l *ᵥ v l = 0) (j : Fin k) :
    v j = A j *ᵥ (∑ l, P l *ᵥ v l) - ∑ l, P l *ᵥ v l := by
  have h1 : ∑ l, ((if j = l then 1 else 0) - (A j - 1) * P l) *ᵥ v l = 0 := by
    simp_rw [hcert, sum_mulVec, ← mulVec_mulVec]
    rw [Finset.sum_comm]
    simp_rw [← mulVec_sum, hv, mulVec_zero, Finset.sum_const_zero]
  have h2 : ∑ l, ((if j = l then 1 else 0) - (A j - 1) * P l) *ᵥ v l =
      v j - (A j *ᵥ (∑ l, P l *ᵥ v l) - ∑ l, P l *ᵥ v l) := by
    simp_rw [sub_mulVec, Finset.sum_sub_distrib, sum_ite_mulVec, ← mulVec_mulVec, ← mulVec_sum,
      sub_mulVec, one_mulVec]
  rw [h2] at h1
  exact sub_eq_zero.mp h1

end Fox

@[expose] def relsW : Fin 4 → List (Fin 2) :=
  ![[0, 0], [1, 1, 1, 1, 1], [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1],
    [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0,
      1]]

theorem relsW_spec : ∀ r, wordEvalM mats5 (relsW r) = 1 := by
  decide +kernel

@[expose] def matsW : Fin 2 → Matrix (Fin 10) (Fin 10) (ZMod 2) := fun i => wedgeMat (mats5 i)

@[expose] def certP0 : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def certP1 : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  !![0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    1, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0, 1, 0, 0, 0;
    1, 0, 0, 1, 1, 0, 0, 0, 0, 0]

@[expose] def certC00 : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def certC01 : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def certC02 : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0]

@[expose] def certC03 : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def certC10 : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def certC11 : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def certC12 : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def certC13 : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def certP : Fin 2 → Matrix (Fin 10) (Fin 10) (ZMod 2) := ![certP0, certP1]

@[expose] def certC : Fin 2 → Fin 4 → Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  ![![certC00, certC01, certC02, certC03], ![certC10, certC11, certC12, certC13]]

theorem cert_spec : ∀ j l : Fin 2, (if j = l then 1 else 0) - (matsW j - 1) * certP l =
    ∑ r, certC j r * foxDM matsW (relsW r) l := by
  decide +kernel

theorem muW_gens5 (i : Fin 2) (w : Fin 10 → ZMod 2) : muW (ZMod 2) (gens5 i) w = matsW i *ᵥ w := by
  rw [muW_apply]
  fin_cases i <;> rfl

theorem Z1A_eq_B1A_wedge
    : Z1A (muW (ZMod 2)) = B1A (muW (ZMod 2)) := by
  refine le_antisymm (fun f hf => ?_) (B1A_le_Z1A _)
  set v : Fin 2 → Fin 10 → ZMod 2 := fun l => f (gens5 l)
  have hfox : ∀ w, foxEval (muW (ZMod 2)) gens5 v w = foxEvalM matsW v w := by
    intro w
    induction w with
    | nil => rfl
    | cons i w ih =>
      change v i + muW (ZMod 2) (gens5 i) (foxEval (muW (ZMod 2)) gens5 v w) =
        v i + matsW i *ᵥ foxEvalM matsW v w
      rw [ih, muW_gens5]
  have hrel : ∀ r, ∑ l, foxDM matsW (relsW r) l *ᵥ v l = 0 := by
    intro r
    have h1 : wordEval gens5 (relsW r) = 1 :=
      wordEval_eq_one (by rw [gens5_coe]; exact relsW_spec r)
    have h2 := Z1A_wordEval hf gens5 (relsW r)
    rw [h1, Z1A_one hf] at h2
    rw [← foxEvalM_eq_sum, ← hfox]
    exact h2.symm
  set x : Fin 10 → ZMod 2 := ∑ l, certP l *ᵥ v l
  have hv : ∀ j, v j = matsW j *ᵥ x - x := eq_cob_of_cert matsW (fun r l => foxDM matsW (relsW r) l)
    certP certC cert_spec hrel
  have hf' : f - coboundaryA (muW (ZMod 2)) x ∈ Z1A (muW (ZMod 2)) :=
    sub_mem hf (B1A_le_Z1A _ ⟨x, rfl⟩)
  have h0 := eq_zero_of_vanish_closure hf'
    (closure_range_eq_top (by rw [gens5_coe]; exact tw5_spec)) (by
      rintro _ ⟨i, rfl⟩
      change f (gens5 i) - (muW (ZMod 2) (gens5 i) x - x) = 0
      rw [muW_gens5, sub_eq_zero]
      exact hv i)
  have e : f = coboundaryA (muW (ZMod 2)) x := sub_eq_zero.mp h0
  rw [e]
  exact ⟨x, rfl⟩

end CFSG.Quasithin.JonesParshall
