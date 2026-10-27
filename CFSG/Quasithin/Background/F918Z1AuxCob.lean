module

public import CFSG.Quasithin.Background.F918Z1Aux
public import CFSG.Quasithin.Background.F918Z1AuxMat

public section

namespace CFSG.Quasithin

open scoped Matrix

namespace D37Lift

variable {GD GX A R : Type*} {d r : ℕ} [Group GD] [Group GX] [AddCommGroup A] [CommRing R]

@[expose] def tens (u : Fin r → R) : (Fin d → R) →+ Matrix (Fin d) (Fin r) R :=
  AddMonoidHom.mk' (fun v => Matrix.vecMulVec v u) (fun a b => Matrix.add_vecMulVec a b u)

theorem tens_apply (u : Fin r → R) (v : Fin d → R) : tens u v = Matrix.vecMulVec v u := rfl

theorem vecMulVec_zero_right (v : Fin d → R) :
    Matrix.vecMulVec v (0 : Fin r → R) = 0 := by
  ext a b
  simp [Matrix.vecMulVec_apply]

namespace LiftData

variable (E : LiftData GD GX A R d r)

@[expose] def cobSub (s : Matrix (Fin d) (Fin r) R →+ A) : Submodule R (Fin r → R) where
  carrier := {u | ∃ f : (Fin d → R) →+ A, (∀ v, E.p (f v) = 0) ∧
    ∀ (g : GD) (v : Fin d → R), E.cochain s g (Matrix.vecMulVec v u) =
      f v - f ((E.ρ g : Matrix (Fin d) (Fin d) R) *ᵥ v)}
  zero_mem' := ⟨0, fun v => map_zero _, fun g v => by simp [vecMulVec_zero_right]⟩
  add_mem' := by
    rintro u u' ⟨f, hf, hfg⟩ ⟨f', hf', hfg'⟩
    refine ⟨f + f', fun v => by simp [hf, hf'], fun g v => ?_⟩
    rw [Matrix.vecMulVec_add, map_add, hfg, hfg']
    simp only [AddMonoidHom.add_apply]
    abel
  smul_mem' := by
    rintro c u ⟨f, hf, hfg⟩
    refine ⟨f.comp (DistribSMul.toAddMonoidHom (Fin d → R) c), fun v => hf _, fun g v => ?_⟩
    have h1 : Matrix.vecMulVec v (c • u) = Matrix.vecMulVec (c • v) u := by
      rw [Matrix.vecMulVec_smul, Matrix.smul_vecMulVec]
    rw [h1, hfg]
    simp [Matrix.mulVec_smul]

theorem sub_mulVec_mem_cobSub {s : Matrix (Fin d) (Fin r) R →+ A} (hs : ∀ M, E.p (s M) = M)
    (x : GX) (w : Fin r → R) :
    w - (E.σ x : Matrix (Fin r) (Fin r) R) *ᵥ w ∈ E.cobSub s := by
  refine ⟨(E.twist s x).comp (tens w), fun v => E.p_twist hs x _, fun g v => ?_⟩
  have h := E.cochain_sub_cochain hs g x (Matrix.vecMulVec v w)
  rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose, Matrix.mul_vecMulVec] at h
  rw [Matrix.vecMulVec_sub, map_sub, h]
  rfl

theorem cobSub_eq_top {s : Matrix (Fin d) (Fin r) R →+ A} (hs : ∀ M, E.p (s M) = M)
    (U_irr : ∀ W : Submodule R (Fin r → R),
      (∀ x : GX, ∀ w ∈ W, (E.σ x : Matrix (Fin r) (Fin r) R) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hσnt : ∃ x, E.σ x ≠ 1) : E.cobSub s = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← span_sub_eq_top E.σ U_irr hσnt]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, w, rfl⟩
  simpa using (E.cobSub s).neg_mem (E.sub_mulVec_mem_cobSub hs x w)

theorem exists_primitive {s : Matrix (Fin d) (Fin r) R →+ A} (htop : E.cobSub s = ⊤) :
    ∃ Φ : Matrix (Fin d) (Fin r) R →+ A, (∀ M, E.p (Φ M) = 0) ∧
      ∀ (g : GD) (M : Matrix (Fin d) (Fin r) R),
        E.cochain s g M = Φ M - Φ ((E.ρ g : Matrix (Fin d) (Fin d) R) * M) := by
  have hmem : ∀ j : Fin r, ∃ f : (Fin d → R) →+ A, (∀ v, E.p (f v) = 0) ∧
      ∀ (g : GD) (v : Fin d → R), E.cochain s g (Matrix.vecMulVec v (Pi.single j 1)) =
        f v - f ((E.ρ g : Matrix (Fin d) (Fin d) R) *ᵥ v) := fun j => by
    have : (Pi.single j 1 : Fin r → R) ∈ E.cobSub s := by rw [htop]; trivial
    exact this
  choose f hf0 hf using hmem
  refine ⟨AddMonoidHom.mk' (fun M => ∑ j, f j (M.col j)) ?_, ?_, ?_⟩
  · intro M N
    show ∑ j, f j ((M + N).col j) = ∑ j, f j (M.col j) + ∑ j, f j (N.col j)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => map_add (f j) _ _
  · intro M
    simp [map_sum, hf0]
  · intro g M
    conv_lhs => rw [colDecomp M]
    rw [map_sum]
    simp only [AddMonoidHom.mk'_apply, hf, Finset.sum_sub_distrib, Matrix.col_mul_eq_mulVec_col]

theorem exists_equivariantD {s : Matrix (Fin d) (Fin r) R →+ A} (hs : ∀ M, E.p (s M) = M)
    (htop : E.cobSub s = ⊤) :
    ∃ s' : Matrix (Fin d) (Fin r) R →+ A, (∀ M, E.p (s' M) = M) ∧
      ∀ (g : GD) (M : Matrix (Fin d) (Fin r) R),
        E.ag g (s' M) = s' ((E.ρ g : Matrix (Fin d) (Fin d) R) * M) := by
  obtain ⟨Φ, hΦ0, hΦ⟩ := E.exists_primitive htop
  refine ⟨s - Φ, fun M => by simp [hs, hΦ0], fun g M => ?_⟩
  have h1 : E.ag g (Φ M) = Φ M := E.ag_fix g _ (hΦ0 M)
  have h2 := hΦ g M
  rw [E.cochain_apply] at h2
  simp only [AddMonoidHom.sub_apply, map_sub, h1]
  linear_combination (norm := abel_nf) h2

theorem eq_zero_of_lmul_invariant
    (I_irr : ∀ W : AddSubgroup (Fin d → R),
      (∀ g : GD, ∀ w ∈ W, (E.ρ g : Matrix (Fin d) (Fin d) R) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hρnt : ∃ g, E.ρ g ≠ 1) (δ : Matrix (Fin d) (Fin r) R →+ A)
    (hδ : ∀ (g : GD) (M : Matrix (Fin d) (Fin r) R),
      δ ((E.ρ g : Matrix (Fin d) (Fin d) R) * M) = δ M) : δ = 0 := by
  have key : ∀ (j : Fin r) (v : Fin d → R), δ (Matrix.vecMulVec v (Pi.single j 1)) = 0 := by
    intro j v
    have hle : AddSubgroup.closure {u : Fin d → R | ∃ (g : GD) (w : Fin d → R),
        u = (E.ρ g : Matrix (Fin d) (Fin d) R) *ᵥ w - w} ≤
          (δ.comp (tens (Pi.single j 1 : Fin r → R))).ker := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨g, w, rfl⟩
      rw [SetLike.mem_coe, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, map_sub, map_sub,
        tens_apply, tens_apply, ← Matrix.mul_vecMulVec, hδ, sub_self]
    have hv : v ∈ AddSubgroup.closure {u : Fin d → R | ∃ (g : GD) (w : Fin d → R),
        u = (E.ρ g : Matrix (Fin d) (Fin d) R) *ᵥ w - w} := by
      rw [closure_sub_eq_top E.ρ I_irr hρnt]; trivial
    have := hle hv
    rwa [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, tens_apply] at this
  ext M
  calc δ M = δ (∑ j, Matrix.vecMulVec (M.col j) (Pi.single j 1 : Fin r → R)) :=
        congrArg δ (colDecomp M)
    _ = ∑ j, δ (Matrix.vecMulVec (M.col j) (Pi.single j 1 : Fin r → R)) := map_sum _ _ _
    _ = 0 := Finset.sum_eq_zero fun j _ => key j _

theorem exists_equivariant (hexp : ∀ a : A, a + a = 0)
    (I_irr : ∀ W : AddSubgroup (Fin d → R),
      (∀ g : GD, ∀ w ∈ W, (E.ρ g : Matrix (Fin d) (Fin d) R) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤)
    (U_irr : ∀ W : Submodule R (Fin r → R),
      (∀ x : GX, ∀ w ∈ W, (E.σ x : Matrix (Fin r) (Fin r) R) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hρnt : ∃ g, E.ρ g ≠ 1) (hσnt : ∃ x, E.σ x ≠ 1) :
    ∃ s : Matrix (Fin d) (Fin r) R →+ A, (∀ M, E.p (s M) = M) ∧
      (∀ (g : GD) (M : Matrix (Fin d) (Fin r) R),
        E.ag g (s M) = s ((E.ρ g : Matrix (Fin d) (Fin d) R) * M)) ∧
      ∀ (x : GX) (M : Matrix (Fin d) (Fin r) R),
        E.ax x (s M) = s (M * (E.σ x : Matrix (Fin r) (Fin r) R)ᵀ) := by
  obtain ⟨s₀, hs₀⟩ := exists_addSection hexp E.p E.p_surj
  obtain ⟨s, hs, hsg⟩ := E.exists_equivariantD hs₀ (E.cobSub_eq_top hs₀ U_irr hσnt)
  refine ⟨s, hs, hsg, fun x M => ?_⟩
  have e1 : ((E.σ x⁻¹ : Matrix.GeneralLinearGroup (Fin r) R) : Matrix (Fin r) (Fin r) R)ᵀ *
      ((E.σ x : Matrix.GeneralLinearGroup (Fin r) R) : Matrix (Fin r) (Fin r) R)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one, Matrix.transpose_one]
  have e2 : ((E.σ x : Matrix.GeneralLinearGroup (Fin r) R) : Matrix (Fin r) (Fin r) R)ᵀ *
      ((E.σ x⁻¹ : Matrix.GeneralLinearGroup (Fin r) R) : Matrix (Fin r) (Fin r) R)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, Matrix.transpose_one]
  obtain ⟨t, ht⟩ : ∃ t : Matrix (Fin d) (Fin r) R →+ A, ∀ N, t N =
      E.ax x (s (N * ((E.σ x⁻¹ : Matrix.GeneralLinearGroup (Fin r) R) :
        Matrix (Fin r) (Fin r) R)ᵀ)) := ⟨(E.ax x).comp (s.comp (E.rmul x⁻¹)), fun N => rfl⟩
  have hδ0 : ∀ N, E.p ((t - s) N) = 0 := by
    intro N
    rw [AddMonoidHom.sub_apply, map_sub, ht, E.p_ax, hs, hs, Matrix.mul_assoc, e1,
      Matrix.mul_one, sub_self]
  have hδ : ∀ (g : GD) (N : Matrix (Fin d) (Fin r) R),
      (t - s) ((E.ρ g : Matrix (Fin d) (Fin d) R) * N) = (t - s) N := by
    intro g N
    have h1 : t ((E.ρ g : Matrix (Fin d) (Fin d) R) * N) = E.ag g (t N) := by
      rw [ht, ht, Matrix.mul_assoc, ← hsg, E.ag_ax]
    simp only [AddMonoidHom.sub_apply]
    rw [h1, ← hsg]
    have h2 := E.ag_fix g _ (hδ0 N)
    simp only [AddMonoidHom.sub_apply, map_sub] at h2
    exact h2
  have hzero := E.eq_zero_of_lmul_invariant I_irr hρnt (t - s) hδ
  have h3 := congrArg (fun δ => δ (M * (E.σ x : Matrix (Fin r) (Fin r) R)ᵀ)) hzero
  simp only [AddMonoidHom.sub_apply, AddMonoidHom.zero_apply, sub_eq_zero, ht, Matrix.mul_assoc, e2,
    Matrix.mul_one] at h3
  exact h3

end LiftData

end D37Lift

end CFSG.Quasithin
