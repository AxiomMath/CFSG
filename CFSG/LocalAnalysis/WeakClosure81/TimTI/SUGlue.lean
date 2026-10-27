module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.Timmesfeld.LieEmbed.UnitaryForms

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TimTI

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.BorelTits CFSG.Timmesfeld.LieEmbed

private theorem timti_su_rank_vecMulVec_eq_one {ι κ K : Type} [Field K] [Fintype ι] [Fintype κ]
    (w : ι → K) (v : κ → K) (i : ι) (j : κ) (hij : w i * v j ≠ 0) :
    (Matrix.vecMulVec w v).rank = 1 := by
  refine le_antisymm (Matrix.rank_vecMulVec_le w v) ?_
  have hdet : ((Matrix.vecMulVec w v).submatrix (fun _ : Fin 1 => i)
      (fun _ : Fin 1 => j)).det ≠ 0 := by
    rw [Matrix.det_unique]
    simpa [Matrix.vecMulVec_apply] using hij
  have h := Matrix.rank_submatrix_le (Matrix.vecMulVec w v) (fun _ : Fin 1 => i)
    (fun _ : Fin 1 => j)
  rw [Matrix.rank_of_isUnit _ (Matrix.isUnit_iff_isUnit_det _ |>.mpr
    (isUnit_iff_ne_zero.mpr hdet))] at h
  simpa using h

private theorem timti_su_rank_conj_sub_one {ι K : Type} [Field K] [Fintype ι] [DecidableEq ι]
    (g h : GL ι K) :
    ((((h * g * h⁻¹ : GL ι K) : Matrix ι ι K)) - 1).rank =
      (((g : GL ι K) : Matrix ι ι K) - 1).rank := by
  have hHH : ((h : GL ι K) : Matrix ι ι K) * ((h⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul]
    simp
  have hmat : (((h * g * h⁻¹ : GL ι K) : Matrix ι ι K)) - 1 =
      ((h : GL ι K) : Matrix ι ι K) * (((g : GL ι K) : Matrix ι ι K) - 1) *
        ((h⁻¹ : GL ι K) : Matrix ι ι K) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hHH]
    simp
  have hdet : IsUnit ((h : GL ι K) : Matrix ι ι K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  have hdet' : IsUnit ((h⁻¹ : GL ι K) : Matrix ι ι K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  rw [hmat, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdet',
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet]

theorem rank_uTrans_sub_one {m : ℕ} {F : Type} [Field F] (σ : F ≃+* F) {a : Fin m → F}
    (ha : a ≠ 0) {c : F} (hc : c ≠ 0) : (uTrans σ a c - 1).rank = 1 := by
  have hu : uTrans σ a c - 1 = Matrix.vecMulVec (c • a) (uRow σ a) := by
    show (1 + c • uNil σ a - 1 : Matrix (Fin m) (Fin m) F) =
      Matrix.vecMulVec (c • a) (uRow σ a)
    rw [add_sub_cancel_left, uNil, ← Matrix.smul_vecMulVec]
  rw [hu]
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    exact ha (funext fun i => by
      by_contra hc'
      exact h ⟨i, hc'⟩)
  obtain ⟨j, hj⟩ : ∃ j, uRow σ a j ≠ 0 := by
    by_contra h
    exact uRow_ne_zero σ ha (funext fun j => by
      by_contra hc'
      exact h ⟨j, hc'⟩)
  refine timti_su_rank_vecMulVec_eq_one _ _ i j ?_
  rw [Pi.smul_apply, smul_eq_mul]
  exact mul_ne_zero (mul_ne_zero hc hi) hj

theorem exists_equiv_psu_of_isUTransGroup {H : Type} [Group H] {f m : ℕ} (hf : 2 ≤ f)
    (hm : 4 ≤ m)
    (Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m) →* H)
    (hΦ : Function.Surjective Φ) (hker : Φ.ker = Subgroup.center _)
    {a : Fin m → GaloisField 2 (2 * f)} (ha : a ≠ 0)
    {T : Subgroup ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m)}
    (hT : IsUTransGroup (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) a T) :
    CFSG.Blueprint.LieModel H .PSU m 2 f ∧
      ∃ e : H ≃* StatedProj (StatedSU m (2 ^ f) (GaloisField 2 (2 * f))),
        ∀ t ∈ T, t ≠ 1 → SevenK.IsUnitaryTransvectionIn m f (e (Φ t)) := by
  classical
  have hf1 : 1 ≤ f := by omega
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  obtain ⟨P, hP⟩ :=
    Unitary.exists_wittMatrix (F := GaloisField 2 (2 * f)) (p := 2) (f := f) hF m
  let ψ : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m ≃*
      StatedSU m (2 ^ f) (GaloisField 2 (2 * f)) :=
    (Unitary.conjEquiv P hP).trans
      (MulEquiv.subgroupCongr (Unitary.SUid_eq_statedSU hF m))
  have hψ : ∀ z : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m,
      ((ψ z : StatedSU m (2 ^ f) (GaloisField 2 (2 * f))) :
          GL (Fin m) (GaloisField 2 (2 * f))) =
        P * (z : GL (Fin m) (GaloisField 2 (2 * f))) * P⁻¹ := by
    intro z
    change (((MulEquiv.subgroupCongr (Unitary.SUid_eq_statedSU hF m)
      (Unitary.conjEquiv P hP z) : StatedSU m (2 ^ f) (GaloisField 2 (2 * f)))) :
        GL (Fin m) (GaloisField 2 (2 * f))) = _
    rw [MulEquiv.subgroupCongr_apply, Unitary.coe_conjEquiv]
  have hZ : Subgroup.center (StatedSU m (2 ^ f) (GaloisField 2 (2 * f))) =
      (StatedScalars (Fin m) (GaloisField 2 (2 * f))).subgroupOf
        (StatedSU m (2 ^ f) (GaloisField 2 (2 * f))) :=
    (Unitary.isQuasisimple_statedSU_of_card (F := GaloisField 2 (2 * f)) (p := 2) (f := f)
      (n := m) hF (by omega) (by
        intro h; have := congrArg Prod.fst h; simp at this; omega)).2
  let e : H ≃* StatedProj (StatedSU m (2 ^ f) (GaloisField 2 (2 * f))) :=
    ((QuotientGroup.quotientKerEquivOfSurjective Φ hΦ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)).trans
      ((QuotientGroup.congr _ _ ψ (Subgroup.map_center_eq ψ)).trans
        (QuotientGroup.quotientMulEquivOfEq hZ))
  have he_mk : ∀ z : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m,
      e (Φ z) = QuotientGroup.mk (ψ z) := by
    intro z
    have hqk : (QuotientGroup.quotientKerEquivOfSurjective Φ hΦ)
        (QuotientGroup.mk z) = Φ z := rfl
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective Φ hΦ).symm (Φ z) =
        QuotientGroup.mk z := by
      rw [← hqk]
      exact MulEquiv.symm_apply_apply _ _
    simp only [e, MulEquiv.trans_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk]
    rw [QuotientGroup.congr_mk, QuotientGroup.quotientMulEquivOfEq_mk]
  have hadm : StatedLieAdmissible .PSU m 2 f :=
    ⟨Nat.prime_two, by omega, by omega, by
      intro h; have := congrArg Prod.fst h; simp at this; omega⟩
  have hLM : CFSG.Blueprint.LieModel H .PSU m 2 f :=
    Or.inl ⟨by decide, ⟨hadm, GaloisField 2 (2 * f), inferInstance, inferInstance, hF, ⟨e⟩⟩⟩
  refine ⟨hLM, e, ?_⟩
  intro t htT ht1
  obtain ⟨c, hc, hsu⟩ := (hT.1 t).1 htT
  have hc0 : c ≠ 0 := by
    intro hc0
    apply ht1
    apply suMat_injective
    rw [hsu, hc0, uTrans_zero, map_one]
  refine ⟨ψ t, (he_mk t).symm, ?_⟩
  rw [hψ t, timti_su_rank_conj_sub_one]
  have hsu' : ((t : GL (Fin m) (GaloisField 2 (2 * f))) :
      Matrix (Fin m) (Fin m) (GaloisField 2 (2 * f))) =
        uTrans (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) a c := hsu
  rw [hsu']
  exact rank_uTrans_sub_one _ ha hc0

end CFSG.LocalAnalysis.WeakClosure81.TimTI
