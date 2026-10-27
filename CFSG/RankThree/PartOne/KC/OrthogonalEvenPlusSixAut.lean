module

public import CFSG.RankThree.PartOne.K159.Klein
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinear
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth

public section

open Matrix Module _root_.QuadraticMap
open CFSG.LocalAnalysis CFSG.LieType.Universal.Spin

namespace CFSG.RankThree.PartOne.K159.Klein

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def congEquiv (g : GL (Fin 4) K) :
    (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K) :=
  LinearEquiv.ofLinearMap (cong (g : Matrix (Fin 4) (Fin 4) K))
    (cong ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, ← cong_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, cong_one]
      rfl)
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, ← cong_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, cong_one]
      rfl)

@[simp] theorem congEquiv_apply (g : GL (Fin 4) K) (v : Fin 3 ⊕ Fin 3 → K) :
    congEquiv g v = cong (g : Matrix (Fin 4) (Fin 4) K) v := rfl

theorem quadPlus_cong_eq_det_mul (g : Matrix (Fin 4) (Fin 4) K)
    (v : Fin 3 ⊕ Fin 3 → K) :
    quadPlus 3 K (cong g v) = g.det * quadPlus 3 K v := by
  rw [quadPlus_eq_pfS_alt, quadPlus_eq_pfS_alt, alt_cong]
  exact pfS_congr g (v (.inl 0)) (v (.inl 1)) (v (.inl 2)) (v (.inr 2))
    (v (.inr 1)) (v (.inr 0))

omit [CharP K 2] in
theorem alt_map_ringEquiv (σ : K ≃+* K) (v : Fin 3 ⊕ Fin 3 → K) :
    alt (fun i => σ (v i)) = (alt v).map σ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [alt, antiMat]

omit [CharP K 2] in
theorem coords_map_ringEquiv (σ : K ≃+* K) (M : Matrix (Fin 4) (Fin 4) K) :
    coords (M.map σ) = fun i => σ (coords M i) := by
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [coords]

omit [CharP K 2] in
theorem cong_map_ringEquiv (σ : K ≃+* K) (g : Matrix (Fin 4) (Fin 4) K)
    (v : Fin 3 ⊕ Fin 3 → K) :
    (fun i => σ (cong g v i)) = cong (g.map σ) (fun i => σ (v i)) := by
  calc
    (fun i => σ (cong g v i)) = coords ((g * alt v * gᵀ).map σ) :=
      (coords_map_ringEquiv σ _).symm
    _ = coords (g.map σ * alt (fun i => σ (v i)) * (g.map σ)ᵀ) := by
      rw [Matrix.map_mul, Matrix.map_mul, ← alt_map_ringEquiv,
        ← Matrix.transpose_map]
    _ = cong (g.map σ) (fun i => σ (v i)) := rfl

theorem alt_funCongrLeft_sumComm (v : Fin 3 ⊕ Fin 3 → K) :
    alt (LinearEquiv.funCongrLeft K K (Equiv.sumComm (Fin 3) (Fin 3)) v) = sharp (alt v) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [alt, antiMat, sharp, altMat, CharTwo.neg_eq]

theorem funCongrLeft_sumComm_cong (g : GL (Fin 4) K)
    (hg : (g : Matrix (Fin 4) (Fin 4) K).det = 1) (v : Fin 3 ⊕ Fin 3 → K) :
    LinearEquiv.funCongrLeft K K (Equiv.sumComm (Fin 3) (Fin 3))
        (cong (g : Matrix (Fin 4) (Fin 4) K) v) =
      cong (((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ)
        (LinearEquiv.funCongrLeft K K (Equiv.sumComm (Fin 3) (Fin 3)) v) := by
  have hAlt : IsAltMat (alt v) := by
    change IsAltMat (antiMat _ _ _ _ _ _)
    rw [← altMat_eq_antiMat]
    exact isAltMat_altMat _ _ _ _ _ _
  have hsharp := (char_two_alternating_four_Pfaffian_identities (F := K)).2.2.2.2
    g (alt v) hAlt
  have hs := hsharp.2.2
  rw [hg, one_smul] at hs
  apply (show Function.LeftInverse coords alt from coords_alt).injective
  rw [alt_funCongrLeft_sumComm, alt_cong, hs, alt_cong,
    alt_funCongrLeft_sumComm, Matrix.transpose_transpose]

variable [Finite K]

theorem exists_similarity_intertwine (β : MulAut (SpecialLinearGroup (Fin 4) K)) :
    ∃ (σ : K ≃+* K) (B : (Fin 3 ⊕ Fin 3 → K) ≃+ (Fin 3 ⊕ Fin 3 → K)) (μ : K),
      (∀ c v, B (c • v) = σ c • B v) ∧ μ ≠ 0 ∧
      (∀ v, quadPlus 3 K (B v) = μ * σ (quadPlus 3 K v)) ∧
      ∀ g v, B (rho g v) = rho (β g) (B v) := by
  classical
  obtain ⟨A, σ, hF | hG⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl (by decide : 3 ≤ 4) β
  all_goals
    let C := congEquiv A
    let R : (Fin 3 ⊕ Fin 3 → K) ≃+ (Fin 3 ⊕ Fin 3 → K) :=
      AddEquiv.piCongrRight fun _ => σ.toAddEquiv
    have hRsemi : ∀ c v, R (c • v) = σ c • R v := by
      intro c v
      ext i
      exact map_mul σ c (v i)
    have hRq : ∀ v, quadPlus 3 K (R v) = σ (quadPlus 3 K v) := by
      intro v
      simp [R, quadPlus_apply, map_sum, map_mul]
    have hRcong : ∀ g v, R (cong g v) = cong (g.map σ) (R v) :=
      cong_map_ringEquiv σ
    have hCq : ∀ v, quadPlus 3 K (C v) =
        (A : Matrix (Fin 4) (Fin 4) K).det * quadPlus 3 K v :=
      quadPlus_cong_eq_det_mul (A : Matrix (Fin 4) (Fin 4) K)
    have hAA : (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) *
        (A : Matrix (Fin 4) (Fin 4) K) = 1 := Units.inv_mul A
    have hdet : (A : Matrix (Fin 4) (Fin 4) K).det ≠ 0 := by
      intro h
      have h' := congrArg Matrix.det (Units.mul_inv A)
      rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h'
      exact zero_ne_one h'
  · let B := R.trans C.toAddEquiv
    refine ⟨σ, B, (A : Matrix (Fin 4) (Fin 4) K).det, ?_, hdet, ?_, ?_⟩
    · intro c v
      change C (R (c • v)) = σ c • C (R v)
      rw [hRsemi, map_smul]
    · intro v
      change quadPlus 3 K (C (R v)) = _
      rw [hCq, hRq]
    · intro g v
      change cong (A : Matrix (Fin 4) (Fin 4) K) (R (cong (g : Matrix (Fin 4) (Fin 4) K) v)) =
        cong (β g : Matrix (Fin 4) (Fin 4) K)
          (cong (A : Matrix (Fin 4) (Fin 4) K) (R v))
      rw [hRcong, hF g, cong_mul, cong_mul,
        ← cong_mul (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
          (A : Matrix (Fin 4) (Fin 4) K) (R v), hAA, cong_one]
  · let D := LinearEquiv.funCongrLeft K K (Equiv.sumComm (Fin 3) (Fin 3))
    have hDq : ∀ v, quadPlus 3 K (D v) = quadPlus 3 K v := by
      intro v
      simp [D, quadPlus_apply, Fin.sum_univ_three, mul_comm]
    have hDcong : ∀ (g : SpecialLinearGroup (Fin 4) K) v,
        D (cong (g : Matrix (Fin 4) (Fin 4) K) v) =
          cong ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ (D v) := by
      intro g v
      have hginv : (((SpecialLinearGroup.toGL g)⁻¹ : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) =
          ((g⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
        simpa only [SpecialLinearGroup.coe_GL_coe_matrix] using
          (congrArg (fun a : GL (Fin 4) K => (a : Matrix (Fin 4) (Fin 4) K))
            (map_inv SpecialLinearGroup.toGL g)).symm
      simpa only [SpecialLinearGroup.coe_GL_coe_matrix, hginv] using
        funCongrLeft_sumComm_cong (SpecialLinearGroup.toGL g)
          (by simpa only [SpecialLinearGroup.coe_GL_coe_matrix] using g.2) v
    let B := D.toAddEquiv.trans (R.trans C.toAddEquiv)
    refine ⟨σ, B, (A : Matrix (Fin 4) (Fin 4) K).det, ?_, hdet, ?_, ?_⟩
    · intro c v
      change C (R (D (c • v))) = σ c • C (R (D v))
      rw [map_smul, hRsemi, map_smul]
    · intro v
      change quadPlus 3 K (C (R (D v))) = _
      rw [hCq, hRq, hDq]
    · intro g v
      change cong (A : Matrix (Fin 4) (Fin 4) K)
          (R (D (cong (g : Matrix (Fin 4) (Fin 4) K) v))) =
        cong (β g : Matrix (Fin 4) (Fin 4) K)
          (cong (A : Matrix (Fin 4) (Fin 4) K) (R (D v)))
      rw [hDcong, hRcong, hG g, cong_mul, cong_mul,
        ← cong_mul (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
          (A : Matrix (Fin 4) (Fin 4) K) (R (D v)), hAA, cong_one]

end CFSG.RankThree.PartOne.K159.Klein

namespace CFSG.RankThree.PartOne.KCOrthogonalAut

open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.PartOne.KCOrthogonalDescent
open CFSG.LocalAnalysis.GLTheoremA.K155XOr

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem orthogonal_aut_semilinear_plus_six
    (α : MulAut (ProjOrthDerived (quadPlus 3 K))) :
    InducedBySemilinear (quadPlus 3 K) α := by
  classical
  let Q := quadPlus 3 K
  have hSP := K159.Klein.sl4_isSimpleGroup_and_perfect (K := K)
  let : IsSimpleGroup (SpecialLinearGroup (Fin 4) K) := hSP.1
  let : Group.IsPerfect (SpecialLinearGroup (Fin 4) K) := hSP.2
  have hle : (K159.Klein.rho (K := K)).range ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨g, rfl⟩
    exact K159.Klein.rho_mem g
  obtain ⟨-, -, -, -, -, -, hcomm, -⟩ :=
    derived_of_index_two_model (TauCeti.QuadraticMap.orthogonalGroup Q) K159.Klein.rho
      K159.Klein.rho_injective hle K159.Klein.card_orthogonalGroup_quadPlus_three
  have hrange : (K159.Klein.rho (K := K)).range = orthDerived Q := hcomm.symm
  let eSL : SpecialLinearGroup (Fin 4) K ≃* orthDerived Q :=
    (MonoidHom.ofInjective K159.Klein.rho_injective).trans (MulEquiv.subgroupCongr hrange)
  have heSL : ∀ g : SpecialLinearGroup (Fin 4) K,
      (eSL g : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) = K159.Klein.rho g :=
    fun _ => rfl
  have hQne : ∃ v, Q v ≠ 0 := by
    refine ⟨Sum.elim (Pi.single (0 : Fin 3) (1 : K)) (Pi.single (0 : Fin 3) (1 : K)), ?_⟩
    simp [Q, quadPlus_apply, Fin.sum_univ_three]
  let eQ : ProjOrthDerived Q ≃* orthDerived Q := orthProjEquiv hQne
  let αΩ : MulAut (orthDerived Q) := MulAut.congr eQ α
  let β : MulAut (SpecialLinearGroup (Fin 4) K) := MulAut.congr eSL.symm αΩ
  have hβ : ∀ g, eSL (β g) = αΩ (eSL g) := by
    intro g
    simp [β, MulAut.congr_apply]
  have hα : ∀ p, eQ (α p) = αΩ (eQ p) := by
    intro p
    simp [αΩ, MulAut.congr_apply]
  have heMk : ∀ g : orthDerived Q, eQ (QuotientGroup.mk g) = g := fun _ => rfl
  obtain ⟨σ, B, μ, hsemi, hμ, hQB, hB⟩ := K159.Klein.exists_similarity_intertwine β
  refine ⟨σ, B, hsemi, μ, hμ, hQB, ?_⟩
  intro g g' hgg
  apply eQ.injective
  rw [hα, heMk, heMk]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  obtain ⟨s, rfl⟩ := eSL.surjective g
  rw [← hβ, heSL]
  have h := hB s (B.symm v)
  rw [AddEquiv.apply_symm_apply] at h
  have hh : (g' : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) v =
      B (K159.Klein.rho s (B.symm v)) := by
    simpa only [heSL] using hgg v
  exact h.symm.trans hh.symm

end CFSG.RankThree.PartOne.KCOrthogonalAut

end
