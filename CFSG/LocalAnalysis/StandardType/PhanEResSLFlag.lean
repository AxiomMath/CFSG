module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagAct
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherBruhat
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherReducedWord

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.LocalAnalysis.ComponentInitial

variable {Fld : Type} [Field Fld] {m n : ℕ}

private lemma hmbSF_glLin_toGL_mulVec (A : SpecialLinearGroup (Fin n) Fld) :
    (glLin (SpecialLinearGroup.toGL A)).toLinearMap =
      Matrix.mulVecLin (A : Matrix (Fin n) (Fin n) Fld) :=
  LinearMap.ext fun v => by
    change (glLin (SpecialLinearGroup.toGL A)) v =
      (A : Matrix (Fin n) (Fin n) Fld).mulVec v
    rw [glLin_apply, SpecialLinearGroup.coe_GL_coe_matrix]

private lemma hmbSF_Vsub_eq_flagSpace (n c : ℕ) :
    Vsub (K := Fld) n c = LinearFlag.flagSpace n Fld c := by
  apply Submodule.ext
  intro v
  rw [LinearFlag.mem_flagSpace (K := Fld)]
  rfl

private lemma hmbSF_Vsub_eq_top {n c : ℕ} (h : n ≤ c) : Vsub (K := Fld) n c = ⊤ := by
  rw [← Vsub_self (K := Fld) (n := n)]
  exact le_antisymm (by rw [Vsub_self]; exact le_top) (Vsub_mono h)

private lemma hmbSF_span_image_smul {n : ℕ} (c : Fin n → Fld) (hc : ∀ k, c k ≠ 0)
    (f : Fin n → (Fin n → Fld)) (S : Set (Fin n)) :
    Submodule.span Fld ((fun k => c k • f k) '' S) = Submodule.span Fld (f '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    have h : f k = (c k)⁻¹ • (c k • f k) := by
      rw [smul_smul, inv_mul_cancel₀ (hc k), one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)

private lemma hmbSF_single_image_perm {n : ℕ} (w : Equiv.Perm (Fin n)) (j : ℕ) :
    (fun k : Fin n => (Pi.single (w k) 1 : Fin n → Fld)) '' {k | k.val < j} =
      (fun k : Fin n => (Pi.single k 1 : Fin n → Fld)) '' {k | (w⁻¹ k).val < j} := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨w k, by simpa using hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨w⁻¹ k, by simpa using hk, by simp⟩

private lemma hmbSF_map_signedPermutation_stdFlag (w : Equiv.Perm (Fin (m + 1))) (j : ℕ) :
    (Vsub (K := Fld) (m + 1) j).map (glLin (SpecialLinearGroup.toGL
        (LinearFlag.signedPermutation (m + 1) Fld w))).toLinearMap =
      Submodule.span Fld ((fun k : Fin (m + 1) => (Pi.single k 1 : Fin (m + 1) → Fld)) ''
        {k | (w⁻¹ k).val < j}) := by
  obtain ⟨c, hc⟩ := LinearFlag.isMonomial_signedPermMatrix (K := Fld) (n := m + 1) w
  have hgl : (glLin (SpecialLinearGroup.toGL
      (LinearFlag.signedPermutation (m + 1) Fld w))).toLinearMap =
      Matrix.mulVecLin (LinearFlag.signedPermMatrix (m + 1) Fld w) := by
    rw [hmbSF_glLin_toGL_mulVec, LinearFlag.coe_signedPermutation]
  rw [hmbSF_Vsub_eq_flagSpace, hgl, LinearFlag.flagSpace, Submodule.map_span, ← Set.image_comp]
  have hfun : (⇑(Matrix.mulVecLin (LinearFlag.signedPermMatrix (m + 1) Fld w)) ∘
        fun k : Fin (m + 1) => (Pi.single k 1 : Fin (m + 1) → Fld)) =
      fun k => (c k : Fld) • (Pi.single (w k) 1 : Fin (m + 1) → Fld) := by
    funext k
    rw [Function.comp_apply, Matrix.mulVecLin_apply]
    exact hc k
  rw [hfun, hmbSF_span_image_smul (fun k => (c k : Fld)) (fun k => (c k).ne_zero)
      (fun k => (Pi.single (w k) 1 : Fin (m + 1) → Fld)) {k | k.val < j},
    hmbSF_single_image_perm w j]

private lemma hmbSF_flagδ_stdFlag_signedPermutation (w : Equiv.Perm (Fin (m + 1))) :
    flagδ m (stdFlag Fld (m + 1))
      (flagAct (SpecialLinearGroup.toGL (LinearFlag.signedPermutation (m + 1) Fld w))
        (stdFlag Fld (m + 1))) = w := by
  have hpos : HasPos (stdFlag Fld (m + 1)) (flagAct (SpecialLinearGroup.toGL
      (LinearFlag.signedPermutation (m + 1) Fld w)) (stdFlag Fld (m + 1))) w⁻¹ := by
    apply hasPos_of_isAdapted
      (b := fun k : Fin (m + 1) => (Pi.single k 1 : Fin (m + 1) → Fld)) (σ := w⁻¹)
    refine ⟨Pi.linearIndependent_single_one (Fin (m + 1)) Fld, ?_, ?_⟩
    · intro i _
      change Vsub (K := Fld) (m + 1) i = Submodule.span Fld
        ((fun k : Fin (m + 1) => (Pi.single k 1 : Fin (m + 1) → Fld)) '' {k | k.val < i})
      rw [hmbSF_Vsub_eq_flagSpace]
      rfl
    · intro j _
      rw [flagAct, flagMap_E]
      exact hmbSF_map_signedPermutation_stdFlag w j
  rw [flagδ, (hasPos_iff).mp hpos, inv_inv]

theorem exists_flagAct_stdFlag (E : FlagK Fld (m + 1)) :
    ∃ A : SpecialLinearGroup (Fin (m + 1)) Fld,
      flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1)) = E := by
  classical
  obtain ⟨b, -, hb, hE, -⟩ :=
    CFSG.ClassicalInvolution.Phan.PhanE.Flag.exists_adapted (K := Fld) (n := m + 1) E E
  set M : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld := Matrix.of fun i k => b k i with hM
  have hMcol : ∀ k, M.col k = b k := by
    intro k
    ext i
    simp [hM]
  have hMdet : M.det ≠ 0 := by
    rw [← isUnit_iff_ne_zero, ← isUnit_iff_isUnit_det (A := M),
      ← Matrix.linearIndependent_cols_iff_isUnit (K := Fld)]
    rw [show M.col = b from funext hMcol]
    exact hb
  let d : Fld := M.det
  let e : Fin (m + 1) → Fld := fun k => if (k : ℕ) = 0 then d⁻¹ else 1
  have he : ∀ k, e k ≠ 0 := by
    intro k
    simp only [e]
    split_ifs
    · exact inv_ne_zero hMdet
    · exact one_ne_zero
  let A₀ : Matrix (Fin (m + 1)) (Fin (m + 1)) Fld := M * Matrix.diagonal e
  have hAdet : A₀.det = 1 := by
    change (M * Matrix.diagonal e).det = 1
    rw [Matrix.det_mul, Matrix.det_diagonal]
    have hprod : (∏ k : Fin (m + 1), e k) = d⁻¹ := by
      rw [Finset.prod_eq_single (0 : Fin (m + 1))]
      · simp [e]
      · intro k _ hk
        simp only [e]
        rw [if_neg]
        intro h0
        exact hk (Fin.ext h0)
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    rw [hprod]
    change M.det * M.det⁻¹ = 1
    exact mul_inv_cancel₀ hMdet
  let Asl : SpecialLinearGroup (Fin (m + 1)) Fld := ⟨A₀, hAdet⟩
  refine ⟨Asl, ?_⟩
  apply FlagK.ext
  intro j
  change (flagMap (glLin (SpecialLinearGroup.toGL Asl)) (stdFlag Fld (m + 1))).E j = E.E j
  rw [flagMap_E, hmbSF_glLin_toGL_mulVec Asl]
  change (Vsub (K := Fld) (m + 1) j).map (Matrix.mulVecLin A₀) = E.E j
  by_cases hj : j ≤ m + 1
  · rw [hmbSF_Vsub_eq_flagSpace, LinearFlag.flagSpace, Submodule.map_span, ← Set.image_comp]
    have hfun : (⇑(Matrix.mulVecLin A₀) ∘
        fun k : Fin (m + 1) => (Pi.single k 1 : Fin (m + 1) → Fld)) =
        fun k => e k • b k := by
      funext k
      rw [Function.comp_apply, Matrix.mulVecLin_apply]
      change (M * Matrix.diagonal e) *ᵥ (Pi.single k 1 : Fin (m + 1) → Fld) = e k • b k
      rw [← mulVec_mulVec, Matrix.diagonal_mulVec_single]
      rw [show (Pi.single k (e k * 1) : Fin (m + 1) → Fld) = e k • Pi.single k 1 by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]]
      rw [mulVec_smul, Matrix.mulVec_single_one, hMcol k]
    rw [hfun, hmbSF_span_image_smul e he b {k | k.val < j}]
    exact (hE j hj).symm
  · have hjn : m + 1 ≤ j := by omega
    rw [hmbSF_Vsub_eq_top hjn, E.top j hjn, Submodule.map_top, LinearMap.range_eq_top]
    exact (glLin (SpecialLinearGroup.toGL Asl)).surjective

theorem flagAct_stdFlag_eq_iff (A : SpecialLinearGroup (Fin (m + 1)) Fld) :
    flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1)) = stdFlag Fld (m + 1) ↔
      A ∈ LinearFlag.upperTriangular (m + 1) Fld := by
  constructor
  · intro h i j hij
    have hle : (j : ℕ) + 1 ≤ (i : ℕ) := by rw [Fin.lt_def] at hij; omega
    have hmem0 : (Pi.single j 1 : Fin (m + 1) → Fld) ∈
        Vsub (K := Fld) (m + 1) ((j : ℕ) + 1) := by
      rw [hmbSF_Vsub_eq_flagSpace]
      exact Submodule.subset_span ⟨j, by simp, rfl⟩
    have hmem1' : (glLin (SpecialLinearGroup.toGL A)).toLinearMap (Pi.single j 1) ∈
        ((stdFlag Fld (m + 1)).E ((j : ℕ) + 1)).map
          (glLin (SpecialLinearGroup.toGL A)).toLinearMap :=
      Submodule.mem_map_of_mem hmem0
    have hmem1 : (glLin (SpecialLinearGroup.toGL A)).toLinearMap (Pi.single j 1) ∈
        (flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1))).E ((j : ℕ) + 1) := by
      rwa [flagAct, flagMap_E]
    rw [h] at hmem1
    have hcoord : (glLin (SpecialLinearGroup.toGL A)).toLinearMap (Pi.single j 1) i = 0 :=
      hmem1 i hle
    change (glLin (SpecialLinearGroup.toGL A) (Pi.single j 1)) i = 0 at hcoord
    rw [glLin_apply, SpecialLinearGroup.coe_GL_coe_matrix, Matrix.mulVec_single_one,
      Matrix.col_apply] at hcoord
    exact hcoord
  · intro hA
    refine flagAct_stdFlag (SpecialLinearGroup.toGL A) ?_
    rw [SpecialLinearGroup.coe_GL_coe_matrix]
    exact LinearFlag.mem_upperTriangular_iff_isUpperTriangular.mp hA

theorem flagδ_flagAct (g : GL (Fin (m + 1)) Fld) (E F : FlagK Fld (m + 1)) :
    flagδ m (flagAct g E) (flagAct g F) = flagδ m E F := by
  have hpos : HasPos (flagAct g E) (flagAct g F) (relPos E F) := by
    intro i j hi hj
    rw [rk]
    have hE : (flagAct g E).E i = (E.E i).map (glLin g).toLinearMap := by
      rw [flagAct, flagMap_E]
    have hF : (flagAct g F).E j = (F.E j).map (glLin g).toLinearMap := by
      rw [flagAct, flagMap_E]
    rw [hE, hF, ← Submodule.map_inf _ (glLin g).injective,
      LinearEquiv.finrank_map_eq (glLin g) (E.E i ⊓ F.E j)]
    exact hasPos_relPos E F i j hi hj
  rw [flagδ, flagδ, (hasPos_iff).mp hpos]

private lemma hmbSF_flagδ_flagAct_left_upper (b : SpecialLinearGroup (Fin (m + 1)) Fld)
    (hb : b ∈ LinearFlag.upperTriangular (m + 1) Fld) (X : FlagK Fld (m + 1)) :
    flagδ m (stdFlag Fld (m + 1)) (flagAct (SpecialLinearGroup.toGL b) X) =
      flagδ m (stdFlag Fld (m + 1)) X := by
  have hfix : flagAct ((SpecialLinearGroup.toGL b)⁻¹) (stdFlag Fld (m + 1)) =
      stdFlag Fld (m + 1) := by
    rw [← map_inv]
    exact (flagAct_stdFlag_eq_iff b⁻¹).mpr ((LinearFlag.upperTriangular (m + 1) Fld).inv_mem hb)
  have hcancel : flagAct ((SpecialLinearGroup.toGL b)⁻¹) (flagAct (SpecialLinearGroup.toGL b) X) =
      X := by
    rw [← flagAct_mul, ← map_inv, ← map_mul, inv_mul_cancel, map_one, flagAct_one]
  have h := flagδ_flagAct ((SpecialLinearGroup.toGL b)⁻¹) (stdFlag Fld (m + 1))
    (flagAct (SpecialLinearGroup.toGL b) X)
  rw [hfix, hcancel] at h
  exact h.symm

theorem flagδ_stdFlag_eq_iff (A : SpecialLinearGroup (Fin (m + 1)) Fld)
    (w : Equiv.Perm (Fin (m + 1))) :
    flagδ m (stdFlag Fld (m + 1)) (flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1))) = w ↔
      A ∈ LinearFlag.bruhatCell w := by
  have hback : ∀ (A : SpecialLinearGroup (Fin (m + 1)) Fld) (w : Equiv.Perm (Fin (m + 1))),
      A ∈ LinearFlag.bruhatCell w →
      flagδ m (stdFlag Fld (m + 1))
        (flagAct (SpecialLinearGroup.toGL A) (stdFlag Fld (m + 1))) = w := by
    intro A w hA
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := LinearFlag.mem_bruhatCell.mp hA
    have hb₂fix : flagAct (SpecialLinearGroup.toGL b₂) (stdFlag Fld (m + 1)) =
        stdFlag Fld (m + 1) :=
      (flagAct_stdFlag_eq_iff b₂).mpr hb₂
    rw [show (b₁ * LinearFlag.signedPermutation (m + 1) Fld w * b₂ :
          SpecialLinearGroup (Fin (m + 1)) Fld) =
        b₁ * (LinearFlag.signedPermutation (m + 1) Fld w * b₂) from mul_assoc _ _ _,
      map_mul, map_mul, flagAct_mul, flagAct_mul, hb₂fix]
    rw [hmbSF_flagδ_flagAct_left_upper b₁ hb₁
      (flagAct (SpecialLinearGroup.toGL (LinearFlag.signedPermutation (m + 1) Fld w))
        (stdFlag Fld (m + 1)))]
    exact hmbSF_flagδ_stdFlag_signedPermutation w
  constructor
  · intro h
    obtain ⟨w', hw'⟩ := LinearFlag.exists_mem_bruhatCell A
    rw [hback A w' hw'] at h
    rw [h] at hw'
    exact hw'
  · exact hback A w

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
