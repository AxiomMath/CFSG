module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelPSL
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSLAux

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
open Matrix

private lemma tcPSL_embedMat_scalar_ne {m r r' : ℕ} {F : Type} [Field F]
    {eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F} (hPP : P * Pinv = 1)
    (hr : 0 < r) (hr' : 0 < r') {c ζ : F} (hc : c ≠ 1)
    (h : bmPSL_embedMat eidx P Pinv (Matrix.scalar (Fin r) c) = Matrix.scalar (Fin (m + 1)) ζ) :
    False := by
  set Rb : Matrix (Fin (m + 1)) (Fin (m + 1)) F := Matrix.reindex eidx eidx
    (Matrix.fromBlocks (Matrix.scalar (Fin r) c) (0 : Matrix (Fin r) (Fin r') F)
      (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F)) with hRb
  have hembed : bmPSL_embedMat eidx P Pinv (Matrix.scalar (Fin r) c) = Pinv * Rb * P := rfl
  rw [hembed] at h
  have hRb' : Rb = Matrix.scalar (Fin (m + 1)) ζ := by
    calc Rb = (P * Pinv) * Rb * (P * Pinv) := by rw [hPP]; simp
      _ = P * (Pinv * Rb * P) * Pinv := by noncomm_ring
      _ = P * Matrix.scalar (Fin (m + 1)) ζ * Pinv := by rw [h]
      _ = Matrix.scalar (Fin (m + 1)) ζ * (P * Pinv) := by
          rw [← (Matrix.scalar_commute ζ (fun r => Commute.all _ r) P).eq]; noncomm_ring
      _ = Matrix.scalar (Fin (m + 1)) ζ := by rw [hPP, mul_one]
  have e1 := congrFun (congrFun hRb' (eidx (Sum.inr ⟨0, hr'⟩))) (eidx (Sum.inr ⟨0, hr'⟩))
  have e2 := congrFun (congrFun hRb' (eidx (Sum.inl ⟨0, hr⟩))) (eidx (Sum.inl ⟨0, hr⟩))
  simp [hRb, Matrix.reindex_apply, Matrix.scalar_apply,
    Matrix.fromBlocks] at e1 e2
  apply hc
  first | exact e2.symm.trans e1.symm | exact e2.trans e1 | exact e2.trans e1.symm

private lemma tcPSL_conj_embedMat {m r r' : ℕ} {F : Type} [Field F]
    {eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F} (hPP : P * Pinv = 1)
    (hPinvP : Pinv * P = 1)
    {g : Matrix (Fin (m + 1)) (Fin (m + 1)) F} {xg : Matrix (Fin r) (Fin r) F}
    {yg : Matrix (Fin r') (Fin r') F}
    (hxy : P * g * Pinv = Matrix.reindex eidx eidx (Matrix.fromBlocks xg 0 0 yg))
    (hx : IsUnit xg.det) (x : Matrix (Fin r) (Fin r) F) :
    g * bmPSL_embedMat eidx P Pinv x = bmPSL_embedMat eidx P Pinv (xg * x * xg⁻¹) * g := by
  have hg : g = Pinv * Matrix.reindex eidx eidx (Matrix.fromBlocks xg 0 0 yg) * P := by
    rw [← hxy]
    calc g = (Pinv * P) * g * (Pinv * P) := by rw [hPinvP]; simp
      _ = Pinv * (P * g * Pinv) * P := by noncomm_ring
  have hblock : Matrix.fromBlocks xg (0 : Matrix (Fin r) (Fin r') F)
      (0 : Matrix (Fin r') (Fin r) F) yg *
        Matrix.fromBlocks x (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
          (1 : Matrix (Fin r') (Fin r') F) =
      Matrix.fromBlocks (xg * x * xg⁻¹) (0 : Matrix (Fin r) (Fin r') F)
        (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F) *
        Matrix.fromBlocks xg (0 : Matrix (Fin r) (Fin r') F)
          (0 : Matrix (Fin r') (Fin r) F) yg := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, mul_one, one_mul]
    congr 1
    rw [mul_assoc (xg * x), Matrix.nonsing_inv_mul _ hx, mul_one]
  have hre : Matrix.reindex eidx eidx
      (Matrix.fromBlocks xg (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F) yg) *
        Matrix.reindex eidx eidx (Matrix.fromBlocks x (0 : Matrix (Fin r) (Fin r') F)
          (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F)) =
      Matrix.reindex eidx eidx (Matrix.fromBlocks (xg * x * xg⁻¹) (0 : Matrix (Fin r) (Fin r') F)
        (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F)) *
        Matrix.reindex eidx eidx
          (Matrix.fromBlocks xg (0 : Matrix (Fin r) (Fin r') F)
            (0 : Matrix (Fin r') (Fin r) F) yg) := by
    change (Matrix.reindexAlgEquiv F F eidx) _ * (Matrix.reindexAlgEquiv F F eidx) _ =
      (Matrix.reindexAlgEquiv F F eidx) _ * (Matrix.reindexAlgEquiv F F eidx) _
    rw [← map_mul, ← map_mul, hblock]
  unfold bmPSL_embedMat
  rw [hg]
  calc Pinv * Matrix.reindex eidx eidx (Matrix.fromBlocks xg 0 0 yg) * P *
        (Pinv * Matrix.reindex eidx eidx (Matrix.fromBlocks x 0 0 1) * P)
      = Pinv * (Matrix.reindex eidx eidx (Matrix.fromBlocks xg 0 0 yg) *
          Matrix.reindex eidx eidx (Matrix.fromBlocks x 0 0 1)) * P := by
        calc _ = Pinv * Matrix.reindex eidx eidx (Matrix.fromBlocks xg 0 0 yg) * (P * Pinv) *
              Matrix.reindex eidx eidx (Matrix.fromBlocks x 0 0 1) * P := by noncomm_ring
          _ = _ := by rw [hPP]; noncomm_ring
    _ = Pinv * (Matrix.reindex eidx eidx (Matrix.fromBlocks (xg * x * xg⁻¹) 0 0 1) *
          Matrix.reindex eidx eidx (Matrix.fromBlocks xg 0 0 yg)) * P := by rw [hre]
    _ = Pinv * Matrix.reindex eidx eidx (Matrix.fromBlocks (xg * x * xg⁻¹) 0 0 1) * P *
        (Pinv * Matrix.reindex eidx eidx (Matrix.fromBlocks xg 0 0 yg) * P) := by
        calc _ = Pinv * Matrix.reindex eidx eidx (Matrix.fromBlocks (xg * x * xg⁻¹) 0 0 1) *
              (P * Pinv) * Matrix.reindex eidx eidx (Matrix.fromBlocks xg 0 0 yg) * P := by
              rw [hPP]; noncomm_ring
          _ = _ := by noncomm_ring

private lemma tcPSL_mul_idem_of_scalar {m r r' : ℕ} {F : Type} [Field F]
    {eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F} (hPP : P * Pinv = 1)
    (hPinvP : Pinv * P = 1) {e D : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hconv : Pinv * D * P = e)
    (hD : D = Matrix.reindex eidx eidx
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F) (0 : Matrix (Fin r) (Fin r') F)
        (0 : Matrix (Fin r') (Fin r) F) (0 : Matrix (Fin r') (Fin r') F)))
    {g : Matrix (Fin (m + 1)) (Fin (m + 1)) F} {yg : Matrix (Fin r') (Fin r') F} (c : F)
    (hxy : P * g * Pinv = Matrix.reindex eidx eidx
      (Matrix.fromBlocks (Matrix.scalar (Fin r) c) 0 0 yg)) :
    g * e = c • e := by
  have hg : g = Pinv * Matrix.reindex eidx eidx
      (Matrix.fromBlocks (Matrix.scalar (Fin r) c) 0 0 yg) * P := by
    rw [← hxy]
    calc g = (Pinv * P) * g * (Pinv * P) := by rw [hPinvP]; simp
      _ = Pinv * (P * g * Pinv) * P := by noncomm_ring
  have hblock : Matrix.fromBlocks (Matrix.scalar (Fin r) c) (0 : Matrix (Fin r) (Fin r') F)
      (0 : Matrix (Fin r') (Fin r) F) yg *
        Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F) (0 : Matrix (Fin r) (Fin r') F)
          (0 : Matrix (Fin r') (Fin r) F) (0 : Matrix (Fin r') (Fin r') F) =
      c • Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F) (0 : Matrix (Fin r) (Fin r') F)
          (0 : Matrix (Fin r') (Fin r) F) (0 : Matrix (Fin r') (Fin r') F) := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, mul_one, smul_zero]
    congr 1
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hre : Matrix.reindex eidx eidx
      (Matrix.fromBlocks (Matrix.scalar (Fin r) c) (0 : Matrix (Fin r) (Fin r') F)
        (0 : Matrix (Fin r') (Fin r) F) yg) * D = c • D := by
    rw [hD]
    change (Matrix.reindexAlgEquiv F F eidx) _ * (Matrix.reindexAlgEquiv F F eidx) _ =
      c • (Matrix.reindexAlgEquiv F F eidx) _
    rw [← map_mul, hblock, map_smul]
  rw [← hconv, hg]
  calc Pinv * Matrix.reindex eidx eidx (Matrix.fromBlocks (Matrix.scalar (Fin r) c) 0 0 yg) * P *
        (Pinv * D * P)
      = Pinv * (Matrix.reindex eidx eidx
          (Matrix.fromBlocks (Matrix.scalar (Fin r) c) 0 0 yg) * D) * P := by
        calc _ = Pinv * Matrix.reindex eidx eidx
              (Matrix.fromBlocks (Matrix.scalar (Fin r) c) 0 0 yg) * (P * Pinv) * D * P := by
              noncomm_ring
          _ = _ := by rw [hPP]; noncomm_ring
    _ = Pinv * (c • D) * P := by rw [hre]
    _ = c • (Pinv * D * P) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]

theorem exists_blockEmbedding_PSL {m f : ℕ} (s : GL (Fin (m + 1)) (GaloisField 2 f))
    (ε : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))
    (hidem : IsIdempotentElem ε) (hne : ε ≠ 0)
    (hεA : ε ∈ Algebra.adjoin (GaloisField 2 f)
      ({(s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))} :
        Set (Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))))
    (hsc : ∀ a ∈ Algebra.adjoin (GaloisField 2 f)
      ({(s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))} :
        Set (Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))),
      ∃ c : GaloisField 2 f, a * ε = c • ε) :
    ∃ (m' : ℕ) (β : Matrix.SpecialLinearGroup (Fin (m' + 1)) (GaloisField 2 f) →*
        Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)),
      m' + 1 = ε.rank ∧ (ε ≠ 1 → m' + 1 < m + 1) ∧ Function.Injective β ∧
      β.range = glBlockCentralizer Matrix.SpecialLinearGroup.toGL
        ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 f))) ε ∧
      (∀ y, β y ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) →
        y ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m' + 1)) (GaloisField 2 f))) ∧
      (ε ≠ 1 → ∀ (z : Matrix.SpecialLinearGroup (Fin (m' + 1)) (GaloisField 2 f))
        (c : GaloisField 2 f), c ≠ 1 →
        (z : Matrix (Fin (m' + 1)) (Fin (m' + 1)) (GaloisField 2 f)) =
          Matrix.scalar (Fin (m' + 1)) c →
        β z ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) ∧
      (∀ g : GL (Fin (m + 1)) (GaloisField 2 f), g * s = s * g →
        ∃ A : GL (Fin (m' + 1)) (GaloisField 2 f),
          (∀ x, g * Matrix.SpecialLinearGroup.toGL (β x) * g⁻¹ =
            Matrix.SpecialLinearGroup.toGL (β (InnerDiagA.conjSL A x))) ∧
          (∀ c : GaloisField 2 f,
            (A : Matrix (Fin (m' + 1)) (Fin (m' + 1)) (GaloisField 2 f)) =
              Matrix.scalar (Fin (m' + 1)) c →
            (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * ε = c • ε)) := by
  classical
  obtain ⟨r, r', eidx, P, Pinv, hPP, hPinvP, hconv, hr, hr', hrpos⟩ := bmPSL_exists_conj_diag hidem
  have hr0 : 0 < r := hrpos hne
  obtain ⟨m', rfl⟩ : ∃ m', r = m' + 1 := ⟨r - 1, by omega⟩
  have hS : ∀ s₁ ∈ ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 f))),
      ∀ s₂ ∈ ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 f))), Commute s₁ s₂ := by
    intro s₁ h₁ s₂ h₂
    rw [Set.mem_singleton_iff.mp h₁, Set.mem_singleton_iff.mp h₂]
  have hA : Algebra.adjoin (GaloisField 2 f)
      (Units.val '' ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 f)))) =
      Algebra.adjoin (GaloisField 2 f)
        ({(s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))} :
          Set (Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))) := by
    rw [Set.image_singleton]
  obtain ⟨hprim, hdeg1⟩ := TableCRes.isPrimIdemIn_of_smul_block
    (A := Algebra.adjoin (GaloisField 2 f)
      ({(s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))} :
        Set (Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)))) hεA hidem hne hsc
  have he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f)
      (Units.val '' ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 f))))) ε := by
    rw [hA]; exact hprim
  have hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f)
      (Units.val '' ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 f))))) ε < 2 := by
    rw [hA, hdeg1]; norm_num
  set D : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f) :=
    Matrix.reindex eidx eidx
      (Matrix.fromBlocks (1 : Matrix (Fin (m' + 1)) (Fin (m' + 1)) (GaloisField 2 f))
        (0 : Matrix (Fin (m' + 1)) (Fin r') (GaloisField 2 f))
        (0 : Matrix (Fin r') (Fin (m' + 1)) (GaloisField 2 f))
        (0 : Matrix (Fin r') (Fin r') (GaloisField 2 f))) with hDdef
  have hD : D = Matrix.reindex eidx eidx
      (Matrix.fromBlocks (1 : Matrix (Fin (m' + 1)) (Fin (m' + 1)) (GaloisField 2 f))
        (0 : Matrix (Fin (m' + 1)) (Fin r') (GaloisField 2 f))
        (0 : Matrix (Fin r') (Fin (m' + 1)) (GaloisField 2 f))
        (0 : Matrix (Fin r') (Fin r') (GaloisField 2 f))) := rfl
  have hr'pos : ε ≠ 1 → 0 < r' := by
    intro hε1
    by_contra hlt
    have hr'0 : r' = 0 := by omega
    subst hr'0
    apply hε1
    have hD1 : D = 1 := by
      rw [hDdef]
      have h1 : Matrix.fromBlocks (1 : Matrix (Fin (m' + 1)) (Fin (m' + 1)) (GaloisField 2 f))
          (0 : Matrix (Fin (m' + 1)) (Fin 0) (GaloisField 2 f))
          (0 : Matrix (Fin 0) (Fin (m' + 1)) (GaloisField 2 f))
          (0 : Matrix (Fin 0) (Fin 0) (GaloisField 2 f)) = 1 := by
        ext i j
        rcases i with i | i
        · rcases j with j | j
          · simp [Matrix.fromBlocks, Matrix.one_apply]
          · exact j.elim0
        · exact i.elim0
      rw [h1]
      simp
    rw [← hconv, hD1, Matrix.mul_one, hPinvP]
  refine ⟨m', bmPSL_embedHom eidx P Pinv hPP hPinvP, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]
    rfl
  · intro hε1
    have := hr'pos hε1
    omega
  · exact bmPSL_embedHom_injective (hPP := hPP) (hPinvP := hPinvP)
  · exact bmPSL_embedHom_range_eq hS he hdeg hPP hPinvP hconv hD
  · intro y hy
    exact bmPSL_center_embed hy
  · intro hε1 z c hc hzc hcen
    obtain ⟨ζ, -, hζ⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
    refine tcPSL_embedMat_scalar_ne (eidx := eidx) hPP hr0 (hr'pos hε1) hc (ζ := ζ) ?_
    rw [← hzc]
    exact hζ.symm
  · intro g hgs
    have hgε : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * ε =
        ε * (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) := by
      have hgs' : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) *
          (s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) =
          (s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) *
            (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) := congrArg Units.val hgs
      have hle : Algebra.adjoin (GaloisField 2 f)
          ({(s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))} :
            Set (Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))) ≤
          Subalgebra.centralizer (GaloisField 2 f)
            ({(g : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))} :
              Set (Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))) := by
        apply Algebra.adjoin_le
        rw [Set.singleton_subset_iff, SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff.mp hx]
        exact hgs'
      have hmem := hle hεA
      rw [Subalgebra.mem_centralizer_iff] at hmem
      exact hmem _ rfl
    obtain ⟨xg, yg, hxy⟩ := bmPSL_block_diag_comm eidx hPP hPinvP hconv hD hgε
    have hdetg : IsUnit (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
    have hdetR : (Matrix.reindex eidx eidx (Matrix.fromBlocks xg 0 0 yg)).det =
        xg.det * yg.det := by
      rw [bmPSL_det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
    have hdetxy : (P * (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * Pinv).det =
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)).det := by
      rw [Matrix.det_mul, Matrix.det_mul, mul_comm P.det, mul_assoc, ← Matrix.det_mul, hPP,
        Matrix.det_one, mul_one]
    have hdetxg : xg.det ≠ 0 := by
      intro h0
      have : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)).det = 0 := by
        rw [← hdetxy, hxy, hdetR, h0, zero_mul]
      exact hdetg.ne_zero this
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero xg hdetxg, ?_, ?_⟩
    · intro x
      apply Units.ext
      have hAcoe : ((Matrix.GeneralLinearGroup.mkOfDetNeZero xg hdetxg : GL (Fin (m' + 1))
          (GaloisField 2 f)) : Matrix (Fin (m' + 1)) (Fin (m' + 1)) (GaloisField 2 f)) = xg :=
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero xg hdetxg
      have hconj := tcPSL_conj_embedMat hPP hPinvP hxy (isUnit_iff_ne_zero.mpr hdetxg)
        (x : Matrix (Fin (m' + 1)) (Fin (m' + 1)) (GaloisField 2 f))
      have hc1 := InnerDiagA.coe_conjSL (Matrix.GeneralLinearGroup.mkOfDetNeZero xg hdetxg) x
      have hinv : (((Matrix.GeneralLinearGroup.mkOfDetNeZero xg hdetxg)⁻¹ : GL (Fin (m' + 1))
          (GaloisField 2 f)) : Matrix (Fin (m' + 1)) (Fin (m' + 1)) (GaloisField 2 f)) = xg⁻¹ := by
        rw [Matrix.GeneralLinearGroup.coe_inv, hAcoe]
      rw [hAcoe, hinv] at hc1
      have hgg : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) *
          ((g⁻¹ : GL (Fin (m + 1)) (GaloisField 2 f)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      show (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) *
          bmPSL_embedMat eidx P Pinv
            (x : Matrix (Fin (m' + 1)) (Fin (m' + 1)) (GaloisField 2 f)) *
          ((g⁻¹ : GL (Fin (m + 1)) (GaloisField 2 f)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) =
        bmPSL_embedMat eidx P Pinv
          (((InnerDiagA.conjSL (Matrix.GeneralLinearGroup.mkOfDetNeZero xg hdetxg) x :
            Matrix.SpecialLinearGroup (Fin (m' + 1)) (GaloisField 2 f)) :
            Matrix (Fin (m' + 1)) (Fin (m' + 1)) (GaloisField 2 f)))
      rw [hc1]
      calc (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) *
            bmPSL_embedMat eidx P Pinv
              (x : Matrix (Fin (m' + 1)) (Fin (m' + 1)) (GaloisField 2 f)) *
            ((g⁻¹ : GL (Fin (m + 1)) (GaloisField 2 f)) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))
          = (bmPSL_embedMat eidx P Pinv (xg * (x : Matrix (Fin (m' + 1)) (Fin (m' + 1))
              (GaloisField 2 f)) * xg⁻¹) *
              (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))) *
            ((g⁻¹ : GL (Fin (m + 1)) (GaloisField 2 f)) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) := by rw [hconj]
        _ = bmPSL_embedMat eidx P Pinv (xg * (x : Matrix (Fin (m' + 1)) (Fin (m' + 1))
              (GaloisField 2 f)) * xg⁻¹) := by rw [mul_assoc, hgg, mul_one]
    · intro c hc
      have hxgc : xg = Matrix.scalar (Fin (m' + 1)) c := by
        rw [← hc]
        exact (Matrix.GeneralLinearGroup.val_mkOfDetNeZero xg hdetxg).symm
      subst hxgc
      exact tcPSL_mul_idem_of_scalar hPP hPinvP hconv hD _ hxy

end CFSG.StandardType.ClassicalPosition
