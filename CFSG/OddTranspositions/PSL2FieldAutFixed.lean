module

public import CFSG.Dihedral.Glauberman.DicksonMaxSubfield
public import CFSG.Walter.PSL2Facts.FieldAut
public import CFSG.Walter.Defs

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.GorensteinWalter CFSG.Walter CFSG.Glauberman.Dickson.MaxSubfield
open scoped MatrixGroups

noncomputable section

variable {F : Type*} [Field F]

private lemma fieldAut_eq_neg_of_sq_mem (σ : F ≃+* F) (K : Subfield F)
    (hK : ∀ x : F, x ∈ K ↔ σ x = x) (t : F) (ht_sq : t ^ 2 ∈ K) (ht_ne : t ∉ K) :
    σ t = -t := by
  have hfix : σ (t ^ 2) = t ^ 2 := (hK (t ^ 2)).mp ht_sq
  rw [map_pow] at hfix
  have hsq : σ t * σ t = t * t := by simpa [pow_two] using hfix
  rcases mul_self_eq_mul_self_iff.mp hsq with h | h
  · exact absurd ((hK t).mpr h) ht_ne
  · exact h

private lemma map_eq_smul_of_div_mem_center (τ : F →+* F)
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (h : Matrix.SpecialLinearGroup.map τ A / A ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) :
    ∃ c : F, c ^ 2 = 1 ∧
      (Matrix.SpecialLinearGroup.map τ A : Matrix (Fin 2) (Fin 2) F) =
        c • (A : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨c, hc2, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  refine ⟨c, by simpa using hc2, ?_⟩
  have hmul : (Matrix.scalar (Fin 2) c) * (A : Matrix (Fin 2) (Fin 2) F) =
      (Matrix.SpecialLinearGroup.map τ A : Matrix (Fin 2) (Fin 2) F) := by
    have h2 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
      (x : Matrix (Fin 2) (Fin 2) F))
      (div_mul_cancel (Matrix.SpecialLinearGroup.map τ A) A)
    rw [Matrix.SpecialLinearGroup.coe_mul] at h2
    rw [← hcA] at h2
    exact h2
  rw [← hmul, Matrix.smul_eq_diagonal_mul, ← Matrix.scalar_apply]

theorem fix_psl2FieldAut_eq_subfieldSubgroup
    {F : Type} [Field F] (σ : F ≃+* F) (hσ2 : σ * σ = 1)
    (K : Subfield F) (hK : ∀ x : F, x ∈ K ↔ σ x = x)
    (t : F) (ht_sq : t ^ 2 ∈ K) (ht_ne : t ∉ K) :
    {q : PSL2 F | psl2FieldAut F σ q = q} =
      (CFSG.Glauberman.Dickson.MaxSubfield.subfieldSubgroup K : Set (PSL2 F)) := by
  classical
  have hpglMap_mk : ∀ {K : Type} [Field K] {E : Type} [Field E]
      (e : K →+* E) (A : Matrix.GeneralLinearGroup (Fin 2) K),
      CFSG.Glauberman.Dickson.h826_pglMap e (Matrix.ProjGenLinGroup.mk A) =
        Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map e A) := by
    intro K _ E _ e A
    unfold CFSG.Glauberman.Dickson.h826_pglMap
    exact Matrix.ProjGenLinGroup.lift_mk _ A
  ext q
  constructor
  · intro hq
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective q
    have hmk : (QuotientGroup.mk'
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
        (Matrix.SpecialLinearGroup.map σ.toRingHom A) : PSL2 F) =
        QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) A := by
      have h : psl2FieldAut F σ (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) A) =
          QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) A := by
        simpa only [Set.mem_setOf_eq, QuotientGroup.mk'_apply] using hq
      simp only [QuotientGroup.mk'_apply] at h
      rw [psl2FieldAut_eq_psl2Map, psl2Map_mk] at h
      simpa only [QuotientGroup.mk'_apply] using h
    obtain ⟨c, hc2, hmap⟩ :=
      map_eq_smul_of_div_mem_center σ.toRingHom A
        (QuotientGroup.eq_iff_div_mem.mp hmk)
    have ht0 : t ≠ 0 := fun h => ht_ne (h ▸ K.zero_mem)
    rcases sq_eq_one_iff.mp hc2 with hc | hc
    ·
      subst c
      have hmapA : (Matrix.SpecialLinearGroup.map σ.toRingHom A :
          Matrix (Fin 2) (Fin 2) F) = (A : Matrix (Fin 2) (Fin 2) F) := by
        simpa using hmap
      have hfixed : ∀ i j, σ ((A : Matrix (Fin 2) (Fin 2) F) i j) =
          (A : Matrix (Fin 2) (Fin 2) F) i j := by
        intro i j
        have h := congrFun (congrFun hmapA i) j
        simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
          Matrix.map_apply] using h
      let M : Matrix (Fin 2) (Fin 2) K :=
        Matrix.of fun i j =>
          ⟨(A : Matrix (Fin 2) (Fin 2) F) i j, (hK _).mpr (hfixed i j)⟩
      have hMmap : M.map K.subtype = (A : Matrix (Fin 2) (Fin 2) F) := by
        ext i j
        rfl
      let A0 : Matrix.SpecialLinearGroup (Fin 2) K :=
        ⟨M, by
          apply K.subtype.injective
          rw [map_one, RingHom.map_det]
          rw [show K.subtype.mapMatrix M = M.map K.subtype from rfl, hMmap, A.2]⟩
      have hmapA0 : Matrix.SpecialLinearGroup.map K.subtype A0 = A := by
        ext i j
        rfl
      have htoGL : Matrix.SpecialLinearGroup.toGL A =
          Matrix.GeneralLinearGroup.map K.subtype
            (Matrix.SpecialLinearGroup.toGL A0) := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        have h := congrFun (congrFun (congrArg
          (fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
            (x : Matrix (Fin 2) (Fin 2) F)) hmapA0) i) j
        simpa [Matrix.GeneralLinearGroup.map_apply] using h.symm
      have hmem : Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk A) ∈
          pglImage K := by
        rw [pglImage]
        refine ⟨Matrix.ProjGenLinGroup.mk
          (Matrix.SpecialLinearGroup.toGL A0), ?_⟩
        rw [hpglMap_mk, ← htoGL, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
      exact hmem
    ·
      subst c
      have hAijσ : ∀ i j, σ ((A : Matrix (Fin 2) (Fin 2) F) i j) =
          - (A : Matrix (Fin 2) (Fin 2) F) i j := by
        intro i j
        have h := congrFun (congrFun hmap i) j
        simpa [Matrix.smul_apply, Matrix.SpecialLinearGroup.map_apply_coe,
          RingHom.mapMatrix_apply, Matrix.map_apply] using h
      have hσt : σ t = -t := fieldAut_eq_neg_of_sq_mem σ K hK t ht_sq ht_ne
      have hmem : ∀ i j, (A : Matrix (Fin 2) (Fin 2) F) i j / t ∈ K := by
        intro i j
        rw [hK]
        rw [map_div₀, hAijσ i j, hσt, neg_div_neg_eq]
      let B0 : Matrix (Fin 2) (Fin 2) K :=
        Matrix.of fun i j =>
          ⟨(A : Matrix (Fin 2) (Fin 2) F) i j / t, hmem i j⟩
      have hAeq : (A : Matrix (Fin 2) (Fin 2) F) = t • B0.map K.subtype := by
        ext i j
        simp [B0, Matrix.map_apply, Matrix.smul_apply, mul_div_cancel₀ _ ht0]
      have hdet : t ^ 2 * (B0.map K.subtype).det = 1 := by
        have h := A.2
        rw [hAeq, Matrix.det_smul] at h
        simpa using h
      have hdetCne : (B0.map K.subtype).det ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hdet
        exact zero_ne_one hdet
      have hmapdet : (B0.map K.subtype).det = K.subtype B0.det := by
        simpa using (RingHom.map_det K.subtype B0).symm
      have hdetB0 : B0.det ≠ 0 := by
        intro h0
        apply hdetCne
        rw [hmapdet, h0, map_zero]
      let B : Matrix.GeneralLinearGroup (Fin 2) K :=
        Matrix.GeneralLinearGroup.mkOfDetNeZero B0 hdetB0
      have hB : (B : Matrix (Fin 2) (Fin 2) K) = B0 := by
        simp [B]
      let u : Fˣ := (Units.mk0 t ht0)⁻¹
      have hu_val : ((u : F)) = t⁻¹ := by simp [u]
      have htu : t * (u : F) = 1 := by
        rw [hu_val, mul_inv_cancel₀ ht0]
      have hGL : Matrix.SpecialLinearGroup.toGL A *
          Matrix.GeneralLinearGroup.scalar (Fin 2) u =
          Matrix.GeneralLinearGroup.map K.subtype B := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        have hAij : (A : Matrix (Fin 2) (Fin 2) F) i j = t * K.subtype (B0 i j) := by
          rw [hAeq, Matrix.smul_apply]
          rfl
        rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
          Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.GeneralLinearGroup.map_apply,
          hB, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
        rw [hAij]
        calc t * K.subtype (B0 i j) * (u : F)
            = t * (K.subtype (B0 i j) * (u : F)) := mul_assoc _ _ _
          _ = t * ((u : F) * K.subtype (B0 i j)) := by
              rw [mul_comm (K.subtype (B0 i j)) (u : F)]
          _ = (t * (u : F)) * K.subtype (B0 i j) := (mul_assoc _ _ _).symm
          _ = 1 * K.subtype (B0 i j) := by rw [htu]
          _ = K.subtype (B0 i j) := one_mul _
      have hmk' : Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL A) =
          Matrix.ProjGenLinGroup.mk
            (Matrix.GeneralLinearGroup.map K.subtype B) :=
        (Matrix.ProjGenLinGroup.mk_eq_mk_iff).mpr ⟨u, hGL⟩
      have htoPGL : Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk A) =
          Matrix.ProjGenLinGroup.mk
            (Matrix.GeneralLinearGroup.map K.subtype B) := by
        rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
        exact hmk'
      have hmem2 : Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk A) ∈
          pglImage K := by
        rw [pglImage]
        exact ⟨Matrix.ProjGenLinGroup.mk B, by
          rw [hpglMap_mk]
          exact htoPGL.symm⟩
      exact hmem2
  · intro hq
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective q
    have htoPGLmem : Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk A) ∈
        pglImage K := hq
    rw [pglImage] at htoPGLmem
    obtain ⟨y, hy⟩ := htoPGLmem
    obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective y
    rw [hpglMap_mk, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk] at hy
    obtain ⟨u, hu⟩ := (Matrix.ProjGenLinGroup.mk_eq_mk_iff).mp hy.symm
    let Bmat : Matrix (Fin 2) (Fin 2) K := B
    let C : Matrix (Fin 2) (Fin 2) F := Bmat.map K.subtype
    let v : F := ((u⁻¹ : Fˣ) : F)
    have hu_mat : (A : Matrix (Fin 2) (Fin 2) F) *
        Matrix.scalar (Fin 2) (u : F) = C := by
      have h := congrArg (fun x : Matrix.GeneralLinearGroup (Fin 2) F =>
        (x : Matrix (Fin 2) (Fin 2) F)) hu
      simpa [Bmat, C, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.map_apply,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using h
    have hAij : ∀ i j, (A : Matrix (Fin 2) (Fin 2) F) i j = v * C i j := by
      intro i j
      have h := congrFun (congrFun hu_mat i) j
      rw [Matrix.scalar_apply, Matrix.mul_diagonal] at h
      have hAeq' : (A : Matrix (Fin 2) (Fin 2) F) i j = C i j / (u : F) := by
        rw [eq_div_iff_mul_eq (Units.ne_zero u)]
        exact h
      rw [hAeq', div_eq_mul_inv]
      dsimp [v]
      rw [mul_comm]
      simp
    have hAeqv : (A : Matrix (Fin 2) (Fin 2) F) = v • C := by
      ext i j
      rw [Matrix.smul_apply]
      exact hAij i j
    have hdetv : v * v * C.det = 1 := by
      have h := A.2
      rw [hAeqv, Matrix.det_smul] at h
      simpa [pow_two] using h
    have hdetCne : C.det ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hdetv
      exact zero_ne_one hdetv
    have hv2 : v ^ 2 = C.det⁻¹ := by
      have h := hdetv
      rw [mul_eq_one_iff_eq_inv₀ hdetCne] at h
      simpa [pow_two] using h
    have hCdet : C.det = K.subtype Bmat.det := by
      simpa [C] using (RingHom.map_det K.subtype Bmat).symm
    have hdetCmem : C.det ∈ K := by
      rw [hCdet]
      exact Bmat.det.2
    have hv2K : v ^ 2 ∈ K := by
      rw [hv2]
      exact K.inv_mem hdetCmem
    have hσv : σ v = v ∨ σ v = -v := by
      have hfix : σ (v ^ 2) = v ^ 2 := (hK (v ^ 2)).mp hv2K
      have hsq : σ v * σ v = v * v := by
        have h : (σ v) ^ 2 = v ^ 2 := by
          rw [← map_pow, hfix]
        simpa [pow_two] using h
      exact mul_self_eq_mul_self_iff.mp hsq
    have hCfixed : ∀ i j, σ (C i j) = C i j := by
      intro i j
      exact (hK (C i j)).mp (by
        change K.subtype (Bmat i j) ∈ K
        exact (Bmat i j).2)
    rcases hσv with hσv | hσv
    · have hmap : Matrix.SpecialLinearGroup.map σ.toRingHom A = A := by
        ext i j
        change σ.toRingHom ((A : Matrix (Fin 2) (Fin 2) F) i j) =
          (A : Matrix (Fin 2) (Fin 2) F) i j
        calc σ.toRingHom ((A : Matrix (Fin 2) (Fin 2) F) i j)
            = σ.toRingHom (v * C i j) := by rw [hAij i j]
          _ = σ v * σ (C i j) := map_mul _ _ _
          _ = v * C i j := by rw [hσv, hCfixed i j]
          _ = (A : Matrix (Fin 2) (Fin 2) F) i j := (hAij i j).symm
      calc psl2FieldAut F σ (QuotientGroup.mk A)
          = psl2Map σ.toRingHom (QuotientGroup.mk A) := psl2FieldAut_eq_psl2Map σ _
        _ = QuotientGroup.mk (Matrix.SpecialLinearGroup.map σ.toRingHom A) :=
            psl2Map_mk σ.toRingHom A
        _ = QuotientGroup.mk A := by rw [hmap]
    · have hmap : Matrix.SpecialLinearGroup.map σ.toRingHom A = -A := by
        ext i j
        change σ.toRingHom ((A : Matrix (Fin 2) (Fin 2) F) i j) =
          -((A : Matrix (Fin 2) (Fin 2) F) i j)
        calc σ.toRingHom ((A : Matrix (Fin 2) (Fin 2) F) i j)
            = σ.toRingHom (v * C i j) := by rw [hAij i j]
          _ = σ v * σ (C i j) := map_mul _ _ _
          _ = (-v) * C i j := by rw [hσv, hCfixed i j]
          _ = -((A : Matrix (Fin 2) (Fin 2) F) i j) := by
            rw [hAij i j]
            ring
      calc psl2FieldAut F σ (QuotientGroup.mk A)
          = psl2Map σ.toRingHom (QuotientGroup.mk A) := psl2FieldAut_eq_psl2Map σ _
        _ = QuotientGroup.mk (Matrix.SpecialLinearGroup.map σ.toRingHom A) :=
            psl2Map_mk σ.toRingHom A
        _ = QuotientGroup.mk (-A) := by rw [hmap]
        _ = QuotientGroup.mk A := by
            simpa [CFSG.PSL2Table.mk] using CFSG.PSL2Table.mk_neg A

end

end CFSG.OddTranspositions.QZ
