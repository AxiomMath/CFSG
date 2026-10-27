module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddU3AutFixed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3AutClass

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.U3

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.QuasithinUnique.Ch1
open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear (isometrySL mem_isometrySL)

variable {p : ℕ} {K : Type} [Field K]

theorem mem_range_of_commute (h : UnitaryFieldData p 1 K) {A : GL (HypIndex 1 1) K} {b : Kˣ}
    {Hm : Matrix (HypIndex 1 1) (Fin (2 * 1 + 1)) K}
    {Wm : Matrix (Fin (2 * 1 + 1)) (HypIndex 1 1) K}
    {C₀ : Matrix (Fin (2 * 1 + 1)) (Fin (2 * 1 + 1)) K}
    {R : Matrix (Fin (2 * 1 + 1)) (Fin (2 * 1 + 1)) h.fixedField} {s : K} (hs0 : s ≠ 0)
    (hHW : Hm * Wm = 1) (hWH : Wm * Hm = 1) (hW : IsGramHypTransport h C₀ Wm)
    (hRC : R.map h.fixedField.subtype = s • C₀) (hgramInv : gramHypInv h C₀ Wm = Hm)
    (hAH : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) * Hm.map h.bar = ((b : K)⁻¹) • Hm)
    (g : hypSU h 1 1)
    (hg : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
        ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map h.bar =
      ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
        (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) :
    hypProj h 1 1 g ∈ ((gramHypProjEquiv h C₀ hW).toMonoidHom.comp
      ((QuotientGroup.mk' _).comp (isometryToGramSU h hs0 hRC))).range := by
  have hWA : Wm * (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      ((b : K)⁻¹) • Wm.map h.bar := by
    have h1 : Wm * (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) * Hm.map h.bar =
        ((b : K)⁻¹) • (1 : Matrix (Fin (2 * 1 + 1)) (Fin (2 * 1 + 1)) K) := by
      rw [Matrix.mul_assoc, hAH, Matrix.mul_smul, hWH]
    have h3 : Hm.map h.bar * Wm.map h.bar = 1 := by
      rw [← Matrix.map_mul, hHW, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]
    calc Wm * (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K)
        = Wm * (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) * (Hm.map h.bar * Wm.map h.bar) := by
          rw [h3, Matrix.mul_one]
      _ = ((b : K)⁻¹) • Wm.map h.bar := by
          rw [← Matrix.mul_assoc, h1, Matrix.smul_mul, Matrix.one_mul]
  have hWb : Wm.map h.bar = (b : K) • (Wm * (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) := by
    rw [hWA, smul_smul, mul_inv_cancel₀ b.ne_zero, one_smul]
  set G : gramSU h C₀ := (gramHypEquiv h C₀ hW).symm g with hGdef
  have hGm : ((G : GL (Fin (2 * 1 + 1)) K) : Matrix (Fin (2 * 1 + 1)) (Fin (2 * 1 + 1)) K) =
      Wm * ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) * Hm := by
    change Wm * ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
      gramHypInv h C₀ Wm = _
    rw [hgramInv]
  have hbarG : ((G : GL (Fin (2 * 1 + 1)) K) :
      Matrix (Fin (2 * 1 + 1)) (Fin (2 * 1 + 1)) K).map h.bar =
      ((G : GL (Fin (2 * 1 + 1)) K) : Matrix (Fin (2 * 1 + 1)) (Fin (2 * 1 + 1)) K) := by
    rw [hGm, Matrix.map_mul, Matrix.map_mul, hWb]
    calc ((b : K) • (Wm * (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K))) *
          ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map h.bar *
            Hm.map h.bar
        = (b : K) • (Wm * ((A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
            ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map h.bar) *
              Hm.map h.bar) := by
          rw [Matrix.smul_mul, Matrix.smul_mul]
          congr 1
          simp only [Matrix.mul_assoc]
      _ = (b : K) • (Wm * (((g : GL (HypIndex 1 1) K) :
            Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
              (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) * Hm.map h.bar) := by rw [hg]
      _ = (b : K) • (Wm * ((g : GL (HypIndex 1 1) K) :
            Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
              ((A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) * Hm.map h.bar)) := by
          congr 1
          simp only [Matrix.mul_assoc]
      _ = Wm * ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) * Hm := by
          rw [hAH, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ b.ne_zero, one_smul]
  let Gf : Matrix (Fin (2 * 1 + 1)) (Fin (2 * 1 + 1)) h.fixedField :=
    Matrix.of fun i j => ⟨((G : GL (Fin (2 * 1 + 1)) K) :
      Matrix (Fin (2 * 1 + 1)) (Fin (2 * 1 + 1)) K) i j,
        h.mem_fixedField.mpr (congrFun (congrFun hbarG i) j)⟩
  have hGfmap : Gf.map h.fixedField.subtype =
      ((G : GL (Fin (2 * 1 + 1)) K) : Matrix (Fin (2 * 1 + 1)) (Fin (2 * 1 + 1)) K) :=
    Matrix.ext fun i j => rfl
  have hdetGf : Gf.det = 1 := by
    apply h.fixedField.subtype.injective
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hGfmap, map_one]
    exact G.2.2
  have hGC : ((G : GL (Fin (2 * 1 + 1)) K) : Matrix (Fin (2 * 1 + 1)) (Fin (2 * 1 + 1)) K)ᵀ *
      C₀ * ((G : GL (Fin (2 * 1 + 1)) K) : Matrix (Fin (2 * 1 + 1)) (Fin (2 * 1 + 1)) K) =
        C₀ := by
    have := G.2.1
    rwa [hbarG] at this
  have hiso : Gfᵀ * R * Gf = R := by
    apply Matrix.map_injective h.fixedField.subtype.injective
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hRC, hGfmap, Matrix.mul_smul,
      Matrix.smul_mul, hGC]
  refine ⟨⟨⟨Gf, hdetGf⟩, mem_isometrySL.mpr hiso⟩, ?_⟩
  have hiG : isometryToGramSU h hs0 hRC ⟨⟨Gf, hdetGf⟩, mem_isometrySL.mpr hiso⟩ = G :=
    Subtype.ext (Units.ext hGfmap)
  change gramHypProjEquiv h C₀ hW (QuotientGroup.mk (isometryToGramSU h hs0 hRC
    ⟨⟨Gf, hdetGf⟩, mem_isometrySL.mpr hiso⟩)) = hypProj h 1 1 g
  rw [hiG, gramHypProjEquiv_mk, hGdef, MulEquiv.apply_symm_apply]
  rfl

theorem exists_fixed_data (h : UnitaryFieldData p 1 K) (hp : p ≠ 2)
    {A : GL (HypIndex 1 1) K} (hA : A ∈ hypUnitary h 1 1) {c : K} (hc0 : c ≠ 0)
    (hAc : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map h.bar = c • 1)
    {σ : K ≃+* K} (hσ : ∀ x, σ x = h.bar x)
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex 1 1) K) ∈ semilinearSimilitudes h 1 1) :
    ∃ (R : Matrix (Fin 3) (Fin 3) h.fixedField)
      (φ : isometrySL R →* hypPSU h 1 1) (Hm : Matrix (HypIndex 1 1) (Fin 3) K)
      (Wm : Matrix (Fin 3) (HypIndex 1 1) K),
      R.det ≠ 0 ∧ Rᵀ = R ∧ Function.Injective φ ∧ Hm * Wm = 1 ∧ Wm * Hm = 1 ∧
      (∀ y, y ∈ φ.range ↔ semilinearAutHom h (le_refl 1) (le_refl 1) ⟨_, hx⟩ y = y) ∧
      ∀ g : isometrySL R, ∃ X : hypSU h 1 1, φ g = hypProj h 1 1 X ∧
        ((X : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
          Hm * ((g : SpecialLinearGroup (Fin 3) h.fixedField) :
            Matrix (Fin 3) (Fin 3) h.fixedField).map h.fixedField.subtype *
              Wm := by
  have : CharP K p := h.charP
  have : Finite K := h.finite
  obtain ⟨b, t, s, ht, hs0, hττ, hfin, B, hBs, hBnd, hBsym⟩ :=
    exists_descended_form h hp (by omega) hA hc0 hAc
  obtain ⟨Hm, Wm, C₀, R, hHW, hWH, hW, hRC, hRdet, hRsym, hcol⟩ :=
    exists_fixed_transport h hp hττ ht t.ne_zero hfin hBs hBnd hBsym
  have hR0 : R ≠ 0 := fun h0 => hRdet (by rw [h0, Matrix.det_zero])
  have hk : ringChar h.fixedField ≠ 2 := by
    rw [ringChar.eq h.fixedField p]
    exact hp
  have hRs : Rᵀ = R := by
    rcases hRsym with hs | hneg
    · exact hs
    · exfalso
      have hdet := congrArg Matrix.det hneg
      rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at hdet
      have h3 : (2 : h.fixedField) * R.det = 0 := by linear_combination hdet
      exact hRdet ((mul_eq_zero.mp h3).resolve_left (Ring.two_ne_zero hk))
  set φ : isometrySL R →* hypPSU h 1 1 := (gramHypProjEquiv h C₀ hW).toMonoidHom.comp
    ((QuotientGroup.mk' _).comp (isometryToGramSU h hs0 hRC)) with hφdef
  have hker : ((LinearFlag.proj (2 * 1 + 1) h.fixedField).comp (isometrySL R).subtype).ker =
      φ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change LinearFlag.proj _ _ (g : Matrix.SpecialLinearGroup (Fin (2 * 1 + 1)) h.fixedField) = 1 ↔
      gramHypProjEquiv h C₀ hW (QuotientGroup.mk (isometryToGramSU h hs0 hRC g)) = 1
    rw [LinearFlag.proj_eq_one_iff, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    exact mem_scalars_iff_mem_normOneScalars h hs0 hRC (by omega) hR0 g
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, ← hker, MonoidHom.ker_eq_bot_iff]
    exact soProj_injective hR0
  have hAH : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) * Hm.map h.bar = ((b : K)⁻¹) • Hm := by
    refine Matrix.ext fun a j => ?_
    have h3 := congrFun (hcol j) a
    change (b : K) * ((A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
      fun k => h.bar (Hm k j)) a = Hm a j at h3
    rw [Matrix.smul_apply, smul_eq_mul, ← h3, ← mul_assoc, inv_mul_cancel₀ b.ne_zero, one_mul]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  have hgramInv : gramHypInv h C₀ Wm = Hm := by
    calc gramHypInv h C₀ Wm = gramHypInv h C₀ Wm * (Wm * Hm) := by rw [hWH, Matrix.mul_one]
      _ = Hm := by rw [← Matrix.mul_assoc, gramHypInv_mul hW, Matrix.one_mul]
  have hmat : ∀ g : isometrySL R,
      φ g = hypProj h 1 1 (gramHypEquiv h C₀ hW (isometryToGramSU h hs0 hRC g)) ∧
      (((gramHypEquiv h C₀ hW (isometryToGramSU h hs0 hRC g) : hypSU h 1 1) :
        GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
          Hm * ((g : SpecialLinearGroup (Fin (2 * 1 + 1)) h.fixedField) :
            Matrix (Fin (2 * 1 + 1)) (Fin (2 * 1 + 1)) h.fixedField).map h.fixedField.subtype *
              Wm := by
    intro g
    refine ⟨?_, ?_⟩
    · change gramHypProjEquiv h C₀ hW (QuotientGroup.mk (isometryToGramSU h hs0 hRC g)) = _
      rw [gramHypProjEquiv_mk]
      rfl
    · rw [coe_gramHypEquiv, hgramInv, coe_isometryToGramSU]
  refine ⟨R, φ, Hm, Wm, hRdet, hRs, hφinj, hHW, hWH, fun y => ⟨?_, ?_⟩,
    fun g => ⟨_, (hmat g).1, (hmat g).2⟩⟩
  ·
    rintro ⟨g, rfl⟩
    rw [(hmat g).1, semilinearAutHom_apply]
    congr 1
    set X := gramHypEquiv h C₀ hW (isometryToGramSU h hs0 hRC g) with hX
    have hG : (((g : SpecialLinearGroup (Fin (2 * 1 + 1)) h.fixedField) :
        Matrix (Fin (2 * 1 + 1)) (Fin (2 * 1 + 1)) h.fixedField).map h.fixedField.subtype).map
          h.bar = ((g : SpecialLinearGroup (Fin (2 * 1 + 1)) h.fixedField) :
            Matrix (Fin (2 * 1 + 1)) (Fin (2 * 1 + 1)) h.fixedField).map h.fixedField.subtype :=
      Matrix.ext fun i j => h.mem_fixedField.mp ((g : SpecialLinearGroup (Fin (2 * 1 + 1))
        h.fixedField) i j).2
    have hcomm := mul_map_bar_conj_eq h hHW hWH hAH hG
    rw [← (hmat g).2] at hcomm
    have hAX : A * glAut σ (X : GL (HypIndex 1 1) K) = (X : GL (HypIndex 1 1) K) * A := by
      have hmap : ((X : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map σ =
          ((X : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map h.bar :=
        Matrix.ext fun i j => hσ _
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul, coe_glAut, hmap]
      exact hcomm
    refine Subtype.ext ?_
    change A * glAut σ (X : GL (HypIndex 1 1) K) * A⁻¹ = (X : GL (HypIndex 1 1) K)
    rw [hAX, mul_inv_cancel_right]
  ·
    intro hy
    obtain ⟨g, rfl, hg⟩ := exists_commuting_rep_of_fixed h (le_refl 1) (le_refl 1)
      (by norm_num) hσ hx hy
    exact mem_range_of_commute h hs0 hHW hWH hW hRC hgramInv hAH g hg

end CFSG.Quasithin.Vol2.Ch11.SecU1.U3
