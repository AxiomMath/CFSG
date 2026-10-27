module

public import CFSG.Quasithin.Vol2.KGNatSL3Lev

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LieType.SteinbergBR CFSG.LieType.SteinbergBR.BlockPar
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)
open scoped MatrixGroups

section Row

variable {K : Type} [Field K]

theorem vecMul_e2 (B : Matrix (Fin 3) (Fin 3) K) (j : Fin 3) :
    (![0, 0, 1] ᵥ* B) j = B 2 j := by
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three]

variable (K) in
@[expose] def stabRow2 : Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {B | ![0, 0, 1] ᵥ* (B : Matrix (Fin 3) (Fin 3) K) = ![0, 0, 1]}
  mul_mem' := fun {a b} ha hb => by
    change ![0, 0, 1] ᵥ* ((a * b : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.vecMul_vecMul]
    rw [show ![0, 0, 1] ᵥ* (a : Matrix (Fin 3) (Fin 3) K) = ![0, 0, 1] from ha]
    exact hb
  one_mem' := by
    change ![0, 0, 1] ᵥ* ((1 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  inv_mem' := fun {a} ha => by
    change ![0, 0, 1] ᵥ* ((a⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    conv_lhs => rw [← show ![0, 0, 1] ᵥ* (a : Matrix (Fin 3) (Fin 3) K) = ![0, 0, 1] from ha]
    rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

theorem mem_stabRow2 {B : SpecialLinearGroup (Fin 3) K} :
    B ∈ stabRow2 K ↔ (B : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
      (B : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 ∧ (B : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
  change ![0, 0, 1] ᵥ* (B : Matrix (Fin 3) (Fin 3) K) = ![0, 0, 1] ↔ _
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    rw [vecMul_e2] at h0 h1 h2
    exact ⟨by simpa using h0, by simpa using h1, by simpa using h2⟩
  · rintro ⟨h0, h1, h2⟩
    refine vec3_eq ?_ ?_ ?_ <;> rw [vecMul_e2] <;> simp [h0, h1, h2]

@[expose] def lev2 (B : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => B (Fin.castSucc i) (Fin.castSucc j)

omit [Field K] in
theorem lev2_apply (B : Matrix (Fin 3) (Fin 3) K) (i j : Fin 2) :
    lev2 B i j = B (Fin.castSucc i) (Fin.castSucc j) := rfl

theorem lev2_mul {A B : Matrix (Fin 3) (Fin 3) K} (b20 : B 2 0 = 0) (b21 : B 2 1 = 0) :
    lev2 (A * B) = lev2 A * lev2 B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lev2, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, b20, b21]

theorem det_lev2 {B : Matrix (Fin 3) (Fin 3) K} (h20 : B 2 0 = 0) (h21 : B 2 1 = 0)
    (h22 : B 2 2 = 1) : (lev2 B).det = B.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_three, h20, h21, h22]
  simp [lev2]

variable (K) in
@[expose] noncomputable def leviHom2 : ↥(stabRow2 K) →* SL(2, K) where
  toFun B := ⟨lev2 ((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), by
    obtain ⟨h20, h21, h22⟩ := mem_stabRow2.mp B.2
    rw [det_lev2 h20 h21 h22]
    exact (B : SpecialLinearGroup (Fin 3) K).2⟩
  map_one' := Subtype.ext (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lev2])
  map_mul' A B := by
    obtain ⟨b20, b21, -⟩ := mem_stabRow2.mp B.2
    refine Subtype.ext ?_
    change lev2 ((((A * B : ↥(stabRow2 K)) : SpecialLinearGroup (Fin 3) K)) :
      Matrix (Fin 3) (Fin 3) K) = lev2 ((A : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * lev2 ((B : SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K)
    rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, lev2_mul b20 b21]

theorem leviHom2_coe (B : ↥(stabRow2 K)) :
    ((leviHom2 K B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      lev2 ((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := rfl

@[expose] def blockSL (A : SL(2, K)) : SpecialLinearGroup (Fin 3) K :=
  ⟨!![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1], by
    have hA := A.2
    rw [Matrix.det_fin_two] at hA
    rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const]
    linear_combination hA⟩

theorem blockSL_mem (A : SL(2, K)) : blockSL A ∈ stabRow2 K :=
  mem_stabRow2.mpr ⟨rfl, rfl, rfl⟩

theorem blockSL_mulVec (A : SL(2, K)) (x : Fin 3 → K) :
    (blockSL A : Matrix (Fin 3) (Fin 3) K) *ᵥ x =
      ![A 0 0 * x 0 + A 0 1 * x 1, A 1 0 * x 0 + A 1 1 * x 1, x 2] := by
  ext i
  fin_cases i <;> simp [blockSL, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem leviHom2_surjective : Function.Surjective (leviHom2 K) := by
  intro A
  refine ⟨⟨blockSL A, blockSL_mem A⟩, Subtype.ext ?_⟩
  rw [leviHom2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem fix_of_leviHom2_eq_one {B : ↥(stabRow2 K)} (hB : leviHom2 K B = 1) :
    ((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0] ∧
      ((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0] =
        ![0, 1, 0] := by
  obtain ⟨h20, h21, -⟩ := mem_stabRow2.mp B.2
  have hl : lev2 ((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← leviHom2_coe, hB, Matrix.SpecialLinearGroup.coe_one]
  have h00 := congrFun (congrFun hl 0) 0
  have h01 := congrFun (congrFun hl 0) 1
  have h10 := congrFun (congrFun hl 1) 0
  have h11 := congrFun (congrFun hl 1) 1
  simp only [lev2_apply, Fin.castSucc_zero, Fin.castSucc_one, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h00 h01 h10 h11
  constructor
  · exact vec3_eq (by simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h00])
      (by simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10])
      (by simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h20])
  · exact vec3_eq (by simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h01])
      (by simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h11])
      (by simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h21])

theorem reindex21_apply (M : SpecialLinearGroup (Fin 2 ⊕ Fin 1) K) (i j : Fin 3) :
    (reindexSL K h21 M : Matrix (Fin 3) (Fin 3) K) i j =
      M.val ((sumEquiv h21).symm i) ((sumEquiv h21).symm j) := by
  rw [reindexSL_val]
  rfl

theorem sumEquiv21_symm : (sumEquiv h21).symm (0 : Fin 3) = Sum.inl 0 ∧
    (sumEquiv h21).symm (1 : Fin 3) = Sum.inl 1 ∧ (sumEquiv h21).symm (2 : Fin 3) = Sum.inr 0 :=
  ⟨rfl, rfl, rfl⟩

theorem mem_parJL21_iff (M : SpecialLinearGroup (Fin 2 ⊕ Fin 1) K) :
    M ∈ parJL K (Fin 2) (Fin 1) ↔ reindexSL K h21 M ∈ stabRow2 K := by
  obtain ⟨s0, s1, s2⟩ := sumEquiv21_symm
  rw [mem_parJL, mem_parQ, mem_stabRow2, reindex21_apply, reindex21_apply, reindex21_apply,
    s0, s1, s2]
  constructor
  · rintro ⟨h21', h22⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [Matrix.toBlocks₂₁] using congrFun (congrFun h21' 0) 0
    · simpa [Matrix.toBlocks₂₁] using congrFun (congrFun h21' 0) 1
    · simpa [Matrix.toBlocks₂₂] using congrFun (congrFun h22 0) 0
  · rintro ⟨e0, e1, e2⟩
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i
      fin_cases j
      · simpa [Matrix.toBlocks₂₁] using e0
      · simpa [Matrix.toBlocks₂₁] using e1
    · ext i j
      fin_cases i
      fin_cases j
      simpa [Matrix.toBlocks₂₂] using e2

end Row

section HU2

variable {K : Type} [Field K] {W : Type*} [CommGroup W]
  {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

theorem mem_perfectCore_HU2_iff [Finite K]
    (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (g : SpecialLinearGroup (Fin 3) K)
    (x : MulAut W) :
    x ∈ perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup)) ↔
      ∃ B : SpecialLinearGroup (Fin 3) K, B ∈ stabRow2 K ∧
        x = ((rho3 π (g * B * g⁻¹) : ↥H) : MulAut W) := by
  rw [← map_parQ_psiPar hf g h21, perfectCore_map _ (psiPar_injective hf g h21),
    perfectCore_parQ21 hSL]
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact ⟨reindexSL K h21 M, (mem_parJL21_iff M).mp hM, psiPar_apply π g h21 M⟩
  · rintro ⟨B, hB, rfl⟩
    refine ⟨(reindexSL K h21).symm B, (mem_parJL21_iff _).mpr ?_, ?_⟩
    · rwa [MulEquiv.apply_symm_apply]
    · rw [psiPar_apply, MulEquiv.apply_symm_apply]

variable [Finite K] [CharP K 2]

theorem levi_of_mem_pCoreOf_HU2 (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (g : SpecialLinearGroup (Fin 3) K)
    {x : MulAut W}
    (hx : x ∈ pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW
      (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup)))) :
    ∃ B : SpecialLinearGroup (Fin 3) K, B ∈ stabRow2 K ∧
      (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0] ∧
      (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0] = ![0, 1, 0] ∧
      x = ((rho3 π (g * B * g⁻¹) : ↥H) : MulAut W) := by
  set L := perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup))
    with hL
  let φ : ↥(stabRow2 K) →* ↥L := MonoidHom.codRestrict
    (H.subtype.comp ((rho3 π).comp ((MulAut.conj g).toMonoidHom.comp (stabRow2 K).subtype))) L
    (fun B => (mem_perfectCore_HU2_iff hSL hf g _).mpr
      ⟨(B : SpecialLinearGroup (Fin 3) K), B.2, rfl⟩)
  have hφinj : Function.Injective φ := by
    intro B B' h
    have h1 : rho3 π (g * (B : SpecialLinearGroup (Fin 3) K) * g⁻¹) =
        rho3 π (g * (B' : SpecialLinearGroup (Fin 3) K) * g⁻¹) :=
      Subtype.ext (congrArg (fun z : ↥L => (z : MulAut W)) h)
    exact Subtype.ext (mul_left_cancel (mul_right_cancel ((rho3_bijective hf).1 h1)))
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨B, hB, rfl⟩ := (mem_perfectCore_HU2_iff hSL hf g y).mp hy
    exact ⟨⟨B, hB⟩, rfl⟩
  set e := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩ with he
  set Λ : ↥L →* SL(2, K) := (leviHom2 K).comp e.symm.toMonoidHom with hΛ
  have hΛsurj : Function.Surjective Λ := leviHom2_surjective.comp e.symm.surjective
  have hcore : CFSG.Open.pCore 2 ↥L ≤ Λ.ker := by
    rw [CFSG.pCore_eq_iSup]
    refine iSup_le fun N => iSup_le fun hN => iSup_le fun hp => ?_
    rw [← Subgroup.map_eq_bot_iff]
    have : (N.map Λ).Normal := hN.map Λ hΛsurj
    exact eq_bot_of_normal_isPGroup_SL2 (hp.map Λ)
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨h0, h1⟩ := fix_of_leviHom2_eq_one (MonoidHom.mem_ker.mp (hcore hy))
  refine ⟨e.symm y, (e.symm y).2, h0, h1, ?_⟩
  have h2 : φ (e.symm y) = y := e.apply_symm_apply y
  exact (congrArg L.subtype h2).symm

end HU2

end CFSG.Quasithin.Vol2.KGNat
