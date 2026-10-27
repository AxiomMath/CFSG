module

public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofBlocks
public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofProj

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228Census3Proof

open Matrix CFSG
open scoped commutatorElement

variable {K : Type} [Field K]

variable (K) in
@[expose] def symJ2 : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

theorem transpose_symJ2_mul (B : Matrix (Fin 2) (Fin 2) K) :
    Bᵀ * symJ2 K * B = B.det • symJ2 K := by
  rw [Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symJ2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[expose] def flatM (B : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  !![B 1 1, -B 1 0; -B 0 1, B 0 0]

variable (K) in
@[expose] def gramPlane : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks (symJ2 K) 0 0 (symJ2 K)

@[expose] def blkOneHom : Matrix (Fin 2) (Fin 2) K →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K where
  toFun B := fromBlocks 1 0 0 B
  map_one' := fromBlocks_one
  map_mul' B B' := by rw [fromBlocks_multiply]; simp

@[expose] noncomputable def iotaPlane : SpecialLinearGroup (Fin 2) K →* GL (Fin 2 ⊕ Fin 2) K :=
  (Units.map blkOneHom).comp SpecialLinearGroup.toGL

theorem coe_iotaPlane (B : SpecialLinearGroup (Fin 2) K) :
    ((iotaPlane B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks 1 0 0 (B : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem iotaPlane_mem (B : SpecialLinearGroup (Fin 2) K) :
    iotaPlane B ∈ gramGroup (gramPlane K) := by
  rw [mem_gramGroup, coe_iotaPlane, gramPlane, fromBlocks_transpose, fromBlocks_multiply,
    fromBlocks_multiply]
  simp [transpose_symJ2_mul, B.2]

theorem isCentData_plane (h3 : (3 : K) ≠ 0) {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1)
    (hM : M * M + M + 1 = 0) {D : GL (Fin 2 ⊕ Fin 2) K}
    (hD : (D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks M 0 0 1) :
    IsCentData (gramGroup (gramPlane K)) D iotaPlane := by
  refine ⟨iotaPlane_mem, fun B => Units.ext ?_, fun g hg h hh hgD hhD => ?_⟩
  · rw [Units.val_mul, Units.val_mul, coe_iotaPlane, hD, fromBlocks_multiply,
      fromBlocks_multiply]
    simp
  · obtain ⟨hk, hkb⟩ := commutator_eq_diag_one h3 hdet hM hD hg hh hgD hhD
    set k := ((g * h * g⁻¹ * h⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₂ with hkdef
    have hgram := mem_gramGroup.mp hk
    rw [hkb, gramPlane, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply] at hgram
    simp only [Matrix.transpose_one, Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.one_mul, Matrix.mul_one] at hgram
    obtain ⟨-, -, -, e22⟩ := Matrix.fromBlocks_inj.mp hgram
    rw [transpose_symJ2_mul] at e22
    have hkdet : k.det = 1 := by
      have := congrFun (congrFun e22 0) 1
      simpa [symJ2] using this
    refine ⟨(⟨k, hkdet⟩ : SpecialLinearGroup (Fin 2) K), Units.ext ?_⟩
    rw [hkb]
    rfl

theorem ker_mk_iotaPlane :
    (ProjGenLinGroup.mk.comp (iotaPlane (K := K))).ker = ⊥ := by
  rw [eq_bot_iff]
  intro B hB
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ProjGenLinGroup.mk_eq_one,
    GeneralLinearGroup.center_eq_range_scalar] at hB
  obtain ⟨u, hu⟩ := hB
  have e := congrArg (fun x : GL (Fin 2 ⊕ Fin 2) K => (x : Matrix (Fin 2 ⊕ Fin 2)
    (Fin 2 ⊕ Fin 2) K)) hu
  simp only [GeneralLinearGroup.coe_scalar, coe_iotaPlane] at e
  have e0 := congrFun (congrFun e (Sum.inl 0)) (Sum.inl 0)
  simp [Matrix.scalar_apply] at e0
  rw [e0, Units.val_one, map_one] at e
  rw [Subgroup.mem_bot]
  ext i j
  have := congrFun (congrFun e (Sum.inr i)) (Sum.inr j)
  simpa [Matrix.one_apply] using this.symm

variable (K) in
@[expose] def gramStd : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fromBlocks 0 1 (-1) 0

variable (K) in
@[expose] def gramTensor : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks 0 (gramS K) (-gramS K) 0

@[expose] def tensorOneHom :
    Matrix (Fin 2) (Fin 2) K →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K where
  toFun B := fromBlocks (B 0 0 • 1) (B 0 1 • 1) (B 1 0 • 1) (B 1 1 • 1)
  map_one' := by
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp
  map_mul' B B' := by
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.one_apply]

@[expose] noncomputable def iotaTensor : SpecialLinearGroup (Fin 2) K →* GL (Fin 2 ⊕ Fin 2) K :=
  (Units.map tensorOneHom).comp SpecialLinearGroup.toGL

theorem coe_iotaTensor (B : SpecialLinearGroup (Fin 2) K) :
    ((iotaTensor B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks ((B : Matrix (Fin 2) (Fin 2) K) 0 0 • 1) ((B : Matrix (Fin 2) (Fin 2) K) 0 1 • 1)
        ((B : Matrix (Fin 2) (Fin 2) K) 1 0 • 1) ((B : Matrix (Fin 2) (Fin 2) K) 1 1 • 1) :=
  rfl

theorem iotaTensor_mem (B : SpecialLinearGroup (Fin 2) K) :
    iotaTensor B ∈ gramGroup (gramTensor K) := by
  have hdet := B.2
  rw [Matrix.det_fin_two] at hdet
  rw [mem_gramGroup, coe_iotaTensor, gramTensor]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [gramS, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] <;>
    first | ring1 | linear_combination 2 * hdet | linear_combination -hdet |
      linear_combination -2 * hdet | linear_combination hdet

theorem tensor_isometry_eqs (h3 : (3 : K) ≠ 0) {k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hb : k.toBlocks₁₁ ∈ cubeAlg K ∧ k.toBlocks₁₂ ∈ cubeAlg K ∧ k.toBlocks₂₁ ∈ cubeAlg K ∧
      k.toBlocks₂₂ ∈ cubeAlg K)
    (hk : kᵀ * gramTensor K * k = gramTensor K) :
    cubeBarM k.toBlocks₁₁ * k.toBlocks₂₁ - cubeBarM k.toBlocks₂₁ * k.toBlocks₁₁ = 0 ∧
      cubeBarM k.toBlocks₁₁ * k.toBlocks₂₂ - cubeBarM k.toBlocks₂₁ * k.toBlocks₁₂ = 1 ∧
      cubeBarM k.toBlocks₁₂ * k.toBlocks₂₁ - cubeBarM k.toBlocks₂₂ * k.toBlocks₁₁ = -1 ∧
      cubeBarM k.toBlocks₁₂ * k.toBlocks₂₂ - cubeBarM k.toBlocks₂₂ * k.toBlocks₁₂ = 0 := by
  obtain ⟨ha, hb', hc, hd⟩ := hb
  set a := k.toBlocks₁₁
  set b := k.toBlocks₁₂
  set c := k.toBlocks₂₁
  set d := k.toBlocks₂₂
  have hS : IsUnit (gramS K) := by
    rw [Matrix.isUnit_iff_isUnit_det, det_gramS]
    exact h3.isUnit
  rw [← fromBlocks_toBlocks k, gramTensor, fromBlocks_transpose, fromBlocks_multiply,
    fromBlocks_multiply] at hk
  simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul] at hk
  obtain ⟨e11, e12, e21, e22⟩ := Matrix.fromBlocks_inj.mp hk
  rw [transpose_mul_gramS ha, transpose_mul_gramS hc] at e11 e12
  rw [transpose_mul_gramS hb', transpose_mul_gramS hd] at e21 e22
  refine ⟨hS.mul_left_cancel ?_, hS.mul_left_cancel ?_, hS.mul_left_cancel ?_,
    hS.mul_left_cancel ?_⟩
  · calc gramS K * (cubeBarM a * c - cubeBarM c * a) =
        -(gramS K * cubeBarM c * a) + gramS K * cubeBarM a * c := by noncomm_ring
      _ = 0 := e11
      _ = gramS K * 0 := (Matrix.mul_zero _).symm
  · calc gramS K * (cubeBarM a * d - cubeBarM c * b) =
        -(gramS K * cubeBarM c * b) + gramS K * cubeBarM a * d := by noncomm_ring
      _ = gramS K := e12
      _ = gramS K * 1 := (Matrix.mul_one _).symm
  · calc gramS K * (cubeBarM b * c - cubeBarM d * a) =
        -(gramS K * cubeBarM d * a) + gramS K * cubeBarM b * c := by noncomm_ring
      _ = -gramS K := e21
      _ = gramS K * -1 := by rw [Matrix.mul_neg, Matrix.mul_one]
  · calc gramS K * (cubeBarM b * d - cubeBarM d * b) =
        -(gramS K * cubeBarM d * b) + gramS K * cubeBarM b * d := by noncomm_ring
      _ = 0 := e22
      _ = gramS K * 0 := (Matrix.mul_zero _).symm

theorem cubeBarM_eq_of_unitary {a b c d : Matrix (Fin 2) (Fin 2) K} (ha : a ∈ cubeAlg K)
    (hb : b ∈ cubeAlg K) (hc : c ∈ cubeAlg K) (hd : d ∈ cubeAlg K)
    (e11 : cubeBarM a * c - cubeBarM c * a = 0) (e12 : cubeBarM a * d - cubeBarM c * b = 1)
    (e21 : cubeBarM b * c - cubeBarM d * a = -1) (e22 : cubeBarM b * d - cubeBarM d * b = 0)
    (edet : a * d - b * c = 1) :
    cubeBarM a = a ∧ cubeBarM b = b ∧ cubeBarM c = c ∧ cubeBarM d = d := by
  set A : cubeAlg K := ⟨a, ha⟩
  set B : cubeAlg K := ⟨b, hb⟩
  set C : cubeAlg K := ⟨c, hc⟩
  set D : cubeAlg K := ⟨d, hd⟩
  set A' : cubeAlg K := ⟨cubeBarM a, cubeBarM_mem a⟩
  set B' : cubeAlg K := ⟨cubeBarM b, cubeBarM_mem b⟩
  set C' : cubeAlg K := ⟨cubeBarM c, cubeBarM_mem c⟩
  set D' : cubeAlg K := ⟨cubeBarM d, cubeBarM_mem d⟩
  have E11 : A' * C - C' * A = 0 := Subtype.ext e11
  have E12 : A' * D - C' * B = 1 := Subtype.ext e12
  have E21 : B' * C - D' * A = -1 := Subtype.ext e21
  have E22 : B' * D - D' * B = 0 := Subtype.ext e22
  have Edet : A * D - B * C = 1 := Subtype.ext edet
  have hA : A' = A := by linear_combination A * E12 - B * E11 - A' * Edet
  have hC : C' = C := by linear_combination -C' * Edet - D * E11 + C * E12
  have hD : D' = D := by linear_combination -D' * Edet - D * E21 + C * E22
  have hB : B' = B := by linear_combination -B' * Edet + A * E22 - B * E21
  exact ⟨congrArg Subtype.val hA, congrArg Subtype.val hB, congrArg Subtype.val hC,
    congrArg Subtype.val hD⟩

theorem isCentData_tensor (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {D : GL (Fin 2 ⊕ Fin 2) K}
    (hD : (D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks (cubeMat K) 0 0 (cubeMat K)) :
    IsCentData (gramGroup (gramTensor K)) D iotaTensor := by
  refine ⟨iotaTensor_mem, fun B => Units.ext ?_, fun g hg h hh hgD hhD => ?_⟩
  · rw [Units.val_mul, Units.val_mul, coe_iotaTensor, hD, fromBlocks_multiply,
      fromBlocks_multiply]
    simp
  · set Cg := gramGroup (gramTensor K) ⊓
      Subgroup.centralizer ({D} : Set (GL (Fin 2 ⊕ Fin 2) K)) with hCg
    have hblk : ∀ x ∈ Cg, ((x : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₁ ∈ cubeAlg K ∧
        ((x : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₂ ∈ cubeAlg K ∧
        ((x : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₁ ∈ cubeAlg K ∧
        ((x : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₂₂ ∈ cubeAlg K := by
      intro x hx
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      apply blocks_mem_cubeAlg
      rw [← hD, ← Units.val_mul, ← Units.val_mul, hc]
    have hdetC : ∀ x ∈ Cg, detC ((x : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∈ cubeAlg K := by
      intro x hx
      obtain ⟨b1, b2, b3, b4⟩ := hblk x hx
      exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ b1 b4) (Subalgebra.mul_mem _ b2 b3)
    have hgC : g ∈ Cg := ⟨hg, Subgroup.mem_centralizer_singleton_iff.mpr hgD⟩
    have hhC : h ∈ Cg := ⟨hh, Subgroup.mem_centralizer_singleton_iff.mpr hhD⟩
    let χ : Cg →* cubeAlg K :=
      { toFun := fun x => ⟨_, hdetC x x.2⟩
        map_one' := by
          apply Subtype.ext
          change detC (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1
          obtain ⟨o1, o2, o3, o4⟩ := toBlocks_one (K := K) (n := Fin 2)
          rw [detC, o1, o2, o3, o4, Matrix.mul_one, Matrix.zero_mul, sub_zero]
        map_mul' := fun x y => Subtype.ext (by
          change detC ((x : GL (Fin 2 ⊕ Fin 2) K) * (y : GL (Fin 2 ⊕ Fin 2) K) :
            GL (Fin 2 ⊕ Fin 2) K).val = _
          rw [Units.val_mul]
          exact detC_mul (hblk x x.2) (hblk y y.2)) }
    have hχ : χ.toHomUnits ⁅(⟨g, hgC⟩ : Cg), ⟨h, hhC⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    have hk : g * h * g⁻¹ * h⁻¹ ∈ Cg :=
      Cg.mul_mem (Cg.mul_mem (Cg.mul_mem hgC hhC) (Cg.inv_mem hgC)) (Cg.inv_mem hhC)
    set k := ((g * h * g⁻¹ * h⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hkdef
    have hkdet : detC k = 1 := by
      have := congrArg (fun u : (cubeAlg K)ˣ => ((u : cubeAlg K) : Matrix (Fin 2) (Fin 2) K)) hχ
      rw [commutatorElement_def] at this
      exact this
    obtain ⟨ha, hb, hc, hd⟩ := hblk _ hk
    obtain ⟨e11, e12, e21, e22⟩ := tensor_isometry_eqs h3 (hblk _ hk) (mem_gramGroup.mp hk.1)
    obtain ⟨fa, fb, fc, fd⟩ := cubeBarM_eq_of_unitary ha hb hc hd e11 e12 e21 e22 hkdet
    have sa := eq_smul_one_of_cubeBarM_eq h2 ha fa
    have sb := eq_smul_one_of_cubeBarM_eq h2 hb fb
    have sc := eq_smul_one_of_cubeBarM_eq h2 hc fc
    have sd := eq_smul_one_of_cubeBarM_eq h2 hd fd
    set B : Matrix (Fin 2) (Fin 2) K := !![k.toBlocks₁₁ 0 0, k.toBlocks₁₂ 0 0;
      k.toBlocks₂₁ 0 0, k.toBlocks₂₂ 0 0] with hBdef
    have hBdet : B.det = 1 := by
      have e := congrFun (congrFun hkdet 0) 0
      rw [detC, sa, sb, sc, sd] at e
      simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e
      rw [Matrix.det_fin_two]
      exact e
    refine ⟨(⟨B, hBdet⟩ : SpecialLinearGroup (Fin 2) K), Units.ext ?_⟩
    change fromBlocks (B 0 0 • 1) (B 0 1 • 1) (B 1 0 • 1) (B 1 1 • 1) = k
    conv_rhs => rw [← fromBlocks_toBlocks k, sa, sb, sc, sd]
    rfl

theorem ker_mk_iotaTensor :
    (ProjGenLinGroup.mk.comp (iotaTensor (K := K))).ker =
      Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
  ext B
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ProjGenLinGroup.mk_eq_one,
    GeneralLinearGroup.center_eq_range_scalar, Matrix.SpecialLinearGroup.mem_center_iff,
    Fintype.card_fin]
  constructor
  · rintro ⟨u, hu⟩
    have e := congrArg (fun x : GL (Fin 2 ⊕ Fin 2) K => (x : Matrix (Fin 2 ⊕ Fin 2)
      (Fin 2 ⊕ Fin 2) K)) hu
    simp only [GeneralLinearGroup.coe_scalar, coe_iotaTensor] at e
    have e00 := congrFun (congrFun e (Sum.inl 0)) (Sum.inl 0)
    have e01 := congrFun (congrFun e (Sum.inl 0)) (Sum.inr 0)
    have e10 := congrFun (congrFun e (Sum.inr 0)) (Sum.inl 0)
    have e11 := congrFun (congrFun e (Sum.inr 0)) (Sum.inr 0)
    simp [Matrix.scalar_apply] at e00 e01 e10 e11
    have hB : (B : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) (u : K) := by
      ext i j
      fin_cases i <;> fin_cases j
      · simpa [Matrix.scalar_apply] using e00.symm
      · simpa [Matrix.scalar_apply] using e01.symm
      · simpa [Matrix.scalar_apply] using e10.symm
      · simpa [Matrix.scalar_apply] using e11.symm
    refine ⟨u, ?_, hB.symm⟩
    have hdet := B.2
    rw [hB, Matrix.det_fin_two] at hdet
    simpa [Matrix.scalar_apply, sq] using hdet
  · rintro ⟨r, hr2, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      norm_num at hr2
    refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar, coe_iotaTensor, ← hr]
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.scalar_apply, fromBlocks]

end CFSG.RankThree.PartTwo.Sec21.Item228Census3Proof
