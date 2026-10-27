module

public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.CentralCover.SteinbergBNSL2Elements

public section

namespace CFSG.RankThree.PartTwo.Census.Exceptional


open TauCeti TauCeti.G2ShortRoot CFSG.RankThree.CentralCover
open scoped MatrixGroups commutatorElement

section Mats

variable {L : Type*} [CommRing L]

@[expose] def phiaMat (A : Matrix (Fin 2) (Fin 2) L) : Matrix (Fin 7) (Fin 7) L :=
  !![A 0 0, A 0 1, 0, 0, 0, 0, 0;
     A 1 0, A 1 1, 0, 0, 0, 0, 0;
     0, 0, A 0 0 ^ 2, 2 * A 0 0 * A 0 1, A 0 1 ^ 2, 0, 0;
     0, 0, A 0 0 * A 1 0, A 0 0 * A 1 1 + A 0 1 * A 1 0, A 0 1 * A 1 1, 0, 0;
     0, 0, A 1 0 ^ 2, 2 * A 1 0 * A 1 1, A 1 1 ^ 2, 0, 0;
     0, 0, 0, 0, 0, A 0 0, A 0 1;
     0, 0, 0, 0, 0, A 1 0, A 1 1]

@[expose] def phibMat (A : Matrix (Fin 2) (Fin 2) L) : Matrix (Fin 7) (Fin 7) L :=
  !![1, 0, 0, 0, 0, 0, 0;
     0, A 0 0, A 0 1, 0, 0, 0, 0;
     0, A 1 0, A 1 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, A 0 0, A 0 1, 0;
     0, 0, 0, 0, A 1 0, A 1 1, 0;
     0, 0, 0, 0, 0, 0, 1]

theorem phiaMat_mul (A B : Matrix (Fin 2) (Fin 2) L) :
    phiaMat (A * B) = phiaMat A * phiaMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phiaMat, Matrix.mul_apply, Fin.sum_univ_seven, Fin.sum_univ_two] <;> ring

theorem phibMat_mul (A B : Matrix (Fin 2) (Fin 2) L) :
    phibMat (A * B) = phibMat A * phibMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phibMat, Matrix.mul_apply, Fin.sum_univ_seven, Fin.sum_univ_two]

theorem phiaMat_one : phiaMat (1 : Matrix (Fin 2) (Fin 2) L) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phiaMat]

theorem phibMat_one : phibMat (1 : Matrix (Fin 2) (Fin 2) L) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phibMat]

end Mats

section Homs

variable (L : Type) [Field L] [Algebra (ZMod 3) L]

@[expose] noncomputable def phiaGL : SL(2, L) →* Matrix.GeneralLinearGroup (Fin 7) L where
  toFun A :=
    { val := phiaMat (A : Matrix (Fin 2) (Fin 2) L)
      inv := phiaMat ((A⁻¹ : SL(2, L)) : Matrix (Fin 2) (Fin 2) L)
      val_inv := by
        rw [← phiaMat_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, phiaMat_one]
      inv_val := by
        rw [← phiaMat_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, phiaMat_one] }
  map_one' := Units.ext (by
    change phiaMat ((1 : SL(2, L)) : Matrix (Fin 2) (Fin 2) L) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, phiaMat_one])
  map_mul' A B := Units.ext (by
    change phiaMat ((A * B : SL(2, L)) : Matrix (Fin 2) (Fin 2) L) = phiaMat _ * phiaMat _
    rw [Matrix.SpecialLinearGroup.coe_mul, phiaMat_mul])

@[expose] noncomputable def phibGL : SL(2, L) →* Matrix.GeneralLinearGroup (Fin 7) L where
  toFun A :=
    { val := phibMat (A : Matrix (Fin 2) (Fin 2) L)
      inv := phibMat ((A⁻¹ : SL(2, L)) : Matrix (Fin 2) (Fin 2) L)
      val_inv := by
        rw [← phibMat_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, phibMat_one]
      inv_val := by
        rw [← phibMat_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, phibMat_one] }
  map_one' := Units.ext (by
    change phibMat ((1 : SL(2, L)) : Matrix (Fin 2) (Fin 2) L) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, phibMat_one])
  map_mul' A B := Units.ext (by
    change phibMat ((A * B : SL(2, L)) : Matrix (Fin 2) (Fin 2) L) = phibMat _ * phibMat _
    rw [Matrix.SpecialLinearGroup.coe_mul, phibMat_mul])

omit [Algebra (ZMod 3) L] in
theorem coe_phiaGL (A : SL(2, L)) :
    ((phiaGL L A : Matrix.GeneralLinearGroup (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) =
      phiaMat (A : Matrix (Fin 2) (Fin 2) L) := rfl

omit [Algebra (ZMod 3) L] in
theorem coe_phibGL (A : SL(2, L)) :
    ((phibGL L A : Matrix.GeneralLinearGroup (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) =
      phibMat (A : Matrix (Fin 2) (Fin 2) L) := rfl

theorem phiaGL_upper (c : L) :
    phiaGL L (sl2Upper c) =
      (PrimeField.rootSubgroupPoints (.inl 0) L (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin 7) L) := by
  refine Units.ext ?_
  rw [coe_phiaGL, PrimeField.coe_rootSubgroupPoints,
    IntegralToralClosure.coe_rootSubgroupPoints_inl_zero, coe_sl2Upper]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phiaMat]

theorem phiaGL_lower (c : L) :
    phiaGL L (CFSG.LocalAnalysis.ComponentInitial.sl2Lower L c) =
      (PrimeField.rootSubgroupPoints (.inr 0) L (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin 7) L) := by
  refine Units.ext ?_
  rw [coe_phiaGL, PrimeField.coe_rootSubgroupPoints,
    IntegralToralClosure.coe_rootSubgroupPoints_inr_zero,
    CFSG.LocalAnalysis.ComponentInitial.coe_sl2Lower]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phiaMat]

theorem phibGL_upper (c : L) :
    phibGL L (sl2Upper c) =
      (PrimeField.rootSubgroupPoints (.inl 1) L (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin 7) L) := by
  refine Units.ext ?_
  rw [coe_phibGL, PrimeField.coe_rootSubgroupPoints,
    IntegralToralClosure.coe_rootSubgroupPoints_inl_one, coe_sl2Upper]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phibMat]

theorem phibGL_lower (c : L) :
    phibGL L (CFSG.LocalAnalysis.ComponentInitial.sl2Lower L c) =
      (PrimeField.rootSubgroupPoints (.inr 1) L (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin 7) L) := by
  refine Units.ext ?_
  rw [coe_phibGL, PrimeField.coe_rootSubgroupPoints,
    IntegralToralClosure.coe_rootSubgroupPoints_inr_one,
    CFSG.LocalAnalysis.ComponentInitial.coe_sl2Lower]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phibMat]

omit [Algebra (ZMod 3) L] in
theorem range_le_of_upper_lower {G : Type*} [Group G] (f : SL(2, L) →* G) (S : Subgroup G)
    (hu : ∀ c, f (sl2Upper c) ∈ S)
    (hl : ∀ c, f (CFSG.LocalAnalysis.ComponentInitial.sl2Lower L c) ∈ S) : f.range ≤ S := by
  rw [MonoidHom.range_eq_map, ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower,
    MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨A, ⟨c, rfl⟩ | ⟨c, rfl⟩, rfl⟩
  · exact hu c
  · exact hl c

@[expose] noncomputable def phia : SL(2, L) →* PrimeField.points L :=
  (phiaGL L).codRestrict _ fun A => range_le_of_upper_lower L (phiaGL L) _
    (fun c => by rw [phiaGL_upper]; exact (PrimeField.rootSubgroupPoints _ _ _).2)
    (fun c => by rw [phiaGL_lower]; exact (PrimeField.rootSubgroupPoints _ _ _).2) ⟨A, rfl⟩

@[expose] noncomputable def phib : SL(2, L) →* PrimeField.points L :=
  (phibGL L).codRestrict _ fun A => range_le_of_upper_lower L (phibGL L) _
    (fun c => by rw [phibGL_upper]; exact (PrimeField.rootSubgroupPoints _ _ _).2)
    (fun c => by rw [phibGL_lower]; exact (PrimeField.rootSubgroupPoints _ _ _).2) ⟨A, rfl⟩

theorem coe_phia (A : SL(2, L)) :
    (((phia L A : PrimeField.points L) : Matrix.GeneralLinearGroup (Fin 7) L) :
      Matrix (Fin 7) (Fin 7) L) = phiaMat (A : Matrix (Fin 2) (Fin 2) L) := rfl

theorem coe_phib (A : SL(2, L)) :
    (((phib L A : PrimeField.points L) : Matrix.GeneralLinearGroup (Fin 7) L) :
      Matrix (Fin 7) (Fin 7) L) = phibMat (A : Matrix (Fin 2) (Fin 2) L) := rfl

theorem phia_upper (c : L) :
    phia L (sl2Upper c) = PrimeField.rootSubgroupPoints (.inl 0) L (Multiplicative.ofAdd c) :=
  Subtype.ext (phiaGL_upper L c)

theorem phia_lower (c : L) :
    phia L (CFSG.LocalAnalysis.ComponentInitial.sl2Lower L c) =
      PrimeField.rootSubgroupPoints (.inr 0) L (Multiplicative.ofAdd c) :=
  Subtype.ext (phiaGL_lower L c)

theorem phib_upper (c : L) :
    phib L (sl2Upper c) = PrimeField.rootSubgroupPoints (.inl 1) L (Multiplicative.ofAdd c) :=
  Subtype.ext (phibGL_upper L c)

theorem phib_lower (c : L) :
    phib L (CFSG.LocalAnalysis.ComponentInitial.sl2Lower L c) =
      PrimeField.rootSubgroupPoints (.inr 1) L (Multiplicative.ofAdd c) :=
  Subtype.ext (phibGL_lower L c)

theorem phia_injective : Function.Injective (phia L) := by
  intro A B h
  have h' := congrArg (fun g : PrimeField.points L =>
    ((g : Matrix.GeneralLinearGroup (Fin 7) L) : Matrix (Fin 7) (Fin 7) L)) h
  simp only [coe_phia] at h'
  ext i j
  fin_cases i <;> fin_cases j
  · exact congrFun (congrFun h' 0) 0
  · exact congrFun (congrFun h' 0) 1
  · exact congrFun (congrFun h' 1) 0
  · exact congrFun (congrFun h' 1) 1

theorem phib_injective : Function.Injective (phib L) := by
  intro A B h
  have h' := congrArg (fun g : PrimeField.points L =>
    ((g : Matrix.GeneralLinearGroup (Fin 7) L) : Matrix (Fin 7) (Fin 7) L)) h
  simp only [coe_phib] at h'
  ext i j
  fin_cases i <;> fin_cases j
  · exact congrFun (congrFun h' 1) 1
  · exact congrFun (congrFun h' 1) 2
  · exact congrFun (congrFun h' 2) 1
  · exact congrFun (congrFun h' 2) 2

end Homs

section Isogeny

variable (L : Type) [Field L] [Algebra (ZMod 3) L] [CharP L 3]

theorem reeMap_sl2Upper (f : L →+* L) (c : L) :
    Matrix.SpecialLinearGroup.map f (sl2Upper c) = sl2Upper (f c) := by
  ext a b
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  fin_cases a <;> fin_cases b <;> simp [sl2Upper]

theorem reeMap_sl2Lower (f : L →+* L) (c : L) :
    Matrix.SpecialLinearGroup.map f (CFSG.LocalAnalysis.ComponentInitial.sl2Lower L c) =
      CFSG.LocalAnalysis.ComponentInitial.sl2Lower L (f c) := by
  ext a b
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  fin_cases a <;> fin_cases b <;> simp [CFSG.LocalAnalysis.ComponentInitial.sl2Lower]

theorem specialIsogeny_phia (A : SL(2, L)) :
    PrimeField.specialIsogeny L (phia L A) =
      phib L (Matrix.SpecialLinearGroup.map (frobenius L 3) A) := by
  have h : (PrimeField.specialIsogeny L).comp (phia L) =
      (phib L).comp (Matrix.SpecialLinearGroup.map (frobenius L 3)) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := L)) ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change PrimeField.specialIsogeny L (phia L (sl2Upper c)) =
        phib L (Matrix.SpecialLinearGroup.map (frobenius L 3) (sl2Upper c))
      rw [phia_upper, PrimeField.specialIsogeny_rootSubgroupPoints, reeMap_sl2Upper, phib_upper,
        PrimeField.specialIsogenyRootIndex_inl, PrimeField.specialIsogenyExponent_inl,
        frobenius_def]
      rfl
    · change PrimeField.specialIsogeny L
          (phia L (CFSG.LocalAnalysis.ComponentInitial.sl2Lower L c)) =
        phib L (Matrix.SpecialLinearGroup.map (frobenius L 3)
          (CFSG.LocalAnalysis.ComponentInitial.sl2Lower L c))
      rw [phia_lower, PrimeField.specialIsogeny_rootSubgroupPoints, reeMap_sl2Lower, phib_lower,
        PrimeField.specialIsogenyRootIndex_inr, PrimeField.specialIsogenyExponent_inr,
        frobenius_def]
      rfl
  exact DFunLike.congr_fun h A

theorem specialIsogeny_phib (A : SL(2, L)) :
    PrimeField.specialIsogeny L (phib L A) = phia L A := by
  have h : (PrimeField.specialIsogeny L).comp (phib L) = phia L := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := L)) ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change PrimeField.specialIsogeny L (phib L (sl2Upper c)) = phia L (sl2Upper c)
      rw [phib_upper, PrimeField.specialIsogeny_rootSubgroupPoints, phia_upper,
        PrimeField.specialIsogenyRootIndex_inl, PrimeField.specialIsogenyExponent_inl]
      simp
    · change PrimeField.specialIsogeny L
          (phib L (CFSG.LocalAnalysis.ComponentInitial.sl2Lower L c)) =
        phia L (CFSG.LocalAnalysis.ComponentInitial.sl2Lower L c)
      rw [phib_lower, PrimeField.specialIsogeny_rootSubgroupPoints, phia_lower,
        PrimeField.specialIsogenyRootIndex_inr, PrimeField.specialIsogenyExponent_inr]
      simp
  exact DFunLike.congr_fun h A

theorem map_frobenius_sl2Weyl :
    Matrix.SpecialLinearGroup.map (frobenius L 3) (sl2Weyl L) = sl2Weyl L := by
  ext a b
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  fin_cases a <;> fin_cases b <;> simp [sl2Weyl, frobenius_def]
  norm_num

end Isogeny

section Pair

variable {L : Type*} [CommRing L]

@[expose] def phi1Mat (A : Matrix (Fin 2) (Fin 2) L) : Matrix (Fin 7) (Fin 7) L :=
  !![A 0 0, 0, -A 0 1, 0, 0, 0, 0;
     0, A 0 0 ^ 2, 0, 2 * A 0 0 * A 0 1, 0, -A 0 1 ^ 2, 0;
     -A 1 0, 0, A 1 1, 0, 0, 0, 0;
     0, A 0 0 * A 1 0, 0, A 0 0 * A 1 1 + A 0 1 * A 1 0, 0, -A 0 1 * A 1 1, 0;
     0, 0, 0, 0, A 0 0, 0, A 0 1;
     0, -A 1 0 ^ 2, 0, -2 * A 1 0 * A 1 1, 0, A 1 1 ^ 2, 0;
     0, 0, 0, 0, A 1 0, 0, A 1 1]

@[expose] def phi2Mat (B : Matrix (Fin 2) (Fin 2) L) : Matrix (Fin 7) (Fin 7) L :=
  !![B 0 0, 0, 0, 0, B 0 1, 0, 0;
     0, 1, 0, 0, 0, 0, 0;
     0, 0, B 0 0, 0, 0, 0, -B 0 1;
     0, 0, 0, 1, 0, 0, 0;
     B 1 0, 0, 0, 0, B 1 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, -B 1 0, 0, 0, 0, B 1 1]

theorem phi1Mat_mul_phi2Mat (A B : Matrix (Fin 2) (Fin 2) L) :
    phi1Mat A * phi2Mat B = phi2Mat B * phi1Mat A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phi1Mat, phi2Mat, Matrix.mul_apply, Fin.sum_univ_seven] <;> ring

theorem phibMat_weyl_mul (A : Matrix (Fin 2) (Fin 2) L) :
    phibMat !![0, 1; -1, 0] * phiaMat A * phibMat !![0, -1; 1, 0] = phi1Mat A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phi1Mat, phiaMat, phibMat, Matrix.mul_apply, Fin.sum_univ_seven]

theorem phiaMat_weyl :
    phiaMat (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) L) =
      !![0, 1, 0, 0, 0, 0, 0;
         -1, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 1, 0, 0;
         0, 0, 0, -1, 0, 0, 0;
         0, 0, 1, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0, 1;
         0, 0, 0, 0, 0, -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phiaMat]

theorem phiaMat_weyl_inv :
    phiaMat (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) L) =
      !![0, -1, 0, 0, 0, 0, 0;
         1, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 1, 0, 0;
         0, 0, 0, -1, 0, 0, 0;
         0, 0, 1, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0, -1;
         0, 0, 0, 0, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phiaMat]

theorem phiaMat_weyl_mul (B : Matrix (Fin 2) (Fin 2) L) :
    phiaMat !![0, 1; -1, 0] * phibMat B * phiaMat !![0, -1; 1, 0] = phi2Mat B := by
  rw [phiaMat_weyl, phiaMat_weyl_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phi2Mat, phibMat, Matrix.mul_apply, Fin.sum_univ_seven]

end Pair

section Weyl

variable (L : Type) [Field L] [Algebra (ZMod 3) L]

@[expose] noncomputable def reeNa : PrimeField.points L := phia L (sl2Weyl L)

@[expose] noncomputable def reeNb : PrimeField.points L := phib L (sl2Weyl L)

@[expose] noncomputable def reePhi1 : SL(2, L) →* PrimeField.points L :=
  (MulAut.conj (reeNb L)).toMonoidHom.comp (phia L)

@[expose] noncomputable def reePhi2 : SL(2, L) →* PrimeField.points L :=
  (MulAut.conj (reeNa L)).toMonoidHom.comp (phib L)

theorem sl2Weyl_inv_coe :
    (((sl2Weyl L)⁻¹ : SL(2, L)) : Matrix (Fin 2) (Fin 2) L) = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_sl2Weyl, Matrix.adjugate_fin_two]
  simp

theorem coe_reePhi1 (A : SL(2, L)) :
    (((reePhi1 L A : PrimeField.points L) : Matrix.GeneralLinearGroup (Fin 7) L) :
      Matrix (Fin 7) (Fin 7) L) = phi1Mat (A : Matrix (Fin 2) (Fin 2) L) := by
  change phibMat ((sl2Weyl L : SL(2, L)) : Matrix (Fin 2) (Fin 2) L) *
      phiaMat (A : Matrix (Fin 2) (Fin 2) L) *
      phibMat (((sl2Weyl L)⁻¹ : SL(2, L)) : Matrix (Fin 2) (Fin 2) L) = _
  rw [sl2Weyl_inv_coe, coe_sl2Weyl, phibMat_weyl_mul]

theorem coe_reePhi2 (B : SL(2, L)) :
    (((reePhi2 L B : PrimeField.points L) : Matrix.GeneralLinearGroup (Fin 7) L) :
      Matrix (Fin 7) (Fin 7) L) = phi2Mat (B : Matrix (Fin 2) (Fin 2) L) := by
  change phiaMat ((sl2Weyl L : SL(2, L)) : Matrix (Fin 2) (Fin 2) L) *
      phibMat (B : Matrix (Fin 2) (Fin 2) L) *
      phiaMat (((sl2Weyl L)⁻¹ : SL(2, L)) : Matrix (Fin 2) (Fin 2) L) = _
  rw [sl2Weyl_inv_coe, coe_sl2Weyl, phiaMat_weyl_mul]

theorem reePhi_commute (A B : SL(2, L)) : reePhi1 L A * reePhi2 L B = reePhi2 L B * reePhi1 L A :=
  Subtype.ext (Units.ext (by
    change (((reePhi1 L A : PrimeField.points L) : Matrix.GeneralLinearGroup (Fin 7) L) :
        Matrix (Fin 7) (Fin 7) L) * (((reePhi2 L B : PrimeField.points L) :
          Matrix.GeneralLinearGroup (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) = _ * _
    rw [coe_reePhi1, coe_reePhi2, phi1Mat_mul_phi2Mat]))

theorem reePhi1_injective : Function.Injective (reePhi1 L) :=
  (MulAut.conj (reeNb L)).injective.comp (phia_injective L)

theorem reePhi2_injective : Function.Injective (reePhi2 L) :=
  (MulAut.conj (reeNa L)).injective.comp (phib_injective L)

theorem reePhi1_neg_one : reePhi1 L (-1) = reePhi2 L (-1) :=
  Subtype.ext (Units.ext (by
    rw [coe_reePhi1, coe_reePhi2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [phi1Mat, phi2Mat]))

end Weyl

section Certificate

@[expose] def reeXaZ : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  !![1, 1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0;
     0, 0, 1, 2, 1, 0, 0;
     0, 0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0, 1]

@[expose] def reeXbZ : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  !![1, 0, 0, 0, 0, 0, 0;
     0, 1, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1]

@[expose] def reeYaZ : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  !![1, 0, 0, 0, 0, 0, 0;
     1, 1, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 0, 0, 0;
     0, 0, 1, 2, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1, 1]

@[expose] def reeYbZ : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  !![1, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0;
     0, 1, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 0, 1]

@[expose] def reeUZ : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  !![1, 0, 0, 2, 0, 1, 1;
     0, 1, 0, 0, 2, 0, 1;
     0, 0, 1, 0, 0, 2, 0;
     0, 0, 0, 1, 0, 0, 1;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1]

@[expose] def reeVZ : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  !![1, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0;
     1, 0, 0, 1, 0, 0, 0;
     0, 2, 0, 0, 1, 0, 0;
     1, 0, 2, 0, 0, 1, 0;
     1, 1, 0, 2, 0, 0, 1]

@[expose] def reeTZ : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  !![2, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0;
     0, 0, 2, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 2, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 2]

@[expose] def reeGZ : Matrix (Fin 7) (Fin 7) (ZMod 3) := reeUZ * reeVZ * reeUZ ^ 2 * reeVZ

@[expose] def reeHZ : Matrix (Fin 7) (Fin 7) (ZMod 3) := reeUZ * reeVZ ^ 2 * reeUZ * reeVZ

@[expose] def reeGiZ : Matrix (Fin 7) (Fin 7) (ZMod 3) := reeVZ ^ 2 * reeUZ * reeVZ ^ 2 * reeUZ ^ 2

@[expose] def reeHiZ : Matrix (Fin 7) (Fin 7) (ZMod 3) := reeVZ ^ 2 * reeUZ ^ 2 * reeVZ * reeUZ ^ 2

theorem ree_check :
    (reeXaZ * reeXbZ) ^ 3 = reeUZ ∧ (reeXbZ * reeXaZ) ^ 3 = reeUZ ∧ reeUZ ^ 3 = 1 ∧
    (reeYaZ * reeYbZ) ^ 3 = reeVZ ∧ (reeYbZ * reeYaZ) ^ 3 = reeVZ ∧
    reeGZ * reeGiZ = 1 ∧ reeHZ * reeHiZ = 1 ∧ reeGZ * reeHZ * reeGiZ * reeHiZ = reeTZ ∧
    reeTZ * (reeUZ * reeTZ * reeUZ ^ 2) ≠ reeUZ * reeTZ * reeUZ ^ 2 * reeTZ := by
  decide +kernel

end Certificate

section Transfer

variable (L : Type) [Field L] [Algebra (ZMod 3) L] [CharP L 3]

noncomputable abbrev reeMat : PrimeField.points L →* Matrix (Fin 7) (Fin 7) L :=
  (Units.coeHom _).comp (PrimeField.points L).subtype

theorem reeMat_injective : Function.Injective (reeMat L) := fun _ _ h =>
  Subtype.ext (Units.ext h)

noncomputable abbrev reeF : Matrix (Fin 7) (Fin 7) (ZMod 3) →+* Matrix (Fin 7) (Fin 7) L :=
  (algebraMap (ZMod 3) L).mapMatrix

theorem reeF_injective : Function.Injective (reeF L) := fun A B h => by
  ext i j
  exact (algebraMap (ZMod 3) L).injective (congrFun (congrFun h i) j)

theorem two_eq_neg_one_of_charThree : (2 : L) = -1 := by
  have h : ((3 : ℕ) : L) = 0 := CharP.cast_eq_zero L 3
  push_cast at h
  linear_combination h

noncomputable abbrev reeXa : PrimeField.points L :=
  PrimeField.rootSubgroupPoints (.inl 0) L (Multiplicative.ofAdd 1)

noncomputable abbrev reeXb : PrimeField.points L :=
  PrimeField.rootSubgroupPoints (.inl 1) L (Multiplicative.ofAdd 1)

noncomputable abbrev reeYa : PrimeField.points L :=
  PrimeField.rootSubgroupPoints (.inr 0) L (Multiplicative.ofAdd 1)

noncomputable abbrev reeYb : PrimeField.points L :=
  PrimeField.rootSubgroupPoints (.inr 1) L (Multiplicative.ofAdd 1)

theorem reeMat_xa : reeMat L (reeXa L) = reeF L reeXaZ := by
  change ((PrimeField.rootSubgroupPoints (.inl 0) L (Multiplicative.ofAdd 1) :
    Matrix.GeneralLinearGroup (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) = _
  rw [PrimeField.coe_rootSubgroupPoints, IntegralToralClosure.coe_rootSubgroupPoints_inl_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reeXaZ, map_ofNat]

theorem reeMat_xb : reeMat L (reeXb L) = reeF L reeXbZ := by
  change ((PrimeField.rootSubgroupPoints (.inl 1) L (Multiplicative.ofAdd 1) :
    Matrix.GeneralLinearGroup (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) = _
  rw [PrimeField.coe_rootSubgroupPoints, IntegralToralClosure.coe_rootSubgroupPoints_inl_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reeXbZ]

theorem reeMat_ya : reeMat L (reeYa L) = reeF L reeYaZ := by
  change ((PrimeField.rootSubgroupPoints (.inr 0) L (Multiplicative.ofAdd 1) :
    Matrix.GeneralLinearGroup (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) = _
  rw [PrimeField.coe_rootSubgroupPoints, IntegralToralClosure.coe_rootSubgroupPoints_inr_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reeYaZ, map_ofNat]

theorem reeMat_yb : reeMat L (reeYb L) = reeF L reeYbZ := by
  change ((PrimeField.rootSubgroupPoints (.inr 1) L (Multiplicative.ofAdd 1) :
    Matrix.GeneralLinearGroup (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) = _
  rw [PrimeField.coe_rootSubgroupPoints, IntegralToralClosure.coe_rootSubgroupPoints_inr_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reeYbZ]

theorem specialIsogeny_reeXa : PrimeField.specialIsogeny L (reeXa L) = reeXb L := by
  rw [PrimeField.specialIsogeny_rootSubgroupPoints, PrimeField.specialIsogenyRootIndex_inl,
    PrimeField.specialIsogenyExponent_inl]
  simp

theorem specialIsogeny_reeXb : PrimeField.specialIsogeny L (reeXb L) = reeXa L := by
  rw [PrimeField.specialIsogeny_rootSubgroupPoints, PrimeField.specialIsogenyRootIndex_inl,
    PrimeField.specialIsogenyExponent_inl]
  simp

theorem specialIsogeny_reeYa : PrimeField.specialIsogeny L (reeYa L) = reeYb L := by
  rw [PrimeField.specialIsogeny_rootSubgroupPoints, PrimeField.specialIsogenyRootIndex_inr,
    PrimeField.specialIsogenyExponent_inr]
  simp

theorem specialIsogeny_reeYb : PrimeField.specialIsogeny L (reeYb L) = reeYa L := by
  rw [PrimeField.specialIsogeny_rootSubgroupPoints, PrimeField.specialIsogenyRootIndex_inr,
    PrimeField.specialIsogenyExponent_inr]
  simp

@[expose] noncomputable def reeU : PrimeField.points L := (reeXa L * reeXb L) ^ 3

@[expose] noncomputable def reeV : PrimeField.points L := (reeYa L * reeYb L) ^ 3

theorem reeMat_u : reeMat L (reeU L) = reeF L reeUZ := by
  rw [reeU, map_pow, map_mul, reeMat_xa, reeMat_xb, ← map_mul, ← map_pow, ree_check.1]

theorem reeMat_v : reeMat L (reeV L) = reeF L reeVZ := by
  rw [reeV, map_pow, map_mul, reeMat_ya, reeMat_yb, ← map_mul, ← map_pow, ree_check.2.2.2.1]

theorem specialIsogeny_reeU : PrimeField.specialIsogeny L (reeU L) = reeU L := by
  apply reeMat_injective
  rw [reeU, map_pow, map_mul, specialIsogeny_reeXa, specialIsogeny_reeXb, map_pow, map_mul,
    reeMat_xa,
    reeMat_xb, ← map_mul, ← map_pow, ree_check.2.1, ← reeMat_u, reeU]

theorem specialIsogeny_reeV : PrimeField.specialIsogeny L (reeV L) = reeV L := by
  apply reeMat_injective
  rw [reeV, map_pow, map_mul, specialIsogeny_reeYa, specialIsogeny_reeYb, map_pow, map_mul,
    reeMat_ya,
    reeMat_yb, ← map_mul, ← map_pow, ree_check.2.2.2.2.1, ← reeMat_v, reeV]

noncomputable abbrev reeT : PrimeField.points L := reePhi1 L (-1)

theorem reeMat_t : reeMat L (reeT L) = reeF L reeTZ := by
  change (((reePhi1 L (-1) : PrimeField.points L) : Matrix.GeneralLinearGroup (Fin 7) L) :
    Matrix (Fin 7) (Fin 7) L) = _
  rw [coe_reePhi1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phi1Mat, reeTZ, two_eq_neg_one_of_charThree]

@[expose] noncomputable def reeG : PrimeField.points L := reeU L * reeV L * reeU L ^ 2 * reeV L

@[expose] noncomputable def reeH : PrimeField.points L := reeU L * reeV L ^ 2 * reeU L * reeV L

@[expose] noncomputable def reeGi : PrimeField.points L :=
  reeV L ^ 2 * reeU L * reeV L ^ 2 * reeU L ^ 2

@[expose] noncomputable def reeHi : PrimeField.points L :=
  reeV L ^ 2 * reeU L ^ 2 * reeV L * reeU L ^ 2

theorem reeMat_g : reeMat L (reeG L) = reeF L reeGZ := by
  rw [reeG, reeGZ]
  simp only [map_mul, map_pow, reeMat_u, reeMat_v]

theorem reeMat_h : reeMat L (reeH L) = reeF L reeHZ := by
  rw [reeH, reeHZ]
  simp only [map_mul, map_pow, reeMat_u, reeMat_v]

theorem reeMat_gi : reeMat L (reeGi L) = reeF L reeGiZ := by
  rw [reeGi, reeGiZ]
  simp only [map_mul, map_pow, reeMat_u, reeMat_v]

theorem reeMat_hi : reeMat L (reeHi L) = reeF L reeHiZ := by
  rw [reeHi, reeHiZ]
  simp only [map_mul, map_pow, reeMat_u, reeMat_v]

theorem ree_commutator : ⁅reeG L, reeH L⁆ = reeT L := by
  have hg : reeGi L = (reeG L)⁻¹ := eq_inv_of_mul_eq_one_right (reeMat_injective L (by
    rw [map_mul, reeMat_g, reeMat_gi, ← map_mul, ree_check.2.2.2.2.2.1, map_one, map_one]))
  have hh : reeHi L = (reeH L)⁻¹ := eq_inv_of_mul_eq_one_right (reeMat_injective L (by
    rw [map_mul, reeMat_h, reeMat_hi, ← map_mul, ree_check.2.2.2.2.2.2.1, map_one, map_one]))
  rw [commutatorElement_def, ← hg, ← hh]
  apply reeMat_injective
  rw [map_mul, map_mul, map_mul, reeMat_g, reeMat_h, reeMat_gi, reeMat_hi, reeMat_t, ← map_mul,
    ← map_mul, ← map_mul, ree_check.2.2.2.2.2.2.2.1]

theorem ree_t_not_commute :
    reeT L * (reeU L * reeT L * reeU L ^ 2) ≠ reeU L * reeT L * reeU L ^ 2 * reeT L := by
  intro h
  apply ree_check.2.2.2.2.2.2.2.2
  apply reeF_injective L
  have h' := congrArg (reeMat L) h
  simpa only [map_mul, map_pow, reeMat_t, reeMat_u] using h'

theorem reeU_pow_three : reeU L ^ 3 = 1 :=
  reeMat_injective L (by rw [map_pow, reeMat_u, ← map_pow, ree_check.2.2.1, map_one, map_one])

end Transfer

end CFSG.RankThree.PartTwo.Census.Exceptional
