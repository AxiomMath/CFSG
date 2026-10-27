module

public import CFSG.RankThree.CentralCover.LinearUnitaryFourGroupWitness
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData

public noncomputable section

universe u

namespace CFSG.RankThree.CentralCover

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
open scoped Pointwise

namespace CycledFourGroup

variable {T : Type*} [Group T] {v₁ v₂ v₃ a b : T}

theorem exists_witness (h : CycledFourGroup v₁ v₂ v₃ a) (hb : b⁻¹ * a * b = a⁻¹)
    {V : Subgroup T} (hV : (V : Set T) = {1, v₁, v₂, v₃}) :
    ∃ (V : Subgroup T) (a b : T), IsKleinFour V ∧ orderOf a = 3 ∧ a ∈ normalizer (V : Set T) ∧
      b⁻¹ * a * b = a⁻¹ ∧
      (∃ w₁ w₂ w₃ : T, (V : Set T) = {1, w₁, w₂, w₃} ∧ w₁ ≠ 1 ∧ w₂ ≠ 1 ∧ w₃ ≠ 1 ∧ w₁ ≠ w₂ ∧
        w₁ ≠ w₃ ∧ w₂ ≠ w₃ ∧ a * w₁ * a⁻¹ = w₂ ∧ a * w₂ * a⁻¹ = w₃ ∧ a * w₃ * a⁻¹ = w₁) ∧
      V ⊓ zpowers a = ⊥ ∧ (V : Set T) * (zpowers a : Set T) = (V ⊔ zpowers a : Subgroup T) ∧
      Nat.card (V ⊔ zpowers a : Subgroup T) = 12 ∧
      ∀ (K : Type u) [Group K] [Finite K] (π : K →* T), Function.Surjective π →
        π.ker ≤ center K → IsPGroup 3 π.ker →
        (∃! U : Subgroup K, IsPGroup 2 U ∧ U.map π = V ∧ Set.InjOn π U) ∧
        ∀ U : Subgroup K, IsPGroup 2 U → U.map π = V → Set.InjOn π U →
          π.ker ⊓ U = ⊥ ∧ π.ker ⊔ U = V.comap π ∧
          ∃ x ∈ normalizer (U : Set K), orderOf x = 3 ∧ π x = a ∧
            (∃ u₁ u₂ u₃ : K, (U : Set K) = {1, u₁, u₂, u₃} ∧ u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₃ ≠ 1 ∧
              u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧
              x * u₁ * x⁻¹ = u₂ ∧ x * u₂ * x⁻¹ = u₃ ∧ x * u₃ * x⁻¹ = u₁) ∧
            x ∉ center K ∧ U ⊓ zpowers x = ⊥ ∧
            (U : Set K) * (zpowers x : Set K) = (U ⊔ zpowers x : Subgroup K) ∧
            (U ⊔ zpowers x).map π = V ⊔ zpowers a ∧
            Set.InjOn π (U ⊔ zpowers x : Subgroup K) ∧
            π.ker ⊓ (U ⊔ zpowers x) = ⊥ ∧
            π.ker ⊔ (U ⊔ zpowers x) = (V ⊔ zpowers a).comap π := by
  obtain ⟨hK, ha3, hN, hdisj, hmul, hcard⟩ := h.quotient_facts hV
  refine ⟨V, a, b, hK, ha3, hN, hb, ⟨v₁, v₂, v₃, hV, h.ne_one, h.two_ne_one, h.three_ne_one,
    h.one_ne_two, h.one_ne_three, h.two_ne_three, h.conj_one, h.conj_two, h.conj_three⟩, hdisj,
    hmul, hcard, ?_⟩
  intro K _ _ π hπ hZ hZ3
  exact h.cover hb hV π hπ hZ hZ3

end CycledFourGroup

section Odd

variable {F : Type} [Field F] {α β : F}

@[expose] def quatBasis (h : α ^ 2 + β ^ 2 = -1) :
    QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) F) (-1 : F) 0 (-1) where
  i := quatI F
  j := quatJ α β
  k := quatI F * quatJ α β
  i_mul_i := by
    rw [quatI_mul_self]
    simp
  j_mul_j := by
    rw [quatJ_mul_self h]
    simp
  i_mul_j := rfl
  j_mul_i := by
    rw [quatI_mul_quatJ_eq_neg]
    simp

@[expose] def quatMat (h : α ^ 2 + β ^ 2 = -1) :
    QuaternionAlgebra F (-1) 0 (-1) →ₐ[F] Matrix (Fin 2) (Fin 2) F :=
  QuaternionAlgebra.lift (quatBasis h)

theorem quatMat_imI (h : α ^ 2 + β ^ 2 = -1) :
    quatMat h ⟨0, 1, 0, 0⟩ = quatI F := by
  change algebraMap F _ 0 + (1 : F) • quatI F + (0 : F) • quatJ α β +
    (0 : F) • (quatI F * quatJ α β) = quatI F
  simp

@[expose] def quatGL (h : α ^ 2 + β ^ 2 = -1) (x y : QuaternionAlgebra F (-1) 0 (-1))
    (hxy : x * y = 1) (hyx : y * x = 1) : GL (Fin 2) F :=
  ⟨quatMat h x, quatMat h y, by rw [← map_mul, hxy, map_one], by rw [← map_mul, hyx, map_one]⟩

variable (h : α ^ 2 + β ^ 2 = -1) (h2 : (2 : F) ≠ 0)

@[expose] def oddI : GL (Fin 2) F :=
  quatGL h ⟨0, 1, 0, 0⟩ ⟨0, -1, 0, 0⟩ (by ext <;> simp) (by ext <;> simp)

@[expose] def oddJ : GL (Fin 2) F :=
  quatGL h ⟨0, 0, 1, 0⟩ ⟨0, 0, -1, 0⟩ (by ext <;> simp) (by ext <;> simp)

@[expose] def oddK : GL (Fin 2) F :=
  quatGL h ⟨0, 0, 0, 1⟩ ⟨0, 0, 0, -1⟩ (by ext <;> simp) (by ext <;> simp)

@[expose] def oddH : GL (Fin 2) F :=
  quatGL h ⟨-2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹⟩ ⟨-2⁻¹, -2⁻¹, -2⁻¹, -2⁻¹⟩
    (by ext; all_goals simp; all_goals field_simp; all_goals ring)
    (by ext; all_goals simp; all_goals field_simp; all_goals ring)

@[expose] def oddD : GL (Fin 2) F :=
  quatGL h ⟨0, 1, -1, 0⟩ ⟨0, -2⁻¹, 2⁻¹, 0⟩
    (by ext; all_goals simp; all_goals field_simp; all_goals ring)
    (by ext; all_goals simp; all_goals field_simp; all_goals ring)

theorem oddI_sq : oddI h ^ 2 = -1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  change quatMat h ⟨0, 1, 0, 0⟩ ^ 2 = -1
  rw [← map_pow, ← map_one (quatMat h), ← map_neg]
  congr 1
  ext <;> simp [sq]

theorem oddI_mul_oddK : oddI h * oddK h = -1 * oddJ h := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_neg, Units.val_one]
  change quatMat h ⟨0, 1, 0, 0⟩ * quatMat h ⟨0, 0, 0, 1⟩ = -1 * quatMat h ⟨0, 0, 1, 0⟩
  rw [← map_mul, ← map_one (quatMat h), ← map_neg, ← map_mul]
  congr 1
  ext <;> simp

theorem oddH_conj_oddI : oddH h h2 * oddI h * (oddH h h2)⁻¹ = oddK h := by
  apply Units.ext
  change quatMat h ⟨-2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹⟩ * quatMat h ⟨0, 1, 0, 0⟩ *
    quatMat h ⟨-2⁻¹, -2⁻¹, -2⁻¹, -2⁻¹⟩ = quatMat h ⟨0, 0, 0, 1⟩
  rw [← map_mul, ← map_mul]
  congr 1
  ext
  all_goals simp
  all_goals field_simp
  all_goals ring

theorem oddH_conj_oddK : oddH h h2 * oddK h * (oddH h h2)⁻¹ = oddJ h := by
  apply Units.ext
  change quatMat h ⟨-2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹⟩ * quatMat h ⟨0, 0, 0, 1⟩ *
    quatMat h ⟨-2⁻¹, -2⁻¹, -2⁻¹, -2⁻¹⟩ = quatMat h ⟨0, 0, 1, 0⟩
  rw [← map_mul, ← map_mul]
  congr 1
  ext
  all_goals simp
  all_goals field_simp
  all_goals ring

theorem oddH_cube : oddH h h2 ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  change quatMat h ⟨-2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹⟩ ^ 3 = 1
  rw [← map_pow, ← map_one (quatMat h)]
  congr 1
  ext
  all_goals simp [pow_three]
  all_goals field_simp
  all_goals ring

theorem oddD_conj_oddH : (oddD h h2)⁻¹ * oddH h h2 * oddD h h2 = (oddH h h2)⁻¹ := by
  apply Units.ext
  change quatMat h ⟨0, -2⁻¹, 2⁻¹, 0⟩ * quatMat h ⟨-2⁻¹, 2⁻¹, 2⁻¹, 2⁻¹⟩ *
    quatMat h ⟨0, 1, -1, 0⟩ = quatMat h ⟨-2⁻¹, -2⁻¹, -2⁻¹, -2⁻¹⟩
  rw [← map_mul, ← map_mul]
  congr 1
  ext
  all_goals simp
  all_goals field_simp
  all_goals ring

variable (F) in
@[expose] def spLeviProj : GL (Fin 2) F →* StatedProj (StatedSp 2 F) :=
  (statedProjMk (StatedSp 2 F)).comp SymplecticTorusWeyl.leviSp

omit h h2 in
theorem spLeviProj_neg_one : spLeviProj F (-1) = 1 := by
  change (QuotientGroup.mk (SymplecticTorusWeyl.leviSp (-1 : GL (Fin 2) F)) :
    StatedProj (StatedSp 2 F)) = 1
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hinv : (-1 : GL (Fin 2) F)⁻¹ = -1 := inv_eq_of_mul_eq_one_right (by simp)
  refine ⟨-1, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, SymplecticTorusWeyl.coe_leviSp, hinv]
  simp only [Units.val_neg, Units.val_one, transpose_neg, transpose_one]
  ext (i | i) (j | j)
  all_goals simp only [Matrix.scalar_apply, diagonal_apply, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.neg_apply,
    Matrix.one_apply, Matrix.zero_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq]
  all_goals split_ifs
  all_goals simp_all

theorem spLeviProj_oddI_ne_one : spLeviProj F (oddI h) ≠ 1 := by
  intro h1
  change (QuotientGroup.mk (SymplecticTorusWeyl.leviSp (oddI h)) :
    StatedProj (StatedSp 2 F)) = 1 at h1
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
  obtain ⟨c, hc⟩ := h1
  have h01 := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) F =>
    (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (Sum.inl 0) (Sum.inl 1)) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    SymplecticTorusWeyl.coe_leviSp] at h01
  change _ = (quatMat h ⟨0, 1, 0, 0⟩) 0 1 at h01
  rw [quatMat_imI] at h01
  simp [quatI] at h01

theorem oddSpCycled :
    CycledFourGroup (spLeviProj F (oddI h)) (spLeviProj F (oddK h)) (spLeviProj F (oddJ h))
      (spLeviProj F (oddH h h2)) where
  ne_one := spLeviProj_oddI_ne_one h
  sq_eq_one := by rw [← map_pow, oddI_sq, spLeviProj_neg_one]
  mul_eq := by rw [← map_mul, oddI_mul_oddK, map_mul, spLeviProj_neg_one, one_mul]
  conj_one := by rw [← map_inv, ← map_mul, ← map_mul, oddH_conj_oddI]
  conj_two := by rw [← map_inv, ← map_mul, ← map_mul, oddH_conj_oddK]
  cube := by rw [← map_pow, oddH_cube, map_one]

theorem oddSp_conj :
    (spLeviProj F (oddD h h2))⁻¹ * spLeviProj F (oddH h h2) * spLeviProj F (oddD h h2) =
      (spLeviProj F (oddH h h2))⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul, oddD_conj_oddH, map_inv]

end Odd

section Even

variable (F : Type) [Field F] [CharP F 2]

@[expose] def evenM : GL (Fin 2) F :=
  ⟨!![0, 1; 1, 1], !![1, 1; 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_two, one_apply, CharTwo.add_self_eq_zero],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_two, one_apply, CharTwo.add_self_eq_zero]⟩

@[expose] def evenN : GL (Fin 2) F :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, one_apply],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, one_apply]⟩

omit [Field F] [CharP F 2] in
theorem transpose_sym (b c d : F) :
    (!![b, c; c, d] : Matrix (Fin 2) (Fin 2) F)ᵀ = !![b, c; c, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def evenU₁Sp : StatedSp 2 F :=
  SymplecticFlag.upperUnipotentSp 2 F (transpose_sym F 1 0 1)

@[expose] def evenU₂Sp : StatedSp 2 F :=
  SymplecticFlag.upperUnipotentSp 2 F (transpose_sym F 1 1 0)

@[expose] def evenU₃Sp : StatedSp 2 F :=
  SymplecticFlag.upperUnipotentSp 2 F (transpose_sym F 0 1 1)

theorem evenSpCycled :
    CycledFourGroup (evenU₁Sp F) (evenU₂Sp F) (evenU₃Sp F)
      (SymplecticTorusWeyl.leviSp (evenM F)) where
  ne_one h1 := by
    have h' := congrArg (fun g : StatedSp 2 F =>
      ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
        (Sum.inl 0) (Sum.inr 0)) h1
    simp [evenU₁Sp, SymplecticFlag.coe_upperUnipotentSp] at h'
  sq_eq_one := by
    apply SymplecticTorusWeyl.statedSp_ext
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, evenU₁Sp,
      SymplecticFlag.coe_upperUnipotentSp]
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [sq, mul_apply, Fintype.sum_sum_type, one_apply, CharTwo.add_self_eq_zero]
  mul_eq := by
    apply SymplecticTorusWeyl.statedSp_ext
    rw [Subgroup.coe_mul, Units.val_mul, evenU₁Sp, evenU₂Sp, evenU₃Sp,
      SymplecticFlag.coe_upperUnipotentSp, SymplecticFlag.coe_upperUnipotentSp,
      SymplecticFlag.coe_upperUnipotentSp]
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fintype.sum_sum_type, one_apply, CharTwo.add_self_eq_zero]
  conj_one := by
    apply SymplecticTorusWeyl.statedSp_ext
    rw [← map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
      SymplecticTorusWeyl.coe_leviSp, SymplecticTorusWeyl.coe_leviSp, inv_inv, evenU₁Sp,
      evenU₂Sp, SymplecticFlag.coe_upperUnipotentSp, SymplecticFlag.coe_upperUnipotentSp]
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [evenM, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, one_apply,
        CharTwo.add_self_eq_zero]
  conj_two := by
    apply SymplecticTorusWeyl.statedSp_ext
    rw [← map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
      SymplecticTorusWeyl.coe_leviSp, SymplecticTorusWeyl.coe_leviSp, inv_inv, evenU₂Sp,
      evenU₃Sp, SymplecticFlag.coe_upperUnipotentSp, SymplecticFlag.coe_upperUnipotentSp]
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [evenM, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, one_apply,
        CharTwo.add_self_eq_zero]
  cube := by
    rw [← map_pow, show evenM F ^ 3 = 1 from Units.ext (by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [evenM, pow_three, mul_apply, Fin.sum_univ_two, one_apply,
          CharTwo.add_self_eq_zero]), map_one]

theorem evenSp_conj :
    (SymplecticTorusWeyl.leviSp (evenN F))⁻¹ * SymplecticTorusWeyl.leviSp (evenM F) *
      SymplecticTorusWeyl.leviSp (evenN F) = (SymplecticTorusWeyl.leviSp (evenM F))⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
  congr 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evenM, evenN, mul_apply, Fin.sum_univ_two]

omit [CharP F 2] in
theorem evenSp_sq : SymplecticTorusWeyl.leviSp (evenN F) ^ 2 = 1 := by
  rw [← map_pow, show evenN F ^ 2 = 1 from Units.ext (by
    ext i j; fin_cases i <;> fin_cases j <;> simp [evenN, sq, mul_apply, Fin.sum_univ_two,
      one_apply]), map_one]

end Even

theorem symplectic_four_central_three_cover_four_group_witness (F : Type) [Field F] [Finite F] :
    ∃ (V : Subgroup (StatedProj (StatedSp 2 F))) (a b : StatedProj (StatedSp 2 F)),
      IsKleinFour V ∧ orderOf a = 3 ∧ a ∈ normalizer (V : Set (StatedProj (StatedSp 2 F))) ∧
      b⁻¹ * a * b = a⁻¹ ∧
      (∃ w₁ w₂ w₃ : StatedProj (StatedSp 2 F), (V : Set (StatedProj (StatedSp 2 F))) =
        {1, w₁, w₂, w₃} ∧ w₁ ≠ 1 ∧ w₂ ≠ 1 ∧ w₃ ≠ 1 ∧ w₁ ≠ w₂ ∧ w₁ ≠ w₃ ∧ w₂ ≠ w₃ ∧
        a * w₁ * a⁻¹ = w₂ ∧ a * w₂ * a⁻¹ = w₃ ∧ a * w₃ * a⁻¹ = w₁) ∧
      V ⊓ zpowers a = ⊥ ∧
      (V : Set (StatedProj (StatedSp 2 F))) * (zpowers a : Set (StatedProj (StatedSp 2 F))) =
        (V ⊔ zpowers a : Subgroup (StatedProj (StatedSp 2 F))) ∧
      Nat.card (V ⊔ zpowers a : Subgroup (StatedProj (StatedSp 2 F))) = 12 ∧
      ∀ (K : Type u) [Group K] [Finite K] (π : K →* StatedProj (StatedSp 2 F)),
        Function.Surjective π → π.ker ≤ center K → IsPGroup 3 π.ker →
        (∃! U : Subgroup K, IsPGroup 2 U ∧ U.map π = V ∧ Set.InjOn π U) ∧
        ∀ U : Subgroup K, IsPGroup 2 U → U.map π = V → Set.InjOn π U →
          π.ker ⊓ U = ⊥ ∧ π.ker ⊔ U = V.comap π ∧
          ∃ x ∈ normalizer (U : Set K), orderOf x = 3 ∧ π x = a ∧
            (∃ u₁ u₂ u₃ : K, (U : Set K) = {1, u₁, u₂, u₃} ∧ u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₃ ≠ 1 ∧
              u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧
              x * u₁ * x⁻¹ = u₂ ∧ x * u₂ * x⁻¹ = u₃ ∧ x * u₃ * x⁻¹ = u₁) ∧
            x ∉ center K ∧ U ⊓ zpowers x = ⊥ ∧
            (U : Set K) * (zpowers x : Set K) = (U ⊔ zpowers x : Subgroup K) ∧
            (U ⊔ zpowers x).map π = V ⊔ zpowers a ∧
            Set.InjOn π (U ⊔ zpowers x : Subgroup K) ∧
            π.ker ⊓ (U ⊔ zpowers x) = ⊥ ∧
            π.ker ⊔ (U ⊔ zpowers x) = (V ⊔ zpowers a).comap π := by
  by_cases hF : ringChar F = 2
  · have : CharP F 2 := ringChar.eq_iff.1 hF
    obtain ⟨-, h', hV, hbc, -⟩ := (evenSpCycled F).quotient_witness (evenSp_conj F)
      (evenSp_sq F) (statedProjMk (StatedSp 2 F)) (ker_statedProjMk_le_center _)
    exact h'.exists_witness hbc hV
  · obtain ⟨α, β, h⟩ := (odd_field_two_dimensional_quaternion_matrices hF).1
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    have hc := oddSpCycled h h2
    exact hc.exists_witness (oddSp_conj h h2) hc.coe_closure

end CFSG.RankThree.CentralCover
