module

public import CFSG.RankThree.PartOne.KC.OrthogonalEvenNormPlane
public import CFSG.LocalAnalysis.SteinbergCEPfaffianFour
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenNormTail

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module Matrix CFSG.LocalAnalysis

section Matrices

variable {E : Type} [Field E]

@[expose] def evenSixHerm (E : Type) [Field E] : Matrix (Fin 4) (Fin 4) E :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

theorem evenSixHerm_transpose : (evenSixHerm E)ᵀ = evenSixHerm E := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evenSixHerm]

theorem evenSixHerm_mul_self : evenSixHerm E * evenSixHerm E = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evenSixHerm, Matrix.mul_apply, Fin.sum_univ_four]

theorem evenSixHerm_map {F : Type*} [FunLike F E E] [RingHomClass F E E] (σ : F) :
    (evenSixHerm E).map σ = evenSixHerm E := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evenSixHerm]

theorem evenSixHerm_mul_altMat_mul (a b c d e f : E) :
    evenSixHerm E * altMat a b c d e f * evenSixHerm E = altMat f b d c e a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evenSixHerm, altMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem evenSix_map_altMat {F : Type*} [FunLike F E E] [RingHomClass F E E] (σ : F)
    (a b c d e f : E) :
    (altMat a b c d e f).map σ = altMat (σ a) (σ b) (σ c) (σ d) (σ e) (σ f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [altMat]

theorem evenSix_altMat_inj {a b c d e f a' b' c' d' e' f' : E}
    (h : altMat a b c d e f = altMat a' b' c' d' e' f') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e' ∧ f = f' := by
  have h01 := congrFun (congrFun h 0) 1
  have h02 := congrFun (congrFun h 0) 2
  have h03 := congrFun (congrFun h 0) 3
  have h12 := congrFun (congrFun h 1) 2
  have h13 := congrFun (congrFun h 1) 3
  have h23 := congrFun (congrFun h 2) 3
  simp [altMat] at h01 h02 h03 h12 h13 h23
  exact ⟨h01, h02, h03, h12, h13, h23⟩

theorem evenSix_sharp_altMat (a b c d e f : E) :
    sharp (altMat a b c d e f) = altMat f e d c b a := by
  simp [sharp, altMat]

theorem evenSix_altMat_add (a b c d e f a' b' c' d' e' f' : E) :
    altMat (a + a') (b + b') (c + c') (d + d') (e + e') (f + f') =
      altMat a b c d e f + altMat a' b' c' d' e' f' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [altMat]

theorem evenSix_altMat_zero : altMat (0 : E) 0 0 0 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [altMat]

theorem evenSix_altMat_smul {R : Type*} [SMulZeroClass R E] (r : R) (a b c d e f : E) :
    altMat (r • a) (r • b) (r • c) (r • d) (r • e) (r • f) = r • altMat a b c d e f := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [altMat]

end Matrices

section Group

variable {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type} [Field E] [Algebra K E]

theorem evenSix_conj_mul {F : Type*} [FunLike F E E] [RingHomClass F E E] (σ : F)
    (G A B : Matrix (Fin 4) (Fin 4) E) :
    ((A * B).map σ)ᵀ * G * (A * B) = (B.map σ)ᵀ * ((A.map σ)ᵀ * G * A) * B := by
  rw [Matrix.map_mul, transpose_mul]
  simp only [Matrix.mul_assoc]

@[expose] def EvenNormPlane.sixSU (D : EvenNormPlane K E) : Subgroup (GL (Fin 4) E) where
  carrier := {g | ((g : Matrix (Fin 4) (Fin 4) E).map D.σ)ᵀ * evenSixHerm E * g =
      evenSixHerm E ∧ (g : Matrix (Fin 4) (Fin 4) E).det = 1}
  mul_mem' {g g'} hg hg' := by
    refine ⟨?_, by rw [Units.val_mul, det_mul, hg.2, hg'.2, one_mul]⟩
    rw [Units.val_mul, evenSix_conj_mul, hg.1, hg'.1]
  one_mem' := ⟨by simp [Matrix.map_one _ (map_zero D.σ) (map_one D.σ)], by simp⟩
  inv_mem' {g} hg := by
    have hgg : (g : Matrix (Fin 4) (Fin 4) E) *
        ((g⁻¹ : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine ⟨?_, ?_⟩
    · have := evenSix_conj_mul D.σ (evenSixHerm E) (g : Matrix (Fin 4) (Fin 4) E)
        ((g⁻¹ : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E)
      rw [hg.1, hgg] at this
      simpa [Matrix.map_one _ (map_zero D.σ) (map_one D.σ)] using this.symm
    · have := congrArg det hgg
      rwa [det_mul, hg.2, one_mul, det_one] at this

theorem EvenNormPlane.mem_sixSU {D : EvenNormPlane K E} {g : GL (Fin 4) E} :
    g ∈ D.sixSU ↔ ((g : Matrix (Fin 4) (Fin 4) E).map D.σ)ᵀ * evenSixHerm E * g =
      evenSixHerm E ∧ (g : Matrix (Fin 4) (Fin 4) E).det = 1 :=
  Iff.rfl

@[expose] def EvenNormPlane.sixSpace (D : EvenNormPlane K E) :
    Submodule K (Matrix (Fin 4) (Fin 4) E) where
  carrier := {X | IsAltMat X ∧ sharp X = evenSixHerm E * X.map D.σ * evenSixHerm E}
  add_mem' {X Y} hX hY := by
    have hmap : (X + Y).map D.σ = X.map D.σ + Y.map D.σ := by
      ext i j
      simp
    refine ⟨⟨by rw [transpose_add, hX.1.1, hY.1.1], fun i => by
      rw [Matrix.add_apply, hX.1.2 i, hY.1.2 i, add_zero]⟩, ?_⟩
    rw [sharp_add, hX.2, hY.2, hmap, Matrix.mul_add, Matrix.add_mul]
  zero_mem' := by
    refine ⟨⟨by simp, fun i => by simp⟩, ?_⟩
    simp [sharp, evenSix_altMat_zero]
  smul_mem' k X hX := by
    have hmap : (k • X).map D.σ = k • X.map D.σ := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply]
      rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, ← Algebra.smul_def]
    refine ⟨⟨by rw [transpose_smul, hX.1.1], fun i => by simp [hX.1.2 i]⟩, ?_⟩
    have hs : sharp (k • X) = k • sharp X := by
      simp only [sharp, Matrix.smul_apply]
      exact evenSix_altMat_smul k _ _ _ _ _ _
    rw [hs, hmap, hX.2, Matrix.mul_smul, Matrix.smul_mul]

theorem EvenNormPlane.mem_sixSpace {D : EvenNormPlane K E} {X : Matrix (Fin 4) (Fin 4) E} :
    X ∈ D.sixSpace ↔ IsAltMat X ∧ sharp X = evenSixHerm E * X.map D.σ * evenSixHerm E :=
  Iff.rfl

end Group

section Coordinates

variable {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type} [Field E] [Algebra K E]
  (D : EvenNormPlane K E)

@[expose] def EvenNormPlane.sixMat (a c d f₀ : K) (b : E) : Matrix (Fin 4) (Fin 4) E :=
  altMat (algebraMap K E a) b (algebraMap K E c) (algebraMap K E d) (D.σ b) (algebraMap K E f₀)

theorem EvenNormPlane.sixMat_inj {a c d f₀ a' c' d' f₀' : K} {b b' : E}
    (h : D.sixMat a c d f₀ b = D.sixMat a' c' d' f₀' b') :
    a = a' ∧ c = c' ∧ d = d' ∧ f₀ = f₀' ∧ b = b' := by
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := evenSix_altMat_inj h
  exact ⟨(algebraMap K E).injective h1, (algebraMap K E).injective h3,
    (algebraMap K E).injective h4, (algebraMap K E).injective h6, h2⟩

theorem EvenNormPlane.mem_sixSpace_iff (X : Matrix (Fin 4) (Fin 4) E) :
    X ∈ D.sixSpace ↔ ∃ (a c d f₀ : K) (b : E), X = D.sixMat a c d f₀ b := by
  constructor
  · rintro ⟨hX, hs⟩
    obtain ⟨a, b, c, d, e, f, rfl⟩ : ∃ a b c d e f, X = altMat a b c d e f :=
      ⟨_, _, _, _, _, _, eq_altMat_of_isAltMat hX⟩
    rw [evenSix_sharp_altMat, evenSix_map_altMat, evenSixHerm_mul_altMat_mul] at hs
    obtain ⟨hf, he, hd, hc, hb, ha⟩ := evenSix_altMat_inj hs
    obtain ⟨a', rfl⟩ := (D.sigma_eq_self_iff a).1 ha.symm
    obtain ⟨c', rfl⟩ := (D.sigma_eq_self_iff c).1 hc.symm
    obtain ⟨d', rfl⟩ := (D.sigma_eq_self_iff d).1 hd.symm
    obtain ⟨f', rfl⟩ := (D.sigma_eq_self_iff f).1 hf.symm
    exact ⟨a', c', d', f', b, by rw [he]; rfl⟩
  · rintro ⟨a, c, d, f₀, b, rfl⟩
    refine ⟨isAltMat_altMat _ _ _ _ _ _, ?_⟩
    rw [EvenNormPlane.sixMat, evenSix_sharp_altMat, evenSix_map_altMat, evenSixHerm_mul_altMat_mul]
    simp [AlgEquiv.commutes, D.sigma_sigma]

theorem EvenNormPlane.sixMat_mem (a c d f₀ : K) (b : E) : D.sixMat a c d f₀ b ∈ D.sixSpace :=
  (D.mem_sixSpace_iff _).2 ⟨a, c, d, f₀, b, rfl⟩

@[expose] def EvenNormPlane.sixToMat :
    (((Fin 2 → K) × (Fin 2 → K)) × E) →ₗ[K] Matrix (Fin 4) (Fin 4) E where
  toFun v := altMat (algebraMap K E (v.1.1 0)) v.2 (algebraMap K E (v.1.1 1))
    (algebraMap K E (v.1.2 1)) (D.σ v.2) (algebraMap K E (v.1.2 0))
  map_add' v w := by
    rw [← evenSix_altMat_add]
    simp
  map_smul' c v := by
    rw [RingHom.id_apply, ← evenSix_altMat_smul]
    simp [Algebra.smul_def]

theorem EvenNormPlane.sixToMat_apply (x y : Fin 2 → K) (z : E) :
    D.sixToMat ((x, y), z) = D.sixMat (x 0) (x 1) (y 1) (y 0) z :=
  rfl

theorem EvenNormPlane.sixToMat_injective : Function.Injective D.sixToMat := by
  rintro ⟨⟨x, y⟩, z⟩ ⟨⟨x', y'⟩, z'⟩ h
  rw [EvenNormPlane.sixToMat_apply, EvenNormPlane.sixToMat_apply] at h
  obtain ⟨h1, h3, h4, h6, h2⟩ := D.sixMat_inj h
  have hx : x = x' := by
    funext i
    fin_cases i
    · exact h1
    · exact h3
  have hy : y = y' := by
    funext i
    fin_cases i
    · exact h6
    · exact h4
  rw [hx, hy, h2]

theorem EvenNormPlane.range_sixToMat : LinearMap.range D.sixToMat = D.sixSpace := by
  ext X
  rw [LinearMap.mem_range, D.mem_sixSpace_iff]
  constructor
  · rintro ⟨⟨⟨x, y⟩, z⟩, rfl⟩
    exact ⟨x 0, x 1, y 1, y 0, z, rfl⟩
  · rintro ⟨a, c, d, f₀, b, rfl⟩
    exact ⟨((![a, c], ![f₀, d]), b), by simp [EvenNormPlane.sixToMat_apply]⟩

@[expose] noncomputable def EvenNormPlane.sixCoord :
    (((Fin 2 → K) × (Fin 2 → K)) × E) ≃ₗ[K] D.sixSpace :=
  (LinearEquiv.ofInjective D.sixToMat D.sixToMat_injective).trans
    (LinearEquiv.ofEq _ _ D.range_sixToMat)

theorem EvenNormPlane.coe_sixCoord (v : ((Fin 2 → K) × (Fin 2 → K)) × E) :
    ((D.sixCoord v : D.sixSpace) : Matrix (Fin 4) (Fin 4) E) =
      D.sixMat (v.1.1 0) (v.1.1 1) (v.1.2 1) (v.1.2 0) v.2 :=
  rfl

@[expose] noncomputable def EvenNormPlane.sixForm : QuadraticForm K D.sixSpace :=
  (evenNormTailForm D.N 2).comp (D.sixCoord.symm : D.sixSpace →ₗ[K] _)

theorem EvenNormPlane.sixForm_sixCoord (v : ((Fin 2 → K) × (Fin 2 → K)) × E) :
    D.sixForm (D.sixCoord v) = evenNormTailForm D.N 2 v := by
  simp [EvenNormPlane.sixForm]

@[expose] noncomputable def EvenNormPlane.sixIsometry :
    (evenNormTailForm D.N 2).IsometryEquiv D.sixForm where
  toLinearEquiv := D.sixCoord
  map_app' := D.sixForm_sixCoord

theorem EvenNormPlane.algebraMap_sixForm (X : D.sixSpace) :
    algebraMap K E (D.sixForm X) = pfaff (X : Matrix (Fin 4) (Fin 4) E) := by
  obtain ⟨v, rfl⟩ := D.sixCoord.surjective X
  obtain ⟨⟨x, y⟩, z⟩ := v
  rw [D.sixForm_sixCoord, EvenNormPlane.coe_sixCoord, evenNormTailForm_apply]
  simp only [EvenNormPlane.sixMat, pfaff, altMat, Fin.sum_univ_two, map_add, map_mul,
    D.algebraMap_N]
  simp
  ring

@[expose] def EvenNormPlane.sixElement (a c d f₀ : K) (b : E) : D.sixSpace :=
  ⟨D.sixMat a c d f₀ b, D.sixMat_mem a c d f₀ b⟩

theorem EvenNormPlane.sixElement_eq_sixCoord (a c d f₀ : K) (b : E) :
    D.sixElement a c d f₀ b = D.sixCoord ((![a, c], ![f₀, d]), b) :=
  rfl

theorem EvenNormPlane.sixForm_sixElement (a c d f₀ : K) (b : E) :
    D.sixForm (D.sixElement a c d f₀ b) = a * f₀ + c * d + D.N b := by
  rw [D.sixElement_eq_sixCoord, D.sixForm_sixCoord, evenNormTailForm_apply]
  simp [Fin.sum_univ_two]

theorem EvenNormPlane.exists_sixElement_eq (X : D.sixSpace) :
    ∃ (a c d f₀ : K) (b : E), X = D.sixElement a c d f₀ b := by
  obtain ⟨a, c, d, f₀, b, hX⟩ := (D.mem_sixSpace_iff X.1).1 X.2
  exact ⟨a, c, d, f₀, b, Subtype.ext hX⟩

end Coordinates

end CFSG.RankThree.PartOne.KCOrthogonal
