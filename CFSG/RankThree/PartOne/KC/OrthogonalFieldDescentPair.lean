module

public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutSemilinear
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalDescent

open Matrix CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

variable {K : Type} [Field K] {d : ℕ}

abbrev sc (c : Kˣ) : GL (Fin d) K := GeneralLinearGroup.scalar (Fin d) c

theorem sc_mul_comm (c : Kˣ) (X : GL (Fin d) K) : X * sc c = sc c * X := by
  have hmem : sc (d := d) c ∈ Subgroup.center (GL (Fin d) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  exact (Subgroup.mem_center_iff.mp hmem X)

theorem sc_mul_sc (c e : Kˣ) : sc (d := d) c * sc e = sc (c * e) :=
  (map_mul (GeneralLinearGroup.scalar (Fin d)) c e).symm

theorem sc_one : sc (d := d) (1 : Kˣ) = 1 := map_one (GeneralLinearGroup.scalar (Fin d))

theorem glFieldAut_sc (σ : K ≃+* K) (c : Kˣ) :
    glFieldAut (Fin d) K σ (sc c) = sc (Units.map σ.toMonoidHom c) :=
  glFieldEquiv_scalar (Fin d) σ c

theorem sc_apply_diag (c : Kˣ) (i : Fin d) :
    ((sc c : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i = c := by
  simp [sc, GeneralLinearGroup.scalar, Matrix.scalar_apply]

theorem sc_injective (hd : 0 < d) : Function.Injective (sc (d := d) (K := K)) := by
  intro c e h
  have := congrArg (fun X : GL (Fin d) K => (X : Matrix (Fin d) (Fin d) K) ⟨0, hd⟩ ⟨0, hd⟩) h
  simp only [sc_apply_diag] at this
  exact Units.ext this

theorem sc_mulVec (c : Kˣ) (v : Fin d → K) :
    ((sc c : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v = (c : K) • v := by
  ext i
  simp [sc, GeneralLinearGroup.scalar, Matrix.mulVec, dotProduct, Matrix.scalar_apply,
    Matrix.diagonal_apply]

@[expose] def twProd (σ : K ≃+* K) (A : GL (Fin d) K) : ℕ → GL (Fin d) K
  | 0 => 1
  | m + 1 => A * glFieldAut (Fin d) K σ (twProd σ A m)

theorem pow_left (g : coordinateSemilinearGroup d K) (m : ℕ) :
    (g ^ m).left = twProd g.right g.left m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ', coordinateSemilinearGroup_mul_matrix, ih]; rfl

theorem pow_right (g : coordinateSemilinearGroup d K) (m : ℕ) :
    (g ^ m).right = g.right ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ', coordinateSemilinearGroup_mul_field, ih, pow_succ']

@[expose] def normSeq (σ : K ≃+* K) (c : Kˣ) : ℕ → Kˣ
  | 0 => 1
  | m + 1 => c * Units.map σ.toMonoidHom (normSeq σ c m)

theorem coe_normSeq (σ : K ≃+* K) (c : Kˣ) (m : ℕ) :
    ((normSeq σ c m : Kˣ) : K) = ∏ i ∈ Finset.range m, (σ ^ i) (c : K) := by
  induction m with
  | zero => simp [normSeq]
  | succ m ih =>
    have h1 : ((Units.map σ.toMonoidHom (normSeq σ c m) : Kˣ) : K) =
        σ ((normSeq σ c m : Kˣ) : K) := rfl
    rw [Finset.prod_range_succ', normSeq, Units.val_mul, h1, ih, map_prod]
    simp only [pow_zero, RingAut.one_apply, pow_succ', RingAut.mul_apply]
    rw [mul_comm]

theorem twProd_sc_mul (σ : K ≃+* K) (c : Kˣ) (A : GL (Fin d) K) (m : ℕ) :
    twProd σ (sc c * A) m = sc (normSeq σ c m) * twProd σ A m := by
  induction m with
  | zero => simp [twProd, normSeq, sc_one]
  | succ m ih =>
    rw [twProd, ih, map_mul, glFieldAut_sc, twProd, normSeq]
    set X := glFieldAut (Fin d) K σ (twProd σ A m)
    set s : Kˣ := Units.map σ.toMonoidHom (normSeq σ c m)
    calc sc c * A * (sc s * X) = sc c * ((A * sc s) * X) := by group
      _ = sc c * ((sc s * A) * X) := by rw [sc_mul_comm]
      _ = (sc c * sc s) * (A * X) := by group
      _ = sc (c * s) * (A * X) := by rw [sc_mul_sc]

@[expose] def scalarPair (c : Kˣ) : coordinateSemilinearGroup d K :=
  SemidirectProduct.inl (sc c)

theorem scalarPair_mul_left (c : Kˣ) (g : coordinateSemilinearGroup d K) :
    (scalarPair c * g).left = sc c * g.left := by
  simp [scalarPair, SemidirectProduct.mul_left]

theorem scalarPair_mul_right (c : Kˣ) (g : coordinateSemilinearGroup d K) :
    (scalarPair c * g).right = g.right := by
  simp [scalarPair, SemidirectProduct.mul_right]

theorem pow_scalarPair_mul_left (c : Kˣ) (g : coordinateSemilinearGroup d K) (m : ℕ) :
    ((scalarPair c * g) ^ m).left = sc (normSeq g.right c m) * (g ^ m).left := by
  rw [pow_left, pow_left, scalarPair_mul_left, scalarPair_mul_right, twProd_sc_mul]

theorem pow_scalarPair_mul_right (c : Kˣ) (g : coordinateSemilinearGroup d K) (m : ℕ) :
    ((scalarPair c * g) ^ m).right = (g ^ m).right := by
  rw [pow_right, pow_right, scalarPair_mul_right]

theorem apply_eq_of_pow_scalar (hd : 0 < d) (g : coordinateSemilinearGroup d K) {p : ℕ} {b : Kˣ}
    (hb : (g ^ p).left = sc b) (hr : (g ^ p).right = 1) : g.right b = b := by
  have hcomm : g * g ^ p = g ^ p * g := (pow_succ' g p).symm.trans (pow_succ g p)
  have h1 := congrArg SemidirectProduct.left hcomm
  rw [coordinateSemilinearGroup_mul_matrix, coordinateSemilinearGroup_mul_matrix, hb, hr,
    glFieldAut_sc] at h1
  have h2 : glFieldAut (Fin d) K 1 g.left = g.left := rfl
  rw [h2, ← sc_mul_comm b g.left] at h1
  have h3 := mul_left_cancel h1
  have h4 := sc_injective hd h3
  exact congrArg Units.val h4

theorem exists_pow_scalarPair_mul_eq_one [Finite K] (hd : 0 < d) (g : coordinateSemilinearGroup d K)
    {p : ℕ} (hσ : orderOf g.right = p) {b : Kˣ} (hb : (g ^ p).left = sc b) :
    ∃ c₀ : Kˣ, (scalarPair c₀ * g) ^ p = 1 := by
  have hr : (g ^ p).right = 1 := by
    rw [pow_right, ← hσ, pow_orderOf_eq_one]
  have hσb := apply_eq_of_pow_scalar hd g hb hr
  have hfix : g.right ((b⁻¹ : Kˣ) : K) = ((b⁻¹ : Kˣ) : K) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hσb]
  obtain ⟨c₀, hc₀⟩ := CFSG.ABGLocalTools.exists_prod_pow_eq g.right hfix
  rw [hσ] at hc₀
  have : Finite (K ≃+* K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
    (fun _ _ h => RingEquiv.ext (congrFun h))
  have hp0 : 0 < p := by
    rw [← hσ]
    exact orderOf_pos _
  have hc₀ne : c₀ ≠ 0 := by
    intro h0
    have : ∏ i ∈ Finset.range p, (g.right ^ i) c₀ = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hp0) (by simp [h0])
    rw [this] at hc₀
    exact Units.ne_zero _ hc₀.symm
  refine ⟨Units.mk0 c₀ hc₀ne, ?_⟩
  apply SemidirectProduct.ext
  · rw [pow_scalarPair_mul_left, hb, sc_mul_sc]
    have : normSeq g.right (Units.mk0 c₀ hc₀ne) p * b = 1 := by
      apply Units.ext
      rw [Units.val_mul, coe_normSeq, Units.val_one]
      simp only [Units.val_mk0]
      rw [hc₀, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero b)]
    rw [this, sc_one]
    rfl
  · rw [pow_scalarPair_mul_right, hr]
    rfl

theorem coordinateSemilinearMap_scalarPair (c : Kˣ) (v : Fin d → K) :
    coordinateSemilinearMap (scalarPair c : coordinateSemilinearGroup d K) v = (c : K) • v := by
  rw [coordinateSemilinearMap_apply]
  exact sc_mulVec c v

theorem scalarPair_mem_similarityPairs (Q : QuadraticForm K (Fin d → K)) (c : Kˣ) :
    scalarPair c ∈ similarityPairs Q := by
  refine ⟨c * c, fun v => ?_⟩
  rw [coordinateSemilinearMap_scalarPair, QuadraticMap.map_smul]
  simp [scalarPair, smul_eq_mul]

theorem matrixProjectiveConjugationHom_scalarPair_mul (Q : QuadraticForm K (Fin d → K))
    (c : Kˣ) (g : similarityPairs Q) :
    matrixProjectiveConjugationHom Q ⟨scalarPair c, scalarPair_mem_similarityPairs Q c⟩ *
      matrixProjectiveConjugationHom Q g = matrixProjectiveConjugationHom Q g := by
  rw [← map_mul]
  refine matrixProjectiveConjugationHom_eq_of_left_eq_mul_scalar Q c ?_ ?_
  · change (scalarPair c * g.val).left = g.val.left * sc c
    rw [scalarPair_mul_left, sc_mul_comm]
  · change (scalarPair c * g.val).right = g.val.right
    exact scalarPair_mul_right c g.val

theorem exists_normalized_pair [Finite K] (Q : QuadraticForm K (Fin d → K)) (hd : 0 < d)
    (g : similarityPairs Q) {p : ℕ} (hσ : orderOf g.val.right = p) {b : Kˣ}
    (hb : (g.val ^ p).left = sc b) :
    ∃ U : similarityPairs Q, U.val.right = g.val.right ∧ U.val ^ p = 1 ∧
      matrixProjectiveConjugationHom Q U = matrixProjectiveConjugationHom Q g := by
  obtain ⟨c₀, hc₀⟩ := exists_pow_scalarPair_mul_eq_one hd g.val hσ hb
  refine ⟨⟨scalarPair c₀, scalarPair_mem_similarityPairs Q c₀⟩ * g, ?_, hc₀, ?_⟩
  · exact scalarPair_mul_right c₀ g.val
  · rw [map_mul]
    exact matrixProjectiveConjugationHom_scalarPair_mul Q c₀ g

end CFSG.RankThree.PartOne.KCOrthogonalDescent
