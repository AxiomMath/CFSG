module

public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Background.Huppert.II.theorem_10_12

public noncomputable section

namespace CFSG.UnitaryThreeRecognition.Model

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open scoped LinearAlgebra.Projectivization Matrix

universe u

variable {K : Type u} [Field K]

@[simp] theorem conj_conj {n : ℕ} (J : HermitianForm n K) (x : K) : J.conj (J.conj x) = x :=
  J.conj_involutive x

theorem selfPairing_mulVec {n : ℕ} (J : HermitianForm n K) {M : GL (Fin n) K}
    (hM : M ∈ J.unitarySubgroup) (v : Fin n → K) :
    dotProduct (fun i => J.conj (((M : Matrix (Fin n) (Fin n) K) *ᵥ v) i))
        (J.form *ᵥ ((M : Matrix (Fin n) (Fin n) K) *ᵥ v)) =
      dotProduct (fun i => J.conj (v i)) (J.form *ᵥ v) := by
  let : Star K := ⟨J.conj⟩
  let : InvolutiveStar K := ⟨J.conj_involutive⟩
  let : StarMul K := ⟨fun r s => by
    change J.conj (r * s) = J.conj s * J.conj r
    rw [map_mul, mul_comm]⟩
  let : StarRing K := ⟨fun r s => by
    change J.conj (r + s) = J.conj r + J.conj s
    rw [map_add]⟩
  let Mmat := ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  change star (Mmat *ᵥ v) ⬝ᵥ J.form *ᵥ (Mmat *ᵥ v) = star v ⬝ᵥ J.form *ᵥ v
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  change star v ᵥ* (J.conjTranspose Mmat * J.form * Mmat) ⬝ᵥ v = _
  rw [(J.mem_unitarySubgroup_iff M).mp hM]
  exact (Matrix.dotProduct_mulVec _ _ _).symm

theorem selfPairing_std (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (v : Fin 3 → K) :
    dotProduct (fun i => J.conj (v i)) (J.form *ᵥ v) =
      J.conj (v 0) * v 2 + J.conj (v 1) * v 1 + J.conj (v 2) * v 0 := by
  rw [hJ]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]

section Points

variable (J : HermitianForm 3 K)

@[expose] def isotropicSet : Set (ℙ K (Fin 3 → K)) :=
  {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0), x = Projectivization.mk K v hv ∧
    dotProduct (fun i => J.conj (v i)) (J.form *ᵥ v) = 0}

abbrev IsoPoint : Type u := {x : ℙ K (Fin 3 → K) // x ∈ isotropicSet J}

theorem smul_mem_isotropicSet (g : ProjectiveSpecialUnitaryMatrixGroup J)
    {x : ℙ K (Fin 3 → K)} (hx : x ∈ isotropicSet J) :
    (g : Matrix.ProjGenLinGroup (Fin 3) K) • x ∈ isotropicSet J := by
  obtain ⟨M, hM, hMg⟩ := Subgroup.mem_map.mp g.property
  obtain ⟨v, hv, rfl, hiso⟩ := hx
  refine ⟨(M : Matrix (Fin 3) (Fin 3) K) *ᵥ v, (smul_ne_zero_iff_ne M).2 hv, ?_, ?_⟩
  · rw [← hMg, Projectivization.PGL.mk_smul_mk]
    rfl
  · rw [selfPairing_mulVec J (J.specialSubgroup_le_unitarySubgroup hM) v]
    exact hiso

instance instMulActionIsoPoint :
    MulAction (ProjectiveSpecialUnitaryMatrixGroup J) (IsoPoint J) where
  smul g x := ⟨(g : Matrix.ProjGenLinGroup (Fin 3) K) • (x : ℙ K (Fin 3 → K)),
    smul_mem_isotropicSet J g x.2⟩
  one_smul x := Subtype.ext (one_smul (Matrix.ProjGenLinGroup (Fin 3) K) (x : ℙ K (Fin 3 → K)))
  mul_smul g h x := Subtype.ext (mul_smul (g : Matrix.ProjGenLinGroup (Fin 3) K)
    (h : Matrix.ProjGenLinGroup (Fin 3) K) (x : ℙ K (Fin 3 → K)))

@[simp] theorem coe_smul (g : ProjectiveSpecialUnitaryMatrixGroup J) (x : IsoPoint J) :
    ((g • x : IsoPoint J) : ℙ K (Fin 3 → K)) =
      (g : Matrix.ProjGenLinGroup (Fin 3) K) • (x : ℙ K (Fin 3 → K)) :=
  rfl

theorem coe_smul_of_eq_mk {g : ProjectiveSpecialUnitaryMatrixGroup J} {M : GL (Fin 3) K}
    (hg : (g : Matrix.ProjGenLinGroup (Fin 3) K) = Matrix.ProjGenLinGroup.mk M)
    {x : IsoPoint J} {v : Fin 3 → K} {hv : v ≠ 0}
    (hx : (x : ℙ K (Fin 3 → K)) = Projectivization.mk K v hv) :
    ((g • x : IsoPoint J) : ℙ K (Fin 3 → K)) =
      Projectivization.mk K ((M : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
        ((smul_ne_zero_iff_ne M).2 hv) := by
  rw [coe_smul, hg, hx, Projectivization.PGL.mk_smul_mk]
  rfl

theorem coe_smul_eq_toLin (g : ProjectiveSpecialUnitaryMatrixGroup J) (x : IsoPoint J)
    (M : J.specialSubgroup)
    (hM : Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) K) = (g : Matrix.ProjGenLinGroup (Fin 3) K)) :
    ((g • x : IsoPoint J) : ℙ K (Fin 3 → K)) =
      (Matrix.GeneralLinearGroup.toLin (M : GL (Fin 3) K)).toLinearEquiv •
        (x : ℙ K (Fin 3 → K)) := by
  rw [coe_smul, ← hM]
  induction (x : ℙ K (Fin 3 → K)) using Projectivization.ind with
  | h v hv => rfl

end Points

theorem ne_zero_of_apply_two_ne_zero {v : Fin 3 → K} (h : v 2 ≠ 0) : v ≠ 0 :=
  fun h0 => h (by simp [h0])

theorem ne_zero_of_apply_zero_ne_zero {v : Fin 3 → K} (h : v 0 ≠ 0) : v ≠ 0 :=
  fun h0 => h (by simp [h0])

section Standard

variable (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

@[expose] def pinf : IsoPoint J :=
  ⟨Projectivization.mk K ![1, 0, 0] (ne_zero_of_apply_zero_ne_zero (by simp)),
    ![1, 0, 0], ne_zero_of_apply_zero_ne_zero (by simp), rfl, by
      rw [selfPairing_std J hJ]
      simp⟩

@[expose] def pzero : IsoPoint J :=
  ⟨Projectivization.mk K ![0, 0, 1] (ne_zero_of_apply_two_ne_zero (by simp)),
    ![0, 0, 1], ne_zero_of_apply_two_ne_zero (by simp), rfl, by
      rw [selfPairing_std J hJ]
      simp⟩

theorem coe_pinf : (pinf J hJ : ℙ K (Fin 3 → K)) =
    Projectivization.mk K ![1, 0, 0] (ne_zero_of_apply_zero_ne_zero (by simp)) :=
  rfl

theorem coe_pzero : (pzero J hJ : ℙ K (Fin 3 → K)) =
    Projectivization.mk K ![0, 0, 1] (ne_zero_of_apply_two_ne_zero (by simp)) :=
  rfl

theorem pinf_ne_pzero : pinf J hJ ≠ pzero J hJ := by
  intro h
  have h' := congrArg Subtype.val h
  rw [coe_pinf, coe_pzero, Projectivization.mk_eq_mk_iff'] at h'
  obtain ⟨c, hc⟩ := h'
  have h0 := congrFun hc 0
  simp at h0

abbrev Coord := hermitianUnipotentCoord J

omit hJ in
theorem coord_mul_val (z w : Coord J) :
    ((z * w : Coord J) : K × K) = (z.1.1 + w.1.1, z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1) :=
  rfl

omit hJ in
theorem coord_one_val : ((1 : Coord J) : K × K) = (0, 0) :=
  rfl

omit hJ in
theorem coord_inv_val (z : Coord J) : ((z⁻¹ : Coord J) : K × K) = (-z.1.1, J.conj z.1.2) :=
  rfl

omit hJ in
theorem coord_eq_one_of_snd_eq_zero {z : Coord J} (hz : z.1.2 = 0) : z = 1 := by
  have hprod : z.1.1 * J.conj z.1.1 = 0 := by
    have h := z.2
    rw [hz, map_zero, zero_add, zero_add] at h
    exact h
  have ha : z.1.1 = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact h
    · exact (map_eq_zero_iff J.conj J.conj.injective).mp h
  apply Subtype.ext
  exact Prod.ext ha hz

omit hJ in
theorem coord_snd_ne_zero {z : Coord J} (hz : z ≠ 1) : z.1.2 ≠ 0 :=
  fun h => hz (coord_eq_one_of_snd_eq_zero J h)

abbrev root : Coord J →* ProjectiveSpecialUnitaryMatrixGroup J :=
  hermitianUnipotentPSU J hJ

theorem coe_root (z : Coord J) :
    ((root J hJ z : ProjectiveSpecialUnitaryMatrixGroup J) : Matrix.ProjGenLinGroup (Fin 3) K) =
      Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J z) :=
  rfl

theorem root_injective : Function.Injective (root J hJ) :=
  CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ

@[expose] def rootGroup : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (root J hJ).range

theorem mem_rootGroup {g : ProjectiveSpecialUnitaryMatrixGroup J} :
    g ∈ rootGroup J hJ ↔ ∃ z : Coord J, root J hJ z = g :=
  MonoidHom.mem_range

theorem root_mem_rootGroup (z : Coord J) : root J hJ z ∈ rootGroup J hJ :=
  ⟨z, rfl⟩

@[expose] def rootCoord : Coord J ≃* rootGroup J hJ :=
  MonoidHom.ofInjective (root_injective J hJ)

@[simp] theorem coe_rootCoord (z : Coord J) :
    ((rootCoord J hJ z : rootGroup J hJ) : ProjectiveSpecialUnitaryMatrixGroup J) = root J hJ z :=
  rfl

theorem coe_root_smul_pzero (z : Coord J) :
    ((root J hJ z • pzero J hJ : IsoPoint J) : ℙ K (Fin 3 → K)) =
      Projectivization.mk K ![z.1.2, -J.conj z.1.1, 1]
        (ne_zero_of_apply_two_ne_zero (by simp)) := by
  rw [coe_smul_of_eq_mk J (coe_root J hJ z) (coe_pzero J hJ)]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨1, ?_⟩
  funext i
  fin_cases i <;> simp [hermitianUnipotentMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem root_smul_pinf (z : Coord J) : root J hJ z • pinf J hJ = pinf J hJ := by
  apply Subtype.ext
  rw [coe_smul_of_eq_mk J (coe_root J hJ z) (coe_pinf J hJ), coe_pinf]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨1, ?_⟩
  funext i
  fin_cases i <;> simp [hermitianUnipotentMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem rootGroup_le_stabilizer :
    rootGroup J hJ ≤ MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) := by
  rintro _ ⟨z, rfl⟩
  exact root_smul_pinf J hJ z

theorem root_smul_pzero_ne_pinf (z : Coord J) : root J hJ z • pzero J hJ ≠ pinf J hJ := by
  intro h
  have h' := congrArg Subtype.val h
  rw [coe_root_smul_pzero, coe_pinf, Projectivization.mk_eq_mk_iff'] at h'
  obtain ⟨c, hc⟩ := h'
  have h2 := congrFun hc 2
  simp at h2

theorem exists_root_smul_pzero_eq (x : IsoPoint J) (hx : x ≠ pinf J hJ) :
    ∃ z : Coord J, root J hJ z • pzero J hJ = x := by
  obtain ⟨y, v, hv, hy, hiso⟩ := x
  rw [selfPairing_std J hJ] at hiso
  by_cases hv2 : v 2 = 0
  · exfalso
    apply hx
    have hv1 : v 1 = 0 := by
      have hprod : J.conj (v 1) * v 1 = 0 := by simpa [hv2] using hiso
      rcases mul_eq_zero.mp hprod with h | h
      · exact (map_eq_zero_iff J.conj J.conj.injective).mp h
      · exact h
    have hv0 : v 0 ≠ 0 := by
      intro hv0
      apply hv
      funext i
      fin_cases i <;> simp [hv0, hv1, hv2]
    apply Subtype.ext
    change y = (pinf J hJ : ℙ K (Fin 3 → K))
    rw [hy, coe_pinf]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨v 0, ?_⟩
    funext i
    fin_cases i <;> simp [hv1, hv2]
  · have hconj2 : J.conj (v 2) ≠ 0 := (map_ne_zero J.conj).2 hv2
    have hab : v 0 / v 2 + J.conj (v 0 / v 2) +
        (-J.conj (v 1 / v 2)) * J.conj (-J.conj (v 1 / v 2)) = 0 := by
      rw [map_neg, J.conj_involutive, map_div₀, map_div₀]
      field_simp
      linear_combination hiso
    refine ⟨⟨(-J.conj (v 1 / v 2), v 0 / v 2), hab⟩, ?_⟩
    apply Subtype.ext
    rw [coe_root_smul_pzero]
    change _ = y
    rw [hy]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨(v 2)⁻¹, ?_⟩
    funext i
    fin_cases i <;> simp [hv2, div_eq_inv_mul]

theorem root_smul_pzero_injective :
    Function.Injective fun z : Coord J => root J hJ z • pzero J hJ := by
  intro z w h
  have h' := congrArg Subtype.val h
  simp only at h'
  rw [coe_root_smul_pzero, coe_root_smul_pzero, Projectivization.mk_eq_mk_iff'] at h'
  obtain ⟨c, hc⟩ := h'
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_one] at h0 h1 h2
  subst h2
  simp only [one_mul, neg_inj] at h0 h1
  apply Subtype.ext
  apply Prod.ext
  · exact (J.conj.injective h1).symm
  · exact h0.symm

theorem rootGroup_regular (β γ : IsoPoint J) (hβ : β ≠ pinf J hJ) (hγ : γ ≠ pinf J hJ) :
    ∃! r : rootGroup J hJ, (r : ProjectiveSpecialUnitaryMatrixGroup J) • β = γ := by
  obtain ⟨z₁, rfl⟩ := exists_root_smul_pzero_eq J hJ β hβ
  obtain ⟨z₂, rfl⟩ := exists_root_smul_pzero_eq J hJ γ hγ
  refine ⟨rootCoord J hJ (z₂ * z₁⁻¹), ?_, ?_⟩
  · dsimp only
    rw [coe_rootCoord, smul_smul, ← map_mul, inv_mul_cancel_right]
  · rintro ⟨r, z, rfl⟩ hr
    apply Subtype.ext
    rw [coe_rootCoord]
    change root J hJ z • (root J hJ z₁ • pzero J hJ) = root J hJ z₂ • pzero J hJ at hr
    rw [smul_smul, ← map_mul] at hr
    have hz := root_smul_pzero_injective J hJ hr
    change root J hJ z = root J hJ (z₂ * z₁⁻¹)
    rw [← hz, mul_inv_cancel_right]

abbrev weyl : ProjectiveSpecialUnitaryMatrixGroup J :=
  hermitianWeylPSU J hJ

theorem coe_weyl :
    ((weyl J hJ : ProjectiveSpecialUnitaryMatrixGroup J) : Matrix.ProjGenLinGroup (Fin 3) K) =
      Matrix.ProjGenLinGroup.mk hermitianWeylGL :=
  rfl

theorem weyl_smul_pinf : weyl J hJ • pinf J hJ = pzero J hJ := by
  apply Subtype.ext
  rw [coe_smul_of_eq_mk J (coe_weyl J hJ) (coe_pinf J hJ), coe_pzero]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨1, ?_⟩
  funext i
  fin_cases i <;> simp [hermitianWeylGL, hermitianWeylMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

theorem weyl_smul_pzero : weyl J hJ • pzero J hJ = pinf J hJ := by
  apply Subtype.ext
  rw [coe_smul_of_eq_mk J (coe_weyl J hJ) (coe_pzero J hJ), coe_pinf]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨1, ?_⟩
  funext i
  fin_cases i <;> simp [hermitianWeylGL, hermitianWeylMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

omit hJ in
theorem hermitianWeylGL_mul_self : (hermitianWeylGL : GL (Fin 3) K) * hermitianWeylGL = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianWeylGL, hermitianWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem weyl_mul_weyl : weyl J hJ * weyl J hJ = 1 := by
  apply Subtype.ext
  change Matrix.ProjGenLinGroup.mk (hermitianWeylGL (K := K)) *
      Matrix.ProjGenLinGroup.mk hermitianWeylGL = 1
  rw [← map_mul, hermitianWeylGL_mul_self, map_one]

theorem weyl_sq : weyl J hJ ^ 2 = 1 := by
  rw [pow_two, weyl_mul_weyl]

theorem weyl_inv : (weyl J hJ)⁻¹ = weyl J hJ :=
  inv_eq_of_mul_eq_one_right (weyl_mul_weyl J hJ)

theorem weyl_ne_one : weyl J hJ ≠ 1 := by
  intro h
  apply pinf_ne_pzero J hJ
  rw [← weyl_smul_pinf J hJ, h, one_smul]

theorem weyl_not_mem_stabilizer :
    weyl J hJ ∉ MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) := by
  intro h
  apply pinf_ne_pzero J hJ
  rw [← weyl_smul_pinf J hJ]
  exact h.symm

omit hJ in
@[expose] def weylCoord (z : Coord J) : Coord J :=
  ⟨(-z.1.1 / J.conj z.1.2, z.1.2⁻¹), by
    by_cases hb : z.1.2 = 0
    · simp [hb]
    · have hconjb : J.conj z.1.2 ≠ 0 := (map_ne_zero J.conj).2 hb
      dsimp only
      rw [map_inv₀, map_div₀, map_neg, J.conj_involutive]
      field_simp
      linear_combination z.2⟩

omit hJ in
theorem weylCoord_val (z : Coord J) :
    ((weylCoord J z : Coord J) : K × K) = (-z.1.1 / J.conj z.1.2, z.1.2⁻¹) :=
  rfl

theorem weyl_smul_root_smul_pzero (z : Coord J) (hz : z ≠ 1) :
    weyl J hJ • (root J hJ z • pzero J hJ) = root J hJ (weylCoord J z) • pzero J hJ := by
  have hb : z.1.2 ≠ 0 := coord_snd_ne_zero J hz
  have hconjb : J.conj z.1.2 ≠ 0 := (map_ne_zero J.conj).2 hb
  apply Subtype.ext
  rw [coe_smul_of_eq_mk J (coe_weyl J hJ) (coe_root_smul_pzero J hJ z), coe_root_smul_pzero]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨z.1.2, ?_⟩
  funext i
  fin_cases i <;> simp [weylCoord, hermitianWeylGL, hermitianWeylMatrix, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, map_div₀, hb]
  field_simp

theorem weyl_smul_rootCoord_smul_pzero (z : Coord J) (hz : z ≠ 1) :
    weyl J hJ • (((rootCoord J hJ z : rootGroup J hJ) : ProjectiveSpecialUnitaryMatrixGroup J) •
        pzero J hJ) =
      ((rootCoord J hJ (weylCoord J z) : rootGroup J hJ) :
        ProjectiveSpecialUnitaryMatrixGroup J) • pzero J hJ :=
  weyl_smul_root_smul_pzero J hJ z hz

omit hJ in
@[expose] def weylCoordRight (z : Coord J) : Coord J :=
  ⟨(-z.1.1 / z.1.2, z.1.2⁻¹), by
    by_cases hb : z.1.2 = 0
    · simp [hb]
    · have hconjb : J.conj z.1.2 ≠ 0 := (map_ne_zero J.conj).2 hb
      dsimp only
      rw [map_inv₀, map_div₀, map_neg]
      field_simp
      linear_combination z.2⟩

omit hJ in
theorem weylCoordRight_val (z : Coord J) :
    ((weylCoordRight J z : Coord J) : K × K) = (-z.1.1 / z.1.2, z.1.2⁻¹) :=
  rfl

omit hJ in
theorem weylCoord_ne_one {z : Coord J} (hz : z ≠ 1) : weylCoord J z ≠ 1 := by
  intro h
  have h2 := congrArg (fun w : Coord J => (w : K × K).2) h
  simp only [weylCoord_val, coord_one_val, inv_eq_zero] at h2
  exact coord_snd_ne_zero J hz h2

omit hJ in
theorem weylCoordRight_ne_one {z : Coord J} (hz : z ≠ 1) : weylCoordRight J z ≠ 1 := by
  intro h
  have h2 := congrArg (fun w : Coord J => (w : K × K).2) h
  simp only [weylCoordRight_val, coord_one_val, inv_eq_zero] at h2
  exact coord_snd_ne_zero J hz h2

omit hJ in
theorem weylCoord_weylCoord (z : Coord J) : weylCoord J (weylCoord J z) = z := by
  by_cases hz : z = 1
  · subst hz
    apply Subtype.ext
    simp [weylCoord_val, coord_one_val]
  · have hb : z.1.2 ≠ 0 := coord_snd_ne_zero J hz
    have hconjb : J.conj z.1.2 ≠ 0 := (map_ne_zero J.conj).2 hb
    apply Subtype.ext
    apply Prod.ext
    · simp only [weylCoord_val, map_inv₀]
      field_simp
    · simp [weylCoord_val]

omit hJ in
theorem weylCoord_inv (z : Coord J) : weylCoord J z⁻¹ = (weylCoordRight J z)⁻¹ := by
  apply Subtype.ext
  simp [weylCoord_val, weylCoordRight_val, coord_inv_val, neg_div]

theorem weyl_smul_root_inv_smul_pzero (z : Coord J) (hz : z ≠ 1) :
    weyl J hJ • ((root J hJ z)⁻¹ • pzero J hJ) =
      (root J hJ (weylCoordRight J z))⁻¹ • pzero J hJ := by
  have hz' : z⁻¹ ≠ 1 := inv_ne_one.mpr hz
  rw [← map_inv, ← map_inv, weyl_smul_root_smul_pzero J hJ z⁻¹ hz', weylCoord_inv]

abbrev torus : Kˣ →* ProjectiveSpecialUnitaryMatrixGroup J :=
  hermitianTorusPSU J hJ

theorem coe_torus (k : Kˣ) :
    ((torus J hJ k : ProjectiveSpecialUnitaryMatrixGroup J) : Matrix.ProjGenLinGroup (Fin 3) K) =
      Matrix.ProjGenLinGroup.mk (hermitianTorusGL J k) :=
  rfl

@[expose] def torusGroup : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (torus J hJ).range

theorem mem_torusGroup {g : ProjectiveSpecialUnitaryMatrixGroup J} :
    g ∈ torusGroup J hJ ↔ ∃ k : Kˣ, torus J hJ k = g :=
  MonoidHom.mem_range

theorem torus_mem_torusGroup (k : Kˣ) : torus J hJ k ∈ torusGroup J hJ :=
  ⟨k, rfl⟩

theorem torus_smul_pinf (k : Kˣ) : torus J hJ k • pinf J hJ = pinf J hJ := by
  apply Subtype.ext
  rw [coe_smul_of_eq_mk J (coe_torus J hJ k) (coe_pinf J hJ), coe_pinf]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨(J.conj (k : K))⁻¹, ?_⟩
  funext i
  fin_cases i <;> simp [hermitianTorusMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem torus_smul_pzero (k : Kˣ) : torus J hJ k • pzero J hJ = pzero J hJ := by
  apply Subtype.ext
  rw [coe_smul_of_eq_mk J (coe_torus J hJ k) (coe_pzero J hJ), coe_pzero]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨(k : K), ?_⟩
  funext i
  fin_cases i <;> simp [hermitianTorusMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem torusGroup_le_stabilizer_pinf :
    torusGroup J hJ ≤
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) := by
  rintro _ ⟨k, rfl⟩
  exact torus_smul_pinf J hJ k

theorem torusGroup_le_stabilizer_pzero :
    torusGroup J hJ ≤
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pzero J hJ) := by
  rintro _ ⟨k, rfl⟩
  exact torus_smul_pzero J hJ k

omit hJ in
theorem torusAction_val (k : Kˣ) (z : Coord J) :
    ((hermitianTorusAction J k z : Coord J) : K × K) =
      (z.1.1 * (k : K) * (J.conj (k : K))⁻¹ ^ 2, z.1.2 * (J.conj (k : K))⁻¹ * (k : K)⁻¹) :=
  rfl

theorem torus_mul_root_mul_inv (k : Kˣ) (z : Coord J) :
    torus J hJ k * root J hJ z * (torus J hJ k)⁻¹ = root J hJ (hermitianTorusAction J k z) := by
  rw [hermitianTorusPSU_mul_unipotent J hJ k z, mul_inv_cancel_right]

theorem torus_mul_rootCoord_mul_inv (k : Kˣ) (z : Coord J) :
    torus J hJ k * ((rootCoord J hJ z : rootGroup J hJ) : ProjectiveSpecialUnitaryMatrixGroup J) *
        (torus J hJ k)⁻¹ =
      ((rootCoord J hJ (hermitianTorusAction J k z) : rootGroup J hJ) :
        ProjectiveSpecialUnitaryMatrixGroup J) :=
  torus_mul_root_mul_inv J hJ k z

theorem torus_smul_root_smul_pzero (k : Kˣ) (z : Coord J) :
    torus J hJ k • (root J hJ z • pzero J hJ) =
      root J hJ (hermitianTorusAction J k z) • pzero J hJ := by
  rw [← torus_mul_root_mul_inv J hJ k z, mul_smul, mul_smul, ← map_inv, torus_smul_pzero]

theorem torusGroup_le_normalizer_rootGroup :
    torusGroup J hJ ≤
      Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  rintro _ ⟨k, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨hermitianTorusAction J k z, (torus_mul_root_mul_inv J hJ k z).symm⟩
  · rintro ⟨z, hz⟩
    refine ⟨hermitianTorusAction J k⁻¹ z, ?_⟩
    have h := torus_mul_root_mul_inv J hJ k⁻¹ z
    rw [map_inv, inv_inv] at h
    rw [← h, hz]
    group

omit hJ in
theorem hermitianWeylGL_mul_torus_mul_weyl (k : Kˣ) :
    (hermitianWeylGL : GL (Fin 3) K) * hermitianTorusGL J k * hermitianWeylGL =
      hermitianTorusGL J (Units.map J.conj.toMonoidHom k)⁻¹ := by
  have hk : (k : K) ≠ 0 := Units.ne_zero k
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianWeylGL, hermitianWeylMatrix, hermitianTorusMatrix, Matrix.mul_apply,
      Fin.sum_univ_three, map_inv₀]
  all_goals ring

theorem weyl_mul_torus_mul_weyl (k : Kˣ) :
    weyl J hJ * torus J hJ k * weyl J hJ = torus J hJ (Units.map J.conj.toMonoidHom k)⁻¹ := by
  apply Subtype.ext
  change Matrix.ProjGenLinGroup.mk (hermitianWeylGL (K := K)) *
      Matrix.ProjGenLinGroup.mk (hermitianTorusGL J k) *
      Matrix.ProjGenLinGroup.mk hermitianWeylGL =
    Matrix.ProjGenLinGroup.mk (hermitianTorusGL J (Units.map J.conj.toMonoidHom k)⁻¹)
  rw [← map_mul, ← map_mul, hermitianWeylGL_mul_torus_mul_weyl]

omit hJ in
theorem hermitianWeylGL_mul_unipotent_mul_weyl (z : Coord J) (hb : z.1.2 ≠ 0) :
    (hermitianWeylGL : GL (Fin 3) K) * hermitianUnipotentGL J z * hermitianWeylGL =
      hermitianUnipotentGL J (weylCoord J z) * hermitianTorusGL J (Units.mk0 z.1.2 hb) *
        hermitianWeylGL * hermitianUnipotentGL J (weylCoordRight J z) := by
  have hconjb : J.conj z.1.2 ≠ 0 := (map_ne_zero J.conj).2 hb
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change
    ((hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) K) * hermitianUnipotentMatrix J z *
        (hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) K)) i j =
      (hermitianUnipotentMatrix J (weylCoord J z) *
        hermitianTorusMatrix J (Units.mk0 z.1.2 hb) *
        (hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) K) *
        hermitianUnipotentMatrix J (weylCoordRight J z)) i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianWeylMatrix, hermitianUnipotentMatrix, hermitianTorusMatrix, weylCoord,
      weylCoordRight, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals field_simp [hb, hconjb]
  all_goals first
    | ring1
    | linear_combination z.2
    | linear_combination -z.2

theorem weyl_mul_root_mul_weyl (z : Coord J) (hz : z ≠ 1) :
    weyl J hJ * root J hJ z * weyl J hJ =
      root J hJ (weylCoord J z) * torus J hJ (Units.mk0 z.1.2 (coord_snd_ne_zero J hz)) *
        weyl J hJ * root J hJ (weylCoordRight J z) := by
  apply Subtype.ext
  change Matrix.ProjGenLinGroup.mk (hermitianWeylGL (K := K)) *
        Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J z) *
        Matrix.ProjGenLinGroup.mk hermitianWeylGL =
      Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J (weylCoord J z)) *
          Matrix.ProjGenLinGroup.mk
            (hermitianTorusGL J (Units.mk0 z.1.2 (coord_snd_ne_zero J hz))) *
        Matrix.ProjGenLinGroup.mk hermitianWeylGL *
        Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J (weylCoordRight J z))
  simp only [← map_mul]
  rw [hermitianWeylGL_mul_unipotent_mul_weyl J z (coord_snd_ne_zero J hz)]

end Standard

end CFSG.UnitaryThreeRecognition.Model
