module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.LinearAlgebra.SelfAdjointIdempotent
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALangHerm
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairLocal
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.ComponentNormal
public import CFSG.Fischer.Classification.Recognition.SymOOrth
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPSURoot
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSU

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

private theorem bmSDU_center_of_injective {X Y : Type} [Group X] [Group Y]
    (ι : X →* Y) (hι : Function.Injective ι) :
    ∀ y, ι y ∈ Subgroup.center Y → y ∈ Subgroup.center X := by
  intro y hy
  rw [Subgroup.mem_center_iff] at hy ⊢
  intro z
  apply hι
  rw [map_mul, map_mul, hy (ι z)]

private def bmSDU_h {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (G : Matrix (Fin n) (Fin n) F) (x y : Fin n → F) : F :=
  dotProduct (Matrix.vecMul (fun i => σ (x i)) G) y

private lemma bmSDU_h_adjoint {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (G a : Matrix (Fin n) (Fin n) F) (hG : IsUnit G.det) (x y : Fin n → F) :
    bmSDU_h σ G (Matrix.mulVec a x) y =
      bmSDU_h σ G x (Matrix.mulVec (formAdj σ G a) y) := by
  have hm : (fun i => σ (Matrix.mulVec a x i)) =
      Matrix.mulVec (a.map σ) (fun i => σ (x i)) := by
    funext i
    exact RingHom.map_mulVec σ a x i
  have hmat : Matrix.transpose (a.map σ) * G = G * formAdj σ G a := by
    calc Matrix.transpose (a.map σ) * G = 1 * (Matrix.transpose (a.map σ) * G) :=
          (Matrix.one_mul _).symm
      _ = (G * G⁻¹) * (Matrix.transpose (a.map σ) * G) := by
            rw [Matrix.mul_nonsing_inv G hG]
      _ = G * (G⁻¹ * Matrix.transpose (a.map σ) * G) := by simp only [Matrix.mul_assoc]
      _ = G * formAdj σ G a := rfl
  have hR : dotProduct (Matrix.vecMul (fun i => σ (x i)) G)
      (Matrix.mulVec (formAdj σ G a) y) =
      dotProduct (fun i => σ (x i)) (Matrix.mulVec G (Matrix.mulVec (formAdj σ G a) y)) := by
    rw [← Matrix.dotProduct_mulVec]
  simp only [bmSDU_h, hm]
  rw [Matrix.vecMul_mulVec, ← Matrix.dotProduct_mulVec, hR, Matrix.mulVec_mulVec, ← hmat]

private lemma bmSDU_mulVec_eq_self_of_mem_range {F : Type} [Field F] {n : ℕ}
    {e : Matrix (Fin n) (Fin n) F} (hE : e * e = e)
    {x : Fin n → F} (hx : x ∈ LinearMap.range e.mulVecLin) : Matrix.mulVec e x = x := by
  obtain ⟨y, rfl⟩ := hx
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hE]

private lemma bmSDU_h_eq_zero {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (hσ : ∀ x, σ (σ x) = x) (G : Matrix (Fin n) (Fin n) F) (hG : IsUnit G.det)
    {y : Fin n → F} (hy : ∀ z, bmSDU_h σ G z y = 0) : y = 0 := by
  refine CFSG.LinearAlgebra.eq_zero_of_forall_dotProduct_mulVec_eq_zero
    ((Matrix.isUnit_iff_isUnit_det G).mpr hG) fun z => ?_
  have h := hy (fun i => σ (z i))
  have hz : (fun i => σ (σ (z i))) = z := by funext i; exact hσ (z i)
  rw [bmSDU_h, hz] at h
  rwa [← Matrix.dotProduct_mulVec] at h

private noncomputable def bmSDU_gramProjection {F : Type} [Field F] {n r : ℕ} (σ : F →+* F)
    (G : Matrix (Fin n) (Fin n) F) (U : Matrix (Fin n) (Fin r) F) : Matrix (Fin n) (Fin n) F :=
  U * (Matrix.transpose (U.map σ) * G * U)⁻¹ * Matrix.transpose (U.map σ) * G

private lemma bmSDU_eq_gramProjection {F : Type} [Field F] {n r : ℕ} (σ : F →+* F)
    (G e : Matrix (Fin n) (Fin n) F) (U : Matrix (Fin n) (Fin r) F)
    (hE2 : e * e = e) (hE : Matrix.transpose (e.map σ) * G = G * e)
    (hUE : LinearMap.range U.mulVecLin = LinearMap.range e.mulVecLin)
    (hG : IsUnit (Matrix.transpose (U.map σ) * G * U)) :
    e = bmSDU_gramProjection σ G U := by
  obtain ⟨V, hV⟩ := CFSG.LinearAlgebra.exists_mul_eq_of_range_le hUE.le
  obtain ⟨M, hM⟩ := CFSG.LinearAlgebra.exists_mul_eq_of_range_le hUE.ge
  have hEU : e * U = U := by rw [← hV, ← Matrix.mul_assoc, hE2]
  have hUGE : Matrix.transpose (U.map σ) * G * e = Matrix.transpose (U.map σ) * G := by
    calc Matrix.transpose (U.map σ) * G * e = Matrix.transpose (U.map σ) * (G * e) :=
          Matrix.mul_assoc _ _ _
      _ = Matrix.transpose (U.map σ) * (Matrix.transpose (e.map σ) * G) := by rw [← hE]
      _ = (Matrix.transpose (U.map σ) * Matrix.transpose (e.map σ)) * G :=
            (Matrix.mul_assoc _ _ _).symm
      _ = Matrix.transpose ((e.map σ) * (U.map σ)) * G := by rw [Matrix.transpose_mul]
      _ = Matrix.transpose ((e * U).map σ) * G := by rw [← Matrix.map_mul]
      _ = Matrix.transpose (U.map σ) * G := by rw [hEU]
  have hM' : M = (Matrix.transpose (U.map σ) * G * U)⁻¹ * (Matrix.transpose (U.map σ) * G) := by
    have h1 : (Matrix.transpose (U.map σ) * G * U) * M = Matrix.transpose (U.map σ) * G := by
      rw [Matrix.mul_assoc, hM, hUGE]
    calc M = (Matrix.transpose (U.map σ) * G * U)⁻¹ *
          ((Matrix.transpose (U.map σ) * G * U) * M) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hG),
            Matrix.one_mul]
      _ = (Matrix.transpose (U.map σ) * G * U)⁻¹ * (Matrix.transpose (U.map σ) * G) := by rw [h1]
  rw [← hM, hM']
  simp only [bmSDU_gramProjection, Matrix.mul_assoc]

private lemma bmSDU_isUnit_gram {F : Type} [Field F] {n r : ℕ} (σ : F →+* F)
    (hσ : ∀ x, σ (σ x) = x) (G e : Matrix (Fin n) (Fin n) F) (hG : IsUnit G.det)
    (hE2 : e * e = e) (hadj : formAdj σ G e = e)
    {U : Matrix (Fin n) (Fin r) F} (hU : Function.Injective U.mulVec)
    (hUE : LinearMap.range U.mulVecLin = LinearMap.range e.mulVecLin) :
    IsUnit (Matrix.transpose (U.map σ) * G * U) := by
  refine Matrix.mulVec_injective_iff_isUnit.mp fun c c' hcc' => hU ?_
  have h0 : Matrix.mulVec (Matrix.transpose (U.map σ) * G * U) (c - c') = 0 := by
    rw [Matrix.mulVec_sub, hcc', sub_self]
  have hUc : Matrix.mulVec U (c - c') ∈ LinearMap.range e.mulVecLin := hUE ▸ ⟨c - c', rfl⟩
  suffices Matrix.mulVec U (c - c') = 0 by
    rwa [Matrix.mulVec_sub, sub_eq_zero] at this
  refine bmSDU_h_eq_zero σ hσ G hG fun z => ?_
  obtain ⟨d, hd⟩ : Matrix.mulVec e z ∈ LinearMap.range U.mulVecLin := hUE ▸ ⟨z, rfl⟩
  rw [← bmSDU_mulVec_eq_self_of_mem_range hE2 hUc]
  rw [← hadj, ← bmSDU_h_adjoint σ G e hG z (Matrix.mulVec U (c - c'))]
  rw [← hd, Matrix.mulVecLin_apply]
  have hmap : (fun i => σ (Matrix.mulVec U d i)) =
      Matrix.mulVec (U.map σ) (fun i => σ (d i)) := by
    funext i; exact RingHom.map_mulVec σ U d i
  rw [bmSDU_h, hmap, Matrix.vecMul_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, h0, dotProduct_zero]

private lemma bmSDU_isUnitaryInvolution {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) :
    CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution
      (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) :=
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALang.isUnitaryInvolution_of_involution
    (by
      intro h
      obtain ⟨c, hc'⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_ne hc
      exact hc' (by simp [h]))
    (by ext c; exact CFSG.LieType.BorelTits.unitaryInvolution_involutive hc c)

private lemma bmSDU_exists_orthonormal {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {r : ℕ} (A : Matrix (Fin r) (Fin r) F)
    (hA : CFSG.LieType.Universal.Unitary.conjTr
      (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) A = A) (hdet : A.det ≠ 0) :
    ∃ Q : Matrix (Fin r) (Fin r) F,
      IsUnit Q ∧
      Matrix.transpose (Q.map (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom) * A * Q
        = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb, horth⟩ := CFSG.LieType.Steinberg.exists_herm_orthonormal
    (bmSDU_isUnitaryInvolution hc) hA hdet
  refine ⟨Matrix.transpose (Matrix.of b), (Matrix.linearIndependent_cols_iff_isUnit).mp hb, ?_⟩
  ext i j
  rw [Matrix.one_apply]
  have h := horth i j
  simp only [CFSG.ClassicalGroups.Unitary.herm, Matrix.mulVec, dotProduct] at h
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
    Matrix.transpose_transpose, Matrix.transpose_map]
  rw [Finset.sum_congr rfl (fun c _ => by rw [Finset.sum_mul])]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun r _ => by simp only [mul_assoc]; rw [← Finset.mul_sum])]
  exact h

private lemma bmSDU_exists_witt {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (r : ℕ) :
    ∃ P : Matrix (Fin r) (Fin r) F,
      IsUnit P ∧
      Matrix.transpose (P.map (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom) * P
        = Unitary.antidiag r := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hc r
  refine ⟨(P : Matrix (Fin r) (Fin r) F), P.isUnit, ?_⟩
  simpa [CFSG.LieType.Universal.Unitary.conjTr] using hP

private noncomputable def bmSDU_imBasis {F : Type} [Field F] {n : ℕ}
    (W : Submodule F (Fin n → F)) : Matrix (Fin n) (Fin (Module.finrank F W)) F :=
  LinearMap.toMatrix' ((Submodule.subtype W).comp
    (Module.finBasis F W).equivFun.symm.toLinearMap)

private lemma bmSDU_imBasis_mulVecLin {F : Type} [Field F] {n : ℕ}
    (W : Submodule F (Fin n → F)) :
    (bmSDU_imBasis W).mulVecLin = (Submodule.subtype W).comp
      (Module.finBasis F W).equivFun.symm.toLinearMap := by
  apply LinearMap.ext
  intro v
  simp only [Matrix.mulVecLin_apply, bmSDU_imBasis]
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

private lemma bmSDU_imBasis_range {F : Type} [Field F] {n : ℕ}
    (W : Submodule F (Fin n → F)) : LinearMap.range (bmSDU_imBasis W).mulVecLin = W := by
  rw [bmSDU_imBasis_mulVecLin, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (Module.finBasis F W).equivFun.symm.surjective,
    Submodule.map_top, Submodule.range_subtype]

private lemma bmSDU_imBasis_inj {F : Type} [Field F] {n : ℕ}
    (W : Submodule F (Fin n → F)) : Function.Injective (bmSDU_imBasis W).mulVec := by
  have hf : Function.Injective ((Submodule.subtype W).comp
      (Module.finBasis F W).equivFun.symm.toLinearMap) :=
    (Submodule.subtype_injective W).comp (Module.finBasis F W).equivFun.symm.injective
  intro a b hab
  apply hf
  rw [← bmSDU_imBasis_mulVecLin]
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hab]

private lemma bmSDU_antidiag_herm {F : Type} [Field F] (σ : F →+* F) (n : ℕ) :
    Matrix.transpose ((Unitary.antidiag n).map σ) = Unitary.antidiag n := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.map_apply]
  have hanti : ∀ (a b : Fin n), (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) a b =
      if b = a.rev then 1 else 0 := fun a b => rfl
  rw [hanti j i, hanti i j]
  by_cases h : i = j.rev
  · have h2 : j = i.rev := by rw [h, Fin.rev_rev]
    rw [if_pos h, if_pos h2, map_one]
  · have h2 : j ≠ i.rev := by intro h2; apply h; rw [h2, Fin.rev_rev]
    rw [if_neg h, if_neg h2, map_zero]

private lemma bmSDU_gram_herm {F : Type} [Field F] {n r : ℕ} (σ : F →+* F)
    (hσ : ∀ x, σ (σ x) = x) (G : Matrix (Fin n) (Fin n) F)
    (hGh : Matrix.transpose (G.map σ) = G) (U : Matrix (Fin n) (Fin r) F) :
    Matrix.transpose ((Matrix.transpose (U.map σ) * G * U).map σ) =
      Matrix.transpose (U.map σ) * G * U := by
  have hU : (U.map σ).map σ = U := by
    rw [Matrix.map_map, show (σ : F → F) ∘ σ = id from funext hσ, Matrix.map_id]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hU]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hGh, Matrix.mul_assoc]

private theorem bmSDU_adapted_basis (n g : ℕ)
    (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hadj : formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e = e) :
    ∃ (r : ℕ) (U : Matrix (Fin n) (Fin r) (GaloisField 2 (2 * (g + 1)))),
      1 ≤ r ∧ Function.Injective U.mulVec ∧
      LinearMap.range U.mulVecLin = LinearMap.range e.mulVecLin ∧
      Matrix.transpose (U.map (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g +
          1))) 2 (g + 1)).toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2
              (2 * (g + 1)))) * U = Unitary.antidiag r := by
  let F' := GaloisField 2 (2 * (g + 1))
  let σe : F' ≃+* F' := CFSG.LieType.BorelTits.unitaryInvolution F' 2 (g + 1)
  let G : Matrix (Fin n) (Fin n) F' := Unitary.antidiag n
  let W : Submodule F' (Fin n → F') := LinearMap.range e.mulVecLin
  have hc : Nat.card F' = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  have hσ : ∀ x, σe (σe x) = x := CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  have hG : IsUnit G.det := isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  have hGh : CFSG.LieType.Universal.Unitary.conjTr σe G = G := by
    simpa [G, CFSG.LieType.Universal.Unitary.conjTr] using bmSDU_antidiag_herm σe.toRingHom n
  have hE2 : e * e = e := he.2.1.eq
  let U₀ : Matrix (Fin n) (Fin (Module.finrank F' W)) F' := bmSDU_imBasis W
  have hU₀inj : Function.Injective U₀.mulVec := bmSDU_imBasis_inj W
  have hU₀range : LinearMap.range U₀.mulVecLin = LinearMap.range e.mulVecLin := bmSDU_imBasis_range
      W
  let A : Matrix (Fin (Module.finrank F' W)) (Fin (Module.finrank F' W)) F' :=
    Matrix.transpose (U₀.map σe.toRingHom) * G * U₀
  have hAherm : CFSG.LieType.Universal.Unitary.conjTr σe A = A := by
    simpa [A, CFSG.LieType.Universal.Unitary.conjTr] using
      bmSDU_gram_herm σe.toRingHom hσ G hGh U₀
  have hAunit : IsUnit A :=
    bmSDU_isUnit_gram σe.toRingHom hσ G e hG hE2 hadj hU₀inj hU₀range
  have hAdet : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).mp hAunit).ne_zero
  obtain ⟨Q, hQunit, hQ⟩ := bmSDU_exists_orthonormal hc A hAherm hAdet
  obtain ⟨P, hPunit, hP⟩ := bmSDU_exists_witt hc (Module.finrank F' W)
  have hWne : W ≠ ⊥ := by
    intro hW
    apply he.2.2.1
    ext i j
    have hmem : e.mulVec (Pi.single j 1) ∈ W := ⟨Pi.single j 1, rfl⟩
    rw [hW, Submodule.mem_bot] at hmem
    have h := congrFun hmem i
    simpa [Matrix.mulVec_single_one] using h
  have hQPunit : IsUnit (Q * P) := hQunit.mul hPunit
  refine ⟨Module.finrank F' W, U₀ * Q * P, (Submodule.one_le_finrank_iff).mpr hWne, ?_, ?_, ?_⟩
  · have hQPinj : Function.Injective (Q * P).mulVec :=
      (Matrix.mulVec_injective_iff_isUnit).mpr hQPunit
    have hcomp : Function.Injective (U₀ * (Q * P)).mulVec := by
      intro a b hab
      have h2 : U₀.mulVec ((Q * P).mulVec a) = U₀.mulVec ((Q * P).mulVec b) := by
        simpa only [← Matrix.mulVec_mulVec] using hab
      exact hQPinj (hU₀inj h2)
    rw [Matrix.mul_assoc]
    exact hcomp
  · have hPsurj : Function.Surjective P.mulVec :=
      (Matrix.mulVec_surjective_iff_isUnit).mpr hPunit
    have hQsurj : Function.Surjective Q.mulVec :=
      (Matrix.mulVec_surjective_iff_isUnit).mpr hQunit
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hPsurj, Submodule.map_top, Matrix.mulVecLin_mul,
      LinearMap.range_comp, LinearMap.range_eq_top.mpr hQsurj, Submodule.map_top]
    exact hU₀range
  · calc Matrix.transpose ((U₀ * Q * P).map σe.toRingHom) * G * (U₀ * Q * P)
        = Matrix.transpose (P.map σe.toRingHom) *
            (Matrix.transpose (Q.map σe.toRingHom) *
              (Matrix.transpose (U₀.map σe.toRingHom) * G * U₀) * Q) * P := by
          rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = Matrix.transpose (P.map σe.toRingHom) *
            (Matrix.transpose (Q.map σe.toRingHom) * A * Q) * P := rfl
      _ = Matrix.transpose (P.map σe.toRingHom) * 1 * P := by rw [hQ]
      _ = Matrix.transpose (P.map σe.toRingHom) * P := by rw [Matrix.mul_one]
      _ = Unitary.antidiag (Module.finrank F' W) := hP

private noncomputable def bmSDU_L {F : Type} [Field F] {n r : ℕ} (σ : F →+* F)
    (G : Matrix (Fin n) (Fin n) F) (U : Matrix (Fin n) (Fin r) F) : Matrix (Fin r) (Fin n) F :=
  (Matrix.transpose (U.map σ) * G * U)⁻¹ * Matrix.transpose (U.map σ) * G

private lemma bmSDU_U_mul_L {F : Type} [Field F] {n r : ℕ} (σ : F →+* F)
    (G e : Matrix (Fin n) (Fin n) F) (U : Matrix (Fin n) (Fin r) F)
    (hE2 : e * e = e) (hE : Matrix.transpose (e.map σ) * G = G * e)
    (hUE : LinearMap.range U.mulVecLin = LinearMap.range e.mulVecLin)
    (hG : IsUnit (Matrix.transpose (U.map σ) * G * U)) :
    U * bmSDU_L σ G U = e := by
  rw [bmSDU_eq_gramProjection σ G e U hE2 hE hUE hG]
  simp only [bmSDU_gramProjection, bmSDU_L, Matrix.mul_assoc]

private lemma bmSDU_L_mul_U {F : Type} [Field F] {n r : ℕ} (σ : F →+* F)
    (G : Matrix (Fin n) (Fin n) F) (U : Matrix (Fin n) (Fin r) F)
    (hG : IsUnit (Matrix.transpose (U.map σ) * G * U)) :
    bmSDU_L σ G U * U = 1 := by
  calc bmSDU_L σ G U * U
      = (Matrix.transpose (U.map σ) * G * U)⁻¹ *
          (Matrix.transpose (U.map σ) * G * U) := by
          simp only [bmSDU_L, Matrix.mul_assoc]
    _ = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hG)

private lemma bmSDU_e_mul_U {F : Type} [Field F] {n r : ℕ}
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e) (hLU : L * U = 1) : e * U = U := by
  rw [← hUL, Matrix.mul_assoc, hLU, Matrix.mul_one]

private lemma bmSDU_L_mul_e {F : Type} [Field F] {n r : ℕ}
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e) (hLU : L * U = 1) : L * e = L := by
  rw [← hUL, ← Matrix.mul_assoc, hLU, Matrix.one_mul]

private lemma bmSDU_L_one_sub {F : Type} [Field F] {n r : ℕ}
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e) (hLU : L * U = 1) :
    L * (1 - e) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, bmSDU_L_mul_e hUL hLU, sub_self]

private lemma bmSDU_one_sub_mul_U {F : Type} [Field F] {n r : ℕ}
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e) (hLU : L * U = 1) :
    (1 - e) * U = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, bmSDU_e_mul_U hUL hLU, sub_self]

private lemma bmSDU_embed_mul {F : Type} [Field F] {n r : ℕ}
    {e : Matrix (Fin n) (Fin n) F} (hE2 : e * e = e)
    {U : Matrix (Fin n) (Fin r) F} {L : Matrix (Fin r) (Fin n) F}
    (hUL : U * L = e) (hLU : L * U = 1) (x y : Matrix (Fin r) (Fin r) F) :
    (U * x * L + (1 - e)) * (U * y * L + (1 - e)) = U * (x * y) * L + (1 - e) := by
  have hid : IsIdempotentElem e := hE2
  have h1e : (1 - e) * (1 - e) = 1 - e := (IsIdempotentElem.one_sub_iff.mpr hid).eq
  have hx : U * x * L * (U * y * L) = U * (x * y) * L := by
    calc U * x * L * (U * y * L)
        = U * x * ((L * U) * (y * L)) := by simp only [Matrix.mul_assoc]
      _ = U * x * (y * L) := by rw [hLU, Matrix.one_mul]
      _ = U * (x * y) * L := by simp only [Matrix.mul_assoc]
  have h2 : U * x * L * (1 - e) = 0 := by
    rw [Matrix.mul_assoc, bmSDU_L_one_sub hUL hLU, Matrix.mul_zero]
  have h3 : (1 - e) * (U * y * L) = 0 := by
    rw [show (1 - e) * (U * y * L) = ((1 - e) * U) * (y * L) from by
      rw [Matrix.mul_assoc (1 - e) U (y * L)]
      simp only [Matrix.mul_assoc],
      bmSDU_one_sub_mul_U hUL hLU, Matrix.zero_mul]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, hx, h2, h3, h1e]
  abel

private lemma bmSDU_embed_isometry {F : Type} [Field F] {n r : ℕ} (σ : F →+* F)
    (G : Matrix (Fin n) (Fin n) F) {e : Matrix (Fin n) (Fin n) F}
    {U : Matrix (Fin n) (Fin r) F} {L : Matrix (Fin r) (Fin n) F}
    (hE2 : e * e = e) (hUL : U * L = e) (hLU : L * U = 1)
    (hadj : Matrix.transpose (e.map σ) * G = G * e)
    (hA : Matrix.transpose (U.map σ) * G * U = Unitary.antidiag r)
    {x : Matrix (Fin r) (Fin r) F}
    (hx : Matrix.transpose (x.map σ) * Unitary.antidiag r * x = Unitary.antidiag r) :
    Matrix.transpose ((U * x * L + (1 - e)).map σ) * G * (U * x * L + (1 - e)) = G := by
  have hid : IsIdempotentElem e := hE2
  have heU : e * U = U := bmSDU_e_mul_U hUL hLU
  have heGe : Matrix.transpose (e.map σ) * G * (1 - e) = 0 := by
    calc Matrix.transpose (e.map σ) * G * (1 - e)
        = G * e * (1 - e) := by rw [hadj]
      _ = G * (e * (1 - e)) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hid.mul_one_sub_self, Matrix.mul_zero]
  have hterm : Matrix.transpose (L.map σ) * (Matrix.transpose (U.map σ) * G * U) * L =
      G * e := by
    calc Matrix.transpose (L.map σ) * (Matrix.transpose (U.map σ) * G * U) * L
        = (Matrix.transpose (L.map σ) * Matrix.transpose (U.map σ)) * G * (U * L) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.transpose ((U.map σ) * (L.map σ)) * G * (U * L) := by rw [Matrix.transpose_mul]
      _ = Matrix.transpose ((U * L).map σ) * G * (U * L) := by rw [Matrix.map_mul]
      _ = Matrix.transpose (e.map σ) * G * e := by rw [hUL]
      _ = G * e := by rw [hadj, Matrix.mul_assoc, hE2]
  have hx' : Matrix.transpose (x.map σ) * (Matrix.transpose (U.map σ) * G * U) * x =
      Matrix.transpose (U.map σ) * G * U := by rw [hA, hx]
  have hAP : Matrix.transpose (L.map σ) * Matrix.transpose (x.map σ) *
      Matrix.transpose (U.map σ) * G * (U * x * L) = G * e := by
    rw [show Matrix.transpose (L.map σ) * Matrix.transpose (x.map σ) *
        Matrix.transpose (U.map σ) * G * (U * x * L) =
        Matrix.transpose (L.map σ) * (Matrix.transpose (x.map σ) *
          (Matrix.transpose (U.map σ) * G * U) * x) * L from by
          simp only [Matrix.mul_assoc]]
    rw [hx', hterm]
  have hUGe : Matrix.transpose (U.map σ) * G * (1 - e) = 0 := by
    calc Matrix.transpose (U.map σ) * G * (1 - e)
        = Matrix.transpose (U.map σ) * G - Matrix.transpose (U.map σ) * G * e := by
          rw [Matrix.mul_sub, Matrix.mul_one]
      _ = Matrix.transpose (U.map σ) * G - Matrix.transpose (U.map σ) * G := by
          congr 1
          calc Matrix.transpose (U.map σ) * G * e
              = Matrix.transpose (U.map σ) * (G * e) := Matrix.mul_assoc _ _ _
            _ = Matrix.transpose (U.map σ) * (Matrix.transpose (e.map σ) * G) := by rw [hadj]
            _ = (Matrix.transpose (U.map σ) * Matrix.transpose (e.map σ)) * G :=
                  (Matrix.mul_assoc _ _ _).symm
            _ = Matrix.transpose ((e.map σ) * (U.map σ)) * G := by rw [Matrix.transpose_mul]
            _ = Matrix.transpose ((e * U).map σ) * G := by rw [Matrix.map_mul]
            _ = Matrix.transpose (U.map σ) * G := by rw [heU]
      _ = 0 := sub_self _
  have hAC : Matrix.transpose (L.map σ) * Matrix.transpose (x.map σ) *
      Matrix.transpose (U.map σ) * G * (1 - e) = 0 := by
    rw [show Matrix.transpose (L.map σ) * Matrix.transpose (x.map σ) *
        Matrix.transpose (U.map σ) * G * (1 - e) =
        Matrix.transpose (L.map σ) * Matrix.transpose (x.map σ) *
          (Matrix.transpose (U.map σ) * G * (1 - e)) from by simp only [Matrix.mul_assoc],
      hUGe, Matrix.mul_zero]
  have hBP : (1 - Matrix.transpose (e.map σ)) * G * (U * x * L) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul]
    have h : Matrix.transpose (e.map σ) * G * (U * x * L) = G * (U * x * L) := by
      calc Matrix.transpose (e.map σ) * G * (U * x * L)
          = (G * e) * (U * x * L) := by rw [hadj]
        _ = G * ((e * U) * (x * L)) := by simp only [Matrix.mul_assoc]
        _ = G * (U * x * L) := by rw [heU, Matrix.mul_assoc]
    rw [h, sub_self]
  have hBC : (1 - Matrix.transpose (e.map σ)) * G * (1 - e) = G * (1 - e) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul, heGe, sub_zero]
  have htr : Matrix.transpose ((U * x * L + (1 - e)).map σ) =
      Matrix.transpose (L.map σ) * Matrix.transpose (x.map σ) * Matrix.transpose (U.map σ) +
        (1 - Matrix.transpose (e.map σ)) := by
    rw [Matrix.map_add σ (map_add σ), Matrix.map_sub σ (map_sub σ),
      Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.map_mul, Matrix.map_mul,
      Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [htr, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hAP, hAC, hBP, hBC,
    add_zero, zero_add, ← Matrix.mul_add]
  rw [show e + (1 - e) = 1 from by abel, Matrix.mul_one]

private lemma bmSDU_embed_det {F : Type} [Field F] {n r : ℕ}
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e) (hLU : L * U = 1)
    {x : Matrix (Fin r) (Fin r) F} (hx : x.det = 1) :
    (U * x * L + (1 - e)).det = 1 := by
  have h : U * x * L + (1 - e) = 1 + U * ((x - 1) * L) := by
    rw [show U * ((x - 1) * L) = U * x * L - e from by
      rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hUL]]
    abel
  rw [h, Matrix.det_one_add_mul_comm U ((x - 1) * L),
    show ((x - 1) * L) * U = x - 1 from by rw [Matrix.mul_assoc, hLU, Matrix.mul_one],
    show (1 : Matrix (Fin r) (Fin r) F) + (x - 1) = x from by abel, hx]

private noncomputable def bmSDU_blockGL {F : Type} [Field F] {n r : ℕ}
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hE2 : e * e = e) (hUL : U * L = e) (hLU : L * U = 1)
    (x : GL (Fin r) F) : GL (Fin n) F :=
  ⟨U * (x : Matrix (Fin r) (Fin r) F) * L + (1 - e),
   U * ((x⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e),
   by
     rw [bmSDU_embed_mul hE2 hUL hLU (x : Matrix (Fin r) (Fin r) F)
       ((x⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)]
     rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, hUL]
     abel,
   by
     rw [bmSDU_embed_mul hE2 hUL hLU ((x⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)
       (x : Matrix (Fin r) (Fin r) F)]
     rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one, hUL]
     abel⟩

private lemma bmSDU_blockGL_mem {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hE2 : e * e = e) (hUL : U * L = e) (hLU : L * U = 1)
    (hadj : Matrix.transpose (e.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    (x : ↥(Unitary.SU σ r)) :
    bmSDU_blockGL hE2 hUL hLU (x : GL (Fin r) F) ∈ Unitary.SU σ n := by
  rw [Unitary.mem_SU]
  exact ⟨bmSDU_embed_det hUL hLU (Unitary.mem_SU.mp x.2).1,
    bmSDU_embed_isometry σ.toRingHom (Unitary.antidiag n) hE2 hUL hLU hadj hA
      (Unitary.mem_SU.mp x.2).2⟩

private lemma bmSDU_blockHom {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hE2 : e * e = e) (hUL : U * L = e)
    (hLU : L * U = 1)
    (hadj : Matrix.transpose (e.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F)) :
    ∃ ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n),
      Function.Injective ι ∧
      ∀ x : ↥(Unitary.SU σ r),
        ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
          U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e) := by
  let ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n) :=
  { toFun := fun x => ⟨bmSDU_blockGL hE2 hUL hLU (x : GL (Fin r) F),
      bmSDU_blockGL_mem σ hE2 hUL hLU hadj hA x⟩
    map_one' := by
      apply Subtype.ext
      apply Units.ext
      show U * (((1 : ↥(Unitary.SU σ r)) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L +
        (1 - e) = 1
      rw [Subgroup.coe_one, Units.val_one, Matrix.mul_one, hUL]
      abel
    map_mul' := fun x y => by
      apply Subtype.ext
      apply Units.ext
      show U * (((x * y : ↥(Unitary.SU σ r)) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L +
        (1 - e) =
        (U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e)) *
          (U * ((y : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
      rw [Subgroup.coe_mul, Units.val_mul]
      exact (bmSDU_embed_mul hE2 hUL hLU ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)
        ((y : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)).symm }
  refine ⟨ι, ?_, ?_⟩
  · intro x y hxy
    have h : U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L =
        U * ((y : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L := by
      have h2 := congrArg (fun g : ↥(Unitary.SU σ n) =>
        ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) hxy
      exact add_right_cancel h2
    have h3 := congrArg (fun M => L * M * U) h
    have key : ∀ z : Matrix (Fin r) (Fin r) F, L * (U * z * L) * U = z := by
      intro z
      calc L * (U * z * L) * U = (L * U) * z * (L * U) := by
            simp only [Matrix.mul_assoc]
        _ = z := by rw [hLU, Matrix.one_mul, Matrix.mul_one]
    apply Subtype.ext
    apply Units.ext
    exact (key ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)).symm.trans
      (h3.trans (key ((y : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)))
  · intro x
    rfl

private lemma bmSDU_scalar_action' {F : Type} [Field F] {n : ℕ}
    (A : Subalgebra F (Matrix (Fin n) (Fin n) F)) {e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn A e) (hdeg : blockDegree A e < 2) :
    ∀ a ∈ A, ∃ c : F, a * e = c • e := by
  intro a ha
  have hmem : e ∈ (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) := by
    rw [Submodule.mem_map]
    exact ⟨1, A.one_mem, by rw [LinearMap.mulRight_apply, one_mul]⟩
  have hne0 : blockDegree A e ≠ 0 := by
    intro h0
    have hbot : (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) = ⊥ :=
      Submodule.finrank_eq_zero.mp h0
    rw [hbot] at hmem
    exact he.2.2.1 (by simpa using hmem)
  have h1 : blockDegree A e = 1 := by omega
  have hae : a * e ∈ (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) := by
    rw [Submodule.mem_map]
    exact ⟨a, ha, by rw [LinearMap.mulRight_apply]⟩
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one h1 hmem he.2.2.1
  rw [hspan] at hae
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hae
  exact ⟨c, hc.symm⟩

private lemma bmSDU_adjoin_comm {F : Type} [Field F] {n : ℕ} {S : Set (GL (Fin n) F)}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S), ∀ b ∈ Algebra.adjoin F (Units.val '' S),
      a * b = b * a := by
  have hcommS : (Units.val '' S : Set (Matrix (Fin n) (Fin n) F)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    show (s : Matrix (Fin n) (Fin n) F) * (s' : Matrix (Fin n) (Fin n) F) =
      (s' : Matrix (Fin n) (Fin n) F) * (s : Matrix (Fin n) (Fin n) F)
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val (hS s hs s' hs').eq
  letI : CommSemiring (Algebra.adjoin F (Units.val '' S)) :=
    Algebra.adjoinCommSemiringOfComm F hcommS
  intro a ha b hb
  have h := mul_comm (⟨a, ha⟩ : Algebra.adjoin F (Units.val '' S))
    (⟨b, hb⟩ : Algebra.adjoin F (Units.val '' S))
  simpa only [Subalgebra.coe_mul] using congrArg Subtype.val h

private lemma bmSDU_embed_det_eq {F : Type} [Field F] {n r : ℕ}
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e) (hLU : L * U = 1)
    (x : Matrix (Fin r) (Fin r) F) :
    (U * x * L + (1 - e)).det = x.det := by
  have h : U * x * L + (1 - e) = 1 + U * ((x - 1) * L) := by
    rw [show U * ((x - 1) * L) = U * x * L - e from by
      rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hUL]]
    abel
  rw [h, Matrix.det_one_add_mul_comm U ((x - 1) * L),
    show ((x - 1) * L) * U = x - 1 from by rw [Matrix.mul_assoc, hLU, Matrix.mul_one],
    show (1 : Matrix (Fin r) (Fin r) F) + (x - 1) = x from by abel]

private lemma bmSDU_embed_fixes_one_sub {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hE2 : e * e = e) (hUL : U * L = e) (hLU : L * U = 1)
    (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    (x : ↥(Unitary.SU σ r)) :
    ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (1 - e) = 1 - e := by
  rw [hιform x, Matrix.add_mul, Matrix.mul_assoc, bmSDU_L_one_sub hUL hLU, Matrix.mul_zero,
    zero_add]
  exact (IsIdempotentElem.one_sub_iff.mpr hE2).eq

private lemma bmSDU_embed_commutes_S {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F)
    (S : Set (GL (Fin n) F)) {e : Matrix (Fin n) (Fin n) F}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) e < 2)
    {U : Matrix (Fin n) (Fin r) F} {L : Matrix (Fin r) (Fin n) F}
    (hUL : U * L = e) (hLU : L * U = 1)
    (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e)) :
    ∀ s ∈ S, ∀ x : ↥(Unitary.SU σ r),
      s * (ι x : GL (Fin n) F) = (ι x : GL (Fin n) F) * s := by
  intro s hs x
  have hAcomm := bmSDU_adjoin_comm hS
  have heA : e ∈ Algebra.adjoin F (Units.val '' S) := he.1
  have hsA : (s : Matrix (Fin n) (Fin n) F) ∈ Algebra.adjoin F (Units.val '' S) :=
    Algebra.subset_adjoin ⟨s, hs, rfl⟩
  obtain ⟨c, hc⟩ := bmSDU_scalar_action' (Algebra.adjoin F (Units.val '' S)) he hdeg
    (s : Matrix (Fin n) (Fin n) F) hsA
  have hse : (s : Matrix (Fin n) (Fin n) F) * e = e * (s : Matrix (Fin n) (Fin n) F) :=
    hAcomm _ hsA _ heA
  have heU : e * U = U := bmSDU_e_mul_U hUL hLU
  have hLUe : L * e = L := bmSDU_L_mul_e hUL hLU
  have h1 : (s : Matrix (Fin n) (Fin n) F) * (1 - e) =
      (1 - e) * (s : Matrix (Fin n) (Fin n) F) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hse]
  have hsU : (s : Matrix (Fin n) (Fin n) F) * U = c • U := by
    calc (s : Matrix (Fin n) (Fin n) F) * U
        = (s : Matrix (Fin n) (Fin n) F) * (e * U) := by rw [heU]
      _ = ((s : Matrix (Fin n) (Fin n) F) * e) * U := (Matrix.mul_assoc _ _ _).symm
      _ = (c • e) * U := by rw [hc]
      _ = c • (e * U) := Matrix.smul_mul _ _ _
      _ = c • U := by rw [heU]
  have hsLe : L * ((s : Matrix (Fin n) (Fin n) F) * e) = c • L := by
    rw [hc, Matrix.mul_smul, hLUe]
  have hsL1e : L * ((s : Matrix (Fin n) (Fin n) F) * (1 - e)) = 0 := by
    rw [h1, ← Matrix.mul_assoc, bmSDU_L_one_sub hUL hLU, Matrix.zero_mul]
  have hsL : L * (s : Matrix (Fin n) (Fin n) F) = c • L := by
    calc L * (s : Matrix (Fin n) (Fin n) F)
        = L * ((s : Matrix (Fin n) (Fin n) F) * e) +
            L * ((s : Matrix (Fin n) (Fin n) F) * (1 - e)) := by
          rw [← Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]
      _ = c • L + 0 := by rw [hsLe, hsL1e]
      _ = c • L := by rw [add_zero]
  have hcomm : (s : Matrix (Fin n) (Fin n) F) *
      (U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L) =
      (U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L) *
        (s : Matrix (Fin n) (Fin n) F) := by
    rw [show (s : Matrix (Fin n) (Fin n) F) *
          (U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L) =
          ((s : Matrix (Fin n) (Fin n) F) * U) *
            ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L from by
            simp only [Matrix.mul_assoc],
      show (U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L) *
            (s : Matrix (Fin n) (Fin n) F) =
          U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) *
            (L * (s : Matrix (Fin n) (Fin n) F)) from by simp only [Matrix.mul_assoc],
      hsU, hsL]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hιform x, Matrix.mul_add, Matrix.add_mul, hcomm, h1]

private lemma bmSDU_range_le {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F)
    (S : Set (GL (Fin n) F)) {e : Matrix (Fin n) (Fin n) F}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) e < 2)
    {U : Matrix (Fin n) (Fin r) F} {L : Matrix (Fin r) (Fin n) F}
    (hUL : U * L = e) (hLU : L * U = 1)
    (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e)) :
    ι.range ≤ glBlockCentralizer (Unitary.SU σ n).subtype S e := by
  intro g hg
  obtain ⟨x, rfl⟩ := hg
  rw [glBlockCentralizer, Subgroup.mem_comap]
  have hE2 : e * e = e := he.2.1.eq
  refine ⟨?_, ?_⟩
  · change (ι x : GL (Fin n) F) ∈ Subgroup.centralizer S
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact bmSDU_embed_commutes_S σ S hS he hdeg hUL hLU ι hιform s hs x
  · change ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (1 - e) = 1 - e
    exact bmSDU_embed_fixes_one_sub σ hE2 hUL hLU ι hιform x

private lemma bmSDU_commute_adjoin {F : Type} [Field F] {n : ℕ} {S : Set (GL (Fin n) F)}
    {x : Matrix (Fin n) (Fin n) F}
    (hx : ∀ s ∈ S, (s : Matrix (Fin n) (Fin n) F) * x = x * (s : Matrix (Fin n) (Fin n) F)) :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S), x * a = a * x := by
  intro a ha
  refine Algebra.adjoin_induction (p := fun a _ => x * a = a * x) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨s, hs, rfl⟩
    exact (hx s hs).symm
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
  · intro a b _ _ ha hb
    rw [Matrix.mul_add, Matrix.add_mul, ha, hb]
  · intro a b _ _ ha hb
    rw [← Matrix.mul_assoc, ha, Matrix.mul_assoc, hb, ← Matrix.mul_assoc]

private lemma bmSDU_retract_isometry {F : Type} [Field F] {n r : ℕ} (σ : F →+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hE2 : e * e = e) (hUL : U * L = e) (hLU : L * U = 1)
    (hadj : Matrix.transpose (e.map σ) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e)
    (hA : Matrix.transpose (U.map σ) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    {G : Matrix (Fin n) (Fin n) F} (hGe : G * e = e * G)
    (hisoG : Matrix.transpose (G.map σ) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * G =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F)) :
    Matrix.transpose ((L * G * U).map σ) * (Unitary.antidiag r : Matrix (Fin r) (Fin r) F) *
      (L * G * U) = (Unitary.antidiag r : Matrix (Fin r) (Fin r) F) := by
  have hEU : e * U = U := bmSDU_e_mul_U hUL hLU
  have hLUσ : Matrix.transpose (L.map σ) * Matrix.transpose (U.map σ) =
      Matrix.transpose (e.map σ) := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hUL]
  have hmap : (L * G * U).map σ = L.map σ * G.map σ * U.map σ := by
    rw [Matrix.map_mul, Matrix.map_mul]
  have htr : Matrix.transpose ((L * G * U).map σ) =
      Matrix.transpose (U.map σ) * Matrix.transpose (G.map σ) *
        Matrix.transpose (L.map σ) := by
    rw [hmap, Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [htr, ← hA]
  calc Matrix.transpose (U.map σ) * Matrix.transpose (G.map σ) * Matrix.transpose (L.map σ) *
        (Matrix.transpose (U.map σ) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U) *
        (L * G * U)
      = Matrix.transpose (U.map σ) * Matrix.transpose (G.map σ) *
          (Matrix.transpose (L.map σ) * Matrix.transpose (U.map σ)) *
          (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U * L * G * U := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.transpose (U.map σ) * Matrix.transpose (G.map σ) *
          Matrix.transpose (e.map σ) *
          (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U * L * G * U := by rw [hLUσ]
    _ = Matrix.transpose (U.map σ) * Matrix.transpose (G.map σ) *
          Matrix.transpose (e.map σ) *
          (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * (U * L) * G * U := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.transpose (U.map σ) * Matrix.transpose (G.map σ) *
          Matrix.transpose (e.map σ) *
          (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e * G * U := by rw [hUL]
    _ = Matrix.transpose (U.map σ) * Matrix.transpose (G.map σ) *
          (Matrix.transpose (e.map σ) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F)) *
          e * G * U := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.transpose (U.map σ) * Matrix.transpose (G.map σ) *
          ((Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e) * e * G * U := by rw [hadj]
    _ = Matrix.transpose (U.map σ) * Matrix.transpose (G.map σ) *
          (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * (e * e) * G * U := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.transpose (U.map σ) * Matrix.transpose (G.map σ) *
          (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e * G * U := by rw [hE2]
    _ = Matrix.transpose (U.map σ) * Matrix.transpose (G.map σ) *
          (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * (e * G) * U := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.transpose (U.map σ) * Matrix.transpose (G.map σ) *
          (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * (G * e) * U := by rw [hGe]
    _ = Matrix.transpose (U.map σ) *
          (Matrix.transpose (G.map σ) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * G) *
          e * U := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.transpose (U.map σ) *
          (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e * U := by rw [hisoG]
    _ = Matrix.transpose (U.map σ) *
          (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * (e * U) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.transpose (U.map σ) *
          (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U := by rw [hEU]

private lemma bmSDU_retract_unit {F : Type} [Field F] {n r : ℕ}
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e) (hLU : L * U = 1)
    {G Gi : Matrix (Fin n) (Fin n) F} (hGe : G * e = e * G)
    (hGiG : Gi * G = 1) (hGGi : G * Gi = 1) :
    (L * G * U) * (L * Gi * U) = 1 ∧ (L * Gi * U) * (L * G * U) = 1 := by
  have hGie : Gi * e = e * Gi := by
    calc Gi * e = Gi * e * 1 := by rw [Matrix.mul_one]
      _ = Gi * e * (G * Gi) := by rw [hGGi, Matrix.mul_one]
      _ = Gi * (e * G) * Gi := by simp only [Matrix.mul_assoc]
      _ = Gi * (G * e) * Gi := by rw [← hGe]
      _ = Gi * G * e * Gi := by simp only [Matrix.mul_assoc]
      _ = e * Gi := by rw [hGiG, Matrix.one_mul]
  constructor
  · calc (L * G * U) * (L * Gi * U)
        = L * G * ((U * L) * (Gi * U)) := by simp only [Matrix.mul_assoc]
      _ = L * G * (e * (Gi * U)) := by rw [hUL]
      _ = L * (G * e) * Gi * U := by simp only [Matrix.mul_assoc]
      _ = L * (e * G) * Gi * U := by rw [hGe]
      _ = L * e * (G * Gi) * U := by simp only [Matrix.mul_assoc]
      _ = L * e * U := by rw [hGGi, Matrix.mul_one]
      _ = L * U := by rw [bmSDU_L_mul_e hUL hLU]
      _ = 1 := hLU
  · calc (L * Gi * U) * (L * G * U)
        = L * Gi * ((U * L) * (G * U)) := by simp only [Matrix.mul_assoc]
      _ = L * Gi * (e * (G * U)) := by rw [hUL]
      _ = L * (Gi * e) * G * U := by simp only [Matrix.mul_assoc]
      _ = L * (e * Gi) * G * U := by rw [hGie]
      _ = L * e * (Gi * G) * U := by simp only [Matrix.mul_assoc]
      _ = L * e * U := by rw [hGiG, Matrix.mul_one]
      _ = L * U := by rw [bmSDU_L_mul_e hUL hLU]
      _ = 1 := hLU

private lemma bmSDU_le_range {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F)
    (S : Set (GL (Fin n) F)) {e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hadj : Matrix.transpose (e.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e)
    {U : Matrix (Fin n) (Fin r) F} {L : Matrix (Fin r) (Fin n) F}
    (hUL : U * L = e) (hLU : L * U = 1)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e)) :
    glBlockCentralizer (Unitary.SU σ n).subtype S e ≤ ι.range := by
  intro g hg
  rw [glBlockCentralizer, Subgroup.mem_comap] at hg
  obtain ⟨hgcent, hgfix⟩ := Subgroup.mem_inf.mp hg
  rw [Subgroup.mem_centralizer_iff] at hgcent
  have hx : ∀ s ∈ S, (s : Matrix (Fin n) (Fin n) F) *
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (s : Matrix (Fin n) (Fin n) F) := by
    intro s hs
    simpa only [Units.val_mul, Subgroup.subtype_apply] using congrArg Units.val (hgcent s hs)
  have hGe : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * e =
      e * ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
    bmSDU_commute_adjoin hx e he.1
  have hG1e : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (1 - e) = 1 - e := hgfix
  have hGGi : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (((g : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : (((g : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨hunit1, hunit2⟩ := bmSDU_retract_unit hUL hLU hGe hGiG hGGi
  have hG_decomp : U * (L * ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * U) * L +
      (1 - e) = ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    have hUL' : U * (L * ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * U) * L =
        ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * e := by
      calc U * (L * ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * U) * L
          = (U * L) * ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (U * L) := by
            simp only [Matrix.mul_assoc]
        _ = e * ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * e := by rw [hUL]
        _ = ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * e := by
            rw [← hGe, Matrix.mul_assoc, he.2.1.eq]
    rw [hUL', ← hG1e, ← Matrix.mul_add, show e + (1 - e) = 1 from by abel, Matrix.mul_one]
  let xunit : GL (Fin r) F :=
    Units.mk (L * ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * U)
      (L * (((g : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * U)
      hunit1 hunit2
  have hx'mem : xunit ∈ Unitary.SU σ r := by
    rw [Unitary.mem_SU]
    refine ⟨?_, ?_⟩
    · show (L * ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * U).det = 1
      rw [← bmSDU_embed_det_eq hUL hLU
          (L * ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * U),
        hG_decomp, (Unitary.mem_SU.mp g.2).1]
    · show Matrix.transpose ((L * ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * U).map
          σ.toRingHom) * (Unitary.antidiag r : Matrix (Fin r) (Fin r) F) *
          (L * ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * U) =
          (Unitary.antidiag r : Matrix (Fin r) (Fin r) F)
      exact bmSDU_retract_isometry σ.toRingHom he.2.1.eq hUL hLU hadj hA hGe
        ((Unitary.mem_SU.mp g.2).2)
  refine MonoidHom.mem_range.mpr ⟨⟨xunit, hx'mem⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [hιform ⟨xunit, hx'mem⟩]
  show U * (L * ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * U) * L + (1 - e) =
    ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  exact hG_decomp

private lemma bmSDU_blockHom_range {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F)
    (S : Set (GL (Fin n) F)) {e : Matrix (Fin n) (Fin n) F}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hadj : Matrix.transpose (e.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e)
    (hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) e < 2)
    {U : Matrix (Fin n) (Fin r) F} {L : Matrix (Fin r) (Fin n) F}
    (hUL : U * L = e) (hLU : L * U = 1)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e)) :
    ι.range = glBlockCentralizer (Unitary.SU σ n).subtype S e := by
  exact le_antisymm
    (bmSDU_range_le σ S hS he hdeg hUL hLU ι hιform)
    (bmSDU_le_range σ S he hadj hUL hLU hA ι hιform)

private lemma bmSDU_anti_map {F : Type} [Field F] (σ : F →+* F) (r : ℕ) :
    (Unitary.antidiag r : Matrix (Fin r) (Fin r) F).map σ = Unitary.antidiag r := by
  ext i j
  rw [Matrix.map_apply]
  have hanti : ∀ a b : Fin r, (Unitary.antidiag r : Matrix (Fin r) (Fin r) F) a b =
      if b = a.rev then 1 else 0 := fun a b => rfl
  rw [hanti i j]
  by_cases h : j = i.rev
  · rw [if_pos h, map_one]
  · rw [if_neg h, map_zero]

private lemma bmSDU_anti_symm {F : Type} [Field F] (r : ℕ) :
    Matrix.transpose (Unitary.antidiag r : Matrix (Fin r) (Fin r) F) = Unitary.antidiag r := by
  have h := bmSDU_antidiag_herm (RingHom.id F) r
  simpa [Matrix.map_id] using h

private lemma bmSDU_anti_vecMul {F : Type} [Field F] {r : ℕ} (v : Fin r → F) :
    Matrix.vecMul v (Unitary.antidiag r) =
      Matrix.mulVec (Unitary.antidiag r : Matrix (Fin r) (Fin r) F) v := by
  ext j
  simp only [Matrix.vecMul_apply, Matrix.mulVec_apply, dotProduct, Matrix.col_apply,
    Matrix.row_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsymm : (Unitary.antidiag r : Matrix (Fin r) (Fin r) F) i j =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F) j i := by
    have h := congrFun (congrFun (bmSDU_anti_symm (F := F) r) j) i
    simpa [Matrix.transpose_apply] using h
  rw [hsymm, mul_comm]

private lemma bmSDU_std_rev_iff {r : ℕ} (hr : 2 ≤ r) (i : Fin r) :
    ((⟨0, by omega⟩ : Fin r) = Fin.rev i) ↔ i = Fin.rev (⟨0, by omega⟩ : Fin r) := by
  constructor
  · intro h; rw [← Fin.rev_rev i, ← h]
  · intro h; rw [h, Fin.rev_rev]

private lemma bmSDU_std_rev_zero_ne {r : ℕ} (hr : 2 ≤ r) :
    Fin.rev (⟨0, by omega⟩ : Fin r) ≠ (⟨0, by omega⟩ : Fin r) := by
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_rev] at hv
  simp at hv
  omega

private lemma bmSDU_std_mulVec_first {F : Type} [Field F] {r : ℕ} (hr : 2 ≤ r) :
    Matrix.mulVec (Unitary.antidiag r : Matrix (Fin r) (Fin r) F)
      (Pi.single (⟨0, by omega⟩ : Fin r) (1 : F)) =
      (Pi.single (Fin.rev (⟨0, by omega⟩ : Fin r)) (1 : F) : Fin r → F) := by
  haveI : NeZero r := ⟨by omega⟩
  funext i
  rw [Matrix.mulVec_apply, dotProduct, Finset.sum_eq_single (⟨0, by omega⟩ : Fin r)]
  · rw [Pi.single_eq_same, mul_one, Matrix.row_apply, Unitary.antidiag, Matrix.of_apply,
      Pi.single_apply]
    by_cases h : i = Fin.rev (⟨0, by omega⟩ : Fin r)
    · rw [if_pos ((bmSDU_std_rev_iff hr i).mpr h), if_pos h]
    · rw [if_neg (fun hh => h ((bmSDU_std_rev_iff hr i).mp hh)), if_neg h]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, mul_zero]
  · simp

private lemma bmSDU_std_mulVec_last {F : Type} [Field F] {r : ℕ} (hr : 2 ≤ r) :
    Matrix.mulVec (Unitary.antidiag r : Matrix (Fin r) (Fin r) F)
      (Pi.single (Fin.rev (⟨0, by omega⟩ : Fin r)) (1 : F)) =
      (Pi.single (⟨0, by omega⟩ : Fin r) (1 : F) : Fin r → F) := by
  haveI : NeZero r := ⟨by omega⟩
  funext i
  rw [Matrix.mulVec_apply, dotProduct,
    Finset.sum_eq_single (Fin.rev (⟨0, by omega⟩ : Fin r))]
  · rw [Pi.single_eq_same, mul_one, Matrix.row_apply, Unitary.antidiag, Matrix.of_apply,
      Pi.single_apply]
    by_cases h : i = (⟨0, by omega⟩ : Fin r)
    · rw [h]; simp
    · have hcond : ¬ ((⟨0, by omega⟩ : Fin r).rev = i.rev) := by
        intro hh
        exact h (Fin.rev_injective hh).symm
      rw [if_neg hcond, if_neg h]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, mul_zero]
  · simp

private lemma bmSDU_transv_std_su_aux {F : Type} [Field F] [CharP F 2] {r : ℕ} (σ : F ≃+* F)
    (c : F) (hc : σ c = c) {v : Fin r → F}
    (hσv : (fun i => σ (v i)) = v)
    (hvv : (Matrix.mulVec (Unitary.antidiag r : Matrix (Fin r) (Fin r) F) v) ⬝ᵥ v = 0) :
    ∃ xunit : GL (Fin r) F,
      (xunit : Matrix (Fin r) (Fin r) F) =
        1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r)) ∧
      xunit ∈ Unitary.SU σ r ∧
      xunit ∈ unitTransvGroup σ.toRingHom (Unitary.antidiag r) v := by
  let A : Matrix (Fin r) (Fin r) F := Unitary.antidiag r
  let w : Fin r → F := Matrix.mulVec A v
  have hvA : Matrix.vecMul v A = w := by rw [bmSDU_anti_vecMul]
  have hφ : Matrix.vecMul (fun i => σ (v i)) A = w := by rw [hσv, hvA]
  let E : Matrix (Fin r) (Fin r) F := Matrix.vecMulVec v w
  have hEeq : Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) A) = E := by rw [hφ]
  have hwσ : (fun i => σ (w i)) = w := by
    funext i
    have hm := RingHom.map_mulVec σ.toRingHom A v i
    rw [bmSDU_anti_map σ.toRingHom r] at hm
    rw [show (⇑σ.toRingHom ∘ v) = (fun j => σ (v j)) from rfl, hσv] at hm
    exact hm
  have hEE : E * E = 0 := by
    simp only [E]
    rw [Matrix.vecMulVec_mul_vecMulVec, hvv, zero_smul, Matrix.vecMulVec_zero]
  have hEtA : Matrix.transpose E * A = Matrix.vecMulVec w w := by
    simp only [E]
    rw [Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul, hvA]
  have hAE : A * E = Matrix.vecMulVec w w := by
    simp only [E]
    rw [Matrix.mul_vecMulVec]
  have hEAE : Matrix.transpose E * A * E = 0 := by
    rw [hEtA]
    simp only [E]
    rw [Matrix.vecMulVec_mul_vecMulVec, hvv, zero_smul, Matrix.vecMulVec_zero]
  have hEmap : E.map σ = E := by
    ext i j
    simp only [E, Matrix.map_apply, Matrix.vecMulVec_apply]
    rw [map_mul, congrFun hσv i, congrFun hwσ j]
  have hcc : (c • E) * (c • E) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hEE, smul_zero]
  have h1 : (1 + c • E) * (1 - c • E) = 1 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hcc]
    abel
  have h2 : (1 - c • E) * (1 + c • E) = 1 := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hcc]
    abel
  let xunit : GL (Fin r) F := ⟨1 + c • E, 1 - c • E, h1, h2⟩
  have hxval : (xunit : Matrix (Fin r) (Fin r) F) = 1 + c • E := rfl
  have hdet : (1 + c • E).det = 1 := by
    let ucol : Matrix (Fin r) (Fin 1) F := Matrix.of (fun i _ => v i)
    let wrow : Matrix (Fin 1) (Fin r) F := Matrix.of (fun _ j => w j)
    have hfac : ucol * wrow = E := by
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_one]
      simp [ucol, wrow, E, Matrix.vecMulVec_apply]
    have hzero : wrow * ucol = 0 := by
      ext i j
      simp only [ucol, wrow, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
      simpa only [dotProduct] using hvv
    rw [show (1 + c • E) = 1 + (c • ucol) * wrow by rw [Matrix.smul_mul, hfac]]
    rw [Matrix.det_one_add_mul_comm, Matrix.mul_smul, hzero, smul_zero, add_zero, Matrix.det_one]
  have hmapE : (1 + c • E).map σ = 1 + σ c • E := by
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      smul_eq_mul]
    rw [map_add, map_mul, show σ (E i j) = E i j from congrFun (congrFun hEmap i) j]
    by_cases h : i = j
    · rw [if_pos h, map_one]
    · rw [if_neg h, map_zero]
  have hiso : Matrix.transpose ((1 + c • E).map σ) * A * (1 + c • E) = A := by
    rw [hmapE, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul]
    calc (1 + σ c • Matrix.transpose E) * A * (1 + c • E)
        = A + σ c • (Matrix.transpose E * A) + c • (A * E) +
            (σ c * c) • (Matrix.transpose E * A * E) := by
          rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_one,
            Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul, smul_add, smul_smul]
          rw [mul_comm (σ c) c]
          abel
      _ = A + σ c • Matrix.vecMulVec w w + c • Matrix.vecMulVec w w +
            (σ c * c) • (0 : Matrix (Fin r) (Fin r) F) := by rw [hEAE, hEtA, hAE]
      _ = A := by
          rw [smul_zero, add_zero]
          rw [show A + σ c • Matrix.vecMulVec w w + c • Matrix.vecMulVec w w =
              A + (σ c • Matrix.vecMulVec w w + c • Matrix.vecMulVec w w) by abel]
          rw [show σ c • Matrix.vecMulVec w w + c • Matrix.vecMulVec w w = 0 by
            rw [← add_smul, hc, CharTwo.add_self_eq_zero, zero_smul]]
          rw [add_zero]
  refine ⟨xunit, ?_, ?_, ?_⟩
  · rw [hxval, ← hEeq]
  · rw [Unitary.mem_SU]
    exact ⟨by rw [hxval]; exact hdet, by rw [hxval]; simpa only [Unitary.conjTr, A] using hiso⟩
  · refine Subgroup.subset_closure ⟨c, hc, ?_⟩
    rw [hxval, ← hEeq]
    rfl

private lemma bmSDU_transv_std_su {F : Type} [Field F] [CharP F 2] {r : ℕ} (σ : F ≃+* F)
    (hr : 2 ≤ r) (c : F) (hc : σ c = c) {v : Fin r → F}
    (hv : v = Pi.single (⟨0, by omega⟩ : Fin r) (1 : F) ∨
      v = Pi.single (Fin.rev (⟨0, by omega⟩ : Fin r)) (1 : F)) :
    ∃ xunit : GL (Fin r) F,
      (xunit : Matrix (Fin r) (Fin r) F) =
        1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r)) ∧
      xunit ∈ Unitary.SU σ r ∧
      xunit ∈ unitTransvGroup σ.toRingHom (Unitary.antidiag r) v := by
  rcases hv with h1 | h2
  · rw [h1]
    refine bmSDU_transv_std_su_aux σ c hc ?_ ?_
    · funext i
      by_cases hi : i = (⟨0, by omega⟩ : Fin r)
      · rw [hi]; simp
      · simp [Pi.single_eq_of_ne hi]
    · rw [bmSDU_std_mulVec_first hr, single_dotProduct, Pi.single_apply,
        if_neg (bmSDU_std_rev_zero_ne hr), mul_zero]
  · rw [h2]
    refine bmSDU_transv_std_su_aux σ c hc ?_ ?_
    · funext i
      by_cases hi : i = (Fin.rev (⟨0, by omega⟩ : Fin r))
      · rw [hi]; simp
      · simp [Pi.single_eq_of_ne hi]
    · rw [bmSDU_std_mulVec_last hr, single_dotProduct, Pi.single_apply,
        if_neg (Ne.symm (bmSDU_std_rev_zero_ne hr)), mul_zero]

private lemma bmSDU_vecMul_transpose {F : Type} [CommSemiring F] {m n : Type}
    [Fintype n] (M : Matrix m n F) (x : n → F) :
    Matrix.vecMul x (Matrix.transpose M) = Matrix.mulVec M x := by
  ext j
  simp only [Matrix.vecMul_apply, Matrix.mulVec_apply, dotProduct, Matrix.col_apply,
    Matrix.row_apply, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm (x i) (M j i)

private lemma bmSDU_transv_std_image {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e) (hLU : L * U = 1)
    (hadj : Matrix.transpose (e.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F)) (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    {v : Fin r → F} {c : F} {xunit : GL (Fin r) F}
    (hx : (xunit : Matrix (Fin r) (Fin r) F) =
      1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r)))
    (hxSU : xunit ∈ Unitary.SU σ r) :
    ((ι ⟨xunit, hxSU⟩ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      1 + c • Matrix.vecMulVec (Matrix.mulVec U v)
        (Matrix.vecMul (fun i => σ (Matrix.mulVec U v i)) (Unitary.antidiag n)) := by
  have hφL : Matrix.vecMul (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r)) L =
      Matrix.vecMul (fun i => σ (Matrix.mulVec U v i)) (Unitary.antidiag n) := by
    have hAL : (Unitary.antidiag r : Matrix (Fin r) (Fin r) F) * L =
        Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) := by
      have heU : e * U = U := bmSDU_e_mul_U hUL hLU
      calc (Unitary.antidiag r : Matrix (Fin r) (Fin r) F) * L
          = (Matrix.transpose (U.map σ.toRingHom) *
              (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U) * L := by rw [hA]
        _ = Matrix.transpose (U.map σ.toRingHom) *
              (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * (U * L) := by
              simp only [Matrix.mul_assoc]
        _ = Matrix.transpose (U.map σ.toRingHom) *
              (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e := by rw [hUL]
        _ = Matrix.transpose (U.map σ.toRingHom) *
              ((Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e) := by
              simp only [Matrix.mul_assoc]
        _ = Matrix.transpose (U.map σ.toRingHom) *
              (Matrix.transpose (e.map σ.toRingHom) *
                (Unitary.antidiag n : Matrix (Fin n) (Fin n) F)) := by rw [← hadj]
        _ = (Matrix.transpose (U.map σ.toRingHom) * Matrix.transpose (e.map σ.toRingHom)) *
              (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) := by simp only [Matrix.mul_assoc]
        _ = Matrix.transpose ((e.map σ.toRingHom) * (U.map σ.toRingHom)) *
              (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) := by rw [Matrix.transpose_mul]
        _ = Matrix.transpose ((e * U).map σ.toRingHom) *
              (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) := by rw [Matrix.map_mul]
        _ = Matrix.transpose (U.map σ.toRingHom) *
              (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) := by rw [heU]
    rw [Matrix.vecMul_vecMul, hAL, ← Matrix.vecMul_vecMul, bmSDU_vecMul_transpose]
    congr 1
    funext i
    exact (RingHom.map_mulVec σ.toRingHom U v i).symm
  have hUEL : U * (1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag
      r))) * L + (1 - e) =
      1 + c • (U * Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r)) * L)
          := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul, hUL]
    abel
  rw [hιform ⟨xunit, hxSU⟩, hx, hUEL]
  congr 1
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hφL]

private lemma bmSDU_transv_group_eq {F : Type} [Field F] [CharP F 2] {n r : ℕ} (σ : F ≃+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e) (hLU : L * U = 1)
    (hadj : Matrix.transpose (e.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    (hr : 2 ≤ r) (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    (v : Fin r → F)
    (hv : v = Pi.single (⟨0, by omega⟩ : Fin r) (1 : F) ∨
      v = Pi.single (Fin.rev (⟨0, by omega⟩ : Fin r)) (1 : F)) :
    ((unitTransvGroup σ.toRingHom (Unitary.antidiag r) v).comap
        (Unitary.SU σ r).subtype).map ι =
      (unitTransvGroup σ.toRingHom (Unitary.antidiag n) (Matrix.mulVec U v)).comap
        (Unitary.SU σ n).subtype := by
  let SK : Set ↥(Unitary.SU σ r) := {z | ∃ c, σ c = c ∧
    ((z : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r))}
  let K : Subgroup ↥(Unitary.SU σ r) := Subgroup.closure SK
  have hgen : {g : GL (Fin r) F | ∃ c, σ c = c ∧
      (g : Matrix (Fin r) (Fin r) F) =
        1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r))} ⊆
      K.map (Unitary.SU σ r).subtype := by
    rintro g ⟨c, hc, hg⟩
    obtain ⟨xunit, hxmat, hxSU, -⟩ := bmSDU_transv_std_su σ hr c hc hv
    refine Subgroup.mem_map.mpr ⟨⟨xunit, hxSU⟩, ?_, ?_⟩
    · exact Subgroup.subset_closure ⟨c, hc, hxmat⟩
    · exact Units.ext (hxmat.trans hg.symm)
  have hT_le : unitTransvGroup σ.toRingHom (Unitary.antidiag r) v ≤
      K.map (Unitary.SU σ r).subtype := by
    rw [unitTransvGroup]
    exact Subgroup.closure_le _ |>.mpr hgen
  have hK_eq : K = (unitTransvGroup σ.toRingHom (Unitary.antidiag r) v).comap
      (Unitary.SU σ r).subtype := by
    apply le_antisymm
    · refine Subgroup.closure_le _ |>.mpr ?_
      rintro z ⟨c, hc, hz⟩
      exact Subgroup.mem_comap.mpr (Subgroup.subset_closure ⟨c, hc, hz⟩)
    · intro z hz
      rw [Subgroup.mem_comap] at hz
      have hz' : z ∈ (K.map (Unitary.SU σ r).subtype).comap (Unitary.SU σ r).subtype :=
        Subgroup.mem_comap.mpr (hT_le hz)
      rwa [Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq] at hz'
  have hK_le : K ≤ ((unitTransvGroup σ.toRingHom (Unitary.antidiag n)
      (Matrix.mulVec U v)).comap (Unitary.SU σ n).subtype).comap ι := by
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro z ⟨c, hc, hz⟩
    exact Subgroup.mem_comap.mpr (Subgroup.mem_comap.mpr (Subgroup.subset_closure ⟨c, hc,
      bmSDU_transv_std_image σ hUL hLU hadj hA ι hιform hz z.2⟩))
  have hK_image_le : K.map ι ≤
      (unitTransvGroup σ.toRingHom (Unitary.antidiag n) (Matrix.mulVec U v)).comap
        (Unitary.SU σ n).subtype :=
    Subgroup.map_le_iff_le_comap.mpr hK_le
  have hgen_n : {g : GL (Fin n) F | ∃ c, σ c = c ∧
      (g : Matrix (Fin n) (Fin n) F) = 1 + c • Matrix.vecMulVec (Matrix.mulVec U v)
        (Matrix.vecMul (fun i => σ (Matrix.mulVec U v i)) (Unitary.antidiag n))} ⊆
      (K.map ι).map (Unitary.SU σ n).subtype := by
    rintro g ⟨c, hc, hg⟩
    obtain ⟨xunit, hxmat, hxSU, -⟩ := bmSDU_transv_std_su σ hr c hc hv
    refine Subgroup.mem_map.mpr ⟨ι ⟨xunit, hxSU⟩, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨⟨xunit, hxSU⟩, Subgroup.subset_closure ⟨c, hc, hxmat⟩, rfl⟩
    · exact Units.ext ((bmSDU_transv_std_image σ hUL hLU hadj hA ι hιform hxmat
        hxSU).trans hg.symm)
  have hTn_le : unitTransvGroup σ.toRingHom (Unitary.antidiag n) (Matrix.mulVec U v) ≤
      (K.map ι).map (Unitary.SU σ n).subtype := by
    rw [unitTransvGroup]
    exact Subgroup.closure_le _ |>.mpr hgen_n
  have hTn_comap_le : (unitTransvGroup σ.toRingHom (Unitary.antidiag n) (Matrix.mulVec U v)).comap
      (Unitary.SU σ n).subtype ≤ K.map ι := by
    intro y hy
    rw [Subgroup.mem_comap] at hy
    have hy' : y ∈ ((K.map ι).map (Unitary.SU σ n).subtype).comap
        (Unitary.SU σ n).subtype := Subgroup.mem_comap.mpr (hTn_le hy)
    rwa [Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq] at hy'
  rw [← hK_eq]
  exact le_antisymm hK_image_le hTn_comap_le

private lemma bmSDU_transv_su_range {F : Type} [Field F] [CharP F 2] {n r : ℕ} (σ : F ≃+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e) (hLU : L * U = 1)
    (hadj : Matrix.transpose (e.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    (hr : 2 ≤ r) (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    (v : Fin r → F)
    (hv : v = Pi.single (⟨0, by omega⟩ : Fin r) (1 : F) ∨
      v = Pi.single (Fin.rev (⟨0, by omega⟩ : Fin r)) (1 : F)) :
    unitTransvGroup σ.toRingHom (Unitary.antidiag n) (Matrix.mulVec U v) ≤
      (Unitary.SU σ n).subtype.range := by
  rw [unitTransvGroup]
  refine Subgroup.closure_le _ |>.mpr ?_
  rintro g ⟨c, hc, hg⟩
  obtain ⟨xunit, hxmat, hxSU, -⟩ := bmSDU_transv_std_su σ hr c hc hv
  have hgι : g = (ι ⟨xunit, hxSU⟩ : GL (Fin n) F) :=
    Units.ext (hg.trans (bmSDU_transv_std_image σ hUL hLU hadj hA ι hιform hxmat
      hxSU).symm)
  rw [Subgroup.range_subtype]
  rw [hgι]
  exact (ι ⟨xunit, hxSU⟩).2

private lemma bmSDU_blockHom_transport {F : Type} [Field F] [CharP F 2] {n r : ℕ} (σ : F ≃+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e)
    (hLU : L * U = 1)
    (hadj : Matrix.transpose (e.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    (hr : 2 ≤ r)
    (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e)) :
    (((unitTransvGroup σ.toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by omega⟩ : Fin r) 1)).comap
        (Unitary.SU σ r).subtype).map ι).map (Unitary.SU σ n).subtype =
      unitTransvGroup σ.toRingHom (Unitary.antidiag n)
        (Matrix.mulVec U (Pi.single (⟨0, by omega⟩ : Fin r) 1)) ∧
    (((unitTransvGroup σ.toRingHom (Unitary.antidiag r)
        (Pi.single (Fin.rev (⟨0, by omega⟩ : Fin r)) 1)).comap
        (Unitary.SU σ r).subtype).map ι).map (Unitary.SU σ n).subtype =
      unitTransvGroup σ.toRingHom (Unitary.antidiag n)
        (Matrix.mulVec U (Pi.single (Fin.rev (⟨0, by omega⟩ : Fin r)) 1)) := by
  constructor
  · rw [bmSDU_transv_group_eq σ hUL hLU hadj hA hr ι hιform
        (Pi.single (⟨0, by omega⟩ : Fin r) 1) (Or.inl rfl),
      Subgroup.map_comap_eq_self (bmSDU_transv_su_range σ hUL hLU hadj hA hr ι hιform
        (Pi.single (⟨0, by omega⟩ : Fin r) 1) (Or.inl rfl))]
  · rw [bmSDU_transv_group_eq σ hUL hLU hadj hA hr ι hιform
        (Pi.single (Fin.rev (⟨0, by omega⟩ : Fin r)) 1) (Or.inr rfl),
      Subgroup.map_comap_eq_self (bmSDU_transv_su_range σ hUL hLU hadj hA hr ι hιform
        (Pi.single (Fin.rev (⟨0, by omega⟩ : Fin r)) 1) (Or.inr rfl))]

private lemma bmSDU_map_dotProduct {F : Type} [Field F] {ι : Type} [Fintype ι] (σ : F →+* F)
    (x y : ι → F) :
    σ (x ⬝ᵥ y) = (fun i => σ (x i)) ⬝ᵥ (fun i => σ (y i)) := by
  simp only [dotProduct]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_mul])

private lemma bmSDU_vecMul_Utranspose_apply {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F)
    (U : Matrix (Fin n) (Fin r) F) (v : Fin r → F) (i : Fin n) :
    Matrix.vecMul (fun i => σ (v i)) (Matrix.transpose (U.map σ.toRingHom)) i =
      σ (Matrix.mulVec U v i) := by
  simp only [Matrix.vecMul, Matrix.mulVec, Matrix.transpose_apply, Matrix.map_apply]
  rw [show σ ((fun j => U i j) ⬝ᵥ v) = (fun j => σ (U i j)) ⬝ᵥ (fun j => σ (v j)) from
    bmSDU_map_dotProduct σ.toRingHom _ _]
  rw [dotProduct_comm]
  rfl

private lemma bmSDU_vecMul_Utranspose {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F)
    (U : Matrix (Fin n) (Fin r) F) (v : Fin r → F) :
    Matrix.vecMul (fun i => σ (v i)) (Matrix.transpose (U.map σ.toRingHom)) =
      fun i => σ (Matrix.mulVec U v i) := by
  funext i
  exact bmSDU_vecMul_Utranspose_apply σ U v i

private lemma bmSDU_vecMul_Ar_L {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    (v : Fin r → F) :
    Matrix.vecMul (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r)) L =
      Matrix.vecMul (fun i => σ ((Matrix.mulVec U v) i)) (Unitary.antidiag n * e) := by
  rw [← hA]
  rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
  rw [bmSDU_vecMul_Utranspose]
  rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hUL]

private lemma bmSDU_mul_vecMulVec_U {F : Type} [Field F] {n r : ℕ} (U : Matrix (Fin n) (Fin r) F)
    (v : Fin r → F) (w : Fin r → F) :
    U * Matrix.vecMulVec v w = Matrix.vecMulVec (Matrix.mulVec U v) w := by
  rw [Matrix.mul_vecMulVec]

private lemma bmSDU_vecMulVec_mul_L {F : Type} [Field F] {n r : ℕ} (L : Matrix (Fin r) (Fin n) F)
    (a : Fin n → F) (b : Fin r → F) :
    Matrix.vecMulVec a b * L = Matrix.vecMulVec a (Matrix.vecMul b L) := by
  rw [Matrix.vecMulVec_mul]

private lemma bmSDU_vecMulVec_covec {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    (v : Fin r → F) :
    Matrix.vecMulVec (Matrix.mulVec U v)
        (Matrix.vecMul (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r)) L) =
      Matrix.vecMulVec (Matrix.mulVec U v)
        (Matrix.vecMul (fun i => σ (Matrix.mulVec U v i)) (Unitary.antidiag n * e)) := by
  rw [bmSDU_vecMul_Ar_L σ hUL hA v]

private lemma bmSDU_transv_generator_matrix {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    (v : Fin r → F) :
    U * Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r)) * L =
      Matrix.vecMulVec (Matrix.mulVec U v)
        (Matrix.vecMul (fun i => σ ((Matrix.mulVec U v) i)) (Unitary.antidiag n * e)) := by
  rw [bmSDU_mul_vecMulVec_U, bmSDU_vecMulVec_mul_L,
    bmSDU_vecMulVec_covec σ hUL hA v]

private lemma bmSDU_transv_generator_mul {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F) {U : Matrix
    (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F}
    (v : Fin r → F) (c : F) :
    U * (1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r))) * L = U
        * L + c • (U * Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r)) *
            L) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_smul, Matrix.smul_mul]

private lemma bmSDU_transv_generator_expand {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    (v : Fin r → F) (c : F) :
    U * (1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r))) * L +
        (1 - e) = 1 + c • Matrix.vecMulVec (Matrix.mulVec U v)
        (Matrix.vecMul (fun i => σ ((Matrix.mulVec U v) i)) (Unitary.antidiag n * e)) := by
  rw [bmSDU_transv_generator_mul σ v c,
    bmSDU_transv_generator_matrix σ hUL hA v, hUL]
  abel

private lemma bmSDU_transv_generator_mem {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F)) (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    (v : Fin r → F)
    (g : ↥(Unitary.SU σ r)) (c : F)
    (hg : (g : GL (Fin r) F) =
      1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r))) :
    ((Unitary.SU σ n).subtype (ι g) : Matrix (Fin n) (Fin n) F) =
      1 + c • Matrix.vecMulVec (Matrix.mulVec U v)
        (Matrix.vecMul (fun i => σ ((Matrix.mulVec U v) i)) (Unitary.antidiag n * e)) := by
  rw [show ((Unitary.SU σ n).subtype (ι g) : Matrix (Fin n) (Fin n) F) =
      U * ((g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e) from hιform g, hg,
    bmSDU_transv_generator_expand σ hUL hA v c]

private lemma bmSDU_transv_group_eq_iso_le_comap_gen {F : Type} [Field F] {n r : ℕ} (σ :
    F ≃+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F)) (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    (v : Fin r → F)
    (g : ↥(Unitary.SU σ r)) (c : F) (hc : σ c = c)
    (hg : (g : GL (Fin r) F) = 1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i))
        (Unitary.antidiag r))) :
      (Unitary.SU σ n).subtype (ι g) ∈
        unitTransvGroup σ.toRingHom (Unitary.antidiag n * e) (Matrix.mulVec U v) := by
  rw [unitTransvGroup]
  exact Subgroup.subset_closure ⟨c, hc,
    bmSDU_transv_generator_mem σ hUL hA ι hιform v g c hg⟩

private lemma bmSDU_transv_group_eq_iso_le_comap_one {F : Type} [Field F] {n r : ℕ} (σ :
    F ≃+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F} (ι : ↥(Unitary.SU σ r) →*
        ↥(Unitary.SU σ n))
    (v : Fin r → F) :
      (Unitary.SU σ n).subtype (ι 1) ∈ unitTransvGroup σ.toRingHom (Unitary.antidiag n * e)
          (Matrix.mulVec U v) := by
  rw [map_one, map_one]
  exact Subgroup.one_mem _

private lemma bmSDU_transv_group_eq_iso_le_comap_mul {F : Type} [Field F] {n r : ℕ} (σ :
    F ≃+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F} (ι : ↥(Unitary.SU σ r) →*
        ↥(Unitary.SU σ n))
    (v : Fin r → F)
    (x y : ↥(Unitary.SU σ r))
    (hx : (Unitary.SU σ n).subtype (ι x) ∈ unitTransvGroup σ.toRingHom (Unitary.antidiag n * e)
        (Matrix.mulVec U v))
    (hy : (Unitary.SU σ n).subtype (ι y) ∈ unitTransvGroup σ.toRingHom (Unitary.antidiag n * e)
        (Matrix.mulVec U v)) :
      (Unitary.SU σ n).subtype (ι (x * y)) ∈ unitTransvGroup σ.toRingHom (Unitary.antidiag n * e)
          (Matrix.mulVec U v) := by
  rw [map_mul, map_mul]
  exact Subgroup.mul_mem _ hx hy

private lemma bmSDU_transv_aux_iso_map
{F : Type} [Field F] {r : ℕ} (σ : F ≃+* F)
    (c : F) (hc : σ c = c) {v : Fin r → F}
    :
    (1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r))).map σ = 1 +
        c • (Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r))).map σ := by
  ext i j
  by_cases h : i = j <;>
    simp [h, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
        hc]

private lemma bmSDU_transv_aux_iso_transpose
{F : Type} [Field F] {r : ℕ} (σ : F ≃+* F)
    (c : F) {v : Fin r → F}
    :
    Matrix.transpose (1 + c • (Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i))
        (Unitary.antidiag r))).map σ) =
      1 + c • Matrix.transpose ((Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i))
          (Unitary.antidiag r))).map σ) := by
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul]

private lemma bmSDU_transv_aux_iso_collect_tA
{F : Type} [Field F] {r : ℕ} (σ : F ≃+* F) (hσ2 : ∀ x, σ (σ x) = x) {v : Fin r → F}
    :
    Matrix.transpose ((Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag
        r))).map σ) * (Unitary.antidiag r) = Matrix.vecMulVec (Matrix.mulVec (Unitary.antidiag r) v)
            (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r)) := by
  set A : Matrix (Fin r) (Fin r) F := Unitary.antidiag r
  set w : Fin r → F := Matrix.vecMul (fun i => σ (v i)) A
  have hKmap : (Matrix.vecMulVec v w).map σ =
      Matrix.vecMulVec (fun i => σ (v i)) (fun i => σ (w i)) := by
    ext i j
    simp [Matrix.map_apply, Matrix.vecMulVec_apply, map_mul]
  have hσw : (fun i => σ (w i)) = Matrix.mulVec A v := by
    funext i
    have hwA : w = Matrix.mulVec A (fun j => σ (v j)) := bmSDU_anti_vecMul (fun j => σ (v j))
    have h1 : σ (w i) = Matrix.mulVec (A.map σ.toRingHom) (σ.toRingHom ∘ fun j => σ (v j)) i := by
      rw [show w i = Matrix.mulVec A (fun j => σ (v j)) i from congrFun hwA i]
      exact RingHom.map_mulVec σ.toRingHom A (fun j => σ (v j)) i
    rw [h1, show A.map σ.toRingHom = A from bmSDU_anti_map σ.toRingHom r,
      show (σ.toRingHom ∘ fun j => σ (v j)) = v from funext fun j => hσ2 (v j)]
  calc
    Matrix.transpose ((Matrix.vecMulVec v w).map σ) * A
        = Matrix.transpose (Matrix.vecMulVec (fun i => σ (v i)) (fun i => σ (w i))) * A := by
          rw [hKmap]
    _ = Matrix.vecMulVec (fun i => σ (w i)) (fun i => σ (v i)) * A := by
          rw [Matrix.transpose_vecMulVec]
    _ = Matrix.vecMulVec (fun i => σ (w i)) (Matrix.vecMul (fun i => σ (v i)) A) := by
          rw [Matrix.vecMulVec_mul]
    _ = Matrix.vecMulVec (fun i => σ (w i)) w := rfl
    _ = Matrix.vecMulVec (Matrix.mulVec A v) w := by rw [hσw]

private lemma bmSDU_transv_aux_iso_collect_AK
{F : Type} [Field F] {r : ℕ} (σ : F ≃+* F) {v : Fin r → F}
    :
    (Unitary.antidiag r) * Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag
        r)) = Matrix.vecMulVec (Matrix.mulVec (Unitary.antidiag r) v) (Matrix.vecMul (fun i => σ (v
            i)) (Unitary.antidiag r)) := by
  exact Matrix.mul_vecMulVec (Unitary.antidiag r) v (Matrix.vecMul (fun i => σ (v i))
      (Unitary.antidiag r))

private lemma bmSDU_transv_aux_iso_collect_tAK
{F : Type} [Field F] {r : ℕ} (σ : F ≃+* F) {v : Fin r → F}
    (hIso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0)
    :
    Matrix.vecMulVec (Matrix.mulVec (Unitary.antidiag r) v) (Matrix.vecMul (fun i => σ (v i))
        (Unitary.antidiag r)) * Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i))
            (Unitary.antidiag r)) = 0 := by
  rw [Matrix.vecMulVec_mul_vecMulVec, hIso, zero_smul, Matrix.vecMulVec_zero]

private lemma bmSDU_transv_aux_iso_collect
{F : Type} [Field F] [CharP F 2] {r : ℕ} (σ : F ≃+* F) (hσ2 : ∀ x, σ (σ x) = x)
    (c : F) {v : Fin r → F}
    (hIso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0)
    :
    (1 + c • Matrix.transpose ((Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i))
        (Unitary.antidiag r))).map σ)) * (Unitary.antidiag r) * (1 + c • Matrix.vecMulVec v
            (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r))) =
      (Unitary.antidiag r) := by
  have hX : Matrix.transpose ((Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i))
      (Unitary.antidiag r))).map σ) * (Unitary.antidiag r) = Matrix.vecMulVec (Matrix.mulVec
          (Unitary.antidiag r) v) (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r)) :=
              bmSDU_transv_aux_iso_collect_tA σ hσ2
  have hY : (Unitary.antidiag r) * Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i))
      (Unitary.antidiag r)) = Matrix.vecMulVec (Matrix.mulVec (Unitary.antidiag r) v) (Matrix.vecMul
          (fun i => σ (v i)) (Unitary.antidiag r)) := bmSDU_transv_aux_iso_collect_AK σ
  have hZ : Matrix.vecMulVec (Matrix.mulVec (Unitary.antidiag r) v) (Matrix.vecMul (fun i => σ (v
      i)) (Unitary.antidiag r)) * Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i))
          (Unitary.antidiag r)) = 0 := bmSDU_transv_aux_iso_collect_tAK σ hIso
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_one,
    Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul, smul_add, smul_smul, hX, hY, hZ, smul_zero]
  rw [add_zero]
  rw [show (Unitary.antidiag r) + c • Matrix.vecMulVec (Matrix.mulVec (Unitary.antidiag r) v)
      (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r)) + c • Matrix.vecMulVec (Matrix.mulVec
          (Unitary.antidiag r) v) (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r)) =
              (Unitary.antidiag r) + (c • Matrix.vecMulVec (Matrix.mulVec (Unitary.antidiag r) v)
                  (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r)) + c • Matrix.vecMulVec
                      (Matrix.mulVec (Unitary.antidiag r) v) (Matrix.vecMul (fun i => σ (v i))
                          (Unitary.antidiag r))) by abel]
  rw [show c • Matrix.vecMulVec (Matrix.mulVec (Unitary.antidiag r) v) (Matrix.vecMul (fun i => σ (v
      i)) (Unitary.antidiag r)) + c • Matrix.vecMulVec (Matrix.mulVec (Unitary.antidiag r) v)
          (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r)) = 0 by rw [← add_smul,
              CharTwo.add_self_eq_zero c, zero_smul]]
  rw [add_zero]

private lemma bmSDU_transv_aux_iso
{F : Type} [Field F] [CharP F 2] {r : ℕ} (σ : F ≃+* F) (hσ2 : ∀ x, σ (σ x) = x)
    (c : F) (hc : σ c = c) {v : Fin r → F}
    (hIso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0)
    :
    Matrix.transpose ((1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i))
        (Unitary.antidiag r))).map σ) * (Unitary.antidiag r) * (1 + c • Matrix.vecMulVec v
            (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r))) =
      (Unitary.antidiag r) := by
  rw [bmSDU_transv_aux_iso_map σ c hc, bmSDU_transv_aux_iso_transpose σ c,
    bmSDU_transv_aux_iso_collect σ hσ2 c hIso]

private lemma bmSDU_transv_aux_det
{F : Type} [Field F] {r : ℕ} (σ : F ≃+* F)
    (c : F) {v : Fin r → F}
    (hIso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0)
    :
    (1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r))).det = 1 :=
        by
  let A : Matrix (Fin r) (Fin r) F := Unitary.antidiag r
  let w : Fin r → F := Matrix.vecMul (fun i => σ (v i)) A
  let E : Matrix (Fin r) (Fin r) F := Matrix.vecMulVec v w
  have hEeq : E = Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r)) := rfl
  have hwv : w ⬝ᵥ v = 0 := hIso
  let ucol : Matrix (Fin r) (Fin 1) F := Matrix.of (fun i _ => v i)
  let wrow : Matrix (Fin 1) (Fin r) F := Matrix.of (fun _ j => w j)
  have hfac : ucol * wrow = E := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_one]
    simp [ucol, wrow, E, Matrix.vecMulVec_apply]
  have hzero : wrow * ucol = 0 := by
    ext i j
    simp only [ucol, wrow, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    simpa only [dotProduct] using hwv
  rw [← hEeq]
  rw [show (1 + c • E) = 1 + (c • ucol) * wrow by rw [Matrix.smul_mul, hfac]]
  rw [Matrix.det_one_add_mul_comm, Matrix.mul_smul, hzero, smul_zero, add_zero, Matrix.det_one]

private lemma bmSDU_transv_aux {F : Type} [Field F] [CharP F 2] {r : ℕ} (σ : F ≃+* F)
    (hσ2 : ∀ x, σ (σ x) = x)
    (c : F) (hc : σ c = c) {v : Fin r → F}
    (hIso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0) :
    ∃ xunit : GL (Fin r) F,
      (xunit : Matrix (Fin r) (Fin r) F) = 1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v
          i)) (Unitary.antidiag r)) ∧
      xunit ∈ Unitary.SU σ r ∧
      xunit ∈ unitTransvGroup σ.toRingHom (Unitary.antidiag r) v := by
  let A : Matrix (Fin r) (Fin r) F := Unitary.antidiag r
  let E : Matrix (Fin r) (Fin r) F := Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) A)
  have hEeq : E = Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r)) := rfl
  have hEE : E * E = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hIso, zero_smul, Matrix.vecMulVec_zero]
  have hcc : (c • E) * (c • E) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hEE, smul_zero]
  have h1 : (1 + c • E) * (1 - c • E) = 1 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul, hEE, smul_zero]
    abel
  have h2 : (1 - c • E) * (1 + c • E) = 1 := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul, hEE, smul_zero]
    abel
  let xunit : GL (Fin r) F := ⟨1 + c • E, 1 - c • E, h1, h2⟩
  have hxval : (xunit : Matrix (Fin r) (Fin r) F) = 1 + c • E := rfl
  refine ⟨xunit, ?_, ?_, ?_⟩
  · rw [hxval, hEeq]
  · rw [Unitary.mem_SU]
    exact ⟨by rw [hxval, hEeq]; exact bmSDU_transv_aux_det σ c hIso,
      by rw [hxval, hEeq]; simpa only [Unitary.conjTr] using bmSDU_transv_aux_iso σ hσ2 c hc hIso⟩
  · refine Subgroup.subset_closure ⟨c, hc, ?_⟩
    rw [hxval, hEeq]
    rfl

private lemma bmSDU_transv_gen_mem_su {F : Type} [Field F] [CharP F 2] {r : ℕ} (σ : F ≃+* F)
    (hσ2 : ∀ x, σ (σ x) = x)
    (v : Fin r → F)
    (hIso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0)
    (c : F) (hc : σ c = c) (g : GL (Fin r) F)
    (hg : (g : Matrix (Fin r) (Fin r) F) = 1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v
        i)) (Unitary.antidiag r))) :
    g ∈ (Unitary.SU σ r).subtype.range := by
  obtain ⟨xunit, hxmat, hxSU, -⟩ := bmSDU_transv_aux σ hσ2 c hc hIso
  refine ⟨⟨xunit, hxSU⟩, ?_⟩
  exact Units.ext (hxmat.trans hg.symm)

private lemma bmSDU_transv_mem_su_range {F : Type} [Field F] [CharP F 2] {r : ℕ} (σ : F ≃+* F)
    (hσ2 : ∀ x, σ (σ x) = x)
    (v : Fin r → F)
    (hIso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0) :
    unitTransvGroup σ.toRingHom (Unitary.antidiag r) v ≤
      (Unitary.SU σ r).subtype.range := by
  rw [unitTransvGroup]
  refine Subgroup.closure_le _ |>.mpr ?_
  rintro g ⟨c, hc, hgV⟩
  exact bmSDU_transv_gen_mem_su σ hσ2 v hIso c hc g hgV

private lemma bmSDU_transv_group_eq_iso_le_comap_pre_mem {F : Type} [Field F] {n r : ℕ}
    (σ : F ≃+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F)) (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    (v : Fin r → F) :
    ∀ (y : GL (Fin r) F), y ∈ {g : GL (Fin r) F | ∃ c, σ c = c ∧ (g : Matrix (Fin r) (Fin r) F) = 1
        + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r))} →
    ∀ (g : ↥(Unitary.SU σ r)), (Unitary.SU σ r).subtype g = y → (Unitary.SU σ n).subtype (ι g) ∈
        unitTransvGroup σ.toRingHom (Unitary.antidiag n * e) (Matrix.mulVec U v) := by
  intro y hy g hg
  obtain ⟨c, hc, hyV⟩ := hy
  exact bmSDU_transv_group_eq_iso_le_comap_gen σ hUL hA ι hιform v g c hc
    (by rw [show (g : GL (Fin r) F) = y from hg, hyV])

private lemma bmSDU_transv_group_eq_iso_le_comap_pre_one {F : Type} [Field F] {n r : ℕ}
    (σ : F ≃+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F} (ι : ↥(Unitary.SU σ r) →*
        ↥(Unitary.SU σ n))
    (v : Fin r → F) :
    ∀ (g : ↥(Unitary.SU σ r)), (Unitary.SU σ r).subtype g = 1 → (Unitary.SU σ n).subtype (ι g) ∈
        unitTransvGroup σ.toRingHom (Unitary.antidiag n * e) (Matrix.mulVec U v) := by
  intro g hg
  have hg1 : g = 1 := Subtype.ext hg
  rw [hg1]
  exact bmSDU_transv_group_eq_iso_le_comap_one σ ι v

private lemma bmSDU_transv_group_eq_iso_le_comap_pre_mul {F : Type} [Field F] [CharP F 2] {n r : ℕ}
    (σ : F ≃+* F)
    (hσ2 : ∀ x, σ (σ x) = x)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F} (ι : ↥(Unitary.SU σ r) →*
        ↥(Unitary.SU σ n))
    (v : Fin r → F)
    (hIso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0) :
    ∀ (y z : GL (Fin r) F), y ∈ Subgroup.closure {g : GL (Fin r) F | ∃ c, σ c = c ∧ (g : Matrix (Fin
        r) (Fin r) F) = 1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i))
            (Unitary.antidiag r))} → z ∈ Subgroup.closure {g : GL (Fin r) F | ∃ c, σ c = c ∧ (g :
                Matrix (Fin r) (Fin r) F) = 1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v
                    i)) (Unitary.antidiag r))} →
    (∀ (g : ↥(Unitary.SU σ r)), (Unitary.SU σ r).subtype g = y → (Unitary.SU σ n).subtype (ι g) ∈
        unitTransvGroup σ.toRingHom (Unitary.antidiag n * e) (Matrix.mulVec U v)) →
    (∀ (g : ↥(Unitary.SU σ r)), (Unitary.SU σ r).subtype g = z → (Unitary.SU σ n).subtype (ι g) ∈
        unitTransvGroup σ.toRingHom (Unitary.antidiag n * e) (Matrix.mulVec U v)) →
    ∀ (g : ↥(Unitary.SU σ r)), (Unitary.SU σ r).subtype g = y * z → (Unitary.SU σ n).subtype (ι g) ∈
        unitTransvGroup σ.toRingHom (Unitary.antidiag n * e) (Matrix.mulVec U v) := by
  intro y z hy hz ihy ihz g hg
  obtain ⟨gx, hgx⟩ := (bmSDU_transv_mem_su_range σ hσ2 v hIso) hy
  obtain ⟨gy, hgy⟩ := (bmSDU_transv_mem_su_range σ hσ2 v hIso) hz
  have hgg : g = gx * gy := Subtype.ext (by
    rw [Subgroup.coe_mul,
      show (g : GL (Fin r) F) = y * z from hg,
      ← show (gx : GL (Fin r) F) = y from hgx,
      ← show (gy : GL (Fin r) F) = z from hgy])
  rw [hgg]
  exact bmSDU_transv_group_eq_iso_le_comap_mul σ ι v gx gy (ihy gx hgx) (ihz gy hgy)

private lemma bmSDU_transv_group_eq_iso_le_comap_pre_inv {F : Type} [Field F] {n r : ℕ}
    (σ : F ≃+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F} (ι : ↥(Unitary.SU σ r) →*
        ↥(Unitary.SU σ n))
    (v : Fin r → F) :
    ∀ (y : GL (Fin r) F), y ∈ Subgroup.closure {g : GL (Fin r) F | ∃ c, σ c = c ∧ (g : Matrix (Fin
        r) (Fin r) F) = 1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i))
            (Unitary.antidiag r))} →
    (∀ (g : ↥(Unitary.SU σ r)), (Unitary.SU σ r).subtype g = y → (Unitary.SU σ n).subtype (ι g) ∈
        unitTransvGroup σ.toRingHom (Unitary.antidiag n * e) (Matrix.mulVec U v)) →
    ∀ (g : ↥(Unitary.SU σ r)), (Unitary.SU σ r).subtype g = y⁻¹ → (Unitary.SU σ n).subtype (ι g) ∈
        unitTransvGroup σ.toRingHom (Unitary.antidiag n * e) (Matrix.mulVec U v) := by
  intro y hy ih g hg
  have hg' : (Unitary.SU σ r).subtype g⁻¹ = y := by
    rw [map_inv, hg, inv_inv]
  have hih := ih g⁻¹ hg'
  have hmap : (Unitary.SU σ n).subtype (ι g⁻¹) = ((Unitary.SU σ n).subtype (ι g))⁻¹ := by
    rw [map_inv, map_inv]
  rw [hmap] at hih
  simpa using Subgroup.inv_mem _ hih

private lemma bmSDU_transv_group_eq_iso_le_comap_closure_pre {F : Type} [Field F] [CharP F 2] {n r :
    ℕ} (σ : F ≃+* F)
    (hσ2 : ∀ x, σ (σ x) = x)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F)) (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    (v : Fin r → F)
    (hIso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0)
    (x : GL (Fin r) F) (hx : x ∈ unitTransvGroup σ.toRingHom (Unitary.antidiag r) v) :
    ∀ (g : ↥(Unitary.SU σ r)), (Unitary.SU σ r).subtype g = x →
      (Unitary.SU σ n).subtype (ι g) ∈ unitTransvGroup σ.toRingHom (Unitary.antidiag n * e)
          (Matrix.mulVec U v) := by
  rw [unitTransvGroup] at hx
  exact Subgroup.closure_induction
    (bmSDU_transv_group_eq_iso_le_comap_pre_mem σ hUL hA ι hιform v)
    (bmSDU_transv_group_eq_iso_le_comap_pre_one σ ι v)
    (bmSDU_transv_group_eq_iso_le_comap_pre_mul σ hσ2 ι v hIso)
    (bmSDU_transv_group_eq_iso_le_comap_pre_inv σ ι v) hx

private lemma bmSDU_transv_group_eq_iso_le_comap_closure {F : Type} [Field F] [CharP F 2] {n r : ℕ}
    (σ : F ≃+* F)
    (hσ2 : ∀ x, σ (σ x) = x)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F)) (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    (v : Fin r → F)
    (hIso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0)
    (g : ↥(Unitary.SU σ r))
    (hg : (Unitary.SU σ r).subtype g ∈ unitTransvGroup σ.toRingHom (Unitary.antidiag r) v) :
      (Unitary.SU σ n).subtype (ι g) ∈ unitTransvGroup σ.toRingHom (Unitary.antidiag n * e)
          (Matrix.mulVec U v) := by
  exact bmSDU_transv_group_eq_iso_le_comap_closure_pre σ hσ2 hUL hA ι hιform v hIso
    ((Unitary.SU σ r).subtype g) hg g rfl

private lemma bmSDU_transv_group_eq_iso_le_comap {F : Type} [Field F] [CharP F 2] {n r : ℕ} (σ : F
    ≃+* F)
    (hσ2 : ∀ x, σ (σ x) = x)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F)) (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    (v : Fin r → F)
    (hIso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0) :
    (unitTransvGroup σ.toRingHom (Unitary.antidiag r) v).comap
        (Unitary.SU σ r).subtype ≤
      ((unitTransvGroup σ.toRingHom (Unitary.antidiag n * e) (Matrix.mulVec U v)).comap
        (Unitary.SU σ n).subtype).comap ι := by
  intro g hg
  exact bmSDU_transv_group_eq_iso_le_comap_closure σ hσ2 hUL hA ι hιform v hIso g hg

private lemma bmSDU_transv_group_eq_iso_le {F : Type} [Field F] [CharP F 2] {n r : ℕ} (σ : F ≃+* F)
    (hσ2 : ∀ x, σ (σ x) = x)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F)) (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    (v : Fin r → F)
    (hIso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0) :
    (((unitTransvGroup σ.toRingHom (Unitary.antidiag r) v).comap
        (Unitary.SU σ r).subtype).map ι) ≤
      (unitTransvGroup σ.toRingHom (Unitary.antidiag n * e) (Matrix.mulVec U v)).comap
        (Unitary.SU σ n).subtype := by
  exact (Subgroup.map_le_iff_le_comap).mpr
    (bmSDU_transv_group_eq_iso_le_comap σ hσ2 hUL hA ι hιform v hIso)

private lemma bmSDU_transv_group_eq_iso_ge_gen {F : Type} [Field F] [CharP F 2] {n r : ℕ} (σ : F ≃+*
    F)
    (hσ2 : ∀ x, σ (σ x) = x)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F)) (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    (v : Fin r → F)
    (hIso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0)
    (c : F) (hc : σ c = c) (T : GL (Fin n) F)
    (hT : (T : Matrix (Fin n) (Fin n) F) =
      1 + c • Matrix.vecMulVec (Matrix.mulVec U v)
        (Matrix.vecMul (fun i => σ ((Matrix.mulVec U v) i)) (Unitary.antidiag n * e))) :
    T ∈ (((unitTransvGroup σ.toRingHom (Unitary.antidiag r) v).comap
        (Unitary.SU σ r).subtype).map ι).map (Unitary.SU σ n).subtype := by
  obtain ⟨xunit, hxmat, hxSU, hxT⟩ := bmSDU_transv_aux σ hσ2 c hc hIso
  refine Subgroup.mem_map.mpr ⟨ι ⟨xunit, hxSU⟩, ?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨⟨xunit, hxSU⟩, hxT, rfl⟩
  · apply Units.ext
    change ((ι ⟨xunit, hxSU⟩ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = (T : Matrix (Fin n) (Fin
        n) F)
    rw [hιform ⟨xunit, hxSU⟩, hxmat, hT]
    exact bmSDU_transv_generator_expand σ hUL hA v c

private lemma bmSDU_transv_group_eq_iso_ge {F : Type} [Field F] [CharP F 2] {n r : ℕ} (σ : F ≃+* F)
    (hσ2 : ∀ x, σ (σ x) = x)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F)) (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    (v : Fin r → F)
    (hIso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0) :
    (unitTransvGroup σ.toRingHom (Unitary.antidiag n * e) (Matrix.mulVec U v)).comap
        (Unitary.SU σ n).subtype ≤
      (((unitTransvGroup σ.toRingHom (Unitary.antidiag r) v).comap
        (Unitary.SU σ r).subtype).map ι) := by
  have hTn : unitTransvGroup σ.toRingHom (Unitary.antidiag n * e) (Matrix.mulVec U v) ≤
      (((unitTransvGroup σ.toRingHom (Unitary.antidiag r) v).comap
        (Unitary.SU σ r).subtype).map ι).map (Unitary.SU σ n).subtype := by
    rw [unitTransvGroup]
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro T ⟨c, hc, hT⟩
    exact bmSDU_transv_group_eq_iso_ge_gen σ hσ2 hUL hA ι hιform v hIso c hc T hT
  intro g hg
  obtain ⟨r', hr', hreq⟩ := Subgroup.mem_map.mp (hTn hg)
  have hrg : r' = g := Subtype.ext hreq
  rwa [hrg] at hr'

private lemma bmSDU_transv_group_eq_iso {F : Type} [Field F] [CharP F 2] {n r : ℕ} (σ : F ≃+* F)
    (hσ2 : ∀ x, σ (σ x) = x)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F)) (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    (v : Fin r → F)
    (hIso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0) :
    ((unitTransvGroup σ.toRingHom (Unitary.antidiag r) v).comap
        (Unitary.SU σ r).subtype).map ι =
      (unitTransvGroup σ.toRingHom (Unitary.antidiag n * e) (Matrix.mulVec U v)).comap
        (Unitary.SU σ n).subtype := by
  exact le_antisymm
    (bmSDU_transv_group_eq_iso_le σ hσ2 hUL hA ι hιform v hIso)
    (bmSDU_transv_group_eq_iso_ge σ hσ2 hUL hA ι hιform v hIso)

private lemma bmSDU_transv_su_range_iso {F : Type} [Field F] [CharP F 2] {n r : ℕ} (σ : F ≃+* F)
    (hσ2 : ∀ x, σ (σ x) = x)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F)) (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    (v : Fin r → F)
    (hIso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0) :
    unitTransvGroup σ.toRingHom (Unitary.antidiag n * e) (Matrix.mulVec U v) ≤
      (Unitary.SU σ n).subtype.range := by
  rw [unitTransvGroup]
  refine Subgroup.closure_le _ |>.mpr ?_
  rintro T ⟨c, hc, hT⟩
  obtain ⟨xunit, hxmat, hxSU, hxT⟩ := bmSDU_transv_aux σ hσ2 c hc hIso
  refine ⟨ι ⟨xunit, hxSU⟩, ?_⟩
  apply Units.ext
  change ((ι ⟨xunit, hxSU⟩ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = (T : Matrix (Fin n) (Fin n)
      F)
  rw [hιform ⟨xunit, hxSU⟩, hxmat, hT]
  exact bmSDU_transv_generator_expand σ hUL hA v c

private lemma bmSDU_transv_transport {F : Type} [Field F] [CharP F 2] {n r : ℕ} (σ : F ≃+* F)
    (hσ2 : ∀ x, σ (σ x) = x)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    (u₀ : Fin r → F) (hIso : Matrix.vecMul (fun i => σ (u₀ i)) (Unitary.antidiag r) ⬝ᵥ u₀ = 0) :
    (((unitTransvGroup σ.toRingHom (Unitary.antidiag r) u₀).comap
        (Unitary.SU σ r).subtype).map ι).map (Unitary.SU σ n).subtype =
      unitTransvGroup σ.toRingHom (Unitary.antidiag n * e) (Matrix.mulVec U u₀) := by
  rw [bmSDU_transv_group_eq_iso σ hσ2 hUL hA ι hιform u₀ hIso,
    Subgroup.map_comap_eq_self (bmSDU_transv_su_range_iso σ hσ2 hUL hA ι hιform u₀
        hIso)]

theorem unitTransvGroup_map_of_unitary_block {F : Type} [Field F] [CharP F 2] {n r : ℕ}
    (σ : F ≃+* F) (hσ2 : ∀ x, σ (σ x) = x)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e) (hLU : L * U = 1)
    (hA : Matrix.transpose (U.map σ.toRingHom) *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    (hadjE : Matrix.transpose (e.map σ.toRingHom) *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e)
    (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    (v : Fin r → F)
    (hIso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0) :
    (((unitTransvGroup σ.toRingHom (Unitary.antidiag r) v).comap
        (Unitary.SU σ r).subtype).map ι).map (Unitary.SU σ n).subtype =
      unitTransvGroup σ.toRingHom (Unitary.antidiag n) (Matrix.mulVec U v) := by
  have htransport := bmSDU_transv_transport σ hσ2 hUL hA ι hιform v hIso
  have hx : Matrix.mulVec (e.map σ.toRingHom) (fun i => σ (Matrix.mulVec U v i)) =
      fun i => σ (Matrix.mulVec U v i) := by
    funext i
    have h := RingHom.map_mulVec σ.toRingHom e (Matrix.mulVec U v) i
    rw [Matrix.mulVec_mulVec, bmSDU_e_mul_U hUL hLU] at h
    exact h.symm
  have hvec : Matrix.vecMul (fun i => σ (Matrix.mulVec U v i)) (Unitary.antidiag n * e) =
      Matrix.vecMul (fun i => σ (Matrix.mulVec U v i)) (Unitary.antidiag n) := by
    have h1 : Matrix.vecMul (fun i => σ (Matrix.mulVec U v i)) (Unitary.antidiag n * e) =
        Matrix.vecMul (Matrix.vecMul (fun i => σ (Matrix.mulVec U v i))
          (Matrix.transpose (e.map σ.toRingHom))) (Unitary.antidiag n) := by
      rw [← hadjE, Matrix.vecMul_vecMul]
    rw [h1]
    have h2 : Matrix.vecMul (fun i => σ (Matrix.mulVec U v i))
        (Matrix.transpose (e.map σ.toRingHom)) =
        Matrix.mulVec (e.map σ.toRingHom) (fun i => σ (Matrix.mulVec U v i)) := by
      ext j
      simp only [Matrix.vecMul_apply, Matrix.transpose_apply, Matrix.mulVec_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [h2, hx]
  have hgroup : unitTransvGroup σ.toRingHom (Unitary.antidiag n * e) (Matrix.mulVec U v) =
      unitTransvGroup σ.toRingHom (Unitary.antidiag n) (Matrix.mulVec U v) := by
    rw [unitTransvGroup, unitTransvGroup]
    congr 1
    ext g
    simp only [Set.mem_setOf_eq]
    constructor <;> rintro ⟨c, hc, hg⟩
    · exact ⟨c, hc, by simpa [hvec] using hg⟩
    · exact ⟨c, hc, by simpa [← hvec] using hg⟩
  exact htransport.trans hgroup

private lemma bmSDU_adj_matrix_form {F : Type} [Field F] (σ : F →+* F) {n : ℕ}
    {G e : Matrix (Fin n) (Fin n) F} (hGdet : IsUnit G.det)
    (hadj : formAdj σ G e = e) :
    Matrix.transpose (e.map σ) * G = G * e := by
  have h := congrArg (fun M => G * M) hadj
  simp only [formAdj, Matrix.mul_assoc] at h
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hGdet, Matrix.one_mul] at h
  exact h

private theorem bmSDU_block_embedding_explicit
    (n g r : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hadj : formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e < 2) {U :
        Matrix (Fin n) (Fin r) (GaloisField 2 (2 * (g + 1)))}
    (hUinj : Function.Injective U.mulVec)
    (hUE : LinearMap.range U.mulVecLin = LinearMap.range e.mulVecLin)
    (hA : Matrix.transpose (U.map (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g +
        1))) 2 (g + 1)).toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2
            * (g + 1)))) * U = Unitary.antidiag r) :
    ∃ (ι : (ggU .PSU r (g + 1)).K →*
        ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g +
            1)) n))
      (L : Matrix (Fin r) (Fin n) (GaloisField 2 (2 * (g + 1)))),
      Function.Injective ι ∧
      ι.range = glBlockCentralizer
        ((Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g +
            1)) n).subtype) S e ∧
      U * L = e ∧ L * U = 1 ∧
      (∀ y : (ggU .PSU r (g + 1)).K,
        ((ι y : GL (Fin n) (GaloisField 2 (2 * (g + 1)))) : Matrix (Fin n) (Fin n) (GaloisField 2 (2
            * (g + 1)))) =
          U * (((Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1)))
              2 (g + 1)) r).subtype y) : Matrix (Fin r) (Fin r) (GaloisField 2 (2 * (g + 1)))) * L +
                  (1 - e)) := by
  let F' := GaloisField 2 (2 * (g + 1))
  let σe : F' ≃+* F' := CFSG.LieType.BorelTits.unitaryInvolution F' 2 (g + 1)
  let G : Matrix (Fin n) (Fin n) F' := Unitary.antidiag n
  let L : Matrix (Fin r) (Fin n) F' := bmSDU_L σe.toRingHom G U
  have hc : Nat.card F' = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  have hσ : ∀ x, σe (σe x) = x := CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  have hE2 : e * e = e := he.2.1.eq
  have hGdet : IsUnit G.det := isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  have hE : Matrix.transpose (e.map σe.toRingHom) * G = G * e :=
    bmSDU_adj_matrix_form σe.toRingHom hGdet hadj
  have hGunit : IsUnit (Matrix.transpose (U.map σe.toRingHom) * G * U) :=
    bmSDU_isUnit_gram σe.toRingHom hσ G e hGdet hE2 hadj hUinj hUE
  have hUL : U * L = e := bmSDU_U_mul_L σe.toRingHom G e U hE2 hE hUE hGunit
  have hLU : L * U = 1 := bmSDU_L_mul_U σe.toRingHom G U hGunit
  obtain ⟨ι, hιinj, hιform⟩ := bmSDU_blockHom σe hE2 hUL hLU hE hA
  exact ⟨ι, L, hιinj, bmSDU_blockHom_range σe S hS he hE hdeg hUL hLU hA ι hιform,
    hUL, hLU, hιform⟩

private lemma bmSDU_vecMul_dot_mulVec {F : Type} [CommSemiring F] {a b c : Type}
    [Fintype a] [Fintype b] [Fintype c]
    (x : a → F) (M : Matrix a b F) (N : Matrix b c F) (y : c → F) :
    dotProduct (Matrix.vecMul x M) (Matrix.mulVec N y) =
      dotProduct (Matrix.vecMul x (M * N)) y := by
  have h1 : Matrix.vecMul x M = Matrix.mulVec (Matrix.transpose M) x := by
    have h := bmSDU_vecMul_transpose (Matrix.transpose M) x
    rwa [Matrix.transpose_transpose] at h
  rw [h1, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.transpose_transpose]

theorem unitary_block_form_apply {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F)
    (U : Matrix (Fin n) (Fin r) F)
    (hA : Matrix.transpose (U.map σ.toRingHom) *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    (x y : Fin r → F) :
    Matrix.vecMul (fun i => σ.toRingHom (Matrix.mulVec U x i)) (Unitary.antidiag n) ⬝ᵥ
        Matrix.mulVec U y =
      Matrix.vecMul (fun i => σ.toRingHom (x i)) (Unitary.antidiag r) ⬝ᵥ y := by
  have hσU : (fun i => σ.toRingHom (Matrix.mulVec U x i)) =
      Matrix.mulVec (U.map σ.toRingHom) (fun i => σ.toRingHom (x i)) :=
    funext fun i => RingHom.map_mulVec σ.toRingHom U x i
  rw [hσU, Matrix.vecMul_mulVec, bmSDU_vecMul_dot_mulVec, hA]

private lemma bmSDU_root_pair_form (n g r : ℕ)
    (U : Matrix (Fin n) (Fin r) (GaloisField 2 (2 * (g + 1))))
    (hA : Matrix.transpose (U.map (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g +
        1))) 2 (g + 1)).toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2
            * (g + 1)))) * U = Unitary.antidiag r)
    (hr : 1 ≤ r) (hr2 : 2 ≤ r) :
    Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1)))
        2 (g + 1)).toRingHom (Matrix.mulVec U (Pi.single (⟨0, hr⟩ : Fin r) 1) i)) (Unitary.antidiag
            n) ⬝ᵥ Matrix.mulVec U (Pi.single (⟨0, hr⟩ : Fin r) 1) = 0 ∧
    Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1)))
        2 (g + 1)).toRingHom (Matrix.mulVec U (Pi.single (Fin.rev (⟨0, hr⟩ : Fin r)) 1) i))
            (Unitary.antidiag n) ⬝ᵥ Matrix.mulVec U (Pi.single (Fin.rev (⟨0, hr⟩ : Fin r)) 1) = 0 ∧
    Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1)))
        2 (g + 1)).toRingHom (Matrix.mulVec U (Pi.single (⟨0, hr⟩ : Fin r) 1) i)) (Unitary.antidiag
            n) ⬝ᵥ Matrix.mulVec U (Pi.single (Fin.rev (⟨0, hr⟩ : Fin r)) 1) = 1 := by
  have hσv : (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g
      + 1)).toRingHom ((Pi.single (⟨0, hr⟩ : Fin r) (1 : (GaloisField 2 (2 * (g + 1)))) : Fin r →
          (GaloisField 2 (2 * (g + 1)))) i)) =
      Pi.single (⟨0, hr⟩ : Fin r) (1 : (GaloisField 2 (2 * (g + 1)))) := by
    funext i
    by_cases hi : i = (⟨0, hr⟩ : Fin r)
    · rw [hi]; simp
    · simp [Pi.single_eq_of_ne hi]
  have hσw : (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g
      + 1)).toRingHom ((Pi.single (Fin.rev (⟨0, hr⟩ : Fin r)) (1 : (GaloisField 2 (2 * (g + 1)))) :
          Fin r → (GaloisField 2 (2 * (g + 1)))) i)) =
      Pi.single (Fin.rev (⟨0, hr⟩ : Fin r)) (1 : (GaloisField 2 (2 * (g + 1)))) := by
    funext i
    by_cases hi : i = Fin.rev (⟨0, hr⟩ : Fin r)
    · rw [hi]; simp
    · simp [Pi.single_eq_of_ne hi]
  refine ⟨?_, ?_, ?_⟩
  · rw [unitary_block_form_apply (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) U hA (Pi.single (⟨0, hr⟩ : Fin r) 1)
        (Pi.single (⟨0, hr⟩ : Fin r) 1), hσv, bmSDU_anti_vecMul, bmSDU_std_mulVec_first hr2]
    rw [single_dotProduct, Pi.single_apply, if_neg (bmSDU_std_rev_zero_ne hr2), mul_zero]
  · rw [unitary_block_form_apply (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) U hA (Pi.single (Fin.rev (⟨0, hr⟩ : Fin r)) 1)
        (Pi.single (Fin.rev (⟨0, hr⟩ : Fin r)) 1), hσw, bmSDU_anti_vecMul, bmSDU_std_mulVec_last
            hr2]
    rw [single_dotProduct, Pi.single_apply, if_neg (Ne.symm (bmSDU_std_rev_zero_ne hr2)), mul_zero]
  · rw [unitary_block_form_apply (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) U hA (Pi.single (⟨0, hr⟩ : Fin r) 1)
        (Pi.single (Fin.rev (⟨0, hr⟩ : Fin r)) 1), hσv, bmSDU_anti_vecMul, bmSDU_std_mulVec_first
            hr2]
    rw [single_dotProduct, Pi.single_eq_same, mul_one]

private lemma bmSDU_root_datum_transfer {F : Type} [Field F] {n r : ℕ} {σ : F ≃+* F}
    {ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n)}
    {H : Subgroup ↥(Unitary.SU σ r)} {T : Subgroup (GL (Fin r) F)}
    {G : Matrix (Fin n) (Fin n) F} {v : Fin n → F}
    (hroot : H.map (Unitary.SU σ r).subtype = T)
    (htr : ((T.comap (Unitary.SU σ r).subtype).map ι).map (Unitary.SU σ n).subtype =
      unitTransvGroup σ.toRingHom G v) :
    ((H.map ι).map (Unitary.SU σ n).subtype) = unitTransvGroup σ.toRingHom G v := by
  rw [← hroot, Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq] at htr
  exact htr

theorem exists_longRoot_pair_transport_of_unitary_block {F : Type} [Field F] [Finite F]
    [CharP F 2] {f r n : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (hn : 2 ≤ n)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e) (hLU : L * U = 1)
    (hA : Matrix.transpose (U.map
        (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom) *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    (hadjE : Matrix.transpose (e.map
        (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom) *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e)
    (ι : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) r) →*
        ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n))
    (hιform : ∀ x : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    {β : Fin (Unitary.rootDatum hc r).rank → ℤ}
    (hβ : β ∈ (Unitary.rootDatum hc r).roots)
    (hl : GGLongRoot (Unitary.rootDatum hc r) β)
    (u : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) r)) :
    ∃ γ : Fin (Unitary.rootDatum hc n).rank → ℤ,
      γ ∈ (Unitary.rootDatum hc n).roots ∧
      GGLongRoot (Unitary.rootDatum hc n) γ ∧
      ∃ a : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n),
        ((((Unitary.rootDatum hc r).rootGroup β).map (MulAut.conj u).toMonoidHom).map ι) =
          ((Unitary.rootDatum hc n).rootGroup γ).map (MulAut.conj a).toMonoidHom ∧
        ((((Unitary.rootDatum hc r).rootGroup (-β)).map (MulAut.conj u).toMonoidHom).map ι) =
          ((Unitary.rootDatum hc n).rootGroup (-γ)).map (MulAut.conj a).toMonoidHom := by
  let σ : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 f
  have hσ2 : ∀ x, σ (σ x) = x := CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  obtain ⟨v, w, hv, hw, hvw, hvroot, hwroot⟩ :=
    CFSG.StandardType.LieKnownR2.Geo.exists_unitTransvGroup_eq_conj_rootGroup_SU
      (F := F) hc r hβ hl u
  have hUv : Matrix.vecMul (fun i => σ.toRingHom (Matrix.mulVec U v i)) (Unitary.antidiag n) ⬝ᵥ
      Matrix.mulVec U v = 0 :=
    (unitary_block_form_apply σ U hA v v).trans hv
  have hUw : Matrix.vecMul (fun i => σ.toRingHom (Matrix.mulVec U w i)) (Unitary.antidiag n) ⬝ᵥ
      Matrix.mulVec U w = 0 :=
    (unitary_block_form_apply σ U hA w w).trans hw
  have hUvw : Matrix.vecMul (fun i => σ.toRingHom (Matrix.mulVec U v i)) (Unitary.antidiag n) ⬝ᵥ
      Matrix.mulVec U w = 1 :=
    (unitary_block_form_apply σ U hA v w).trans hvw
  obtain ⟨γ, hγ, hlongγ, a, ha, ha'⟩ :=
    exists_conj_rootGroup_eq_unitTransvGroup_PSU (F := F) (f := f) hc n hn
      (Matrix.mulVec U v) (Matrix.mulVec U w) hUv hUw hUvw
  have hvMap : ((((Unitary.rootDatum hc r).rootGroup β).map
        (MulAut.conj u).toMonoidHom).map ι).map (Unitary.SU σ n).subtype =
      unitTransvGroup σ.toRingHom (Unitary.antidiag n) (Matrix.mulVec U v) :=
    bmSDU_root_datum_transfer hvroot
      (unitTransvGroup_map_of_unitary_block σ hσ2 hUL hLU hA hadjE ι hιform v hv)
  have hwMap : ((((Unitary.rootDatum hc r).rootGroup (-β)).map
        (MulAut.conj u).toMonoidHom).map ι).map (Unitary.SU σ n).subtype =
      unitTransvGroup σ.toRingHom (Unitary.antidiag n) (Matrix.mulVec U w) :=
    bmSDU_root_datum_transfer hwroot
      (unitTransvGroup_map_of_unitary_block σ hσ2 hUL hLU hA hadjE ι hιform w hw)
  refine ⟨γ, hγ, hlongγ, a, ?_, ?_⟩
  · exact Subgroup.map_injective (Subgroup.subtype_injective (Unitary.SU σ n))
      (hvMap.trans ha.symm)
  · exact Subgroup.map_injective (Subgroup.subtype_injective (Unitary.SU σ n))
      (hwMap.trans ha'.symm)

private lemma bmSDU_root_datum_long
    (g r : ℕ) (hr2 : 2 ≤ r) :
    ∃ (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ),
      β₀ ∈ (ggU .PSU r (g + 1)).D.roots ∧ GGLongRoot (ggU .PSU r (g + 1)).D β₀ ∧
      (∀ δ ∈ (ggU .PSU r (g + 1)).D.roots, CFSG.LieType.Steinberg.ht δ ≤
        CFSG.LieType.Steinberg.ht β₀) := by
  have hc : Nat.card (GaloisField 2 (2 * (g + 1))) = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  obtain ⟨γ, hγ, hmax⟩ :=
    exists_maxHeight (D := Unitary.rootDatum hc r) (show 0 < r / 2 by omega)
  exact ⟨γ, hγ, ⟨1, γ, hγ, hmax, by rfl⟩, hmax⟩

private lemma bmSDU_map_subtype_le_iff {F : Type} [Field F] {r : ℕ} (σ : F ≃+* F)
    (H : Subgroup ↥(Unitary.SU σ r)) (T : Subgroup (GL (Fin r) F)) :
    H.map (Unitary.SU σ r).subtype ≤ T ↔ ∀ g ∈ H, (g : GL (Fin r) F) ∈ T := by
  constructor
  · intro h g hg
    exact h (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
  · rintro h y ⟨g, hg, rfl⟩
    exact h g hg

private lemma bmSDU_le_comap_iff {G H : Type} [Group G] [Group H] (f : G →* H)
    (K : Subgroup G) (L : Subgroup H) :
    K ≤ L.comap f ↔ ∀ g ∈ K, f g ∈ L :=
  ⟨fun h g hg => h hg, fun h g hg => h g hg⟩

private lemma bmSDU_map_subtype_le_comap_iff {G' H' : Type} [Group G'] [Group H']
    (f : G' →* H') (K : Subgroup G') (L : Subgroup H') :
    K.map f ≤ L ↔ K ≤ L.comap f :=
  Subgroup.map_le_iff_le_comap

private lemma bmSDU_root_datum_pos_le_comap_gen_sub_image_of_gen
    (g r : ℕ) (hr2 : 2 ≤ r) (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ)
    (hgen : ∀ g₀ ∈ (ggU .PSU r (g + 1)).D.rootGroup β₀,
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
          r).subtype g₀ ∈ (unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2
              (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by omega⟩ :
                  Fin r) 1))) :
    ((ggU .PSU r (g + 1)).D.rootGroup β₀).map (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) r).subtype ≤ (unitTransvGroup
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g +
                1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by omega⟩ : Fin r) 1)) := by
  exact (bmSDU_map_subtype_le_comap_iff (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) r).subtype
    ((ggU .PSU r (g + 1)).D.rootGroup β₀) (unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by
            omega⟩ : Fin r) 1))).mpr
    ((bmSDU_le_comap_iff (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 *
        (g + 1))) 2 (g + 1)) r).subtype
      ((ggU .PSU r (g + 1)).D.rootGroup β₀) (unitTransvGroup
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g +
              1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by omega⟩ : Fin r) 1))).mpr hgen)

private lemma bmSDU_comap_le_forall_mem {G' H' : Type} [Group G'] [Group H']
    (f : G' →* H') (K : Subgroup G') (L : Subgroup H') (h : K ≤ L.comap f) :
    ∀ g ∈ K, f g ∈ L :=
  (bmSDU_le_comap_iff f K L).mp h

private theorem bmSDU_weight_lowIdx {n : ℕ} (a : Fin (n / 2)) :
    Unitary.weight n (Unitary.lowIdx a) = Pi.single a 1 := by
  funext c
  rw [Unitary.SUExtras.weight_apply', Unitary.val_lowIdx, Pi.single_apply]
  by_cases h : c = a
  · subst h
    simp
  · have h' : a.val ≠ c.val := fun e => h (Fin.ext e.symm)
    have h2 : a.val + c.val + 1 ≠ n := by
      have ha := a.isLt
      have hc := c.isLt
      omega
    simp [h, h', h2]

private theorem bmSDU_toStd_apply_of_even {n : ℕ} (he : Even n) (v : Fin (n / 2) → ℤ)
    (a : Fin (n / 2)) :
    Unitary.toStd n v a = (if a.val + 1 = n / 2 then 2 else 1) * v a -
      (if h : 0 < a.val then v ⟨a.val - 1, by omega⟩ else 0) := by
  rw [Unitary.toStd, if_pos he]
  rfl

private theorem bmSDU_exists_highest {n : ℕ} (hn : 2 ≤ n) :
    ∃ θ : Fin (n / 2) → ℤ,
      Unitary.toStd n θ = 2 • Unitary.weight n (Unitary.lowIdx (⟨0, by omega⟩ : Fin (n / 2))) := by
  have hm : 0 < n / 2 := by omega
  by_cases he : Even n
  · refine ⟨fun a => if a.val + 1 = n / 2 then 1 else 2, ?_⟩
    funext a
    rw [bmSDU_toStd_apply_of_even he, bmSDU_weight_lowIdx, Pi.smul_apply,
      Pi.single_apply, nsmul_eq_mul]
    by_cases h0 : a.val = 0
    · have : a = ⟨0, hm⟩ := Fin.ext h0
      subst this
      simp
      split_ifs <;> simp_all <;> omega
    · have h1 : 0 < a.val := Nat.pos_of_ne_zero h0
      have hne : ¬ (a = ⟨0, hm⟩) := fun e => h0 (by rw [e])
      simp [h1, hne]
      split_ifs <;> simp_all <;> omega
  · refine ⟨fun _ => 2, ?_⟩
    funext a
    rw [bmSDU_weight_lowIdx, Pi.smul_apply, Pi.single_apply, nsmul_eq_mul]
    simp only [Unitary.toStd, if_neg he]
    by_cases h0 : a.val = 0
    · have : a = ⟨0, hm⟩ := Fin.ext h0
      subst this
      simp
    · have h1 : 0 < a.val := Nat.pos_of_ne_zero h0
      have hne : ¬ (a = ⟨0, hm⟩) := fun e => h0 (by rw [e])
      simp [h1, hne]

private theorem bmSDU_toStd_maxHeight {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n)
    {γ : Fin (n / 2) → ℤ} (hγ : γ ∈ (Unitary.rootDatum hc n).roots)
    (hmax : ∀ δ ∈ (Unitary.rootDatum hc n).roots, CFSG.LieType.Steinberg.ht δ ≤
      CFSG.LieType.Steinberg.ht γ) :
    Unitary.toStd n γ = 2 • Unitary.weight n (⟨0, by omega⟩ : Fin n) := by
  obtain ⟨θ, hθ⟩ := bmSDU_exists_highest hn
  have hm : 0 < n / 2 := by omega
  have hθr : θ ∈ (Unitary.rootDatum hc n).roots := by
    show θ ∈ roots (Unitary.isFiniteType_cartan n) (Unitary.divisible n)
    rw [Unitary.roots_eq]
    exact Or.inr (Or.inl ⟨Unitary.lowIdx ⟨0, hm⟩, Unitary.lowIdx_ne_rev _ _, hθ⟩)
  have hle : CFSG.LieType.Steinberg.ht θ ≤ CFSG.LieType.Steinberg.ht γ := hmax θ hθr
  have hθ2 : CFSG.LieType.Steinberg.ht θ = (n : ℤ) - 1 := by
    have h := Unitary.SUExtras.two_mul_ht θ
    have h0 : (Unitary.lowIdx (⟨0, hm⟩ : Fin (n / 2))).val = 0 := Unitary.val_lowIdx _
    rw [hθ, map_nsmul, Unitary.SUExtras.lv_weight, h0] at h
    simp only [nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_zero, mul_zero, sub_zero] at h
    omega
  have h2 := Unitary.SUExtras.two_mul_ht γ
  have hγ'' : γ ∈ roots (Unitary.isFiniteType_cartan n) (Unitary.divisible n) := hγ
  rw [Unitary.roots_eq] at hγ''
  rcases hγ'' with ⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, hi, h⟩ | ⟨he, i, hi, h⟩
  · exfalso
    rw [h, map_sub, Unitary.SUExtras.lv_weight, Unitary.SUExtras.lv_weight] at h2
    have hi' := i.isLt
    have hj' := j.isLt
    exact hji (Fin.ext (by rw [Fin.val_rev]; omega))
  · have h3 : 2 * CFSG.LieType.Steinberg.ht γ =
        2 * ((n : ℤ) - 1 - 2 * (i : ℤ)) := by
      rw [Unitary.SUExtras.two_mul_ht, h, map_nsmul, Unitary.SUExtras.lv_weight]
      simp only [nsmul_eq_mul]
      ring
    have h4 : (n : ℤ) - 1 ≤ CFSG.LieType.Steinberg.ht γ := by rw [← hθ2]; exact hle
    have hi0 : i.val = 0 := by
      have : (i : ℤ) ≤ 0 := by linarith
      omega
    have hieq : i = (⟨0, by omega⟩ : Fin n) := Fin.ext hi0
    rw [hieq] at h
    simpa using h
  · exfalso
    rw [h, Unitary.SUExtras.lv_weight] at h2
    have hi' := i.isLt
    omega

private theorem bmSDU_traceZero_iff {F : Type} [Field F] [CharP F 2] (σ : F →+* F)
    (c : F) : c + σ c = 0 ↔ σ c = c := by
  constructor
  · intro h
    have h2 : σ c = -c := eq_neg_of_add_eq_zero_right h
    rw [h2, CharTwo.neg_eq]
  · intro h
    rw [h, ← two_mul]
    exact mul_eq_zero_of_left (CharP.cast_eq_zero F 2) c

private theorem bmSDU_IsUTransGroup_map_subtype {F : Type} [Field F] [CharP F 2]
    {n : ℕ} (σ : F ≃+* F) {v : Fin n → F} {X : Subgroup (Unitary.SU σ n)}
    (hX : CFSG.Timmesfeld.LieEmbed.IsUTransGroup σ v X) :
    X.map (Unitary.SU σ n).subtype =
      unitTransvGroup σ.toRingHom (Unitary.antidiag n) v := by
  apply le_antisymm
  · rintro g ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hx'⟩ := (hX.1 x).1 hx
    have hc' : σ c = c := (bmSDU_traceZero_iff σ.toRingHom c).1 hc
    refine Subgroup.subset_closure ⟨c, hc', ?_⟩
    change CFSG.Timmesfeld.LieEmbed.suMat σ n x = _
    rw [hx']
    simp only [CFSG.Timmesfeld.LieEmbed.uTrans, CFSG.Timmesfeld.LieEmbed.uNil,
      CFSG.Timmesfeld.LieEmbed.uRow]
    rfl
  · refine Subgroup.closure_le _ |>.mpr ?_
    rintro g ⟨c, hc, hg⟩
    have hc' : c + σ c = 0 := (bmSDU_traceZero_iff σ.toRingHom c).2 hc
    obtain ⟨x, hx⟩ := hX.2 c hc'
    refine Subgroup.mem_map.2 ⟨x, ?_, ?_⟩
    · rw [hX.1 x]
      exact ⟨c, hc', hx⟩
    · apply Units.ext
      change CFSG.Timmesfeld.LieEmbed.suMat σ n x =
        ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      rw [hx, hg]
      simp only [CFSG.Timmesfeld.LieEmbed.uTrans, CFSG.Timmesfeld.LieEmbed.uNil,
        CFSG.Timmesfeld.LieEmbed.uRow]
      rfl

private theorem bmSDU_toStd_neg (n : ℕ) (v : Fin (n / 2) → ℤ) :
    Unitary.toStd n (-v) = -Unitary.toStd n v := by
  by_cases he : Even n
  · funext a
    simp only [Unitary.toStd, if_pos he, CFSG.LieType.Universal.Symplectic.toStd, Pi.neg_apply]
    split_ifs <;> ring
  · funext a
    simp only [Unitary.toStd, if_neg he, Pi.neg_apply]
    split_ifs <;> ring

private theorem bmSDU_rootGroup_map_subtype_of_toStd {F : Type} [Field F] [CharP F 2] {n : ℕ}
    (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c) {γ : Fin (n / 2) → ℤ} {i : Fin n}
    (hi : i ≠ i.rev) (hγ : Unitary.toStd n γ = 2 • Unitary.weight n i) :
    (Unitary.rootGroup σ hσ n γ).map (Unitary.SU σ n).subtype =
      unitTransvGroup σ.toRingHom (Unitary.antidiag n) (Pi.single i 1) :=
  bmSDU_IsUTransGroup_map_subtype σ
    (CFSG.Timmesfeld.Transvection.ModelRank.isUTransGroup_rootGroup_long' hσ hi hγ)

private theorem bmSDU_canonical_root_eq {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n) (σ : F ≃+* F)
    (hσ : ∀ c, σ (σ c) = c)
    {γ : Fin (n / 2) → ℤ} (hγ : γ ∈ (Unitary.rootDatum hc n).roots)
    (hmax : ∀ δ ∈ (Unitary.rootDatum hc n).roots, CFSG.LieType.Steinberg.ht δ ≤
      CFSG.LieType.Steinberg.ht γ) :
    (Unitary.rootGroup σ hσ n γ).map (Unitary.SU σ n).subtype =
      unitTransvGroup σ.toRingHom (Unitary.antidiag n)
        (Pi.single (⟨0, by omega⟩ : Fin n) 1) := by
  have hto := bmSDU_toStd_maxHeight hc hn hγ hmax
  have hi : (⟨0, by omega⟩ : Fin n) ≠ (⟨0, by omega⟩ : Fin n).rev := by
    rw [Fin.rev]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hI : CFSG.Timmesfeld.LieEmbed.IsUTransGroup σ
      (Pi.single (⟨0, by omega⟩ : Fin n) 1) (Unitary.rootGroup σ hσ n γ) :=
    CFSG.Timmesfeld.Transvection.ModelRank.isUTransGroup_rootGroup_long' hσ hi hto
  exact bmSDU_IsUTransGroup_map_subtype σ hI

private lemma bmSDU_root_datum_pos_le_comap_gen_sub_image_gen_sub_gen_sub_image
    (g r : ℕ) (hr2 : 2 ≤ r) (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ)
    (hβ₀ : β₀ ∈ (ggU .PSU r (g + 1)).D.roots)
    (hlong : ∀ δ ∈ (ggU .PSU r (g + 1)).D.roots, CFSG.LieType.Steinberg.ht δ ≤
      CFSG.LieType.Steinberg.ht β₀) :
    ((ggU .PSU r (g + 1)).D.rootGroup β₀).map (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) r).subtype ≤ (unitTransvGroup
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g +
                1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by omega⟩ : Fin r) 1)) := by
  have hc : Nat.card (GaloisField 2 (2 * (g + 1))) = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  have hσ : ∀ c, (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
      (g + 1))
      ((CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) c) = c :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  exact (bmSDU_canonical_root_eq (n := r) hc hr2
    (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) hσ
    hβ₀ hlong).le

private lemma bmSDU_root_datum_pos_le_comap_gen_sub_image_gen_sub_gen_sub_of_image
    (g r : ℕ) (hr2 : 2 ≤ r) (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ)
    (h : ((ggU .PSU r (g + 1)).D.rootGroup β₀).map (Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
            r).subtype ≤ (unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2
                (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by omega⟩ :
                    Fin r) 1))) :
    (ggU .PSU r (g + 1)).D.rootGroup β₀ ≤ (unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by
            omega⟩ : Fin r) 1)).comap (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
                (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) r).subtype :=
  (bmSDU_map_subtype_le_comap_iff (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField
      2 (2 * (g + 1))) 2 (g + 1)) r).subtype
    ((ggU .PSU r (g + 1)).D.rootGroup β₀) (unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by
            omega⟩ : Fin r) 1))).mp h

private lemma bmSDU_root_datum_pos_le_comap_gen_sub_image_gen_sub_gen_sub
    (g r : ℕ) (hr2 : 2 ≤ r) (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ)
    (hβ₀ : β₀ ∈ (ggU .PSU r (g + 1)).D.roots)
    (hlong : ∀ δ ∈ (ggU .PSU r (g + 1)).D.roots, CFSG.LieType.Steinberg.ht δ ≤
      CFSG.LieType.Steinberg.ht β₀) :
    (ggU .PSU r (g + 1)).D.rootGroup β₀ ≤ (unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by
            omega⟩ : Fin r) 1)).comap (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
                (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) r).subtype := by
  exact bmSDU_root_datum_pos_le_comap_gen_sub_image_gen_sub_gen_sub_of_image g r hr2 β₀
    (bmSDU_root_datum_pos_le_comap_gen_sub_image_gen_sub_gen_sub_image g r hr2 β₀ hβ₀ hlong)

private lemma bmSDU_root_datum_pos_le_comap_gen_sub_image_gen_sub_gen
    (g r : ℕ) (hr2 : 2 ≤ r) (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ)
    (hβ₀ : β₀ ∈ (ggU .PSU r (g + 1)).D.roots)
    (hlong : ∀ δ ∈ (ggU .PSU r (g + 1)).D.roots, CFSG.LieType.Steinberg.ht δ ≤
      CFSG.LieType.Steinberg.ht β₀) :
    ∀ g₀ ∈ (ggU .PSU r (g + 1)).D.rootGroup β₀,
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
          r).subtype g₀ ∈ (unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2
              (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by omega⟩ :
                  Fin r) 1)) := by
  exact bmSDU_comap_le_forall_mem (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField
      2 (2 * (g + 1))) 2 (g + 1)) r).subtype
    ((ggU .PSU r (g + 1)).D.rootGroup β₀) (unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by
            omega⟩ : Fin r) 1))
    (bmSDU_root_datum_pos_le_comap_gen_sub_image_gen_sub_gen_sub g r hr2 β₀ hβ₀ hlong)

private lemma bmSDU_root_datum_pos_le_comap_gen_sub_image_gen_sub
    (g r : ℕ) (hr2 : 2 ≤ r) (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ)
    (hβ₀ : β₀ ∈ (ggU .PSU r (g + 1)).D.roots)
    (hlong : ∀ δ ∈ (ggU .PSU r (g + 1)).D.roots, CFSG.LieType.Steinberg.ht δ ≤
      CFSG.LieType.Steinberg.ht β₀) :
    (ggU .PSU r (g + 1)).D.rootGroup β₀ ≤ (unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by
            omega⟩ : Fin r) 1)).comap (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
                (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) r).subtype := by
  exact (bmSDU_le_comap_iff (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2
      * (g + 1))) 2 (g + 1)) r).subtype
    ((ggU .PSU r (g + 1)).D.rootGroup β₀) (unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by
            omega⟩ : Fin r) 1))).mpr
    (bmSDU_root_datum_pos_le_comap_gen_sub_image_gen_sub_gen g r hr2 β₀ hβ₀ hlong)

private lemma bmSDU_root_datum_pos_le_comap_gen_sub_image_gen
    (g r : ℕ) (hr2 : 2 ≤ r) (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ)
    (hβ₀ : β₀ ∈ (ggU .PSU r (g + 1)).D.roots)
    (hlong : ∀ δ ∈ (ggU .PSU r (g + 1)).D.roots, CFSG.LieType.Steinberg.ht δ ≤
      CFSG.LieType.Steinberg.ht β₀) :
    ∀ g₀ ∈ (ggU .PSU r (g + 1)).D.rootGroup β₀,
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
          r).subtype g₀ ∈ (unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2
              (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by omega⟩ :
                  Fin r) 1)) := by
  exact (bmSDU_le_comap_iff (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2
      * (g + 1))) 2 (g + 1)) r).subtype
    ((ggU .PSU r (g + 1)).D.rootGroup β₀) (unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by
            omega⟩ : Fin r) 1))).mp
    (bmSDU_root_datum_pos_le_comap_gen_sub_image_gen_sub g r hr2 β₀ hβ₀ hlong)

private lemma bmSDU_root_datum_pos_le_comap_gen_sub_image
    (g r : ℕ) (hr2 : 2 ≤ r) (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ)
    (hβ₀ : β₀ ∈ (ggU .PSU r (g + 1)).D.roots)
    (hlong : ∀ δ ∈ (ggU .PSU r (g + 1)).D.roots, CFSG.LieType.Steinberg.ht δ ≤
      CFSG.LieType.Steinberg.ht β₀) :
    ((ggU .PSU r (g + 1)).D.rootGroup β₀).map (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) r).subtype ≤ (unitTransvGroup
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g +
                1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by omega⟩ : Fin r) 1)) := by
  exact bmSDU_root_datum_pos_le_comap_gen_sub_image_of_gen g r hr2 β₀
    (bmSDU_root_datum_pos_le_comap_gen_sub_image_gen g r hr2 β₀ hβ₀ hlong)

private lemma bmSDU_root_datum_pos_le_comap_gen_sub
    (g r : ℕ) (hr2 : 2 ≤ r) (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ)
    (hβ₀ : β₀ ∈ (ggU .PSU r (g + 1)).D.roots)
    (hlong : ∀ δ ∈ (ggU .PSU r (g + 1)).D.roots, CFSG.LieType.Steinberg.ht δ ≤
      CFSG.LieType.Steinberg.ht β₀) :
    (ggU .PSU r (g + 1)).D.rootGroup β₀ ≤ ((unitTransvGroup
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
            (Unitary.antidiag r) (Pi.single (⟨0, by omega⟩ : Fin r) 1))).comap (Unitary.SU
                (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
                    r).subtype := by
  exact (bmSDU_map_subtype_le_comap_iff (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) r).subtype
    ((ggU .PSU r (g + 1)).D.rootGroup β₀) (unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by
            omega⟩ : Fin r) 1))).mp
    (bmSDU_root_datum_pos_le_comap_gen_sub_image g r hr2 β₀ hβ₀ hlong)

private lemma bmSDU_root_datum_pos_le_comap_gen_mem
    (g r : ℕ) (hr2 : 2 ≤ r) (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ)
    (hβ₀ : β₀ ∈ (ggU .PSU r (g + 1)).D.roots)
    (hlong : ∀ δ ∈ (ggU .PSU r (g + 1)).D.roots, CFSG.LieType.Steinberg.ht δ ≤
      CFSG.LieType.Steinberg.ht β₀) :
    ∀ g₀ ∈ (ggU .PSU r (g + 1)).D.rootGroup β₀,
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
          r).subtype g₀ ∈ (unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2
              (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by omega⟩ :
                  Fin r) 1)) := by
  exact (bmSDU_le_comap_iff (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2
      * (g + 1))) 2 (g + 1)) r).subtype
    ((ggU .PSU r (g + 1)).D.rootGroup β₀) ((unitTransvGroup
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
            (Unitary.antidiag r) (Pi.single (⟨0, by omega⟩ : Fin r) 1)))).mp
    (bmSDU_root_datum_pos_le_comap_gen_sub g r hr2 β₀ hβ₀ hlong)

private lemma bmSDU_root_datum_pos_le_comap_gen
    (g r : ℕ) (hr2 : 2 ≤ r) (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ)
    (hβ₀ : β₀ ∈ (ggU .PSU r (g + 1)).D.roots)
    (hlong : ∀ δ ∈ (ggU .PSU r (g + 1)).D.roots, CFSG.LieType.Steinberg.ht δ ≤
      CFSG.LieType.Steinberg.ht β₀) :
    ∀ g₀ ∈ (ggU .PSU r (g + 1)).D.rootGroup β₀,
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
          r).subtype g₀ ∈
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g
            + 1)).toRingHom (Unitary.antidiag r)
          (Pi.single (⟨0, by omega⟩ : Fin r) 1) := by
  exact bmSDU_root_datum_pos_le_comap_gen_mem g r hr2 β₀ hβ₀ hlong

private lemma bmSDU_root_datum_pos_le_comap
    (g r : ℕ) (hr2 : 2 ≤ r) (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ)
    (hβ₀ : β₀ ∈ (ggU .PSU r (g + 1)).D.roots)
    (hlong : ∀ δ ∈ (ggU .PSU r (g + 1)).D.roots, CFSG.LieType.Steinberg.ht δ ≤
      CFSG.LieType.Steinberg.ht β₀) :
    (ggU .PSU r (g + 1)).D.rootGroup β₀ ≤
      (unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g
          + 1)).toRingHom (Unitary.antidiag r)
        (Pi.single (⟨0, by omega⟩ : Fin r) 1)).comap (Unitary.SU
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
                r).subtype := by
  exact (bmSDU_le_comap_iff
    (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        r).subtype
    ((ggU .PSU r (g + 1)).D.rootGroup β₀)
    (unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g +
        1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by omega⟩ : Fin r) 1))).mpr
    (bmSDU_root_datum_pos_le_comap_gen g r hr2 β₀ hβ₀ hlong)

private lemma bmSDU_root_datum_pos_le_gen
    (g r : ℕ) (hr2 : 2 ≤ r) (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ)
    (hβ₀ : β₀ ∈ (ggU .PSU r (g + 1)).D.roots)
    (hlong : ∀ δ ∈ (ggU .PSU r (g + 1)).D.roots, CFSG.LieType.Steinberg.ht δ ≤
      CFSG.LieType.Steinberg.ht β₀) :
    ∀ g₀ ∈ (ggU .PSU r (g + 1)).D.rootGroup β₀,
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
          r).subtype g₀ ∈
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g
            + 1)).toRingHom (Unitary.antidiag r)
          (Pi.single (⟨0, by omega⟩ : Fin r) 1) := by
  intro g₀ hg₀
  exact bmSDU_root_datum_pos_le_comap g r hr2 β₀ hβ₀ hlong hg₀

private lemma bmSDU_root_datum_pos_le
    (g r : ℕ) (hr2 : 2 ≤ r) (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ)
    (hβ₀ : β₀ ∈ (ggU .PSU r (g + 1)).D.roots)
    (hlong : ∀ δ ∈ (ggU .PSU r (g + 1)).D.roots, CFSG.LieType.Steinberg.ht δ ≤
      CFSG.LieType.Steinberg.ht β₀) :
    ((ggU .PSU r (g + 1)).D.rootGroup β₀).map (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) r).subtype ≤
      unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g +
          1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by omega⟩ : Fin r) 1) := by
  exact (bmSDU_map_subtype_le_iff (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g +
      1))) 2 (g + 1))
    ((ggU .PSU r (g + 1)).D.rootGroup β₀)
    (unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g +
        1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by omega⟩ : Fin r) 1))).mpr
    (bmSDU_root_datum_pos_le_gen g r hr2 β₀ hβ₀ hlong)

private lemma bmSDU_root_datum_pos_ge
    (g r : ℕ) (hr2 : 2 ≤ r) (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ)
    (hβ₀ : β₀ ∈ (ggU .PSU r (g + 1)).D.roots)
    (hlong : ∀ δ ∈ (ggU .PSU r (g + 1)).D.roots, CFSG.LieType.Steinberg.ht δ ≤
      CFSG.LieType.Steinberg.ht β₀) :
    unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g +
        1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by omega⟩ : Fin r) 1) ≤
      ((ggU .PSU r (g + 1)).D.rootGroup β₀).map (Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
              r).subtype := by
  have hc : Nat.card (GaloisField 2 (2 * (g + 1))) = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  have hσ : ∀ c, (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
      (g + 1))
      ((CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) c) = c :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  have heq := bmSDU_canonical_root_eq (n := r) hc hr2
    (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) hσ
    hβ₀ hlong
  exact le_of_eq heq.symm

private lemma bmSDU_root_datum_pos
    (g r : ℕ) (hr2 : 2 ≤ r) (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ)
    (hβ₀ : β₀ ∈ (ggU .PSU r (g + 1)).D.roots)
    (hlong : ∀ δ ∈ (ggU .PSU r (g + 1)).D.roots, CFSG.LieType.Steinberg.ht δ ≤
      CFSG.LieType.Steinberg.ht β₀) :
    (((ggU .PSU r (g + 1)).D.rootGroup β₀).map (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) r).subtype =
      unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g +
          1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by omega⟩ : Fin r) 1)) := by
  exact le_antisymm (bmSDU_root_datum_pos_le g r hr2 β₀ hβ₀ hlong)
    (bmSDU_root_datum_pos_ge g r hr2 β₀ hβ₀ hlong)

private lemma bmSDU_root_datum_neg
    (g r : ℕ) (hr2 : 2 ≤ r) (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ)
    (hβ₀ : β₀ ∈ (ggU .PSU r (g + 1)).D.roots)
    (hlong : ∀ δ ∈ (ggU .PSU r (g + 1)).D.roots, CFSG.LieType.Steinberg.ht δ ≤
      CFSG.LieType.Steinberg.ht β₀) :
    (((ggU .PSU r (g + 1)).D.rootGroup (-β₀)).map (Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
            r).subtype =
      unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g +
          1)).toRingHom (Unitary.antidiag r)
        (Pi.single (Fin.rev (⟨0, by omega⟩ : Fin r)) 1)) := by
  have hc : Nat.card (GaloisField 2 (2 * (g + 1))) = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  have hσ : ∀ c, (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
      (g + 1))
      ((CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) c) = c :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  have hto := bmSDU_toStd_maxHeight (n := r) hc hr2 hβ₀ hlong
  have hneg : Unitary.toStd r (-β₀) =
      2 • Unitary.weight r (Fin.rev (⟨0, by omega⟩ : Fin r)) := by
    have h1 : Unitary.toStd r (-(β₀ : Fin (r / 2) → ℤ)) =
        -Unitary.toStd r (β₀ : Fin (r / 2) → ℤ) :=
      bmSDU_toStd_neg r (β₀ : Fin (r / 2) → ℤ)
    rw [h1, hto, Unitary.SUExtras.weight_rev', smul_neg]
  have hi0 : (⟨0, by omega⟩ : Fin r) ≠ (⟨0, by omega⟩ : Fin r).rev := by
    rw [Fin.rev]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hi : (Fin.rev (⟨0, by omega⟩ : Fin r)) ≠
      (Fin.rev (⟨0, by omega⟩ : Fin r)).rev := by
    rw [Fin.rev_rev]
    exact fun h => hi0 h.symm
  exact bmSDU_rootGroup_map_subtype_of_toStd
    (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) hσ hi hneg

private lemma bmSDU_root_datum
    (g r : ℕ) (hr2 : 2 ≤ r) :
    ∃ (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ),
      β₀ ∈ (ggU .PSU r (g + 1)).D.roots ∧
      GGLongRoot (ggU .PSU r (g + 1)).D β₀ ∧
      (((ggU .PSU r (g + 1)).D.rootGroup β₀).map (Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
              r).subtype =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g
            + 1)).toRingHom (Unitary.antidiag r) (Pi.single (⟨0, by omega⟩ : Fin r) 1)) ∧
      (((ggU .PSU r (g + 1)).D.rootGroup (-β₀)).map (Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
              r).subtype =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g
            + 1)).toRingHom (Unitary.antidiag r)
          (Pi.single (Fin.rev (⟨0, by omega⟩ : Fin r)) 1)) := by
  obtain ⟨β₀, hβ₀, hlong, hmax⟩ := bmSDU_root_datum_long g r hr2
  exact ⟨β₀, hβ₀, hlong, bmSDU_root_datum_pos g r hr2 β₀ hβ₀ hmax,
    bmSDU_root_datum_neg g r hr2 β₀ hβ₀ hmax⟩

private lemma bmSDU_two_le_of_good (r g : ℕ)
    (hgood : (3 ≤ r ∧ ¬ (r = 3 ∧ 2 ^ (g + 1) = 2)) ∨ (r = 2 ∧ 4 ≤ 2 ^ (g + 1))) :
    2 ≤ r := by
  rcases hgood with h | h <;> omega

private lemma bmSDU_not_good_cases (r g : ℕ)
    (hbad : ¬ ((3 ≤ r ∧ ¬ (r = 3 ∧ 2 ^ (g + 1) = 2)) ∨
      (r = 2 ∧ 4 ≤ 2 ^ (g + 1)))) :
    r ≤ 1 ∨ (g = 0 ∧ r = 2) ∨ (g = 0 ∧ r = 3) := by
  by_cases hg : g = 0
  · subst hg
    have hbad' : ¬ (3 ≤ r ∧ r ≠ 3) := by
      intro hcon
      exact hbad (Or.inl ⟨hcon.1, fun h => hcon.2 h.1⟩)
    have hr3 : r ≤ 3 := by
      by_contra h
      exact hbad' ⟨by omega, by omega⟩
    simp only [eq_self_iff_true, true_and]
    omega
  · left
    have hq : 4 ≤ 2 ^ (g + 1) := by
      have h2 : 2 ≤ g + 1 := by omega
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (g + 1) := Nat.pow_le_pow_right (by norm_num) h2
    have hq2 : 2 ^ (g + 1) ≠ 2 := by omega
    have h2 : ¬ (r = 2 ∧ 4 ≤ 2 ^ (g + 1)) := fun h => hbad (Or.inr h)
    have h2' : r ≠ 2 := by
      intro hr
      exact h2 ⟨hr, hq⟩
    have h1 : ¬ (3 ≤ r ∧ ¬ (r = 3 ∧ 2 ^ (g + 1) = 2)) := fun h => hbad (Or.inl h)
    have hlt : r < 3 := by
      by_contra h
      exact h1 ⟨by omega, fun hc => hq2 hc.2⟩
    omega

private lemma bmSDU_SU_le_one_solvable {F : Type} [Field F] (σ : F ≃+* F) {r : ℕ} (hr : r ≤ 1) :
    Group.IsSolvable ↥(Unitary.SU σ r) := by
  rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
  · haveI : Subsingleton ↥(Unitary.SU σ 0) := inferInstance
    exact Group.isSolvable_of_comm (fun a b => Subsingleton.elim _ _)
  · exact Group.isSolvable_of_comm (fun a b => Subtype.ext (by
      apply Units.ext
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.mul_apply, mul_comm]))

private theorem bmSDU_solvable_of_le_one
    (r g : ℕ) (hr : r ≤ 1) :
    Group.IsSolvable ((ggU .PSU r (g + 1)).K) :=
  bmSDU_SU_le_one_solvable (CFSG.LieType.BorelTits.unitaryInvolution
    (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) hr

private lemma bmSDU_primeFactors_PSU_two_zero
    :
    (Nat.card ((ggU .PSU 2 1).K)).primeFactors.card ≤ 2 := by
  have hcard : Nat.card ((ggU .PSU 2 1).K) = 6 := by
    change Nat.card ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 2) 2 1) 2) = 6
    have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 (GaloisField 2 2) :=
      ⟨Nat.prime_two, le_rfl, by
        have hc := CFSG.LieType.Universal.card_galoisField_two_mul 2 1 (by norm_num)
        simpa using hc⟩
    have hG : ((Unitary.antidiag 2).map h.bar).transpose = Unitary.antidiag 2 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Unitary.antidiag, Matrix.map_apply, Matrix.transpose_apply, map_zero, map_one]
    rw [CFSG.StandardType.RootDetectSU.SU_eq_gramSU_antidiag (n := 2) h,
      CFSG.ClassicalGroups.UnitaryFlag.card_gramSU]
    obtain ⟨-, hcard, -⟩ := CFSG.LinearGroups.unitary_full_group_order h
      (CFSG.ClassicalGroups.UnitaryFlag.gramForm_isSymm h hG)
      (CFSG.ClassicalGroups.UnitaryFlag.gramForm_separatingLeft h
        (Unitary.det_antidiag_ne_zero (F := GaloisField 2 2) 2))
      (n := 2) (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]) (by norm_num)
    norm_num at hcard
    exact_mod_cast hcard
  rw [hcard]
  norm_num [Nat.primeFactors]

private theorem bmSDU_solvable_PSU_two_zero
    :
    Group.IsSolvable ((ggU .PSU 2 1).K) := by
  haveI : Finite ((ggU .PSU 2 1).K) :=
    (inferInstance : Finite ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 2) 2 1) 2))
  exact CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    (G := ((ggU .PSU 2 1).K)) bmSDU_primeFactors_PSU_two_zero

private theorem bmSDU_solvable_PSU_three_zero
    :
    Group.IsSolvable ((ggU .PSU 3 1).K) := by
  haveI : Finite ((ggU .PSU 3 1).K) :=
    (inferInstance : Finite ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 2) 2 1) 3))
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    (G := ((ggU .PSU 3 1).K)) ?_
  have hcard : Nat.card ((ggU .PSU 3 1).K) = 216 := by
    change Nat.card ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 2) 2 1) 3) = 216
    have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 (GaloisField 2 2) :=
      ⟨Nat.prime_two, le_rfl, by
        have hc := CFSG.LieType.Universal.card_galoisField_two_mul 2 1 (by norm_num)
        simpa using hc⟩
    have hG : ((Unitary.antidiag 3).map h.bar).transpose = Unitary.antidiag 3 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Unitary.antidiag, Matrix.map_apply, Matrix.transpose_apply, map_zero, map_one]
    rw [CFSG.StandardType.RootDetectSU.SU_eq_gramSU_antidiag (n := 3) h,
      CFSG.ClassicalGroups.UnitaryFlag.card_gramSU]
    obtain ⟨-, hcard, -⟩ := CFSG.LinearGroups.unitary_full_group_order h
      (CFSG.ClassicalGroups.UnitaryFlag.gramForm_isSymm h hG)
      (CFSG.ClassicalGroups.UnitaryFlag.gramForm_separatingLeft h
        (Unitary.det_antidiag_ne_zero (F := GaloisField 2 2) 3))
      (n := 3) (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]) (by norm_num)
    norm_num [Finset.prod_Icc_succ_top] at hcard
    exact_mod_cast hcard
  rw [hcard]
  norm_num [Nat.primeFactors]

private theorem bmSDU_solvable_of_not_good
    (r g : ℕ)
    (hbad : ¬ ((3 ≤ r ∧ ¬ (r = 3 ∧ 2 ^ (g + 1) = 2)) ∨
      (r = 2 ∧ 4 ≤ 2 ^ (g + 1)))) :
    Group.IsSolvable ((ggU .PSU r (g + 1)).K) := by
  rcases bmSDU_not_good_cases r g hbad with hr | ⟨hg, hr⟩ | ⟨hg, hr⟩
  · exact bmSDU_solvable_of_le_one r g hr
  · rw [hg, hr]
    exact bmSDU_solvable_PSU_two_zero
  · rw [hg, hr]
    exact bmSDU_solvable_PSU_three_zero

private theorem bmSDU_not_solvable_of_component
    (n g r : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (ι : (ggU .PSU r (g + 1)).K →*
        ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n))
    (hrange : ι.range = glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S e)
    {J' : Subgroup ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype)
      S e,
      glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S e⁆) :
    ¬ Group.IsSolvable ((ggU .PSU r (g + 1)).K) := by
  intro hK
  have hGe : Group.IsSolvable ↥(ι.range) := by
    haveI : Group.IsSolvable ((ggU .PSU r (g + 1)).K) := hK
    exact Group.isSolvable_of_surjective (f := ι.rangeRestrict) ι.rangeRestrict_surjective
  set H := glBlockCentralizer
    ((Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
      (g + 1)) n).subtype) S e with hHdef
  have hH : Group.IsSolvable ↥H := by
    rw [← hrange]
    exact hGe
  have hcomm : Group.IsSolvable ↥⁅H,H⁆ := by
    haveI : Group.IsSolvable ↥H := hH
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (Subgroup.commutator_le_self H))
  haveI : Group.IsSolvable ↥⁅H,H⁆ := hcomm
  exact CFSG.StandardType.LinSemisimple.false_of_isQuasisimple_of_le_isSolvable hJe.2.2 hJe.1

private theorem bmSDU_good_parameters
    (n g r : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (ι : (ggU .PSU r (g + 1)).K →*
        ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n))
    (hrange : ι.range = glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S e)
    {J' : Subgroup ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype)
      S e,
      glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S e⁆) :
    (3 ≤ r ∧ ¬ (r = 3 ∧ 2 ^ (g + 1) = 2)) ∨ (r = 2 ∧ 4 ≤ 2 ^ (g + 1)) := by
  by_contra hbad
  exact bmSDU_not_solvable_of_component n g r S ι hrange hJe
    (bmSDU_solvable_of_not_good r g hbad)
private theorem bmSDU_block_construction
    (n g : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hadj : formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e < 2)
    {J' : Subgroup ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype)
      S e,
      glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S e⁆) :
    ∃ (r : ℕ) (ι : (ggU .PSU r (g + 1)).K →*
        ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n))
      (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ)
      (v w : Fin n → (GaloisField 2 (2 * (g + 1)))),
      1 ≤ r ∧ Function.Injective ι ∧
      ι.range = glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S e ∧
      GGLongRoot (ggU .PSU r (g + 1)).D β₀ ∧
      Matrix.vecMul
        (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0 ∧
      Matrix.vecMul
        (fun i =>
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (w i))
        (Unitary.antidiag n) ⬝ᵥ w = 0 ∧
      Matrix.vecMul
        (fun i =>
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v i))
        (Unitary.antidiag n) ⬝ᵥ w = 1 ∧
      ((((ggU .PSU r (g + 1)).D.rootGroup β₀).map ι).map
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) = unitTransvGroup
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) v) ∧
      ((((ggU .PSU r (g + 1)).D.rootGroup (-β₀)).map ι).map
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) = unitTransvGroup
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) w) ∧
      ∃ (U : Matrix (Fin n) (Fin r) (GaloisField 2 (2 * (g + 1))))
        (L : Matrix (Fin r) (Fin n) (GaloisField 2 (2 * (g + 1)))),
        Function.Injective U.mulVec ∧
        LinearMap.range U.mulVecLin = LinearMap.range e.mulVecLin ∧
        U * L = e ∧ L * U = 1 ∧
        (∀ x : ↥(Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) r),
          ((ι x : GL (Fin n) (GaloisField 2 (2 * (g + 1)))) :
            Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) =
            U * ((x : GL (Fin r) (GaloisField 2 (2 * (g + 1)))) :
              Matrix (Fin r) (Fin r) (GaloisField 2 (2 * (g + 1)))) * L + (1 - e)) ∧
        Matrix.transpose (U.map
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
              (g + 1)).toRingHom) *
          (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * U =
          (Unitary.antidiag r : Matrix (Fin r) (Fin r) (GaloisField 2 (2 * (g + 1)))) ∧
        Matrix.transpose (e.map
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
              (g + 1)).toRingHom) *
          (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) =
          (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * e := by
  obtain ⟨r, U, h1r, hUinj, hUE, hA⟩ := bmSDU_adapted_basis n g S he hadj
  obtain ⟨ι₀, L, hι₀inj, hι₀range, hUL, hLU, hι₀form⟩ :=
    bmSDU_block_embedding_explicit n g r S hS he hadj hdeg hUinj hUE hA
  have hgood := bmSDU_good_parameters n g r S ι₀ hι₀range hJe
  have hr2 := bmSDU_two_le_of_good r g hgood
  have hE2 : e * e = e := he.2.1.eq
  let F' := GaloisField 2 (2 * (g + 1))
  let σe : F' ≃+* F' := CFSG.LieType.BorelTits.unitaryInvolution F' 2 (g + 1)
  have hGdet : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) F').det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  have hE : Matrix.transpose (e.map σe.toRingHom) *
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F') =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F') * e :=
    bmSDU_adj_matrix_form σe.toRingHom hGdet hadj
  obtain ⟨htr₀, htr₁⟩ := bmSDU_blockHom_transport σe hUL hLU hE hA hr2 ι₀ hι₀form
  obtain ⟨β₀, hβ₀mem, hlong, hroot0, hroot1⟩ := bmSDU_root_datum g r hr2
  obtain ⟨hv, hw, hvw⟩ := bmSDU_root_pair_form n g r U hA h1r hr2
  let v : Fin n → (GaloisField 2 (2 * (g + 1))) :=
    Matrix.mulVec U (Pi.single (⟨0, by omega⟩ : Fin r) 1)
  let w : Fin n → (GaloisField 2 (2 * (g + 1))) :=
    Matrix.mulVec U (Pi.single (Fin.rev (⟨0, by omega⟩ : Fin r)) 1)
  refine ⟨r, ι₀, β₀, v, w, h1r, hι₀inj, hι₀range, hlong, ?_, ?_, ?_,
    bmSDU_root_datum_transfer (v := v) hroot0 htr₀,
    bmSDU_root_datum_transfer (v := w) hroot1 htr₁,
    U, L, hUinj, hUE, hUL, hLU, ?_, hA, hE⟩
  · show Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0
    simpa only [v] using hv
  · show Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (w i)) (Unitary.antidiag n) ⬝ᵥ w = 0
    simpa only [w] using hw
  · show Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (v i)) (Unitary.antidiag n) ⬝ᵥ w = 1
    simpa only [v, w] using hvw
  · intro x
    exact hι₀form x

private theorem bmSDU_blockGroup_quasisimple
    (n g r : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (ι : (ggU .PSU r (g + 1)).K →*
        ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n))
    (hι : Function.Injective ι)
    (hrange : ι.range = glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S e)
    (hgood : (3 ≤ r ∧ ¬ (r = 3 ∧ 2 ^ (g + 1) = 2)) ∨ (r = 2 ∧ 4 ≤ 2 ^ (g + 1))) :
    CFSG.IsQuasisimple ↥(glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S e) := by
  have hKq : CFSG.IsQuasisimple ((ggU .PSU r (g + 1)).K) := by
    rcases hgood with ⟨hr, hrq⟩ | ⟨hr2, hq⟩
    · exact CFSG.LieType.Universal.Unitary.isQuasisimple_SU
        (F := GaloisField 2 (2 * (g + 1))) (p := 2) (f := g + 1) (n := r)
        (CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)) hr
        (fun h => hrq (Prod.ext_iff.mp h))
    · subst hr2
      have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (g + 1)
          (GaloisField 2 (2 * (g + 1))) :=
        ⟨Nat.prime_two, by omega, by
          have hc := CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
          simpa [pow_mul, Nat.mul_comm] using hc⟩
      have hf : 2 ≤ g + 1 := by
        by_contra hlt
        have h1 : g + 1 ≤ 1 := by omega
        have h2 : 2 ^ (g + 1) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
        omega
      have hU := CFSG.StandardType.SURepair.isQuasisimple_unitarySU_two h hf
      let G₀ : Matrix (Fin 2) (Fin 2) (GaloisField 2 (2 * (g + 1))) := 1
      have hG₀ : ∀ i j, h.bar (G₀ j i) = G₀ i j := by
        intro i j
        simp [G₀, Matrix.one_apply, eq_comm]
      have hdet₀ : G₀.det ≠ 0 := by
        simp [G₀]
      obtain ⟨ψ⟩ := CFSG.LieType.Steinberg.nonempty_SUgram_mulEquiv
        (K := GaloisField 2 (2 * (g + 1))) (p := 2) (f := g + 1) h
        (n := 2) (G₀ := G₀) hG₀ hdet₀
      have he : CFSG.LieType.Steinberg.SUgram h.bar
          (1 : Matrix (Fin 2) (Fin 2) (GaloisField 2 (2 * (g + 1))))
          = CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 (g + 1)
            (GaloisField 2 (2 * (g + 1))) 2 := by
        rw [show h.bar = (CFSG.LieType.BorelTits.unitaryInvolution
            (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom from rfl,
          CFSG.LieType.Steinberg.SUgram_one,
          CFSG.LieType.Universal.Unitary.SUid_eq_statedSU
            (CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega))]
      have hU' : CFSG.IsQuasisimple ↥(CFSG.LieType.Steinberg.SUgram h.bar
          (1 : Matrix (Fin 2) (Fin 2) (GaloisField 2 (2 * (g + 1))))) := by
        rw [he]
        exact hU
      exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv ψ hU'
  have hbij : Function.Bijective ι.rangeRestrict :=
    ⟨fun x y hxy => hι (congrArg Subtype.val hxy), ι.rangeRestrict_surjective⟩
  let φ : (ggU .PSU r (g + 1)).K ≃* ↥(glBlockCentralizer
      ((Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
        (g + 1)) n).subtype) S e) :=
    (MulEquiv.ofBijective ι.rangeRestrict hbij).trans (MulEquiv.subgroupCongr hrange)
  exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv φ hKq

private theorem bmSDU_component_eq
    (n g : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    {J' : Subgroup ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hH : CFSG.IsQuasisimple ↥(glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S e))
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype)
      S e,
      glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S e⁆) :
    J' = glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S e := by
  set H := glBlockCentralizer
    ((Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
      (g + 1)) n).subtype) S e with hHdef
  have hiff := isComponentOf_iff_of_normal_of_commutator_le
    (H := H) (N := ⁅H,H⁆) (K := J') (Subgroup.commutator_le_self H)
    (fun a ha b hb => (Subgroup.commutator_le.mp le_rfl) a ha b hb)
  have hJeH : CFSG.Open.IsComponentOf J' H :=
    CFSG.Assembly.isComponentOf_iff_open.mp (hiff.mpr hJe)
  have hHo : CFSG.Open.IsQuasisimple ↥H :=
    CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp hH
  exact CFSG.Fischer.Classification.Recognition.IsComponentOf.eq_of_isQuasisimple hJeH hHo

private lemma bmSDU_antidiag_mulVec_apply {F : Type} [Field F] {r : ℕ}
    (x : Fin r → F) (i : Fin r) :
    (Matrix.mulVec (Unitary.antidiag r : Matrix (Fin r) (Fin r) F) x) i = x (Fin.rev i) := by
  rw [Matrix.mulVec_apply, dotProduct]
  rw [Finset.sum_eq_single (Fin.rev i)]
  · rw [Matrix.row_apply]; simp [Unitary.antidiag]
  · intro j _ hj
    rw [Matrix.row_apply]
    simp only [Unitary.antidiag, Matrix.of_apply, if_neg hj, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma bmSDU_isotropic_form_sum {F : Type} [Field F] {r : ℕ} (σ : F →+* F)
    (v w : Fin r → F) :
    Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ w =
      ∑ i, σ (v (Fin.rev i)) * w i := by
  rw [bmSDU_anti_vecMul, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bmSDU_antidiag_mulVec_apply]

private lemma bmSDU_isotropic_partner {F : Type} [Field F] (σ : F ≃+* F) (r : ℕ) (v : Fin r → F) (hv
    : v ≠ 0)
    (hiso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0) :
    ∃ w : Fin r → F, Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ w = 0 ∧
      Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ w = 1 := by
  have hsum : (∑ i, σ (v (Fin.rev i)) * v i) = 0 :=
    (bmSDU_isotropic_form_sum σ.toRingHom v v).symm.trans hiso
  have hex : ∃ j : Fin r, v j ≠ 0 ∧ j ≠ Fin.rev j := by
    by_contra h
    have h' : ∀ j, v j ≠ 0 → j = Fin.rev j := by
      intro j hj
      by_contra hjj
      exact h ⟨j, hj, hjj⟩
    obtain ⟨m, hm⟩ : ∃ m, v m ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hv (funext fun i => hc i)
    have hvm : m = Fin.rev m := h' m hm
    have hsingle : (∑ i, σ (v (Fin.rev i)) * v i) = σ (v m) * v m := by
      rw [Finset.sum_eq_single m]
      · rw [← hvm]
      · intro i _ hi
        have hvi : v i = 0 := by
          by_contra hvi
          have hfix : i = m := by
            apply Fin.ext
            have hi' : i.val = r - (i.val + 1) := by
              have := congrArg Fin.val (h' i hvi); simpa [Fin.rev] using this
            have hm' : m.val = r - (m.val + 1) := by
              have := congrArg Fin.val hvm; simpa [Fin.rev] using this
            have hi_lt : i.val < r := i.isLt
            have hm_lt : m.val < r := m.isLt
            omega
          exact hi hfix
        rw [hvi, mul_zero]
      · intro hnot; exact absurd (Finset.mem_univ m) hnot
    rw [hsingle] at hsum
    have hσvm : σ (v m) ≠ 0 := fun h => hm (σ.injective (by simpa using h))
    exact (mul_ne_zero hσvm hm) hsum
  obtain ⟨j, hvj, hjrev⟩ := hex
  let w : Fin r → F := Pi.single (Fin.rev j) (1 / σ (v j))
  have hwj : w j = 0 := by
    dsimp only [w]
    rw [Pi.single_eq_of_ne]
    intro h; exact hjrev h
  have hwrevj : w (Fin.rev j) = 1 / σ (v j) := by
    dsimp only [w]; rw [Pi.single_eq_same]
  have hσvj : σ (v j) ≠ 0 := fun h => hvj (σ.injective (by simpa using h))
  refine ⟨w, ?_, ?_⟩
  · have hww : Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ w =
        ∑ i, σ (w (Fin.rev i)) * w i := bmSDU_isotropic_form_sum (σ : F →+* F) w w
    rw [hww, Finset.sum_eq_zero]
    intro i _
    by_cases hij : i = Fin.rev j
    · rw [hij, Fin.rev_rev, hwj, map_zero, zero_mul]
    · dsimp only [w]
      rw [Pi.single_eq_of_ne hij, mul_zero]
  · have hvw : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ w =
        ∑ i, σ (v (Fin.rev i)) * w i := bmSDU_isotropic_form_sum (σ : F →+* F) v w
    rw [hvw, Finset.sum_eq_single (Fin.rev j)]
    · rw [Fin.rev_rev, hwrevj, one_div, mul_inv_cancel₀ hσvj]
    · intro i _ hi
      dsimp only [w]
      rw [Pi.single_eq_of_ne hi, mul_zero]
    · intro hnot; exact absurd (Finset.mem_univ (Fin.rev j)) hnot

private lemma bmSDU_model_transv_conj_rootGroup
    (g r : ℕ) (hr : 2 ≤ r)
    (v' : Fin r → (GaloisField 2 (2 * (g + 1)))) (hv' : v' ≠ 0)
    (hv'iso : Matrix.vecMul
      (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
      (v' i)) (Unitary.antidiag r) ⬝ᵥ v' = 0) :
    ∃ (β : Fin (ggU .PSU r (g + 1)).D.rank → ℤ) (u : (ggU .PSU r (g + 1)).K),
      β ∈ (ggU .PSU r (g + 1)).D.roots ∧ GGLongRoot (ggU .PSU r (g + 1)).D β ∧
      (unitTransvGroup
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag r) v').comap (Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
            r).subtype
      = (((ggU .PSU r (g + 1)).D.rootGroup β).map (MulAut.conj u).toMonoidHom) := by
  let F' := GaloisField 2 (2 * (g + 1))
  let σe : F' ≃+* F' := CFSG.LieType.BorelTits.unitaryInvolution F' 2 (g + 1)
  have hc : Nat.card F' = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  obtain ⟨w, hw, hvw⟩ := bmSDU_isotropic_partner σe r v' hv' hv'iso
  obtain ⟨β, hβ, hlong, u, hu, _⟩ :=
    exists_conj_rootGroup_eq_unitTransvGroup_PSU hc r hr v' w hv'iso hw hvw
  refine ⟨β, u, hβ, hlong, ?_⟩
  rw [← hu]
  rw [Subgroup.comap_map_eq_self_of_injective (f := (Unitary.SU σe r).subtype)
    (fun x y h => Subtype.ext h)]
  rfl

private lemma bmSDU_vec_mem_block_of_transv {F : Type} [Field F] {n r : ℕ}
    (σ : F ≃+* F) {e : Matrix (Fin n) (Fin n) F}
    {U : Matrix (Fin n) (Fin r) F} {L : Matrix (Fin r) (Fin n) F}
    (hUL : U * L = e) (hLU : L * U = 1)
    (hadj : Matrix.transpose (e.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e)
    (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    (v₀ : Fin n → F) (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul (fun i => σ (v₀ i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0)
    (hle : unitTransvGroup σ.toRingHom (Unitary.antidiag n) v₀ ≤
      ι.range.map (Unitary.SU σ n).subtype) :
    ∃ v' : Fin r → F, v₀ = Matrix.mulVec U v' := by
  have hE2 : e * e = e := by
    have hLUL : L * (U * L) = L := by rw [← Matrix.mul_assoc, hLU, Matrix.one_mul]
    rw [← hUL, Matrix.mul_assoc, hLUL, hUL]
  have hGdet : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) F).det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  have h1e : (1 - e) * (1 - e) = 1 - e := (IsIdempotentElem.one_sub_iff.mpr hE2).eq
  let φ : Fin n → F := Matrix.vecMul (fun i => σ (v₀ i)) (Unitary.antidiag n)
  let W : Matrix (Fin n) (Fin n) F := Matrix.vecMulVec v₀ φ
  have hvv : φ ⬝ᵥ v₀ = 0 := hiso
  have hW2 : W * W = 0 := by
    simp only [W]
    rw [Matrix.vecMulVec_mul_vecMulVec, hvv, zero_smul, Matrix.vecMulVec_zero]
  have h1 : (1 + W) * (1 - W) = 1 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hW2]
    abel
  have h2 : (1 - W) * (1 + W) = 1 := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hW2]
    abel
  let T : GL (Fin n) F := ⟨1 + W, 1 - W, h1, h2⟩
  have hTmem : T ∈ unitTransvGroup σ.toRingHom (Unitary.antidiag n) v₀ := by
    refine Subgroup.subset_closure ⟨1, map_one σ.toRingHom, ?_⟩
    show (T : Matrix (Fin n) (Fin n) F) = 1 + (1 : F) • Matrix.vecMulVec v₀
        (Matrix.vecMul (fun i => σ.toRingHom (v₀ i)) (Unitary.antidiag n))
    rw [one_smul]
    rfl
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp (hle hTmem)
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
  have hxT : (ι x : GL (Fin n) F) = T := by
    rw [← hx] at hyeq
    exact hyeq
  have hTmat : (T : Matrix (Fin n) (Fin n) F) =
      U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e) := by
    rw [← hxT]
    exact hιform x
  have hfix : (T : Matrix (Fin n) (Fin n) F) * (1 - e) = 1 - e := by
    rw [hTmat, Matrix.add_mul]
    rw [show U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L * (1 - e) = 0 by
      rw [Matrix.mul_assoc, bmSDU_L_one_sub hUL hLU, Matrix.mul_zero]]
    rw [zero_add, h1e]
  have hW1 : W * (1 - e) = 0 := by
    have h := hfix
    rw [show (T : Matrix (Fin n) (Fin n) F) = 1 + W from rfl, Matrix.add_mul, Matrix.one_mul] at h
    exact add_left_cancel (h.trans (add_zero (1 - e)).symm)
  have hW1' : Matrix.vecMul φ (1 - e) = 0 := by
    have h1 : Matrix.vecMulVec v₀ (Matrix.vecMul φ (1 - e)) = 0 := by
      rw [← Matrix.vecMulVec_mul]
      simpa only [W] using hW1
    obtain ⟨i, hi⟩ : ∃ i, v₀ i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv₀ (funext fun i => h i)
    funext j
    have hij : v₀ i * Matrix.vecMul φ (1 - e) j = 0 := by
      have := congrFun (congrFun h1 i) j
      simpa [Matrix.vecMulVec_apply] using this
    exact (mul_eq_zero.mp hij).resolve_left hi
  have hA1e : Matrix.vecMul (fun i => σ ((Matrix.mulVec (1 - e) v₀) i)) (Unitary.antidiag n) = 0 :=
      by
    have h : Matrix.vecMul (fun i => σ (v₀ i)) (Unitary.antidiag n * (1 - e)) = 0 := by
      rw [← Matrix.vecMul_vecMul]
      exact hW1'
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.vecMul_sub, ← hadj, ← Matrix.vecMul_vecMul,
      bmSDU_vecMul_Utranspose] at h
    rw [bmSDU_anti_vecMul, bmSDU_anti_vecMul, ← Matrix.mulVec_sub] at h
    have hf : (fun i => σ (v₀ i)) - (fun i => σ (Matrix.mulVec e v₀ i)) =
        fun i => σ (Matrix.mulVec (1 - e) v₀ i) := by
      funext i
      rw [Pi.sub_apply, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, map_sub]
    rw [hf] at h
    rw [← bmSDU_anti_vecMul] at h
    exact h
  have hmul : Matrix.mulVec (Unitary.antidiag n) (fun i => σ ((Matrix.mulVec (1 - e) v₀) i)) = 0 :=
      by
    rw [← bmSDU_anti_vecMul]
    exact hA1e
  have hσw : (fun i => σ ((Matrix.mulVec (1 - e) v₀) i)) = 0 :=
    (Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det (Unitary.antidiag n)).mpr hGdet))
      (by rw [hmul, Matrix.mulVec_zero])
  have hw : Matrix.mulVec (1 - e) v₀ = 0 := by
    funext i
    exact σ.injective ((congrFun hσw i).trans (map_zero σ).symm)
  have hev : Matrix.mulVec e v₀ = v₀ := by
    have h := hw
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h.symm
  refine ⟨Matrix.mulVec L v₀, ?_⟩
  calc v₀ = Matrix.mulVec e v₀ := hev.symm
    _ = Matrix.mulVec (U * L) v₀ := by rw [hUL]
    _ = Matrix.mulVec U (Matrix.mulVec L v₀) := by rw [Matrix.mulVec_mulVec]

private lemma bmSDU_vecMulVec_eq_of_indep {F : Type} [Field F] {n : ℕ} {x y a b : Fin n → F}
    (hlin : LinearIndependent F ![x, y])
    (h : Matrix.vecMulVec x a = Matrix.vecMulVec y b) : a = 0 ∧ b = 0 := by
  have key : ∀ (p q : F), p • x + q • y = 0 → p = 0 ∧ q = 0 := by
    intro p q hpq
    have hg : (∑ i : Fin 2, (![p, q] : Fin 2 → F) i • ![x, y] i) = 0 := by
      simpa [Fin.sum_univ_two] using hpq
    have h0 := (Fintype.linearIndependent_iff.mp hlin) ![p, q] hg
    exact ⟨by simpa using h0 0, by simpa using h0 1⟩
  have hcol : ∀ j, a j • x = b j • y := by
    intro j
    funext i
    have hi := congrFun (congrFun h i) j
    simp only [Matrix.vecMulVec_apply] at hi
    simp only [Pi.smul_apply]
    calc a j * x i = x i * a j := mul_comm _ _
      _ = y i * b j := hi
      _ = b j * y i := mul_comm _ _
  have hzero : ∀ j, a j = 0 ∧ b j = 0 := by
    intro j
    have h1 : a j • x + (-(b j)) • y = 0 := by
      rw [neg_smul, ← sub_eq_add_neg, hcol j, sub_self]
    exact ⟨(key _ _ h1).1, neg_eq_zero.mp (key _ _ h1).2⟩
  exact ⟨funext fun j => (hzero j).1, funext fun j => (hzero j).2⟩

private lemma bmSDU_one_sub_vec_of_vecMul_one_sub {F : Type} [Field F] {n : ℕ}
    (σ : F ≃+* F) {e : Matrix (Fin n) (Fin n) F}
    (hadj : Matrix.transpose (e.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e)
    {v : Fin n → F}
    (h : Matrix.vecMul (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag n)) (1 - e) = 0) :
    Matrix.mulVec (1 - e) v = 0 := by
  have hGdet : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) F).det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  have hA1e : Matrix.vecMul (fun i => σ ((Matrix.mulVec (1 - e) v) i)) (Unitary.antidiag n) = 0 :=
      by
    have h' : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag n * (1 - e)) = 0 := by
      rw [← Matrix.vecMul_vecMul]
      exact h
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.vecMul_sub, ← hadj, ← Matrix.vecMul_vecMul,
      bmSDU_vecMul_Utranspose] at h'
    rw [bmSDU_anti_vecMul, bmSDU_anti_vecMul, ← Matrix.mulVec_sub] at h'
    have hf : (fun i => σ (v i)) - (fun i => σ (Matrix.mulVec e v i)) =
        fun i => σ (Matrix.mulVec (1 - e) v i) := by
      funext i
      rw [Pi.sub_apply, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, map_sub]
    rw [hf] at h'
    rw [← bmSDU_anti_vecMul] at h'
    exact h'
  have hmul : Matrix.mulVec (Unitary.antidiag n) (fun i => σ ((Matrix.mulVec (1 - e) v) i)) = 0 :=
      by
    rw [← bmSDU_anti_vecMul]
    exact hA1e
  have hσw : (fun i => σ ((Matrix.mulVec (1 - e) v) i)) = 0 :=
    (Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det (Unitary.antidiag n)).mpr hGdet))
      (by rw [hmul, Matrix.mulVec_zero])
  funext i
  exact σ.injective ((congrFun hσw i).trans (map_zero σ).symm)

private lemma bmSDU_vec_mem_block_of_pair {F : Type} [Field F] {n r : ℕ}
    (σ : F ≃+* F) {e : Matrix (Fin n) (Fin n) F}
    {U : Matrix (Fin n) (Fin r) F} {L : Matrix (Fin r) (Fin n) F}
    (hUL : U * L = e) (hLU : L * U = 1)
    (hadj : Matrix.transpose (e.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e)
    (ι : ↥(Unitary.SU σ r) →* ↥(Unitary.SU σ n))
    (hιform : ∀ x : ↥(Unitary.SU σ r),
      ((ι x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
    (v₀ w₀ : Fin n → F)
    (hlin : LinearIndependent F ![v₀, w₀])
    (hv₀iso : Matrix.vecMul (fun i => σ (v₀ i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0)
    (hw₀iso : Matrix.vecMul (fun i => σ (w₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (horth₀ : Matrix.vecMul (fun i => σ (v₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (horth₀' : Matrix.vecMul (fun i => σ (w₀ i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0)
    (hle : unitPairGroup σ.toRingHom (Unitary.antidiag n) v₀ w₀ ≤
      ι.range.map (Unitary.SU σ n).subtype) :
    (∃ v' : Fin r → F, v₀ = Matrix.mulVec U v') ∧ ∃ w' : Fin r → F, w₀ = Matrix.mulVec U w' := by
  have hE2 : e * e = e := by
    have hLUL : L * (U * L) = L := by rw [← Matrix.mul_assoc, hLU, Matrix.one_mul]
    rw [← hUL, Matrix.mul_assoc, hLUL, hUL]
  have h1e : (1 - e) * (1 - e) = 1 - e := (IsIdempotentElem.one_sub_iff.mpr hE2).eq
  let A : Fin n → F := Matrix.vecMul (fun i => σ (w₀ i)) (Unitary.antidiag n)
  let B : Fin n → F := Matrix.vecMul (fun i => σ (v₀ i)) (Unitary.antidiag n)
  have hAv : A ⬝ᵥ v₀ = 0 := horth₀'
  have hAw : A ⬝ᵥ w₀ = 0 := hw₀iso
  have hBv : B ⬝ᵥ v₀ = 0 := hv₀iso
  have hBw : B ⬝ᵥ w₀ = 0 := horth₀
  let N : Matrix (Fin n) (Fin n) F := Matrix.vecMulVec v₀ A - Matrix.vecMulVec w₀ B
  have hN2 : N * N = 0 := by
    simp only [N, Matrix.sub_mul, Matrix.mul_sub, Matrix.vecMulVec_mul_vecMulVec, hAv, hAw,
      hBv, hBw, zero_smul]
    abel
  have h1 : (1 + N) * (1 - N) = 1 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hN2]
    abel
  have h2 : (1 - N) * (1 + N) = 1 := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hN2]
    abel
  let gU : GL (Fin n) F := ⟨1 + N, 1 - N, h1, h2⟩
  have hgmem : gU ∈ unitPairGroup σ.toRingHom (Unitary.antidiag n) v₀ w₀ := by
    refine Subgroup.subset_closure ⟨1, ?_⟩
    show (gU : Matrix (Fin n) (Fin n) F) = 1 + (1 : F) • Matrix.vecMulVec v₀
        (Matrix.vecMul (fun i => σ.toRingHom (w₀ i)) (Unitary.antidiag n)) -
        σ.toRingHom (1 : F) • Matrix.vecMulVec w₀
        (Matrix.vecMul (fun i => σ.toRingHom (v₀ i)) (Unitary.antidiag n))
    rw [map_one, one_smul, one_smul]
    show (1 + N : Matrix (Fin n) (Fin n) F) = 1 + Matrix.vecMulVec v₀ A - Matrix.vecMulVec w₀ B
    rw [show N = Matrix.vecMulVec v₀ A - Matrix.vecMulVec w₀ B from rfl]
    abel_nf
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp (hle hgmem)
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
  have hxU : (ι x : GL (Fin n) F) = gU := by
    rw [← hx] at hyeq
    exact hyeq
  have hNfix : N * (1 - e) = 0 := by
    have hmat : (gU : Matrix (Fin n) (Fin n) F) =
        U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e) := by
      rw [← hxU]
      exact hιform x
    have hg : (gU : Matrix (Fin n) (Fin n) F) * (1 - e) = 1 - e := by
      rw [hmat, Matrix.add_mul, Matrix.mul_assoc, bmSDU_L_one_sub hUL hLU, Matrix.mul_zero,
        zero_add, h1e]
    rw [show (gU : Matrix (Fin n) (Fin n) F) = 1 + N from rfl, Matrix.add_mul, Matrix.one_mul]
      at hg
    exact add_left_cancel (hg.trans (add_zero (1 - e)).symm)
  have hrelation : Matrix.vecMulVec v₀ (Matrix.vecMul A (1 - e)) =
      Matrix.vecMulVec w₀ (Matrix.vecMul B (1 - e)) := by
    have h := hNfix
    rw [show N = Matrix.vecMulVec v₀ A - Matrix.vecMulVec w₀ B from rfl, Matrix.sub_mul,
      Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, sub_eq_zero] at h
    exact h
  obtain ⟨hA1e, hB1e⟩ := bmSDU_vecMulVec_eq_of_indep hlin hrelation
  have hw : Matrix.mulVec (1 - e) w₀ = 0 := by
    refine bmSDU_one_sub_vec_of_vecMul_one_sub σ hadj ?_
    show Matrix.vecMul (Matrix.vecMul (fun i => σ (w₀ i)) (Unitary.antidiag n)) (1 - e) = 0
    exact hA1e
  have hv : Matrix.mulVec (1 - e) v₀ = 0 := by
    refine bmSDU_one_sub_vec_of_vecMul_one_sub σ hadj ?_
    show Matrix.vecMul (Matrix.vecMul (fun i => σ (v₀ i)) (Unitary.antidiag n)) (1 - e) = 0
    exact hB1e
  refine ⟨?_, ?_⟩
  · refine ⟨Matrix.mulVec L v₀, ?_⟩
    have hev : Matrix.mulVec e v₀ = v₀ := by
      have h := hv
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
      exact h.symm
    calc v₀ = Matrix.mulVec e v₀ := hev.symm
      _ = Matrix.mulVec (U * L) v₀ := by rw [hUL]
      _ = Matrix.mulVec U (Matrix.mulVec L v₀) := by rw [Matrix.mulVec_mulVec]
  · refine ⟨Matrix.mulVec L w₀, ?_⟩
    have hew : Matrix.mulVec e w₀ = w₀ := by
      have h := hw
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
      exact h.symm
    calc w₀ = Matrix.mulVec e w₀ := hew.symm
      _ = Matrix.mulVec (U * L) w₀ := by rw [hUL]
      _ = Matrix.mulVec U (Matrix.mulVec L w₀) := by rw [Matrix.mulVec_mulVec]

private theorem bmSDU_closure_long
    (n g r : ℕ) (hr2 : 2 ≤ r)
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    {J' : Subgroup ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (ι : (ggU .PSU r (g + 1)).K →*
        ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n))
    {U : Matrix (Fin n) (Fin r) (GaloisField 2 (2 * (g + 1)))}
    {L : Matrix (Fin r) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (hUL : U * L = e) (hLU : L * U = 1)
    (hιform : ∀ x : ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) r),
        ((ι x : GL (Fin n) (GaloisField 2 (2 * (g + 1)))) :
          Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) =
          U * ((x : GL (Fin r) (GaloisField 2 (2 * (g + 1)))) :
            Matrix (Fin r) (Fin r) (GaloisField 2 (2 * (g + 1)))) * L + (1 - e))
    (hA : Matrix.transpose (U.map
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
          (g + 1)).toRingHom) *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * U =
        (Unitary.antidiag r : Matrix (Fin r) (Fin r) (GaloisField 2 (2 * (g + 1)))))
    (hadjE : Matrix.transpose (e.map
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
          (g + 1)).toRingHom) *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) =
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * e)
    (hrange : ι.range = J')
    (v₀ : Fin n → (GaloisField 2 (2 * (g + 1)))) (hv₀ : v₀ ≠ 0)
    (hiso : Matrix.vecMul
      (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
      (v₀ i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0)
    (hle : unitTransvGroup
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) v₀ ≤ J'.map
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
      n).subtype)) :
    ∃ (β : Fin (ggU .PSU r (g + 1)).D.rank → ℤ) (u : (ggU .PSU r (g + 1)).K),
      β ∈ (ggU .PSU r (g + 1)).D.roots ∧ GGLongRoot (ggU .PSU r (g + 1)).D β ∧
      (((((ggU .PSU r (g + 1)).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) = unitTransvGroup
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) v₀) := by
  let F' := GaloisField 2 (2 * (g + 1))
  let σe : F' ≃+* F' := CFSG.LieType.BorelTits.unitaryInvolution F' 2 (g + 1)
  have hc : Nat.card F' = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  have hσ2 : ∀ x, σe (σe x) = x := CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  have hle' : unitTransvGroup σe.toRingHom (Unitary.antidiag n) v₀ ≤
      ι.range.map (Unitary.SU σe n).subtype := by
    rw [hrange]; exact hle
  obtain ⟨v', hv'⟩ := bmSDU_vec_mem_block_of_transv σe hUL hLU hadjE ι hιform v₀ hv₀ hiso hle'
  have hv'0 : v' ≠ 0 := by
    intro h0
    rw [h0, Matrix.mulVec_zero] at hv'
    exact hv₀ hv'
  have hiso' : Matrix.vecMul (fun i => σe (v' i)) (Unitary.antidiag r) ⬝ᵥ v' = 0 := by
    have h1 : Matrix.vecMul (fun i => σe (Matrix.mulVec U v' i)) (Unitary.antidiag n) ⬝ᵥ
        Matrix.mulVec U v' = 0 := by
      rw [← hv']; exact hiso
    exact (unitary_block_form_apply σe U hA v' v').symm.trans h1
  have htransport :=
    unitTransvGroup_map_of_unitary_block σe hσ2 hUL hLU hA hadjE ι hιform v' hiso'
  obtain ⟨β, u, hβ, hlong, hEq⟩ := bmSDU_model_transv_conj_rootGroup g r hr2 v' hv'0 hiso'
  refine ⟨β, u, hβ, hlong, ?_⟩
  rw [← hEq, hv']
  exact htransport

private lemma bmSDU_pair_sigma_stable {F : Type} [Field F] (σ : F →+* F) {n : ℕ}
    {e : Matrix (Fin n) (Fin n) F} {x : Fin n → F} (hx : Matrix.mulVec e x = x) :
    Matrix.mulVec (e.map σ) (fun i => σ (x i)) = fun i => σ (x i) := by
  funext i
  have h := RingHom.map_mulVec σ e x i
  rw [hx] at h
  exact h.symm

private noncomputable def bmSDU_pair_embedGL {F : Type} [Field F] {n r : ℕ}
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hE2 : e * e = e) (hUL : U * L = e)
    (hLU : L * U = 1) : GL (Fin r) F →* GL (Fin n) F :=
  { toFun := bmSDU_blockGL hE2 hUL hLU
    map_one' := by
      apply Units.ext
      show U * ((1 : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e) =
        (1 : Matrix (Fin n) (Fin n) F)
      rw [Units.val_one, Matrix.mul_one, hUL]
      abel
    map_mul' := fun x y => by
      apply Units.ext
      show U * ((x * y : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e) =
        (U * ((x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e)) *
          (U * ((y : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * L + (1 - e))
      rw [Units.val_mul]
      exact (bmSDU_embed_mul hE2 hUL hLU (x : Matrix (Fin r) (Fin r) F)
        (y : Matrix (Fin r) (Fin r) F)).symm }

private lemma bmSDU_pair_embedGL_apply {F : Type} [Field F] {n r : ℕ}
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hE2 : e * e = e) (hUL : U * L = e)
    (hLU : L * U = 1) (x : GL (Fin r) F) :
    ((bmSDU_pair_embedGL hE2 hUL hLU x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      U * (x : Matrix (Fin r) (Fin r) F) * L + (1 - e) := rfl

private lemma bmSDU_pair_embedGL_injective {F : Type} [Field F] {n r : ℕ}
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hE2 : e * e = e) (hUL : U * L = e)
    (hLU : L * U = 1) : Function.Injective (bmSDU_pair_embedGL hE2 hUL hLU) := by
  intro x y hxy
  have h : U * (x : Matrix (Fin r) (Fin r) F) * L =
      U * (y : Matrix (Fin r) (Fin r) F) * L := by
    have h2 := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) hxy
    rw [bmSDU_pair_embedGL_apply, bmSDU_pair_embedGL_apply] at h2
    exact add_right_cancel h2
  have h3 := congrArg (fun M : Matrix (Fin n) (Fin n) F => L * M * U) h
  have key : ∀ z : Matrix (Fin r) (Fin r) F, L * (U * z * L) * U = z := by
    intro z
    calc L * (U * z * L) * U = (L * U) * z * (L * U) := by simp only [Matrix.mul_assoc]
      _ = z := by rw [hLU, Matrix.one_mul, Matrix.mul_one]
  apply Units.ext
  exact (key (x : Matrix (Fin r) (Fin r) F)).symm.trans
    (h3.trans (key (y : Matrix (Fin r) (Fin r) F)))

private lemma bmSDU_pair_vecMul_mul_e {F : Type} [Field F] (σ : F →+* F) {n : ℕ}
    {e : Matrix (Fin n) (Fin n) F}
    (hadj : Matrix.transpose (e.map σ) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e)
    {x : Fin n → F} (hx : Matrix.mulVec (e.map σ) x = x) :
    Matrix.vecMul x ((Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e) =
      Matrix.vecMul x (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) := by
  have h1 : Matrix.vecMul x ((Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e) =
      Matrix.vecMul (Matrix.vecMul x (Matrix.transpose (e.map σ)))
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) := by
    rw [← hadj, Matrix.vecMul_vecMul]
  rw [h1]
  have h2 : Matrix.vecMul x (Matrix.transpose (e.map σ)) = Matrix.mulVec (e.map σ) x := by
    ext j
    simp only [Matrix.vecMul_apply, Matrix.transpose_apply, Matrix.mulVec_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h2, hx]

private lemma bmSDU_pair_vecMul_L {F : Type} [Field F] {n r : ℕ} (σ : F ≃+* F)
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hUL : U * L = e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    (u : Fin r → F) :
    Matrix.vecMul (Matrix.vecMul (fun i => σ (u i)) (Unitary.antidiag r)) L =
      Matrix.vecMul (fun i => σ ((Matrix.mulVec U u) i)) (Unitary.antidiag n * e) := by
  rw [← hA]
  rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
  rw [bmSDU_vecMul_Utranspose]
  rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hUL]

private lemma bmSDU_pair_generator_transport {F : Type} [Field F] (σ : F ≃+* F) {n r :
    ℕ}
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hE2 : e * e = e) (hUL : U * L = e) (hLU : L * U = 1)
    (hadj : Matrix.transpose (e.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    (v' w' : Fin r → F) (c : F) (x : GL (Fin r) F)
    (hx : (x : Matrix (Fin r) (Fin r) F) =
      1 + c • Matrix.vecMulVec v' (Matrix.vecMul (fun i => σ (w' i)) (Unitary.antidiag r)) -
        σ c • Matrix.vecMulVec w' (Matrix.vecMul (fun i => σ (v' i)) (Unitary.antidiag r))) :
    ((bmSDU_pair_embedGL hE2 hUL hLU x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      1 + c • Matrix.vecMulVec (Matrix.mulVec U v')
          (Matrix.vecMul (fun i => σ ((Matrix.mulVec U w') i)) (Unitary.antidiag n)) -
        σ c • Matrix.vecMulVec (Matrix.mulVec U w')
          (Matrix.vecMul (fun i => σ ((Matrix.mulVec U v') i)) (Unitary.antidiag n)) := by
  have hMu : ∀ (a u : Fin r → F),
      U * Matrix.vecMulVec a (Matrix.vecMul (fun i => σ (u i)) (Unitary.antidiag r)) * L =
        Matrix.vecMulVec (Matrix.mulVec U a)
          (Matrix.vecMul (fun i => σ ((Matrix.mulVec U u) i)) (Unitary.antidiag n)) := by
    intro a u
    rw [bmSDU_mul_vecMulVec_U, bmSDU_vecMulVec_mul_L]
    congr 1
    rw [bmSDU_pair_vecMul_L σ hUL hA u]
    have hEU : Matrix.mulVec e (Matrix.mulVec U u) = Matrix.mulVec U u := by
      rw [Matrix.mulVec_mulVec, bmSDU_e_mul_U hUL hLU]
    exact bmSDU_pair_vecMul_mul_e σ.toRingHom hadj (bmSDU_pair_sigma_stable σ.toRingHom hEU)
  rw [bmSDU_pair_embedGL_apply, hx]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul,
    Matrix.sub_mul, Matrix.smul_mul, hUL]
  rw [show U * Matrix.vecMulVec v' (Matrix.vecMul (fun i => σ (w' i)) (Unitary.antidiag r)) * L =
      Matrix.vecMulVec (Matrix.mulVec U v')
        (Matrix.vecMul (fun i => σ ((Matrix.mulVec U w') i)) (Unitary.antidiag n)) from hMu v' w',
    show U * Matrix.vecMulVec w' (Matrix.vecMul (fun i => σ (v' i)) (Unitary.antidiag r)) * L =
      Matrix.vecMulVec (Matrix.mulVec U w')
        (Matrix.vecMul (fun i => σ ((Matrix.mulVec U v') i)) (Unitary.antidiag n)) from hMu w' v']
  abel

private lemma bmSDU_pair_comap_phi {F : Type} [Field F] (σ : F ≃+* F) {n r : ℕ}
    {e : Matrix (Fin n) (Fin n) F} {U : Matrix (Fin n) (Fin r) F}
    {L : Matrix (Fin r) (Fin n) F} (hE2 : e * e = e) (hUL : U * L = e) (hLU : L * U = 1)
    (hadj : Matrix.transpose (e.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * e)
    (hA : Matrix.transpose (U.map σ.toRingHom) * (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) * U
        =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) F))
    (v' w' : Fin r → F)
    (hw'iso : Matrix.vecMul (fun i => σ (w' i)) (Unitary.antidiag r) ⬝ᵥ w' = 0)
    (horth' : Matrix.vecMul (fun i => σ (v' i)) (Unitary.antidiag r) ⬝ᵥ w' = 0)
    (horth'' : Matrix.vecMul (fun i => σ (w' i)) (Unitary.antidiag r) ⬝ᵥ v' = 0) :
    (unitPairGroup σ.toRingHom (Unitary.antidiag n) (Matrix.mulVec U v') (Matrix.mulVec U w')).comap
        (bmSDU_pair_embedGL hE2 hUL hLU) =
      unitPairGroup σ.toRingHom (Unitary.antidiag r) v' w' := by
  let f := bmSDU_pair_embedGL hE2 hUL hLU
  have hinj : Function.Injective f := bmSDU_pair_embedGL_injective hE2 hUL hLU
  have hmap : (unitPairGroup σ.toRingHom (Unitary.antidiag r) v' w').map f =
      unitPairGroup σ.toRingHom (Unitary.antidiag n) (Matrix.mulVec U v') (Matrix.mulVec U w') := by
    apply le_antisymm
    · rw [unitPairGroup, unitPairGroup, MonoidHom.map_closure]
      apply Subgroup.closure_mono
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨c, hxmat⟩ := hx
      exact ⟨c, bmSDU_pair_generator_transport σ hE2 hUL hLU hadj hA v' w' c x hxmat⟩
    · rw [unitPairGroup, unitPairGroup]
      refine (Subgroup.closure_le _).mpr ?_
      intro T hT
      obtain ⟨c, hT⟩ := hT
      let M : Matrix (Fin r) (Fin r) F :=
        Matrix.vecMulVec v' (Matrix.vecMul (fun i => σ (w' i)) (Unitary.antidiag r))
      let N : Matrix (Fin r) (Fin r) F :=
        Matrix.vecMulVec w' (Matrix.vecMul (fun i => σ (v' i)) (Unitary.antidiag r))
      have hMM : M * M = 0 := by
        simp only [M]
        rw [Matrix.vecMulVec_mul_vecMulVec, horth'', zero_smul, Matrix.vecMulVec_zero]
      have hNN : N * N = 0 := by
        simp only [N]
        rw [Matrix.vecMulVec_mul_vecMulVec, horth', zero_smul, Matrix.vecMulVec_zero]
      have hMN : M * N = 0 := by
        simp only [M, N]
        rw [Matrix.vecMulVec_mul_vecMulVec, hw'iso, zero_smul, Matrix.vecMulVec_zero]
      have h1M : (1 + c • M) * (1 - c • M) = 1 := by
        rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hMM, smul_zero]
        abel
      have h2M : (1 - c • M) * (1 + c • M) = 1 := by
        rw [Matrix.mul_add, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul]
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hMM, smul_zero]
        abel
      let E1 : GL (Fin r) F := ⟨1 + c • M, 1 - c • M, h1M, h2M⟩
      have h1N : (1 - (σ c) • N) * (1 + (σ c) • N) = 1 := by
        rw [Matrix.mul_add, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul]
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hNN, smul_zero]
        abel
      have h2N : (1 + (σ c) • N) * (1 - (σ c) • N) = 1 := by
        rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hNN, smul_zero]
        abel
      let E2 : GL (Fin r) F := ⟨1 - (σ c) • N, 1 + (σ c) • N, h1N, h2N⟩
      let x : GL (Fin r) F := E1 * E2
      have hxmat : (x : Matrix (Fin r) (Fin r) F) =
          1 + c • Matrix.vecMulVec v' (Matrix.vecMul (fun i => σ (w' i)) (Unitary.antidiag r)) -
            σ c • Matrix.vecMulVec w' (Matrix.vecMul (fun i => σ (v' i)) (Unitary.antidiag r)) := by
        show ((1 + c • M) * (1 - (σ c) • N)) = _
        rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hMN, smul_zero]
        abel
      have hxmem : x ∈ unitPairGroup σ.toRingHom (Unitary.antidiag r) v' w' := by
        rw [unitPairGroup]
        exact Subgroup.subset_closure ⟨c, hxmat⟩
      refine Subgroup.mem_map.mpr ⟨x, hxmem, ?_⟩
      exact Units.ext ((bmSDU_pair_generator_transport σ hE2 hUL hLU hadj hA v' w' c x hxmat).trans
          hT.symm)
  rw [← hmap]
  exact Subgroup.comap_map_eq_self_of_injective hinj _

private lemma bmSDU_four_le_of_isotropic_pair {F : Type} [Field F] (σ : F ≃+* F)
    (r : ℕ) (v w : Fin r → F) (hlin : LinearIndependent F ![v, w])
    (hviso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0)
    (hwise : Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ w = 0)
    (horth : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ w = 0)
    (horth' : Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ v = 0) :
    4 ≤ r := by
  classical
  have hlinσ : LinearIndependent F ![fun i => σ (v i), fun i => σ (w i)] := by
    rw [linearIndependent_fin2] at hlin ⊢
    obtain ⟨hw0, h1⟩ := hlin
    refine ⟨fun h => hw0 (funext fun i => σ.injective ((congrFun h i).trans (map_zero σ).symm)),
      fun a ha => ?_⟩
    refine h1 (σ.symm a) ?_
    ext i
    apply σ.injective
    have hi := congrFun ha i
    simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
    rw [map_mul, RingEquiv.apply_symm_apply]
    exact hi
  set B : LinearMap.BilinForm F (Fin r → F) :=
    (Unitary.antidiag r : Matrix (Fin r) (Fin r) F).toBilin' with hBdef
  have hB : B.Nondegenerate :=
    Matrix.Nondegenerate.toBilin'
      ((Matrix.nondegenerate_iff_det_ne_zero).mpr (Unitary.det_antidiag_ne_zero r))
  have hBxy : ∀ x y : Fin r → F, B (fun i => σ (x i)) y =
      Matrix.vecMul (fun i => σ (x i)) (Unitary.antidiag r) ⬝ᵥ y := by
    intro x y
    rw [hBdef, Matrix.toBilin'_apply', Matrix.dotProduct_mulVec]
  have hBvv : B (fun i => σ (v i)) v = 0 := (hBxy v v).trans hviso
  have hBwv : B (fun i => σ (w i)) v = 0 := (hBxy w v).trans horth'
  have hBvw : B (fun i => σ (v i)) w = 0 := (hBxy v w).trans horth
  have hBww : B (fun i => σ (w i)) w = 0 := (hBxy w w).trans hwise
  let U : Submodule F (Fin r → F) := Submodule.span F (Set.range ![v, w])
  let U' : Submodule F (Fin r → F) :=
    Submodule.span F (Set.range ![fun i => σ (v i), fun i => σ (w i)])
  have hUfin : Module.finrank F U = 2 := by
    rw [show U = Submodule.span F (Set.range ![v, w]) from rfl, finrank_span_eq_card hlin,
      Fintype.card_fin]
  have hU'fin : Module.finrank F U' = 2 := by
    rw [show U' = Submodule.span F (Set.range ![fun i => σ (v i), fun i => σ (w i)]) from rfl,
      finrank_span_eq_card hlinσ, Fintype.card_fin]
  have hUU' : U ≤ B.orthogonal U' := by
    rw [show U = Submodule.span F (Set.range ![v, w]) from rfl, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · simp only [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      have hker : U' ≤ LinearMap.ker (B.flip v) := by
        rw [show U' = Submodule.span F (Set.range ![fun i => σ (v i), fun i => σ (w i)]) from rfl,
          Submodule.span_le]
        rintro y ⟨j, rfl⟩
        fin_cases j
        · simpa [LinearMap.BilinForm.flip_apply] using hBvv
        · simpa [LinearMap.BilinForm.flip_apply] using hBwv
      exact hker hn
    · simp only [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      have hker : U' ≤ LinearMap.ker (B.flip w) := by
        rw [show U' = Submodule.span F (Set.range ![fun i => σ (v i), fun i => σ (w i)]) from rfl,
          Submodule.span_le]
        rintro y ⟨j, rfl⟩
        fin_cases j
        · simpa [LinearMap.BilinForm.flip_apply] using hBvw
        · simpa [LinearMap.BilinForm.flip_apply] using hBww
      exact hker hn
  have hmono : Module.finrank F U ≤ Module.finrank F (B.orthogonal U') :=
    Submodule.finrank_mono hUU'
  rw [LinearMap.BilinForm.finrank_orthogonal hB U', hU'fin, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] at hmono
  omega

private lemma bmSDU_exists_dot_eq_family {F : Type} [Field F] {r k : ℕ} {u : Fin k → Fin r → F}
    (hlin : LinearIndependent F u) (a : Fin k → F) :
    ∃ x : Fin r → F, ∀ i, u i ⬝ᵥ x = a i := by
  classical
  set Bd : LinearMap.BilinForm F (Fin r → F) := (1 : Matrix (Fin r) (Fin r) F).toBilin' with hBddef
  have hBdnd : Bd.Nondegenerate := by
    apply Matrix.Nondegenerate.toBilin'
    rw [Matrix.nondegenerate_iff_det_ne_zero]
    simp
  set W : Submodule F (Fin r → F) := Submodule.span F (Set.range u) with hW
  have hWfin : Module.finrank F W = k := by
    rw [hW, finrank_span_eq_card hlin, Fintype.card_fin]
  have hkr : k ≤ r := by
    have h := Submodule.finrank_mono (le_top : W ≤ ⊤)
    rw [hWfin, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    exact h
  set Φ : (Fin r → F) →ₗ[F] (Fin k → F) := LinearMap.pi (fun i => Bd (u i)) with hΦ
  have hker : LinearMap.ker Φ = Bd.orthogonal W := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [LinearMap.mem_ker] at hx
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      have hx' : ∀ i, Bd (u i) x = 0 := by
        intro i
        simpa [hΦ, LinearMap.pi_apply] using congrFun hx i
      have hsub : W ≤ LinearMap.ker (Bd.flip x) := by
        rw [hW, Submodule.span_le]
        rintro w ⟨i, rfl⟩
        simpa [LinearMap.BilinForm.flip_apply] using hx' i
      exact hsub hw
    · intro x hx
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
      rw [LinearMap.mem_ker]
      ext i
      simpa [hΦ, LinearMap.pi_apply] using
        hx (u i) (Submodule.subset_span (Set.mem_range_self i))
  have hkerfin : Module.finrank F (LinearMap.ker Φ) = r - k := by
    rw [hker, LinearMap.BilinForm.finrank_orthogonal hBdnd W, hWfin,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have htop : LinearMap.range Φ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hrn := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hkerfin, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrn
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega
  obtain ⟨x, hx⟩ := (show a ∈ LinearMap.range Φ from htop ▸ Submodule.mem_top)
  refine ⟨x, fun i => ?_⟩
  simpa [hΦ, LinearMap.pi_apply, hBddef, Matrix.toBilin'_apply'] using congrFun hx i

private lemma bmSDU_h_self_fix {F : Type} [Field F] (σ : F ≃+* F) {r : ℕ}
    (hσ2 : ∀ x, σ (σ x) = x) (x : Fin r → F) :
    σ (Matrix.vecMul (fun i => σ (x i)) (Unitary.antidiag r) ⬝ᵥ x)
      = Matrix.vecMul (fun i => σ (x i)) (Unitary.antidiag r) ⬝ᵥ x := by
  change σ.toRingHom (Matrix.vecMul (fun i => σ.toRingHom (x i)) (Unitary.antidiag r) ⬝ᵥ x)
      = Matrix.vecMul (fun i => σ.toRingHom (x i)) (Unitary.antidiag r) ⬝ᵥ x
  have hσ2' : ∀ z : F, σ.toRingHom (σ.toRingHom z) = z := fun z => hσ2 z
  let e : Fin r ≃ Fin r := ⟨Fin.rev, Fin.rev, fun i => by simp, fun i => by simp⟩
  have key : Matrix.vecMul (fun i => σ.toRingHom (x i)) (Unitary.antidiag r) ⬝ᵥ x
      = σ.toRingHom (Matrix.vecMul (fun i => σ.toRingHom (x i)) (Unitary.antidiag r) ⬝ᵥ x) := by
    calc Matrix.vecMul (fun i => σ.toRingHom (x i)) (Unitary.antidiag r) ⬝ᵥ x
        = ∑ i, σ.toRingHom (x (Fin.rev i)) * x i := bmSDU_isotropic_form_sum σ.toRingHom x x
      _ = ∑ i, σ.toRingHom (x (Fin.rev (e i))) * x (e i) := by
          rw [← Equiv.sum_comp e (fun i => σ.toRingHom (x (Fin.rev i)) * x i)]
      _ = ∑ i, x (Fin.rev i) * σ.toRingHom (x i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          dsimp [e]; rw [Fin.rev_rev, mul_comm]
      _ = σ.toRingHom (∑ i, σ.toRingHom (x (Fin.rev i)) * x i) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul, hσ2']
      _ = σ.toRingHom (Matrix.vecMul (fun i => σ.toRingHom (x i)) (Unitary.antidiag r) ⬝ᵥ x) := by
          rw [bmSDU_isotropic_form_sum σ.toRingHom x x]
  exact key.symm

private lemma bmSDU_trace_surjective {F : Type} [Field F] [CharP F 2] (σ : F ≃+* F)
    (hσ2 : ∀ x, σ (σ x) = x) (hσne : ∃ t : F, σ t ≠ t) {c : F} (hc : σ c = c) :
    ∃ lam : F, lam + σ lam = c := by
  obtain ⟨t, ht⟩ := hσne
  have hfix : σ (t + σ t) = t + σ t := by rw [map_add, hσ2, add_comm]
  have hne : t + σ t ≠ 0 := by
    intro h
    exact ht (CharTwo.add_eq_zero.mp h).symm
  refine ⟨c * t * (t + σ t)⁻¹, ?_⟩
  have hinv : σ ((t + σ t)⁻¹) = (t + σ t)⁻¹ := by rw [map_inv₀, hfix]
  rw [map_mul, map_mul, hc, hinv]
  rw [← add_mul, ← mul_add, mul_assoc, mul_inv_cancel₀ hne, mul_one]

private lemma bmSDU_h_eq_dot_bilin {F : Type} [Field F] {r : ℕ} (σ : F →+* F) (y x : Fin r → F) :
    Matrix.vecMul (fun i => σ (y i)) (Unitary.antidiag r) ⬝ᵥ x
      = (Matrix.mulVec (Unitary.antidiag r) (fun i => σ (y i))) ⬝ᵥ x := by
  rw [bmSDU_anti_vecMul]

private lemma bmSDU_pair_antidiag_linind {F : Type} [Field F] {r : ℕ} (σ : F ≃+* F)
    {v w : Fin r → F} (hlin : LinearIndependent F ![v, w]) :
    LinearIndependent F ![
      Matrix.mulVec (Unitary.antidiag r) (fun i => σ (v i)),
      Matrix.mulVec (Unitary.antidiag r) (fun i => σ (w i))] := by
  have hlinσ : LinearIndependent F ![fun i => σ (v i), fun i => σ (w i)] := by
    rw [linearIndependent_fin2] at hlin ⊢
    obtain ⟨hw0, h1⟩ := hlin
    refine ⟨fun h => hw0 (funext fun i => σ.injective ((congrFun h i).trans (map_zero σ).symm)),
      fun a ha => ?_⟩
    refine h1 (σ.symm a) ?_
    ext i
    apply σ.injective
    have hi := congrFun ha i
    simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
    rw [map_mul, RingEquiv.apply_symm_apply]
    exact hi
  have hG : IsUnit ((Unitary.antidiag r : Matrix (Fin r) (Fin r) F).det) :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero r)
  have hinj : Function.Injective
      (fun y : Fin r → F => Matrix.mulVec (Unitary.antidiag r : Matrix (Fin r) (Fin r) F) y) :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hG)
  have hker : LinearMap.ker ((Unitary.antidiag r : Matrix (Fin r) (Fin r) F).mulVecLin) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro y y' h
    exact hinj (by simpa [Matrix.mulVecLin_apply] using h)
  have hmap := hlinσ.map' ((Unitary.antidiag r : Matrix (Fin r) (Fin r) F).mulVecLin) hker
  have heq : ((Unitary.antidiag r : Matrix (Fin r) (Fin r) F).mulVecLin) ∘
        ![fun i => σ (v i), fun i => σ (w i)]
      = ![Matrix.mulVec (Unitary.antidiag r) (fun i => σ (v i)),
          Matrix.mulVec (Unitary.antidiag r) (fun i => σ (w i))] := by
    funext i
    fin_cases i <;> simp [Matrix.mulVecLin_apply]
  simpa only [heq] using hmap

private lemma bmSDU_h_hermitian_symm {F : Type} [Field F] (σ : F ≃+* F) {r : ℕ}
    (hσ2 : ∀ x, σ (σ x) = x) (y x : Fin r → F) :
    Matrix.vecMul (fun i => σ (y i)) (Unitary.antidiag r) ⬝ᵥ x
      = σ (Matrix.vecMul (fun i => σ (x i)) (Unitary.antidiag r) ⬝ᵥ y) := by
  change Matrix.vecMul (fun i => σ.toRingHom (y i)) (Unitary.antidiag r) ⬝ᵥ x
      = σ.toRingHom (Matrix.vecMul (fun i => σ.toRingHom (x i)) (Unitary.antidiag r) ⬝ᵥ y)
  have hσ2' : ∀ z : F, σ.toRingHom (σ.toRingHom z) = z := fun z => hσ2 z
  let e : Fin r ≃ Fin r := ⟨Fin.rev, Fin.rev, fun i => by simp, fun i => by simp⟩
  calc Matrix.vecMul (fun i => σ.toRingHom (y i)) (Unitary.antidiag r) ⬝ᵥ x
      = ∑ i, σ.toRingHom (y (Fin.rev i)) * x i := bmSDU_isotropic_form_sum σ.toRingHom y x
    _ = ∑ i, σ.toRingHom (y (Fin.rev (e i))) * x (e i) := by
        rw [← Equiv.sum_comp e (fun i => σ.toRingHom (y (Fin.rev i)) * x i)]
    _ = ∑ i, x (Fin.rev i) * σ.toRingHom (y i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp [e]; rw [Fin.rev_rev, mul_comm]
    _ = σ.toRingHom (∑ i, σ.toRingHom (x (Fin.rev i)) * y i) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, hσ2']
    _ = σ.toRingHom (Matrix.vecMul (fun i => σ.toRingHom (x i)) (Unitary.antidiag r) ⬝ᵥ y) := by
        rw [bmSDU_isotropic_form_sum σ.toRingHom x y]

private lemma bmSDU_h_eq_bilin {F : Type} [Field F] {r : ℕ} (σ : F ≃+* F) (x y : Fin r → F) :
    Matrix.vecMul (fun i => σ (x i)) (Unitary.antidiag r) ⬝ᵥ y
      = (Unitary.antidiag r : Matrix (Fin r) (Fin r) F).toBilin' (fun i => σ (x i)) y := by
  rw [Matrix.toBilin'_apply', Matrix.dotProduct_mulVec]

private lemma bmSDU_h_add_smul {F : Type} [Field F] {r : ℕ} (σ : F ≃+* F)
    (x y z : Fin r → F) (c : F) :
    Matrix.vecMul (fun i => σ (x i)) (Unitary.antidiag r) ⬝ᵥ (y + c • z)
      = Matrix.vecMul (fun i => σ (x i)) (Unitary.antidiag r) ⬝ᵥ y
        + c * (Matrix.vecMul (fun i => σ (x i)) (Unitary.antidiag r) ⬝ᵥ z) := by
  rw [bmSDU_h_eq_bilin σ x (y + c • z), bmSDU_h_eq_bilin σ x y,
    bmSDU_h_eq_bilin σ x z, map_add, map_smul, smul_eq_mul]

private lemma bmSDU_h_add_smul_left {F : Type} [Field F] {r : ℕ} (σ : F ≃+* F)
    (x y z : Fin r → F) (c : F) :
    Matrix.vecMul (fun i => σ ((y + c • z) i)) (Unitary.antidiag r) ⬝ᵥ x
      = Matrix.vecMul (fun i => σ (y i)) (Unitary.antidiag r) ⬝ᵥ x
        + σ c * (Matrix.vecMul (fun i => σ (z i)) (Unitary.antidiag r) ⬝ᵥ x) := by
  have h1 : (fun i => σ ((y + c • z) i)) = (fun i => σ (y i)) + σ c • (fun i => σ (z i)) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  rw [bmSDU_h_eq_bilin σ (y + c • z) x, bmSDU_h_eq_bilin σ y x,
    bmSDU_h_eq_bilin σ z x, h1, map_add, map_smul]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]

private lemma bmSDU_h_quad {F : Type} [Field F] {r : ℕ} (σ : F ≃+* F)
    (x y : Fin r → F) (c : F) :
    Matrix.vecMul (fun i => σ ((x + c • y) i)) (Unitary.antidiag r) ⬝ᵥ (x + c • y)
      = Matrix.vecMul (fun i => σ (x i)) (Unitary.antidiag r) ⬝ᵥ x
        + c * (Matrix.vecMul (fun i => σ (x i)) (Unitary.antidiag r) ⬝ᵥ y)
        + σ c * (Matrix.vecMul (fun i => σ (y i)) (Unitary.antidiag r) ⬝ᵥ x)
        + σ c * c * (Matrix.vecMul (fun i => σ (y i)) (Unitary.antidiag r) ⬝ᵥ y) := by
  rw [bmSDU_h_add_smul_left σ (x + c • y) x y c, bmSDU_h_add_smul σ x x y c,
    bmSDU_h_add_smul σ y x y c]
  ring

private lemma bmSDU_pair_isotropic_partner {F : Type} [Field F] [CharP F 2] (σ : F ≃+* F) (hσ2 : ∀
    x, σ (σ x) = x) (hσne : ∃ t : F, σ t ≠ t)
    (r : ℕ) (v w : Fin r → F) (hlin : LinearIndependent F ![v, w])
    (hviso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0)
    (horth' : Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ v = 0) :
    ∃ w₂ : Fin r → F,
      Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ w₂ = 1 ∧
      Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ w₂ = 0 ∧
      Matrix.vecMul (fun i => σ (w₂ i)) (Unitary.antidiag r) ⬝ᵥ w₂ = 0 := by
  obtain ⟨w₂₀, hw₂₀⟩ := bmSDU_exists_dot_eq_family (bmSDU_pair_antidiag_linind σ hlin) ![1, 0]
  have hvw₀ : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ w₂₀ = 1 :=
    (bmSDU_h_eq_dot_bilin σ.toRingHom v w₂₀).trans (hw₂₀ 0)
  have hww₀ : Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ w₂₀ = 0 :=
    (bmSDU_h_eq_dot_bilin σ.toRingHom w w₂₀).trans (hw₂₀ 1)
  obtain ⟨lam, hlam⟩ := bmSDU_trace_surjective σ hσ2 hσne (bmSDU_h_self_fix σ hσ2 w₂₀)
  refine ⟨w₂₀ + lam • v, ?_, ?_, ?_⟩
  · rw [bmSDU_h_add_smul σ v w₂₀ v lam, hvw₀, hviso, mul_zero, add_zero]
  · rw [bmSDU_h_add_smul σ w w₂₀ v lam, hww₀, horth', mul_zero, add_zero]
  · rw [bmSDU_h_quad σ w₂₀ v lam, hviso, mul_zero, add_zero,
      bmSDU_h_hermitian_symm σ hσ2 w₂₀ v, hvw₀, map_one]
    simp only [mul_one]
    rw [add_assoc, hlam, CharTwo.add_self_eq_zero]

private lemma bmSDU_exists_dot_eq_two {F : Type} [Field F] {r : ℕ}
    {u₁ u₂ : Fin r → F} (hlin : LinearIndependent F ![u₁, u₂]) (a b : F) :
    ∃ x : Fin r → F, u₁ ⬝ᵥ x = a ∧ u₂ ⬝ᵥ x = b := by
  obtain ⟨x, hx⟩ := bmSDU_exists_dot_eq_family (u := ![u₁, u₂]) hlin ![a, b]
  exact ⟨x, by simpa using hx 0, by simpa using hx 1⟩

private lemma bmSDU_pair_dual_companion {F : Type} [Field F] (σ : F ≃+* F)
    (r : ℕ) (v w : Fin r → F) (hlin : LinearIndependent F ![v, w]) :
    ∃ u : Fin r → F,
      Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ u = 0 ∧
      Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ u = 1 := by
  obtain ⟨u, hu₁, hu₂⟩ :=
    bmSDU_exists_dot_eq_two (bmSDU_pair_antidiag_linind σ hlin) 0 1
  refine ⟨u, ?_, ?_⟩
  · rw [bmSDU_anti_vecMul]; exact hu₁
  · rw [bmSDU_anti_vecMul]; exact hu₂

private lemma bmSDU_pair_shift_companion {F : Type} [Field F] [CharP F 2] (σ : F ≃+* F)
    (hσ2 : ∀ x, σ (σ x) = x) (r : ℕ) (v w w₂ u : Fin r → F)
    (hviso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0)
    (horth : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ w = 0)
    (hvu : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ u = 0)
    (hwu : Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ u = 1)
    (hvw₂ : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ w₂ = 1) :
    ∃ v₂₀ : Fin r → F,
      Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ v₂₀ = 1 ∧
      Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v₂₀ = 0 ∧
      Matrix.vecMul (fun i => σ (w₂ i)) (Unitary.antidiag r) ⬝ᵥ v₂₀ = 0 := by
  have hw₂v : Matrix.vecMul (fun i => σ (w₂ i)) (Unitary.antidiag r) ⬝ᵥ v = 1 :=
    (bmSDU_h_hermitian_symm σ hσ2 w₂ v).trans (by rw [hvw₂, map_one])
  have hwv : Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ v = 0 :=
    (bmSDU_h_hermitian_symm σ hσ2 w v).trans (by rw [horth, map_zero])
  refine ⟨u + (Matrix.vecMul (fun i => σ (w₂ i)) (Unitary.antidiag r) ⬝ᵥ u) • v, ?_, ?_, ?_⟩
  · rw [bmSDU_h_add_smul σ w u v
      (Matrix.vecMul (fun i => σ (w₂ i)) (Unitary.antidiag r) ⬝ᵥ u), hwu, hwv,
      mul_zero, add_zero]
  · rw [bmSDU_h_add_smul σ v u v
      (Matrix.vecMul (fun i => σ (w₂ i)) (Unitary.antidiag r) ⬝ᵥ u), hvu, hviso,
      mul_zero, add_zero]
  · rw [bmSDU_h_add_smul σ w₂ u v
      (Matrix.vecMul (fun i => σ (w₂ i)) (Unitary.antidiag r) ⬝ᵥ u), hw₂v, mul_one]
    exact CharTwo.add_self_eq_zero _

private lemma bmSDU_pair_isotropize_companion {F : Type} [Field F] [CharP F 2] (σ : F ≃+* F) (hσ2 :
    ∀ x, σ (σ x) = x) (hσne : ∃ t : F, σ t ≠ t)
    (r : ℕ) (v w w₂ v₂₀ : Fin r → F)
    (hwise : Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ w = 0)
    (horth : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ w = 0)
    (hwv₂₀ : Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ v₂₀ = 1)
    (hvv₂₀ : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v₂₀ = 0)
    (hw₂v₂₀ : Matrix.vecMul (fun i => σ (w₂ i)) (Unitary.antidiag r) ⬝ᵥ v₂₀ = 0)
    (hww₂ : Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ w₂ = 0) :
    ∃ v₂ : Fin r → F,
      Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ v₂ = 1 ∧
      Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v₂ = 0 ∧
      Matrix.vecMul (fun i => σ (w₂ i)) (Unitary.antidiag r) ⬝ᵥ v₂ = 0 ∧
      Matrix.vecMul (fun i => σ (v₂ i)) (Unitary.antidiag r) ⬝ᵥ v₂ = 0 := by
  have hw₂w : Matrix.vecMul (fun i => σ (w₂ i)) (Unitary.antidiag r) ⬝ᵥ w = 0 :=
    (bmSDU_h_hermitian_symm σ hσ2 w₂ w).trans (by rw [hww₂, map_zero])
  obtain ⟨mu, hmu⟩ := bmSDU_trace_surjective σ hσ2 hσne (bmSDU_h_self_fix σ hσ2 v₂₀)
  refine ⟨v₂₀ + mu • w, ?_, ?_, ?_, ?_⟩
  · rw [bmSDU_h_add_smul σ w v₂₀ w mu, hwv₂₀, hwise, mul_zero, add_zero]
  · rw [bmSDU_h_add_smul σ v v₂₀ w mu, hvv₂₀, horth, mul_zero, add_zero]
  · rw [bmSDU_h_add_smul σ w₂ v₂₀ w mu, hw₂v₂₀, hw₂w, mul_zero, add_zero]
  · rw [bmSDU_h_quad σ v₂₀ w mu, hwise, mul_zero, add_zero,
      bmSDU_h_hermitian_symm σ hσ2 v₂₀ w, hwv₂₀, map_one]
    simp only [mul_one]
    rw [add_assoc, hmu, CharTwo.add_self_eq_zero]

private lemma bmSDU_pair_isotropic_companion {F : Type} [Field F] [CharP F 2] (σ : F ≃+* F) (hσ2 : ∀
    x, σ (σ x) = x) (hσne : ∃ t : F, σ t ≠ t)
    (r : ℕ) (v w w₂ : Fin r → F) (hlin : LinearIndependent F ![v, w])
    (hviso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0)
    (hwise : Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ w = 0)
    (horth : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ w = 0)
    (hvw₂ : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ w₂ = 1)
    (hww₂ : Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ w₂ = 0) :
    ∃ v₂ : Fin r → F,
      Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ v₂ = 1 ∧
      Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v₂ = 0 ∧
      Matrix.vecMul (fun i => σ (w₂ i)) (Unitary.antidiag r) ⬝ᵥ v₂ = 0 ∧
      Matrix.vecMul (fun i => σ (v₂ i)) (Unitary.antidiag r) ⬝ᵥ v₂ = 0 := by
  obtain ⟨u, hvu, hwu⟩ := bmSDU_pair_dual_companion σ r v w hlin
  obtain ⟨v₂₀, hwv₂₀, hvv₂₀, hw₂v₂₀⟩ :=
    bmSDU_pair_shift_companion σ hσ2 r v w w₂ u hviso horth hvu hwu hvw₂
  exact bmSDU_pair_isotropize_companion σ hσ2 hσne r v w w₂ v₂₀ hwise horth hwv₂₀ hvv₂₀
    hw₂v₂₀ hww₂

private lemma bmSDU_pair_hyperbolic_completion {F : Type} [Field F] [CharP F 2] (σ : F ≃+* F) (hσ2 :
    ∀ x, σ (σ x) = x) (hσne : ∃ t : F, σ t ≠ t)
    (r : ℕ) (v w : Fin r → F)
    (hlin : LinearIndependent F ![v, w])
    (hviso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0)
    (hwise : Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ w = 0)
    (horth : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ w = 0)
    (horth' : Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ v = 0) :
    ∃ (v₂ w₂ : Fin r → F),
      Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ w₂ = 1 ∧
      Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ v₂ = 1 ∧
      (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0 ∧
       Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ w = 0 ∧
       Matrix.vecMul (fun i => σ (v₂ i)) (Unitary.antidiag r) ⬝ᵥ v₂ = 0 ∧
       Matrix.vecMul (fun i => σ (w₂ i)) (Unitary.antidiag r) ⬝ᵥ w₂ = 0 ∧
       Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ w = 0 ∧
       Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v₂ = 0 ∧
       Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ w₂ = 0 ∧
       Matrix.vecMul (fun i => σ (v₂ i)) (Unitary.antidiag r) ⬝ᵥ w₂ = 0) := by
  obtain ⟨w₂, hvw₂, hww₂, hw₂w₂⟩ :=
    bmSDU_pair_isotropic_partner σ hσ2 hσne r v w hlin hviso horth'
  obtain ⟨v₂, hwv₂, hvv₂, hw₂v₂, hv₂v₂⟩ :=
    bmSDU_pair_isotropic_companion σ hσ2 hσne r v w w₂ hlin hviso hwise horth hvw₂ hww₂
  exact ⟨v₂, w₂, hvw₂, hwv₂, hviso, hwise, hv₂v₂, hw₂w₂, horth, hvv₂, hww₂,
    (bmSDU_h_hermitian_symm σ hσ2 v₂ w₂).trans (by rw [hw₂v₂, map_zero])⟩

private lemma bmSDU_pair_short_completion {F : Type} [Field F] [CharP F 2] (σ : F ≃+* F)
    (hσ2 : ∀ x, σ (σ x) = x) (hσne : ∃ t : F, σ t ≠ t)
    (r : ℕ) (v w : Fin r → F)
    (hlin : LinearIndependent F ![v, w])
    (hviso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0)
    (hwise : Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ w = 0)
    (horth : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ w = 0)
    (horth' : Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ v = 0) :
    ∃ (v₂ w₂ : Fin r → F), 4 ≤ r ∧
      Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ w₂ = 1 ∧
      Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ v₂ = 1 ∧
      (Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v = 0 ∧
       Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ w = 0 ∧
       Matrix.vecMul (fun i => σ (v₂ i)) (Unitary.antidiag r) ⬝ᵥ v₂ = 0 ∧
       Matrix.vecMul (fun i => σ (w₂ i)) (Unitary.antidiag r) ⬝ᵥ w₂ = 0 ∧
       Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ w = 0 ∧
       Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag r) ⬝ᵥ v₂ = 0 ∧
       Matrix.vecMul (fun i => σ (w i)) (Unitary.antidiag r) ⬝ᵥ w₂ = 0 ∧
       Matrix.vecMul (fun i => σ (v₂ i)) (Unitary.antidiag r) ⬝ᵥ w₂ = 0) := by
  obtain ⟨v₂, w₂, h₁, h₂, h₀⟩ :=
    bmSDU_pair_hyperbolic_completion σ hσ2 hσne r v w hlin hviso hwise horth horth'
  exact ⟨v₂, w₂,
    bmSDU_four_le_of_isotropic_pair σ r v w hlin hviso hwise horth horth', h₁, h₂, h₀⟩

private lemma bmSDU_model_pair_conj_rootGroup
    (g r : ℕ)
    (v' w' : Fin r → (GaloisField 2 (2 * (g + 1))))
    (hlin : LinearIndependent (GaloisField 2 (2 * (g + 1))) ![v', w'])
    (hv'iso : Matrix.vecMul
      (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
      (v' i)) (Unitary.antidiag r) ⬝ᵥ v' = 0)
    (hw'iso : Matrix.vecMul
      (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
      (w' i)) (Unitary.antidiag r) ⬝ᵥ w' = 0)
    (horth' : Matrix.vecMul
      (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
      (v' i)) (Unitary.antidiag r) ⬝ᵥ w' = 0)
    (horth'' : Matrix.vecMul
      (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
      (w' i)) (Unitary.antidiag r) ⬝ᵥ v' = 0) :
    ∃ (β : Fin (ggU .PSU r (g + 1)).D.rank → ℤ) (u : (ggU .PSU r (g + 1)).K),
      β ∈ (ggU .PSU r (g + 1)).D.roots ∧ GGShortTag .PSU ∧
      2 • β ∉ (ggU .PSU r (g + 1)).D.roots ∧
      (unitPairGroup
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag r) v' w').comap (Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
          (g + 1)) r).subtype
      = (((ggU .PSU r (g + 1)).D.rootGroup β).map (MulAut.conj u).toMonoidHom) := by
  classical
  let F' := GaloisField 2 (2 * (g + 1))
  let σe : F' ≃+* F' := CFSG.LieType.BorelTits.unitaryInvolution F' 2 (g + 1)
  have hc : Nat.card F' = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  obtain ⟨v₂, w₂, hr4, h₁, h₂, h₀⟩ :=
    bmSDU_pair_short_completion σe
      (CFSG.LieType.BorelTits.unitaryInvolution_involutive hc)
      (CFSG.LieType.BorelTits.exists_unitaryInvolution_ne hc)
      r v' w' hlin hv'iso hw'iso horth' horth''
  obtain ⟨β, hβ, h2β, u, hu, _⟩ :=
    exists_conj_rootGroup_eq_unitPairGroup_PSU hc r hr4 v' w' v₂ w₂ h₁ h₂ h₀
  refine ⟨β, u, hβ, Or.inr (Or.inr (Or.inl rfl)), h2β, ?_⟩
  rw [← hu]
  rw [Subgroup.comap_map_eq_self_of_injective (f := (Unitary.SU σe r).subtype)
    (fun x y h => Subtype.ext h)]
  rfl

private theorem bmSDU_closure_short
    (n g r : ℕ)
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    {J' : Subgroup ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (ι : (ggU .PSU r (g + 1)).K →*
        ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n))
    {U : Matrix (Fin n) (Fin r) (GaloisField 2 (2 * (g + 1)))}
    {L : Matrix (Fin r) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (hUL : U * L = e) (hLU : L * U = 1)
    (hιform : ∀ x : ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) r),
        ((ι x : GL (Fin n) (GaloisField 2 (2 * (g + 1)))) :
          Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) =
          U * ((x : GL (Fin r) (GaloisField 2 (2 * (g + 1)))) :
            Matrix (Fin r) (Fin r) (GaloisField 2 (2 * (g + 1)))) * L + (1 - e))
    (hA : Matrix.transpose (U.map
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
          (g + 1)).toRingHom) *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * U =
        (Unitary.antidiag r : Matrix (Fin r) (Fin r) (GaloisField 2 (2 * (g + 1)))))
    (hadjE : Matrix.transpose (e.map
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
          (g + 1)).toRingHom) *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) =
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * e)
    (hrange : ι.range = J')
    (v₀ w₀ : Fin n → (GaloisField 2 (2 * (g + 1)))) (hv₀ : v₀ ≠ 0) (hw₀ : w₀ ≠ 0)
    (hlin : LinearIndependent (GaloisField 2 (2 * (g + 1))) ![v₀, w₀])
    (hiso₁ : Matrix.vecMul
      (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
      (v₀ i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0)
    (hiso₂ : Matrix.vecMul
      (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
      (w₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (horth : Matrix.vecMul
      (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
      (v₀ i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0)
    (hle : unitPairGroup
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) v₀ w₀ ≤ J'.map
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
      n).subtype)) :
    ∃ (β : Fin (ggU .PSU r (g + 1)).D.rank → ℤ) (u : (ggU .PSU r (g + 1)).K),
      β ∈ (ggU .PSU r (g + 1)).D.roots ∧ GGShortTag .PSU ∧
      2 • β ∉ (ggU .PSU r (g + 1)).D.roots ∧
      (((((ggU .PSU r (g + 1)).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) = unitPairGroup
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) v₀ w₀) := by
  let F' := GaloisField 2 (2 * (g + 1))
  let σe : F' ≃+* F' := CFSG.LieType.BorelTits.unitaryInvolution F' 2 (g + 1)
  have hιinj : Function.Injective ι := by
    intro x y hxy
    have h2 : ((ι x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
        ((ι y : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') := by
      rw [hxy]
    rw [hιform x, hιform y] at h2
    have h3 := add_right_cancel h2
    have h4 := congrArg (fun M : Matrix (Fin n) (Fin n) F' => L * M * U) h3
    have key : ∀ z : Matrix (Fin r) (Fin r) F', L * (U * z * L) * U = z := by
      intro z
      calc L * (U * z * L) * U = (L * U) * z * (L * U) := by simp only [Matrix.mul_assoc]
        _ = z := by rw [hLU, Matrix.one_mul, Matrix.mul_one]
    apply Subtype.ext
    apply Units.ext
    exact (key _).symm.trans (h4.trans (key _))
  have hc : Nat.card F' = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  have hσ2 : ∀ x, σe (σe x) = x := CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  have hσ2' : ∀ x, σe (σe.toRingHom x) = x := fun x => hσ2 x
  have hswap : ∀ (x y : Fin n → F'), Matrix.vecMul (fun i => σe (y i)) (Unitary.antidiag n) ⬝ᵥ x =
      σe (Matrix.vecMul (fun i => σe (x i)) (Unitary.antidiag n) ⬝ᵥ y) := by
    have hσ2' : ∀ z : F', σe.toRingHom (σe.toRingHom z) = z := fun z => hσ2 z
    intro x y
    change Matrix.vecMul (fun i => σe.toRingHom (y i)) (Unitary.antidiag n) ⬝ᵥ x =
      σe.toRingHom (Matrix.vecMul (fun i => σe.toRingHom (x i)) (Unitary.antidiag n) ⬝ᵥ y)
    let e : Fin n ≃ Fin n := ⟨Fin.rev, Fin.rev, fun i => by simp, fun i => by simp⟩
    calc Matrix.vecMul (fun i => σe.toRingHom (y i)) (Unitary.antidiag n) ⬝ᵥ x
        = ∑ i, σe.toRingHom (y (Fin.rev i)) * x i := bmSDU_isotropic_form_sum σe.toRingHom y x
      _ = ∑ i, σe.toRingHom (y (Fin.rev (e i))) * x (e i) := by
          rw [← Equiv.sum_comp e (fun i => σe.toRingHom (y (Fin.rev i)) * x i)]
      _ = ∑ i, x (Fin.rev i) * σe.toRingHom (y i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          dsimp [e]; rw [Fin.rev_rev, mul_comm]
      _ = σe.toRingHom (∑ i, σe.toRingHom (x (Fin.rev i)) * y i) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul, hσ2']
      _ = σe.toRingHom (Matrix.vecMul (fun i => σe.toRingHom (x i)) (Unitary.antidiag n) ⬝ᵥ y) := by
          rw [bmSDU_isotropic_form_sum σe.toRingHom x y]
  have horth₀' : Matrix.vecMul (fun i => σe (w₀ i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0 :=
    (hswap v₀ w₀).trans (by rw [horth, map_zero])
  have hle' : unitPairGroup σe.toRingHom (Unitary.antidiag n) v₀ w₀ ≤
      ι.range.map (Unitary.SU σe n).subtype := by rw [hrange]; exact hle
  obtain ⟨⟨v', hv'⟩, ⟨w', hw'⟩⟩ :=
    bmSDU_vec_mem_block_of_pair σe hUL hLU hadjE ι hιform v₀ w₀ hlin
      hiso₁ hiso₂ horth horth₀' hle'
  have hv'ne : v' ≠ 0 := by
    intro h0
    rw [h0, Matrix.mulVec_zero] at hv'
    exact hv₀ hv'
  have hw'ne : w' ≠ 0 := by
    intro h0
    rw [h0, Matrix.mulVec_zero] at hw'
    exact hw₀ hw'
  have hlin' : LinearIndependent F' ![v', w'] := by
    refine LinearIndependent.of_comp (Matrix.mulVecLin U) ?_
    have hcomp2 : (Matrix.mulVecLin U) ∘ ![v', w'] = ![v₀, w₀] := by
      ext i
      fin_cases i <;> simp [Matrix.mulVecLin_apply, hv', hw']
    rw [hcomp2]
    exact hlin
  have hv'iso : Matrix.vecMul (fun i => σe (v' i)) (Unitary.antidiag r) ⬝ᵥ v' = 0 := by
    refine (unitary_block_form_apply σe U hA v' v').symm.trans ?_
    rw [← hv']; exact hiso₁
  have hw'iso : Matrix.vecMul (fun i => σe (w' i)) (Unitary.antidiag r) ⬝ᵥ w' = 0 := by
    refine (unitary_block_form_apply σe U hA w' w').symm.trans ?_
    rw [← hw']; exact hiso₂
  have horth' : Matrix.vecMul (fun i => σe (v' i)) (Unitary.antidiag r) ⬝ᵥ w' = 0 := by
    refine (unitary_block_form_apply σe U hA v' w').symm.trans ?_
    rw [← hv', ← hw']; exact horth
  have horth'' : Matrix.vecMul (fun i => σe (w' i)) (Unitary.antidiag r) ⬝ᵥ v' = 0 := by
    refine (unitary_block_form_apply σe U hA w' v').symm.trans ?_
    rw [← hw', ← hv']
    exact horth₀'
  have hE2 : e * e = e := by
    have hLUL : L * (U * L) = L := by rw [← Matrix.mul_assoc, hLU, Matrix.one_mul]
    rw [← hUL, Matrix.mul_assoc, hLUL, hUL]
  have hcomap_phi : (unitPairGroup σe.toRingHom (Unitary.antidiag n) (Matrix.mulVec U v')
      (Matrix.mulVec U w')).comap
      (bmSDU_pair_embedGL hE2 hUL hLU) =
      unitPairGroup σe.toRingHom (Unitary.antidiag r) v' w' :=
    bmSDU_pair_comap_phi σe hE2 hUL hLU hadjE hA v' w' hw'iso horth' horth''
  have hcomp : ((Unitary.SU σe n).subtype.comp ι) =
      (bmSDU_pair_embedGL hE2 hUL hLU).comp ((Unitary.SU σe r).subtype) := by
    refine MonoidHom.ext fun x => ?_
    refine Units.ext ?_
    show ((ι x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      ((bmSDU_pair_embedGL hE2 hUL hLU ((Unitary.SU σe r).subtype x) : GL (Fin n) F') :
        Matrix (Fin n) (Fin n) F')
    rw [hιform x, bmSDU_pair_embedGL_apply]
    rfl
  have hHpair : (unitPairGroup σe.toRingHom (Unitary.antidiag n) v₀ w₀).comap
      ((Unitary.SU σe n).subtype.comp ι) =
      (unitPairGroup σe.toRingHom (Unitary.antidiag r) v' w').comap ((Unitary.SU σe r).subtype) :=
          by
    rw [hcomp, hv', hw']
    exact (Subgroup.comap_comap _ (bmSDU_pair_embedGL hE2 hUL hLU) ((Unitary.SU σe
        r).subtype)).symm.trans
      (congrArg (fun K => K.comap ((Unitary.SU σe r).subtype)) hcomap_phi)
  set j := (Unitary.SU σe n).subtype with hjdef
  have hrange' : (j.comp ι).range = J'.map j := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_map, ← MonoidHom.range_eq_map, hrange]
  have hcomap : ((unitPairGroup σe.toRingHom (Unitary.antidiag n) v₀ w₀).comap (j.comp ι)).map
      (j.comp ι) =
      unitPairGroup σe.toRingHom (Unitary.antidiag n) v₀ w₀ := by
    rw [Subgroup.map_comap_eq, hrange', inf_eq_right.mpr hle]
  obtain ⟨β, u, hβ, hshort, h2β, hEq⟩ :=
    bmSDU_model_pair_conj_rootGroup g r v' w' hlin' hv'iso hw'iso horth' horth''
  refine ⟨β, u, hβ, hshort, h2β, ?_⟩
  rw [← hEq, ← hHpair, Subgroup.map_map]
  exact hcomap

private theorem bmSDUx_rank_eq {F : Type} [Field F] {n r : ℕ}
    (e : Matrix (Fin n) (Fin n) F) (U : Matrix (Fin n) (Fin r) F)
    (hU : Function.Injective U.mulVec)
    (hrange : LinearMap.range U.mulVecLin = LinearMap.range e.mulVecLin) :
    r = Module.finrank F (LinearMap.range (Matrix.toLin' e)) := by
  have h1 : Module.finrank F (LinearMap.range U.mulVecLin) = Module.finrank F (Fin r → F) :=
    LinearMap.finrank_range_of_inj hU
  rw [Module.finrank_fin_fun] at h1
  rw [hrange] at h1
  rw [Matrix.toLin'_apply']
  exact h1.symm

theorem exists_blockModel_selfDual_PSU_explicit
    (n g : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hadj : formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e = e)
      (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e < 2)
    {J' : Subgroup
      ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype)
      S (e),
      glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S (e)⁆) :
    ∃ (r : ℕ)
      (ι : (ggU .PSU r (g + 1)).K →*
      ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n))
      (β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ), r = Module.finrank (GaloisField 2 (2 * (g + 1)))
          (LinearMap.range (Matrix.toLin' e)) ∧
      GGLongRoot (ggU .PSU r (g + 1)).D β₀ ∧
      (∀ y, ι y ∈ Subgroup.center
        ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n) → y ∈
        Subgroup.center (ggU .PSU r (g + 1)).K) ∧ ι.range = J' ∧
      ∃ v w : Fin n → (GaloisField 2 (2 * (g + 1))), Matrix.vecMul
        (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0 ∧
        Matrix.vecMul
          (fun i =>
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (w i))
          (Unitary.antidiag n) ⬝ᵥ w = 0 ∧
        Matrix.vecMul
          (fun i =>
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v i))
          (Unitary.antidiag n) ⬝ᵥ w = 1 ∧
        (((ggU .PSU r (g + 1)).D.rootGroup β₀).map ι).map
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) = unitTransvGroup
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) v ∧
        (((ggU .PSU r (g + 1)).D.rootGroup (-β₀)).map ι).map
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) = unitTransvGroup
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) w := by
  obtain ⟨r, ι, β₀, v, w, _, hιinj, hrange, hlong, hv, hw, hvw, h1, h2,
    U, _, hUinj, hUrange, _, _, _, _, _⟩ :=
    bmSDU_block_construction n g S hS he hadj hdeg hJe
  have hr : r = Module.finrank (GaloisField 2 (2 * (g + 1)))
      (LinearMap.range (Matrix.toLin' e)) := bmSDUx_rank_eq e U hUinj hUrange
  have hgood := bmSDU_good_parameters n g r S ι hrange hJe
  have hH := bmSDU_blockGroup_quasisimple n g r S ι hιinj hrange hgood
  have hJ := bmSDU_component_eq n g S hH hJe
  refine ⟨r, ι, β₀, hr, hlong, ?_, hrange.trans hJ.symm, v, w, hv, hw, hvw, h1, h2⟩
  exact bmSDU_center_of_injective ι hιinj

theorem exists_blockModelClosure_selfDual_PSU_explicit
    (n g : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hadj : formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e = e)
      (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e < 2)
    {J' : Subgroup
      ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype)
      S (e),
      glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S (e)⁆) :
    ∃ (r : ℕ) (ι : (ggU .PSU r (g + 1)).K →* ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)),
      r = Module.finrank (GaloisField 2 (2 * (g + 1))) (LinearMap.range (Matrix.toLin' e)) ∧
      (∀ y, ι y ∈ Subgroup.center ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n) → y ∈ Subgroup.center (ggU .PSU r (g + 1)).K)
              ∧
      ι.range = J' ∧
      (∀ v₀ : Fin n → GaloisField 2 (2 * (g + 1)), v₀ ≠ 0 → Matrix.vecMul (fun i =>
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v₀
          i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0 → unitTransvGroup
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g +
          1)).toRingHom (Unitary.antidiag n) v₀ ≤ J'.map (Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
          n).subtype →
        ∃ (β : Fin (ggU .PSU r (g + 1)).D.rank → ℤ) (u : (ggU .PSU r (g + 1)).K), β ∈ (ggU .PSU r (g
            + 1)).D.roots ∧
            GGLongRoot (ggU .PSU r (g + 1)).D β ∧
          ((((ggU .PSU r (g + 1)).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
              (Unitary.SU
              (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
              n).subtype = unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2
              (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag n) v₀) ∧
      (∀ v₀ w₀ : Fin n → GaloisField 2 (2 * (g + 1)), v₀ ≠ 0 → w₀ ≠ 0 → LinearIndependent
          (GaloisField 2 (2 * (g + 1))) ![v₀, w₀] → Matrix.vecMul (fun i =>
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v₀
          i)) (Unitary.antidiag n) ⬝ᵥ v₀ = 0 → Matrix.vecMul (fun i =>
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (w₀
          i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0 → Matrix.vecMul (fun i =>
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v₀
          i)) (Unitary.antidiag n) ⬝ᵥ w₀ = 0 → unitPairGroup
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g +
          1)).toRingHom (Unitary.antidiag n) v₀ w₀ ≤ J'.map (Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
          n).subtype →
        ∃ (β : Fin (ggU .PSU r (g + 1)).D.rank → ℤ) (u : (ggU .PSU r (g + 1)).K), β ∈ (ggU .PSU r (g
            + 1)).D.roots ∧
            GGShortTag .PSU ∧ 2 • β ∉ (ggU .PSU r (g + 1)).D.roots ∧
          ((((ggU .PSU r (g + 1)).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
              (Unitary.SU
              (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
              n).subtype = unitPairGroup (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2
              (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag n) v₀ w₀) := by
  obtain ⟨r, ι, _, _, _, _, hιinj, hrangeL1, _, _, _, _, _, _,
    U, L, hUinj, hUrange, hUL, hLU, hιform, hA, hadjE⟩ :=
    bmSDU_block_construction n g S hS he hadj hdeg hJe
  have hgood := bmSDU_good_parameters n g r S ι hrangeL1 hJe
  have hr2 : 2 ≤ r := bmSDU_two_le_of_good r g hgood
  have hH := bmSDU_blockGroup_quasisimple n g r S ι hιinj hrangeL1 hgood
  have hJ := bmSDU_component_eq n g S hH hJe
  have hrange : ι.range = J' := hrangeL1.trans hJ.symm
  have hr : r = Module.finrank (GaloisField 2 (2 * (g + 1)))
      (LinearMap.range (Matrix.toLin' e)) := bmSDUx_rank_eq e U hUinj hUrange
  refine ⟨r, ι, hr, ?_, hrange, ?_, ?_⟩
  · exact bmSDU_center_of_injective ι hιinj
  · intro v₀ hv₀ hiso hle
    exact bmSDU_closure_long n g r hr2 ι hUL hLU hιform hA hadjE hrange v₀ hv₀ hiso hle
  · intro v₀ w₀ hv₀ hw₀ hlin hiso₁ hiso₂ horth hle
    exact bmSDU_closure_short n g r ι hUL hLU hιform hA hadjE hrange v₀ w₀ hv₀ hw₀ hlin hiso₁
        hiso₂ horth hle

theorem exists_linearBlockModel_selfDual_PSU
    (n g : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hadj : formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e = e)
      (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e < 2)
    {J' : Subgroup
      ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype)
      S (e),
      glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S (e)⁆) :

    ∃ (r : ℕ)
      (ι : ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) r) →*
      ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n))
      (E : (Fin r → GaloisField 2 (2 * (g + 1))) →ₗ[GaloisField 2 (2 * (g + 1))]
        (Fin n → GaloisField 2 (2 * (g + 1))))
      (W : Submodule (GaloisField 2 (2 * (g + 1))) (Fin n → GaloisField 2 (2 * (g + 1)))),
      ((3 ≤ r ∧ ¬ (r = 3 ∧ 2 ^ (g + 1) = 2)) ∨ (r = 2 ∧ 4 ≤ 2 ^ (g + 1))) ∧
      Function.Injective ι ∧ ι.range = J' ∧ Function.Injective E ∧
      (∀ x y,
        Matrix.vecMul
          (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
            (g + 1)).toRingHom (x i))
          (Unitary.antidiag r) ⬝ᵥ y =
        Matrix.vecMul
          (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
            (g + 1)).toRingHom (E x i))
          (Unitary.antidiag n) ⬝ᵥ E y) ∧
      (∀ (u : ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) r)) x,
        Matrix.mulVec
          (((ι u : ↥(Unitary.SU
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
              (g + 1)) n)) : GL (Fin n) (GaloisField 2 (2 * (g + 1)))) :
            Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) (E x) =
          E (Matrix.mulVec
            (((u : ↥(Unitary.SU
              (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
                (g + 1)) r)) : GL (Fin r) (GaloisField 2 (2 * (g + 1)))) :
              Matrix (Fin r) (Fin r) (GaloisField 2 (2 * (g + 1)))) x)) ∧
      (∀ (u : ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) r)) w,
        w ∈ W →
        Matrix.mulVec
          (((ι u : ↥(Unitary.SU
            (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
              (g + 1)) n)) : GL (Fin n) (GaloisField 2 (2 * (g + 1)))) :
            Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) w = w) ∧
      (∀ v, ∃ x, ∃ w ∈ W, v = E x + w) ∧
      (∀ x w, w ∈ W →
        Matrix.vecMul
          (fun i => (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
            (g + 1)).toRingHom (E x i))
          (Unitary.antidiag n) ⬝ᵥ w = 0) := by
  obtain ⟨r, ι, β₀, v, w, h1r, hιinj, hrange, hlong, hv, hw, hvw, h1, h2,
    U, L, hUinj, hUrange, hUL, hLU, hιform, hA, hE⟩ :=
    bmSDU_block_construction n g S hS he hadj hdeg hJe
  have hgood := bmSDU_good_parameters n g r S ι hrange hJe
  have hH := bmSDU_blockGroup_quasisimple n g r S ι hιinj hrange hgood
  have hJ := bmSDU_component_eq n g S hH hJe
  let F' := GaloisField 2 (2 * (g + 1))
  let σe : F' ≃+* F' := CFSG.LieType.BorelTits.unitaryInvolution F' 2 (g + 1)
  have hG : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) F').det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  have hE2 : e * e = e := he.2.1.eq
  obtain ⟨ιNew, hιNew, hιNewform⟩ := bmSDU_blockHom σe hE2 hUL hLU hE hA
  have hrangeNew : ιNew.range = glBlockCentralizer (Unitary.SU σe n).subtype S e :=
    bmSDU_blockHom_range σe S hS he hE hdeg hUL hLU hA ιNew hιNewform
  have hEinj : Function.Injective U.mulVecLin := by
    intro a b hab
    apply hUinj
    simpa only [Matrix.mulVecLin_apply] using hab
  have hiso : ∀ x y : Fin r → F',
      Matrix.vecMul (fun i => σe.toRingHom (x i))
          (Unitary.antidiag r : Matrix (Fin r) (Fin r) F') ⬝ᵥ y =
      Matrix.vecMul (fun i => σe.toRingHom (U.mulVec x i))
          (Unitary.antidiag n : Matrix (Fin n) (Fin n) F') ⬝ᵥ U.mulVec y := by
    intro x y
    have hm : (fun i => σe.toRingHom (U.mulVec x i)) =
        Matrix.mulVec (U.map σe.toRingHom) (fun i => σe.toRingHom (x i)) := by
      funext i
      exact RingHom.map_mulVec σe.toRingHom U x i
    have h1 : Matrix.vecMul (fun i => σe.toRingHom (x i))
          (Unitary.antidiag r : Matrix (Fin r) (Fin r) F') ⬝ᵥ y =
        (fun i => σe.toRingHom (x i)) ⬝ᵥ
          Matrix.mulVec (Unitary.antidiag r : Matrix (Fin r) (Fin r) F') y :=
      (Matrix.dotProduct_mulVec (fun i => σe.toRingHom (x i))
        (Unitary.antidiag r : Matrix (Fin r) (Fin r) F') y).symm
    have h2 : (fun i => σe.toRingHom (x i)) ⬝ᵥ
          Matrix.mulVec (Unitary.antidiag r : Matrix (Fin r) (Fin r) F') y =
        (fun i => σe.toRingHom (x i)) ⬝ᵥ
          Matrix.mulVec (Matrix.transpose (U.map σe.toRingHom) *
            (Unitary.antidiag n : Matrix (Fin n) (Fin n) F') * U) y := by
      rw [hA]
    have h3 : (fun i => σe.toRingHom (x i)) ⬝ᵥ
          Matrix.mulVec (Matrix.transpose (U.map σe.toRingHom) *
            (Unitary.antidiag n : Matrix (Fin n) (Fin n) F') * U) y =
        (fun i => σe.toRingHom (x i)) ⬝ᵥ
          Matrix.mulVec (Matrix.transpose (U.map σe.toRingHom) *
            (Unitary.antidiag n : Matrix (Fin n) (Fin n) F')) (Matrix.mulVec U y) := by
      rw [← Matrix.mulVec_mulVec]
    have h4 : (fun i => σe.toRingHom (x i)) ⬝ᵥ
          Matrix.mulVec (Matrix.transpose (U.map σe.toRingHom) *
            (Unitary.antidiag n : Matrix (Fin n) (Fin n) F')) (Matrix.mulVec U y) =
        Matrix.vecMul (fun i => σe.toRingHom (x i))
          (Matrix.transpose (U.map σe.toRingHom) *
            (Unitary.antidiag n : Matrix (Fin n) (Fin n) F')) ⬝ᵥ Matrix.mulVec U y :=
      Matrix.dotProduct_mulVec (fun i => σe.toRingHom (x i))
        (Matrix.transpose (U.map σe.toRingHom) *
          (Unitary.antidiag n : Matrix (Fin n) (Fin n) F')) (Matrix.mulVec U y)
    have h5 : dotProduct
          (Matrix.vecMul (fun i => σe.toRingHom (x i))
            (Matrix.transpose (U.map σe.toRingHom) *
              (Unitary.antidiag n : Matrix (Fin n) (Fin n) F')))
          ((Matrix.mulVec U y : Fin n → F')) =
        dotProduct
          (Matrix.vecMul (Matrix.mulVec (U.map σe.toRingHom)
            (fun i => σe.toRingHom (x i)))
            (Unitary.antidiag n : Matrix (Fin n) (Fin n) F'))
          ((Matrix.mulVec U y : Fin n → F')) := by
      rw [Matrix.vecMul_mulVec]
    have h6 : dotProduct
          (Matrix.vecMul (Matrix.mulVec (U.map σe.toRingHom)
            (fun i => σe.toRingHom (x i)))
            (Unitary.antidiag n : Matrix (Fin n) (Fin n) F'))
          ((Matrix.mulVec U y : Fin n → F')) =
        dotProduct
          (Matrix.vecMul (fun i => σe.toRingHom (U.mulVec x i))
            (Unitary.antidiag n : Matrix (Fin n) (Fin n) F'))
          ((U.mulVec y : Fin n → F')) := by
      rw [← hm]
    exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))
  have hinter : ∀ (u : ↥(Unitary.SU σe r)) x,
      Matrix.mulVec (((ιNew u : ↥(Unitary.SU σe n)) : GL (Fin n) F') :
          Matrix (Fin n) (Fin n) F') (U.mulVec x) =
        U.mulVec (Matrix.mulVec (((u : ↥(Unitary.SU σe r)) : GL (Fin r) F') :
          Matrix (Fin r) (Fin r) F') x) := by
    intro u x
    calc Matrix.mulVec (((ιNew u : ↥(Unitary.SU σe n)) : GL (Fin n) F') :
          Matrix (Fin n) (Fin n) F') (U.mulVec x)
        = Matrix.mulVec (U * ((u : GL (Fin r) F') : Matrix (Fin r) (Fin r) F') * L +
            (1 - e)) (U.mulVec x) := by rw [hιNewform u]
      _ = Matrix.mulVec (U * ((u : GL (Fin r) F') : Matrix (Fin r) (Fin r) F') * L)
            (U.mulVec x) + Matrix.mulVec (1 - e) (U.mulVec x) := by
          rw [Matrix.add_mulVec]
      _ = U.mulVec (Matrix.mulVec (((u : GL (Fin r) F') : Matrix (Fin r) (Fin r) F')) x) +
            0 := by
        rw [show Matrix.mulVec (U * ((u : GL (Fin r) F') : Matrix (Fin r) (Fin r) F') * L)
              (U.mulVec x) =
            U.mulVec (Matrix.mulVec (((u : GL (Fin r) F') : Matrix (Fin r) (Fin r) F')) x) from by
          calc Matrix.mulVec (U * ((u : GL (Fin r) F') : Matrix (Fin r) (Fin r) F') * L)
                (U.mulVec x)
              = Matrix.mulVec (U * ((u : GL (Fin r) F') : Matrix (Fin r) (Fin r) F'))
                  (Matrix.mulVec L (U.mulVec x)) := by rw [← Matrix.mulVec_mulVec]
            _ = Matrix.mulVec U (Matrix.mulVec ((u : GL (Fin r) F') :
                  Matrix (Fin r) (Fin r) F') (Matrix.mulVec L (U.mulVec x))) := by
                rw [← Matrix.mulVec_mulVec]
            _ = Matrix.mulVec U (Matrix.mulVec ((u : GL (Fin r) F') :
                  Matrix (Fin r) (Fin r) F') (Matrix.mulVec (L * U) x)) := by
                rw [Matrix.mulVec_mulVec x L U]
            _ = Matrix.mulVec U (Matrix.mulVec ((u : GL (Fin r) F') :
                  Matrix (Fin r) (Fin r) F') x) := by rw [hLU, Matrix.one_mulVec],
          show Matrix.mulVec (1 - e) (U.mulVec x) = 0 from by
            rw [Matrix.sub_mulVec, Matrix.one_mulVec]
            have h : Matrix.mulVec e (U.mulVec x) = U.mulVec x := by
              rw [Matrix.mulVec_mulVec, bmSDU_e_mul_U hUL hLU]
            rw [h, sub_self]]
      _ = U.mulVec (Matrix.mulVec (((u : GL (Fin r) F') : Matrix (Fin r) (Fin r) F')) x) := by
          rw [add_zero]
  have hfixW : ∀ (u : ↥(Unitary.SU σe r)) w, w ∈ LinearMap.ker e.mulVecLin →
      Matrix.mulVec (((ιNew u : ↥(Unitary.SU σe n)) : GL (Fin n) F') :
        Matrix (Fin n) (Fin n) F') w = w := by
    intro u w hw
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
    have hLw : L.mulVec w = 0 := by
      apply hUinj
      rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, hUL, hw]
    calc Matrix.mulVec (((ιNew u : ↥(Unitary.SU σe n)) : GL (Fin n) F') :
          Matrix (Fin n) (Fin n) F') w
        = Matrix.mulVec (U * ((u : GL (Fin r) F') : Matrix (Fin r) (Fin r) F') * L +
            (1 - e)) w := by rw [hιNewform u]
      _ = Matrix.mulVec (U * ((u : GL (Fin r) F') : Matrix (Fin r) (Fin r) F') * L) w +
            Matrix.mulVec (1 - e) w := by rw [Matrix.add_mulVec]
      _ = 0 + w := by
        rw [show Matrix.mulVec (U * ((u : GL (Fin r) F') : Matrix (Fin r) (Fin r) F') * L)
              w = 0 from by
          calc Matrix.mulVec (U * ((u : GL (Fin r) F') : Matrix (Fin r) (Fin r) F') * L) w
              = Matrix.mulVec (U * ((u : GL (Fin r) F') : Matrix (Fin r) (Fin r) F'))
                  (Matrix.mulVec L w) := by rw [← Matrix.mulVec_mulVec]
            _ = Matrix.mulVec U (Matrix.mulVec ((u : GL (Fin r) F') :
                  Matrix (Fin r) (Fin r) F') (Matrix.mulVec L w)) := by rw [← Matrix.mulVec_mulVec]
            _ = 0 := by rw [hLw, Matrix.mulVec_zero, Matrix.mulVec_zero],
          show Matrix.mulVec (1 - e) w = w from by
            rw [Matrix.sub_mulVec, Matrix.one_mulVec, hw, sub_zero]]
      _ = w := by rw [zero_add]
  have hsplit : ∀ v : Fin n → F', ∃ x : Fin r → F', ∃ w ∈ LinearMap.ker e.mulVecLin,
      v = U.mulVec x + w := by
    intro v
    refine ⟨L.mulVec v, v - e.mulVec v, ?_, ?_⟩
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub,
        Matrix.mulVec_mulVec, hE2, sub_self]
    · rw [show U.mulVec (L.mulVec v) = e.mulVec v from by
        rw [Matrix.mulVec_mulVec, hUL]]
      abel
  have horth : ∀ x w, w ∈ LinearMap.ker e.mulVecLin →
      bmSDU_h σe.toRingHom (Unitary.antidiag n) (U.mulVec x) w = 0 := by
    intro x w hw
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
    have hEU : Matrix.mulVec e (U.mulVec x) = U.mulVec x := by
      rw [Matrix.mulVec_mulVec, bmSDU_e_mul_U hUL hLU]
    have hadj' := bmSDU_h_adjoint σe.toRingHom (Unitary.antidiag n) e hG (U.mulVec x) w
    rw [hadj, hEU, hw] at hadj'
    simpa [bmSDU_h] using hadj'
  refine ⟨r, ιNew, U.mulVecLin, LinearMap.ker e.mulVecLin, hgood, hιNew, hrangeNew.trans hJ.symm,
    hEinj, ?_, ?_, hfixW, ?_, ?_⟩
  · intro x y
    simpa only [Matrix.mulVecLin_apply] using hiso x y
  · intro u x
    simpa only [Matrix.mulVecLin_apply] using hinter u x
  · intro v
    simpa only [Matrix.mulVecLin_apply] using hsplit v
  · intro x w hw
    simpa only [Matrix.mulVecLin_apply, bmSDU_h] using horth x w hw

theorem exists_blockModel_selfDual_PSU_matrix
    (n g : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hadj : formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e < 2)
    {J' : Subgroup ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype)
      S e,
      glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S e⁆) :
    ∃ (r : ℕ) (ι : (ggU .PSU r (g + 1)).K →*
        ↥(Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n))
      (U : Matrix (Fin n) (Fin r) (GaloisField 2 (2 * (g + 1))))
      (L : Matrix (Fin r) (Fin n) (GaloisField 2 (2 * (g + 1)))),
      Function.Injective ι ∧ ι.range = J' ∧
      ((3 ≤ r ∧ ¬ (r = 3 ∧ 2 ^ (g + 1) = 2)) ∨ (r = 2 ∧ 4 ≤ 2 ^ (g + 1))) ∧
      U * L = e ∧ L * U = 1 ∧
      (∀ x : ↥(Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) r),
        ((ι x : GL (Fin n) (GaloisField 2 (2 * (g + 1)))) :
          Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) =
          U * ((x : GL (Fin r) (GaloisField 2 (2 * (g + 1)))) :
            Matrix (Fin r) (Fin r) (GaloisField 2 (2 * (g + 1)))) * L + (1 - e)) ∧
      Matrix.transpose (U.map
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
            (g + 1)).toRingHom) *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * U =
        (Unitary.antidiag r : Matrix (Fin r) (Fin r) (GaloisField 2 (2 * (g + 1)))) ∧
      Matrix.transpose (e.map
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
            (g + 1)).toRingHom) *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) =
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * e := by
  obtain ⟨r, ι, -, -, -, -, hιinj, hrange, -, -, -, -, -, -, U, L, -, -, hUL, hLU, hform, hiso,
    hadjm⟩ := bmSDU_block_construction n g S hS he hadj hdeg hJe
  have hgood := bmSDU_good_parameters n g r S ι hrange hJe
  have hH := bmSDU_blockGroup_quasisimple n g r S ι hιinj hrange hgood
  have hJ := bmSDU_component_eq n g S hH hJe
  exact ⟨r, ι, U, L, hιinj, hrange.trans hJ.symm, hgood, hUL, hLU, hform, hiso, hadjm⟩

end CFSG.StandardType.ClassicalPosition
