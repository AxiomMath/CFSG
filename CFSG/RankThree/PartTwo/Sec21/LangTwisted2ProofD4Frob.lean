module

public import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4Iso

public noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CFSG.RankThree.PartTwo.Sec8.LangTwisted2Proof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley LangTwistedProof Matrix
open scoped MatrixGroups


variable {L : Type} [Field L] [CharP L 2]

@[expose] def secFrob (Fr : L →+* L) : ModGL TwistTag.D4.tag L →* ModGL TwistTag.D4.tag L :=
  (MulAut.conj (weylElt TwistTag.D4.tag L 2 1)).toMonoidHom.comp (twistHom TwistTag.D4 L Fr)

theorem secFrob_apply (Fr : L →+* L) (g : ModGL TwistTag.D4.tag L) :
    secFrob Fr g = weylElt TwistTag.D4.tag L 2 1 * twistHom TwistTag.D4 L Fr g *
      (weylElt TwistTag.D4.tag L 2 1)⁻¹ := rfl

theorem twistHom_pinnedX_of_two (Fr : L →+* L) {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ) (c : L) :
    twistHom TwistTag.D4 L Fr (pinnedX TwistTag.D4.tag L γ c) =
      pinnedX TwistTag.D4.tag L (permLattice TwistTag.D4.perm γ) (Fr c) := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have e : twistHom TwistTag.D4 L Fr (pinnedX TwistTag.D4.tag L γ c) =
      twistHom TwistTag.D4 L (RingHom.id L) (pinnedX TwistTag.D4.tag L γ (Fr c)) := by
    rw [twistHom_id_eq, twistHom_apply]
    congr 2
    exact Units.ext (entrywise_pinnedX Fr γ c)
  rw [e, twistHom_id_pinnedX h2 hγ]

theorem weylElt_two_conj_pinnedX {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ) (c : L) :
    weylElt TwistTag.D4.tag L 2 1 * pinnedX TwistTag.D4.tag L γ c *
        (weylElt TwistTag.D4.tag L 2 1)⁻¹ =
      pinnedX TwistTag.D4.tag L (reflect TwistTag.D4.tag 2 γ) c := by
  rw [← canonicalRep_simple (coxeterSystem TwistTag.D4.tag) L 2,
    canonicalRep_mul_pinnedX_mul_inv_of_two (CharP.cast_eq_zero L 2) _ hγ, simple_smul]

theorem secFrob_pinnedX (Fr : L →+* L) {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ) (c : L) :
    secFrob Fr (pinnedX TwistTag.D4.tag L γ c) = pinnedX TwistTag.D4.tag L
      (reflect TwistTag.D4.tag 2 (permLattice TwistTag.D4.perm γ)) (Fr c) := by
  rw [secFrob_apply, twistHom_pinnedX_of_two Fr hγ,
    weylElt_two_conj_pinnedX (hγ.permLattice TwistTag.D4.cartan_perm)]

@[expose] def secFrobIdx : Fin 3 → Fin 3 := ![1, 0, 2]

theorem reflect_permLattice_secVec : ∀ j : Fin 3,
    reflect TwistTag.D4.tag 2 (permLattice TwistTag.D4.perm (secVec j 0)) =
        secVec (secFrobIdx j) 1 ∧
      reflect TwistTag.D4.tag 2 (permLattice TwistTag.D4.perm (secVec j 1)) =
        secVec (secFrobIdx j) 2 ∧
      reflect TwistTag.D4.tag 2 (permLattice TwistTag.D4.perm (secVec j 2)) =
        secVec (secFrobIdx j) 0 := by
  decide +kernel

theorem reflect_permLattice_neg_secVec : ∀ j : Fin 3,
    reflect TwistTag.D4.tag 2 (permLattice TwistTag.D4.perm (-secVec j 0)) =
        -secVec (secFrobIdx j) 1 ∧
      reflect TwistTag.D4.tag 2 (permLattice TwistTag.D4.perm (-secVec j 1)) =
        -secVec (secFrobIdx j) 2 ∧
      reflect TwistTag.D4.tag 2 (permLattice TwistTag.D4.perm (-secVec j 2)) =
        -secVec (secFrobIdx j) 0 := by
  decide +kernel

theorem secFrob_triple (Fr : L →+* L) (j : Fin 3) (a b c : L) :
    secFrob Fr (pinnedX TwistTag.D4.tag L (secVec j 0) a *
        pinnedX TwistTag.D4.tag L (secVec j 1) b * pinnedX TwistTag.D4.tag L (secVec j 2) c) =
      pinnedX TwistTag.D4.tag L (secVec (secFrobIdx j) 0) (Fr c) *
        pinnedX TwistTag.D4.tag L (secVec (secFrobIdx j) 1) (Fr a) *
          pinnedX TwistTag.D4.tag L (secVec (secFrobIdx j) 2) (Fr b) := by
  obtain ⟨e0, e1, e2⟩ := reflect_permLattice_secVec j
  rw [map_mul, map_mul, secFrob_pinnedX Fr (isRoot_secVec j 0),
    secFrob_pinnedX Fr (isRoot_secVec j 1), secFrob_pinnedX Fr (isRoot_secVec j 2), e0, e1, e2]
  have c0 := (commute_secVec_pp (L := L) (secFrobIdx j) (i := 0) (k := 1) (Fr c) (Fr a)).mul_right
    (commute_secVec_pp (L := L) (secFrobIdx j) (i := 0) (k := 2) (Fr c) (Fr b))
  rw [← c0.eq, ← mul_assoc]

theorem secFrob_neg_triple (Fr : L →+* L) (j : Fin 3) (a b c : L) :
    secFrob Fr (pinnedX TwistTag.D4.tag L (-secVec j 0) a *
        pinnedX TwistTag.D4.tag L (-secVec j 1) b * pinnedX TwistTag.D4.tag L (-secVec j 2) c) =
      pinnedX TwistTag.D4.tag L (-secVec (secFrobIdx j) 0) (Fr c) *
        pinnedX TwistTag.D4.tag L (-secVec (secFrobIdx j) 1) (Fr a) *
          pinnedX TwistTag.D4.tag L (-secVec (secFrobIdx j) 2) (Fr b) := by
  obtain ⟨e0, e1, e2⟩ := reflect_permLattice_neg_secVec j
  rw [map_mul, map_mul, secFrob_pinnedX Fr (IsRoot.neg (isRoot_secVec j 0)),
    secFrob_pinnedX Fr (IsRoot.neg (isRoot_secVec j 1)),
    secFrob_pinnedX Fr (IsRoot.neg (isRoot_secVec j 2)), e0, e1, e2]
  have c0 := (commute_secVec_nn (L := L) (secFrobIdx j) (i := 0) (k := 1) (Fr c) (Fr a)).mul_right
    (commute_secVec_nn (L := L) (secFrobIdx j) (i := 0) (k := 2) (Fr c) (Fr b))
  rw [← c0.eq, ← mul_assoc]

section Orbits

variable {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) (Fr : L →+* L) (hFr : Fr (μ : L) = (μ : L) ^ 2)

include hμ hFr

theorem secFrob_secOrbitX_zero (c : L) :
    secFrob Fr (secOrbitX μ 0 c) = secOrbitX μ 1 (μ * Fr c) := by
  have h3 : (μ : L) ^ 3 = 1 := by grind
  rw [secOrbitX, secFrob_triple, secOrbitX, secKappa_zero, secKappa_one]
  have e1 : (μ : L) ^ 2 * ((μ : L) * Fr c) = Fr c := by grind
  have e2 : ((μ : L) ^ 2) ^ 2 * ((μ : L) * Fr c) = Fr ((μ : L) * c) := by
    rw [map_mul, hFr]; grind
  have e0 : (μ : L) * Fr c = Fr ((μ : L) ^ 2 * c) := by
    rw [map_mul, map_pow, hFr]; grind
  rw [e1, e2, e0]
  rfl

theorem secFrob_secOrbitX_one (c : L) :
    secFrob Fr (secOrbitX μ 1 c) = secOrbitX μ 0 ((μ : L) ^ 2 * Fr c) := by
  have h3 : (μ : L) ^ 3 = 1 := by grind
  rw [secOrbitX, secFrob_triple, secOrbitX, secKappa_zero, secKappa_one]
  have e1 : (μ : L) * ((μ : L) ^ 2 * Fr c) = Fr c := by grind
  have e2 : (μ : L) ^ 2 * ((μ : L) ^ 2 * Fr c) = Fr ((μ : L) ^ 2 * c) := by
    rw [map_mul, map_pow, hFr]; grind
  have e0 : (μ : L) ^ 2 * Fr c = Fr (((μ : L) ^ 2) ^ 2 * c) := by
    rw [map_mul, map_pow, map_pow, hFr]; grind
  rw [e1, e2, e0]
  rfl

theorem secFrob_secOrbitX_two (c : L) :
    secFrob Fr (secOrbitX μ 2 c) = secOrbitX μ 2 (Fr c) := by
  have hμ3 : μ ^ 3 = 1 := pow_three_of_sq_add hμ
  rw [secOrbitX, secFrob_triple, secOrbitX, secKappa_two hμ3]
  simp only [one_pow, one_mul]
  rfl

theorem secFrob_secOrbitY_zero (c : L) :
    secFrob Fr (secOrbitY μ 0 c) = secOrbitY μ 1 ((μ : L) ^ 2 * Fr c) := by
  have h3 : (μ : L) ^ 3 = 1 := by grind
  rw [secOrbitY, secFrob_neg_triple, secOrbitY, secKappa_zero, secKappa_one]
  have e1 : ((μ : L) ^ 2) ^ 2 * ((μ : L) ^ 2 * Fr c) = Fr c := by
    grind
  have e2 : (μ : L) ^ 2 * ((μ : L) ^ 2 * Fr c) = Fr ((μ : L) ^ 2 * c) := by
    rw [map_mul, map_pow, hFr]; grind
  have e0 : (μ : L) ^ 2 * Fr c = Fr ((μ : L) * c) := by
    rw [map_mul, hFr]
  rw [e1, e2, e0]
  rfl

theorem secFrob_secOrbitY_one (c : L) :
    secFrob Fr (secOrbitY μ 1 c) = secOrbitY μ 0 ((μ : L) * Fr c) := by
  have h3 : (μ : L) ^ 3 = 1 := by grind
  rw [secOrbitY, secFrob_neg_triple, secOrbitY, secKappa_zero, secKappa_one]
  have e1 : (μ : L) ^ 2 * ((μ : L) * Fr c) = Fr c := by grind
  have e2 : (μ : L) * ((μ : L) * Fr c) = Fr (((μ : L) ^ 2) ^ 2 * c) := by
    rw [map_mul, map_pow, map_pow, hFr]
    grind
  have e0 : (μ : L) * Fr c = Fr ((μ : L) ^ 2 * c) := by
    rw [map_mul, map_pow, hFr]; grind
  rw [e1, e2, e0]
  rfl

theorem secFrob_secOrbitY_two (c : L) :
    secFrob Fr (secOrbitY μ 2 c) = secOrbitY μ 2 (Fr c) := by
  have hμ3 : μ ^ 3 = 1 := pow_three_of_sq_add hμ
  rw [secOrbitY, secFrob_neg_triple, secOrbitY, secKappa_two hμ3]
  simp only [one_pow, one_mul]
  rfl

end Orbits

@[expose] def secFrobTuple (Fr : L →+* L) (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    Fin TwistTag.D4.tag.rank → Lˣ :=
  ![Units.map Fr.toMonoidHom (a 0) * Units.map Fr.toMonoidHom (a 2),
    Units.map Fr.toMonoidHom (a 0) * Units.map Fr.toMonoidHom (a 2),
    (Units.map Fr.toMonoidHom (a 2))⁻¹,
    Units.map Fr.toMonoidHom (a 0) * Units.map Fr.toMonoidHom (a 2)]

theorem d4_cases (i : Fin TwistTag.D4.tag.rank) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  revert i
  decide

theorem secFrob_rootDiagUnit (Fr : L →+* L) {a : Fin TwistTag.D4.tag.rank → Lˣ}
    (ha1 : a 1 = a 0) (ha3 : a 3 = a 0) :
    secFrob Fr (rootDiagUnit TwistTag.D4.tag a) =
      rootDiagUnit TwistTag.D4.tag (secFrobTuple Fr a) := by
  rw [secFrob_apply, twistHom_rootDiagUnit_eq, ← canonicalRep_simple (coxeterSystem _) L 2,
    canonicalRep_conj_rootDiagUnit]
  congr 1
  have hinv : (fun i => Units.map Fr.toMonoidHom (a (TwistTag.D4.perm.symm i))) =
      fun i => Units.map Fr.toMonoidHom (a i) := by
    funext i
    rcases d4_cases i with rfl | rfl | rfl | rfl
    · rw [show TwistTag.D4.perm.symm 0 = 3 by decide, ha3]
    · rw [show TwistTag.D4.perm.symm 1 = 0 by decide, ha1]
    · rw [show TwistTag.D4.perm.symm 2 = 2 by decide]
    · rw [show TwistTag.D4.perm.symm 3 = 1 by decide, ha1, ha3]
  rw [hinv]
  funext i
  simp only [weylTuple, simple_inv_D4, simple_smul]
  have e : ∀ v : Fin TwistTag.D4.tag.rank → ℤ,
      rootChar (fun i => Units.map Fr.toMonoidHom (a i)) v =
        Units.map Fr.toMonoidHom (a 0) ^ v 0 * Units.map Fr.toMonoidHom (a 1) ^ v 1 *
          Units.map Fr.toMonoidHom (a 2) ^ v 2 * Units.map Fr.toMonoidHom (a 3) ^ v 3 := by
    intro v
    simp only [rootChar]
    exact Fin.prod_univ_four (fun i => Units.map Fr.toMonoidHom (a i) ^ v i)
  rw [e, ha1, ha3]
  rcases d4_cases i with rfl | rfl | rfl | rfl
  · rw [show reflect TwistTag.D4.tag 2 (Pi.single 0 1) = dv 1 0 1 0 by decide +kernel]
    obtain ⟨d0, d1, d2, d3⟩ := dv_apply 1 0 1 0
    rw [d0, d1, d2, d3]
    simp [secFrobTuple]
  · rw [show reflect TwistTag.D4.tag 2 (Pi.single 1 1) = dv 0 1 1 0 by decide +kernel]
    obtain ⟨d0, d1, d2, d3⟩ := dv_apply 0 1 1 0
    rw [d0, d1, d2, d3]
    simp [secFrobTuple]
  · rw [show reflect TwistTag.D4.tag 2 (Pi.single 2 1) = dv 0 0 (-1) 0 by decide +kernel]
    obtain ⟨d0, d1, d2, d3⟩ := dv_apply 0 0 (-1) 0
    rw [d0, d1, d2, d3]
    simp [secFrobTuple]
  · rw [show reflect TwistTag.D4.tag 2 (Pi.single 3 1) = dv 0 0 1 1 by decide +kernel]
    obtain ⟨d0, d1, d2, d3⟩ := dv_apply 0 0 1 1
    rw [d0, d1, d2, d3]
    simp [secFrobTuple, mul_comm]

@[expose] def secH (μ : L) : Matrix (Fin 3) (Fin 3) L := !![0, 0, 1; 0, μ, 0; 1, 0, 0]

@[expose] def secHinv (μ : L) : Matrix (Fin 3) (Fin 3) L := !![0, 0, 1; 0, μ⁻¹, 0; 1, 0, 0]

theorem secHinv_mul_secH {μ : L} (hμ : μ ≠ 0) : secHinv μ * secH μ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [secH, secHinv, Matrix.mul_apply, Fin.sum_univ_three, hμ]

theorem secH_mul_secHinv {μ : L} (hμ : μ ≠ 0) : secH μ * secHinv μ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [secH, secHinv, Matrix.mul_apply, Fin.sum_univ_three, hμ]

@[expose] def secFrobGL (μ : Lˣ) (Fr : L →+* L) : GL (Fin 3) L →* GL (Fin 3) L where
  toFun g :=
    { val := secH (μ : L) * ((((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)).map Fr)ᵀ *
        secHinv (μ : L)
      inv := secH (μ : L) * (((g : Matrix (Fin 3) (Fin 3) L)).map Fr)ᵀ * secHinv (μ : L)
      val_inv := by
        have e : secH (μ : L) * ((((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)).map Fr)ᵀ *
            secHinv (μ : L) * (secH (μ : L) * (((g : Matrix (Fin 3) (Fin 3) L)).map Fr)ᵀ *
              secHinv (μ : L)) = secH (μ : L) * ((((g : Matrix (Fin 3) (Fin 3) L) *
                ((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L))).map Fr)ᵀ * secHinv (μ : L) := by
          rw [Matrix.map_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (secHinv _), secHinv_mul_secH (Units.ne_zero μ), Matrix.one_mul]
        rw [e, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one Fr (map_zero Fr)
          (map_one Fr), Matrix.transpose_one, Matrix.mul_one, secH_mul_secHinv (Units.ne_zero μ)]
      inv_val := by
        have e : secH (μ : L) * (((g : Matrix (Fin 3) (Fin 3) L)).map Fr)ᵀ * secHinv (μ : L) *
            (secH (μ : L) * ((((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)).map Fr)ᵀ *
              secHinv (μ : L)) = secH (μ : L) * (((((g⁻¹ : GL (Fin 3) L) :
                Matrix (Fin 3) (Fin 3) L) * (g : Matrix (Fin 3) (Fin 3) L))).map Fr)ᵀ *
                  secHinv (μ : L) := by
          rw [Matrix.map_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (secHinv _), secHinv_mul_secH (Units.ne_zero μ), Matrix.one_mul]
        rw [e, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one Fr (map_zero Fr)
          (map_one Fr), Matrix.transpose_one, Matrix.mul_one, secH_mul_secHinv (Units.ne_zero μ)] }
  map_one' := by
    refine Units.ext ?_
    simp only [inv_one, Units.val_one, Matrix.map_one Fr (map_zero Fr) (map_one Fr),
      Matrix.transpose_one, Matrix.mul_one, secH_mul_secHinv (Units.ne_zero μ)]
  map_mul' g g' := by
    refine Units.ext ?_
    simp only [Units.val_mul, _root_.mul_inv_rev, Matrix.map_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (secHinv _) (secH _), secHinv_mul_secH (Units.ne_zero μ),
      Matrix.one_mul]

theorem coe_secFrobGL (μ : Lˣ) (Fr : L →+* L) (g : GL (Fin 3) L) :
    ((secFrobGL μ Fr g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      secH (μ : L) * ((((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)).map Fr)ᵀ *
        secHinv (μ : L) := rfl

theorem secFrobGL_center (μ : Lˣ) (Fr : L →+* L) :
    Subgroup.center (GL (Fin 3) L) ≤ (Subgroup.center (GL (Fin 3) L)).comap (secFrobGL μ Fr) := by
  intro g hg
  rw [Subgroup.mem_comap]
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg ⊢
  obtain ⟨c, rfl⟩ := hg
  refine ⟨Units.map Fr.toMonoidHom c⁻¹, Units.ext ?_⟩
  rw [coe_secFrobGL, ← map_inv, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.scalar_apply,
    Matrix.diagonal_map (map_zero Fr), Matrix.diagonal_transpose, ← Matrix.smul_one_eq_diagonal,
    ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    secH_mul_secHinv (Units.ne_zero μ)]
  rfl

@[expose] def secFrobPGL (μ : Lˣ) (Fr : L →+* L) : PGL(3, L) →* PGL(3, L) :=
  QuotientGroup.map _ _ (secFrobGL μ Fr) (secFrobGL_center μ Fr)

theorem secFrobPGL_mk (μ : Lˣ) (Fr : L →+* L) (g : GL (Fin 3) L) :
    secFrobPGL μ Fr (ProjGenLinGroup.mk g) = ProjGenLinGroup.mk (secFrobGL μ Fr g) := rfl

theorem coe_secFrobGL_tvGL (μ : Lˣ) (Fr : L →+* L) {i j : Fin 3} (hij : i ≠ j) (c : L) :
    ((secFrobGL μ Fr (tvGL hij c) : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      secH (μ : L) * ((Matrix.transvection i j (-c)).map Fr)ᵀ * secHinv (μ : L) := rfl

theorem coe_tvGL {i j : Fin 3} (hij : i ≠ j) (c : L) :
    ((tvGL hij c : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = Matrix.transvection i j c := rfl


section Partners

variable {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) (Fr : L →+* L)

include hμ

theorem inv_eq_sq_of_sq_add : (μ : L)⁻¹ = (μ : L) ^ 2 := by
  have h3 : (μ : L) ^ 2 * μ = 1 := by linear_combination ((μ : L) - 1) * hμ
  exact (eq_inv_of_mul_eq_one_left h3).symm

theorem secFrobGL_tv01 (c : L) :
    secFrobGL μ Fr (tvGL (i := 0) (j := 1) (by decide) c) =
      tvGL (i := 1) (j := 2) (by decide) ((μ : L) * Fr c) := by
  refine Units.ext ?_
  rw [coe_secFrobGL_tvGL, coe_tvGL]
  have hinv := inv_eq_sq_of_sq_add hμ
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [secH, secHinv, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply, Matrix.single_apply, hinv, Matrix.vecMul, dotProduct,
      Matrix.map_apply, Matrix.transpose_apply] <;>
    grind

theorem secFrobGL_tv12 (c : L) :
    secFrobGL μ Fr (tvGL (i := 1) (j := 2) (by decide) c) =
      tvGL (i := 0) (j := 1) (by decide) ((μ : L) ^ 2 * Fr c) := by
  refine Units.ext ?_
  rw [coe_secFrobGL_tvGL, coe_tvGL]
  have hinv := inv_eq_sq_of_sq_add hμ
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [secH, secHinv, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply, Matrix.single_apply, hinv, Matrix.vecMul, dotProduct,
      Matrix.map_apply, Matrix.transpose_apply] <;>
    grind

theorem secFrobGL_tv02 (c : L) :
    secFrobGL μ Fr (tvGL (i := 0) (j := 2) (by decide) c) =
      tvGL (i := 0) (j := 2) (by decide) (Fr c) := by
  refine Units.ext ?_
  rw [coe_secFrobGL_tvGL, coe_tvGL]
  have hinv := inv_eq_sq_of_sq_add hμ
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [secH, secHinv, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply, Matrix.single_apply, hinv, Matrix.vecMul, dotProduct,
      Matrix.map_apply, Matrix.transpose_apply] <;>
    grind

theorem secFrobGL_tv10 (c : L) :
    secFrobGL μ Fr (tvGL (i := 1) (j := 0) (by decide) c) =
      tvGL (i := 2) (j := 1) (by decide) ((μ : L) ^ 2 * Fr c) := by
  refine Units.ext ?_
  rw [coe_secFrobGL_tvGL, coe_tvGL]
  have hinv := inv_eq_sq_of_sq_add hμ
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [secH, secHinv, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply, Matrix.single_apply, hinv, Matrix.vecMul, dotProduct,
      Matrix.map_apply, Matrix.transpose_apply] <;>
    grind

theorem secFrobGL_tv21 (c : L) :
    secFrobGL μ Fr (tvGL (i := 2) (j := 1) (by decide) c) =
      tvGL (i := 1) (j := 0) (by decide) ((μ : L) * Fr c) := by
  refine Units.ext ?_
  rw [coe_secFrobGL_tvGL, coe_tvGL]
  have hinv := inv_eq_sq_of_sq_add hμ
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [secH, secHinv, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply, Matrix.single_apply, hinv, Matrix.vecMul, dotProduct,
      Matrix.map_apply, Matrix.transpose_apply] <;>
    grind

theorem secFrobGL_tv20 (c : L) :
    secFrobGL μ Fr (tvGL (i := 2) (j := 0) (by decide) c) =
      tvGL (i := 2) (j := 0) (by decide) (Fr c) := by
  refine Units.ext ?_
  rw [coe_secFrobGL_tvGL, coe_tvGL]
  have hinv := inv_eq_sq_of_sq_add hμ
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [secH, secHinv, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply, Matrix.single_apply, hinv, Matrix.vecMul, dotProduct,
      Matrix.map_apply, Matrix.transpose_apply] <;>
    grind

end Partners

theorem mk_secFrobGL_dgGL (μ : Lˣ) (Fr : L →+* L) (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    ProjGenLinGroup.mk (secFrobGL μ Fr (dgGL a)) =
      ProjGenLinGroup.mk (dgGL (secFrobTuple Fr a)) := by
  have hs : (Units.map Fr.toMonoidHom (a 0) : L) = Fr (a 0) := rfl
  have hu : (Units.map Fr.toMonoidHom (a 2) : L) = Fr (a 2) := rfl
  have h0 : Fr (a 0 : L) ≠ 0 := (map_ne_zero Fr).2 (Units.ne_zero _)
  have h2 : Fr (a 2 : L) ≠ 0 := (map_ne_zero Fr).2 (Units.ne_zero _)
  have hμ0 : (μ : L) ≠ 0 := Units.ne_zero μ
  rw [ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.map Fr.toMonoidHom (a 0) ^ 2 * Units.map Fr.toMonoidHom (a 2), Units.ext ?_⟩
  rw [Units.val_mul, coe_secFrobGL, Matrix.GeneralLinearGroup.coe_scalar]
  change secH (μ : L) * ((secTorDinv a).map Fr)ᵀ * secHinv (μ : L) * Matrix.scalar (Fin 3) _ =
    secTorD (secFrobTuple Fr a)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [secH, secHinv, secTorD, secTorDinv, secFrobTuple, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal_apply, Matrix.vecMul, dotProduct, Matrix.map_apply, Matrix.transpose_apply,
      hs, hu, hμ0, h0, h2] <;>
    field_simp

theorem secGraph_secFrob [IsAlgClosed L] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {Fr : L →+* L} (hFr : Fr (μ : L) = (μ : L) ^ 2) {m : ModGL TwistTag.D4.tag L}
    (hm : m ∈ secM μ) :
    ∀ P, (m, P) ∈ secGraph μ → (secFrob Fr m, secFrobPGL μ Fr P) ∈ secGraph μ := by
  induction hm using Subgroup.iSup_induction' with
  | hp o x hx =>
    intro P hP
    rcases o with _ | ⟨j, _ | _⟩
    · obtain ⟨htT, htP⟩ := hx
      obtain ⟨a, ha1, ha3, rfl⟩ := exists_rootDiagUnit_of_mem_torus_fixed htT htP
      have hPa := secGraph_snd_eq hP (mem_secGraph (mem_secM_of_mem_torus μ htT htP)
        (adRel_rootDiagUnit μ ha1 ha3))
      subst hPa
      rw [secFrobPGL_mk, mk_secFrobGL_dgGL, secFrob_rootDiagUnit Fr ha1 ha3]
      set a' := secFrobTuple Fr a with ha'
      have ha'1 : a' 1 = a' 0 := rfl
      have ha'3 : a' 3 = a' 0 := rfl
      have hT : rootDiagUnit TwistTag.D4.tag a' ∈ torusGroup TwistTag.D4.tag L :=
        rootDiagUnit_mem_torusGroup a'
      have hP' : rootDiagUnit TwistTag.D4.tag a' ∈
          graphCentralizer TwistTag.D4.tag L (diagramMap TwistTag.D4 L) := by
        have hTG : torusGroup TwistTag.D4.tag L ≤ adjointGroup TwistTag.D4.tag L :=
          (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
        refine Subgroup.mem_inf.2 ⟨hTG hT, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        refine (rootDiagUnit_commute_diagramMap_iff a').2 ?_
        funext i
        rcases d4_cases i with rfl | rfl | rfl | rfl
        · rw [show TwistTag.D4.perm.symm 0 = 3 by decide, ha'3]
        · rw [show TwistTag.D4.perm.symm 1 = 0 by decide, ha'1]
        · rw [show TwistTag.D4.perm.symm 2 = 2 by decide]
        · rw [show TwistTag.D4.perm.symm 3 = 1 by decide, ha'1, ha'3]
      exact mem_secGraph (mem_secM_of_mem_torus μ hT hP') (adRel_rootDiagUnit μ ha'1 ha'3)
    · obtain ⟨c, rfl⟩ := hx
      fin_cases j
      · have hPc := secGraph_snd_eq hP (mem_secGraph (secOrbitY_mem_secM μ 0 _)
          (adRel_secOrbitY_zero μ hμ (Multiplicative.toAdd c)))
        subst hPc
        change (secFrob Fr (secOrbitY μ 0 _), _) ∈ _
        rw [secFrobPGL_mk, secFrobGL_tv10 hμ, secFrob_secOrbitY_zero hμ Fr hFr]
        exact mem_secGraph (secOrbitY_mem_secM μ 1 _) (adRel_secOrbitY_one μ hμ _)
      · have hPc := secGraph_snd_eq hP (mem_secGraph (secOrbitY_mem_secM μ 1 _)
          (adRel_secOrbitY_one μ hμ (Multiplicative.toAdd c)))
        subst hPc
        change (secFrob Fr (secOrbitY μ 1 _), _) ∈ _
        rw [secFrobPGL_mk, secFrobGL_tv21 hμ, secFrob_secOrbitY_one hμ Fr hFr]
        exact mem_secGraph (secOrbitY_mem_secM μ 0 _) (adRel_secOrbitY_zero μ hμ _)
      · have hPc := secGraph_snd_eq hP (mem_secGraph (secOrbitY_mem_secM μ 2 _)
          (adRel_secOrbitY_two μ hμ (Multiplicative.toAdd c)))
        subst hPc
        change (secFrob Fr (secOrbitY μ 2 _), _) ∈ _
        rw [secFrobPGL_mk, secFrobGL_tv20 hμ, secFrob_secOrbitY_two hμ Fr hFr]
        exact mem_secGraph (secOrbitY_mem_secM μ 2 _) (adRel_secOrbitY_two μ hμ _)
    · obtain ⟨c, rfl⟩ := hx
      fin_cases j
      · have hPc := secGraph_snd_eq hP (mem_secGraph (secOrbitX_mem_secM μ 0 _)
          (adRel_secOrbitX_zero μ hμ (Multiplicative.toAdd c)))
        subst hPc
        change (secFrob Fr (secOrbitX μ 0 _), _) ∈ _
        rw [secFrobPGL_mk, secFrobGL_tv01 hμ, secFrob_secOrbitX_zero hμ Fr hFr]
        exact mem_secGraph (secOrbitX_mem_secM μ 1 _) (adRel_secOrbitX_one μ hμ _)
      · have hPc := secGraph_snd_eq hP (mem_secGraph (secOrbitX_mem_secM μ 1 _)
          (adRel_secOrbitX_one μ hμ (Multiplicative.toAdd c)))
        subst hPc
        change (secFrob Fr (secOrbitX μ 1 _), _) ∈ _
        rw [secFrobPGL_mk, secFrobGL_tv12 hμ, secFrob_secOrbitX_one hμ Fr hFr]
        exact mem_secGraph (secOrbitX_mem_secM μ 0 _) (adRel_secOrbitX_zero μ hμ _)
      · have hPc := secGraph_snd_eq hP (mem_secGraph (secOrbitX_mem_secM μ 2 _)
          (adRel_secOrbitX_two μ hμ (Multiplicative.toAdd c)))
        subst hPc
        change (secFrob Fr (secOrbitX μ 2 _), _) ∈ _
        rw [secFrobPGL_mk, secFrobGL_tv02 hμ, secFrob_secOrbitX_two hμ Fr hFr]
        exact mem_secGraph (secOrbitX_mem_secM μ 2 _) (adRel_secOrbitX_two μ hμ _)
  | h1 =>
    intro P hP
    have hP1 := secGraph_snd_eq hP (secGraph μ).one_mem
    subst hP1
    rw [map_one, map_one]
    exact (secGraph μ).one_mem
  | hmul x y hx hy ihx ihy =>
    intro P hP
    obtain ⟨Px, hPx⟩ := exists_secGraph_of_mem_secM hμ hx
    obtain ⟨Py, hPy⟩ := exists_secGraph_of_mem_secM hμ hy
    have hxy : (x * y, Px * Py) ∈ secGraph μ := (secGraph μ).mul_mem hPx hPy
    have hP' := secGraph_snd_eq hP hxy
    subst hP'
    have h := (secGraph μ).mul_mem (ihx Px hPx) (ihy Py hPy)
    rw [Prod.mk_mul_mk, ← map_mul, ← map_mul] at h
    exact h

@[expose] def secFixG (μ : Lˣ) (Fr : L →+* L) : Subgroup (ModGL TwistTag.D4.tag L) :=
  secM μ ⊓ (secFrob Fr).eqLocus (MonoidHom.id _)

@[expose] def pglFix (μ : Lˣ) (Fr : L →+* L) : Subgroup PGL(3, L) :=
  (secFrobPGL μ Fr).eqLocus (MonoidHom.id _)

theorem secPhi_mem_pglFix [IsAlgClosed L] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {Fr : L →+* L} (hFr : Fr (μ : L) = (μ : L) ^ 2) {m : ModGL TwistTag.D4.tag L}
    (hm : m ∈ secFixG μ Fr) : secPhi μ hμ ⟨m, hm.1⟩ ∈ pglFix μ Fr := by
  have h1 := secPhi_mem hμ ⟨m, hm.1⟩
  have h2 := secGraph_secFrob hμ hFr hm.1 _ h1
  have hfix : secFrob Fr m = m := hm.2
  rw [hfix] at h2
  exact (secGraph_snd_eq h1 h2).symm

@[expose] def secFixHom [IsAlgClosed L] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {Fr : L →+* L} (hFr : Fr (μ : L) = (μ : L) ^ 2) : secFixG μ Fr →* pglFix μ Fr where
  toFun m := ⟨secPhi μ hμ ⟨m.1, m.2.1⟩, secPhi_mem_pglFix hμ hFr m.2⟩
  map_one' := Subtype.ext (map_one (secPhi μ hμ))
  map_mul' m m' := Subtype.ext (map_mul (secPhi μ hμ) ⟨m.1, m.2.1⟩ ⟨m'.1, m'.2.1⟩)

theorem secFixHom_bijective [IsAlgClosed L] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {Fr : L →+* L} (hFr : Fr (μ : L) = (μ : L) ^ 2) :
    Function.Bijective (secFixHom hμ hFr) := by
  refine ⟨fun m m' h => ?_, fun P => ?_⟩
  · have h' : secPhi μ hμ ⟨m.1, m.2.1⟩ = secPhi μ hμ ⟨m'.1, m'.2.1⟩ :=
      congrArg Subtype.val h
    have := (secPhi μ hμ).injective h'
    exact Subtype.ext (congrArg (fun x : secM μ => (x : ModGL TwistTag.D4.tag L)) this)
  · set m := (secPhi μ hμ).symm P.1 with hm
    have hmP : ((m : ModGL TwistTag.D4.tag L), P.1) ∈ secGraph μ := by
      have := secPhi_mem hμ m
      rwa [hm, MulEquiv.apply_symm_apply] at this
    have h2 := secGraph_secFrob hμ hFr m.2 _ hmP
    have hPfix : secFrobPGL μ Fr P.1 = P.1 := P.2
    rw [hPfix] at h2
    have h3 := (secGraph μ).mul_mem h2 ((secGraph μ).inv_mem hmP)
    rw [Prod.inv_mk, Prod.mk_mul_mk, mul_inv_cancel] at h3
    have h4 := eq_one_of_mem_secGraph hμ h3
    have hfix : secFrob Fr (m : ModGL TwistTag.D4.tag L) = m := mul_inv_eq_one.1 h4
    refine ⟨⟨m, m.2, hfix⟩, Subtype.ext ?_⟩
    change secPhi μ hμ ⟨m.1, m.2⟩ = P.1
    rw [hm]
    exact MulEquiv.apply_symm_apply _ _

@[expose] def secFixEquiv [IsAlgClosed L] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {Fr : L →+* L} (hFr : Fr (μ : L) = (μ : L) ^ 2) : secFixG μ Fr ≃* pglFix μ Fr :=
  MulEquiv.ofBijective _ (secFixHom_bijective hμ hFr)

end CFSG.RankThree.PartTwo.Sec8.LangTwisted2Proof
