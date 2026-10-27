module

public import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4Unitary

public noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley LangTwistedProof LangTwisted2Proof Matrix
open scoped MatrixGroups
open CFSG.Assembly.RankThreeEven (projImage)


variable {L : Type} [Field L] [CharP L 2]

theorem permLattice_secVec : ∀ j : Fin 3,
    permLattice TwistTag.D4.perm (secVec j 0) = secVec j 1 ∧
      permLattice TwistTag.D4.perm (secVec j 1) = secVec j 2 ∧
      permLattice TwistTag.D4.perm (secVec j 2) = secVec j 0 := by
  decide +kernel

theorem permLattice_neg_secVec : ∀ j : Fin 3,
    permLattice TwistTag.D4.perm (-secVec j 0) = -secVec j 1 ∧
      permLattice TwistTag.D4.perm (-secVec j 1) = -secVec j 2 ∧
      permLattice TwistTag.D4.perm (-secVec j 2) = -secVec j 0 := by
  decide +kernel

theorem twistHom_triple (Fr : L →+* L) (j : Fin 3) (a b c : L) :
    twistHom TwistTag.D4 L Fr (pinnedX TwistTag.D4.tag L (secVec j 0) a *
        pinnedX TwistTag.D4.tag L (secVec j 1) b * pinnedX TwistTag.D4.tag L (secVec j 2) c) =
      pinnedX TwistTag.D4.tag L (secVec j 0) (Fr c) *
        pinnedX TwistTag.D4.tag L (secVec j 1) (Fr a) *
          pinnedX TwistTag.D4.tag L (secVec j 2) (Fr b) := by
  obtain ⟨e0, e1, e2⟩ := permLattice_secVec j
  rw [map_mul, map_mul, twistHom_pinnedX_of_two Fr (isRoot_secVec j 0),
    twistHom_pinnedX_of_two Fr (isRoot_secVec j 1), twistHom_pinnedX_of_two Fr (isRoot_secVec j 2),
    e0, e1, e2]
  have c0 := (commute_secVec_pp (L := L) j (i := 0) (k := 1) (Fr c) (Fr a)).mul_right
    (commute_secVec_pp (L := L) j (i := 0) (k := 2) (Fr c) (Fr b))
  rw [← c0.eq, ← mul_assoc]

theorem twistHom_neg_triple (Fr : L →+* L) (j : Fin 3) (a b c : L) :
    twistHom TwistTag.D4 L Fr (pinnedX TwistTag.D4.tag L (-secVec j 0) a *
        pinnedX TwistTag.D4.tag L (-secVec j 1) b * pinnedX TwistTag.D4.tag L (-secVec j 2) c) =
      pinnedX TwistTag.D4.tag L (-secVec j 0) (Fr c) *
        pinnedX TwistTag.D4.tag L (-secVec j 1) (Fr a) *
          pinnedX TwistTag.D4.tag L (-secVec j 2) (Fr b) := by
  obtain ⟨e0, e1, e2⟩ := permLattice_neg_secVec j
  rw [map_mul, map_mul, twistHom_pinnedX_of_two Fr (IsRoot.neg (isRoot_secVec j 0)),
    twistHom_pinnedX_of_two Fr (IsRoot.neg (isRoot_secVec j 1)),
    twistHom_pinnedX_of_two Fr (IsRoot.neg (isRoot_secVec j 2)), e0, e1, e2]
  have c0 := (commute_secVec_nn (L := L) j (i := 0) (k := 1) (Fr c) (Fr a)).mul_right
    (commute_secVec_nn (L := L) j (i := 0) (k := 2) (Fr c) (Fr b))
  rw [← c0.eq, ← mul_assoc]

section Orbits

variable {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) (Fr : L →+* L) (hFr : Fr (μ : L) = (μ : L))

include hμ hFr

theorem twistHom_secOrbitX_zero (c : L) :
    twistHom TwistTag.D4 L Fr (secOrbitX μ 0 c) = secOrbitX μ 0 ((μ : L) ^ 2 * Fr c) := by
  have h3 : (μ : L) ^ 3 = 1 := by grind
  rw [secOrbitX, twistHom_triple, secOrbitX, secKappa_zero]
  have e0 : Fr ((μ : L) ^ 2 * c) = (μ : L) ^ 2 * Fr c := by rw [map_mul, map_pow, hFr]
  have e1 : (μ : L) * ((μ : L) ^ 2 * Fr c) = Fr c := by grind
  have e2 : (μ : L) ^ 2 * ((μ : L) ^ 2 * Fr c) = Fr ((μ : L) * c) := by
    rw [map_mul, hFr]; grind
  rw [e0, e1, e2]

theorem twistHom_secOrbitX_one (c : L) :
    twistHom TwistTag.D4 L Fr (secOrbitX μ 1 c) = secOrbitX μ 1 ((μ : L) * Fr c) := by
  have h3 : (μ : L) ^ 3 = 1 := by grind
  rw [secOrbitX, twistHom_triple, secOrbitX, secKappa_one]
  have e0 : Fr (((μ : L) ^ 2) ^ 2 * c) = (μ : L) * Fr c := by
    rw [map_mul, map_pow, map_pow, hFr]; grind
  have e1 : (μ : L) ^ 2 * ((μ : L) * Fr c) = Fr c := by grind
  have e2 : ((μ : L) ^ 2) ^ 2 * ((μ : L) * Fr c) = Fr ((μ : L) ^ 2 * c) := by
    rw [map_mul, map_pow, hFr]; grind
  rw [e0, e1, e2]

theorem twistHom_secOrbitX_two (c : L) :
    twistHom TwistTag.D4 L Fr (secOrbitX μ 2 c) = secOrbitX μ 2 (Fr c) := by
  have hμ3 : μ ^ 3 = 1 := pow_three_of_sq_add hμ
  rw [secOrbitX, twistHom_triple, secOrbitX, secKappa_two hμ3]
  simp only [one_pow, one_mul]

theorem twistHom_secOrbitY_zero (c : L) :
    twistHom TwistTag.D4 L Fr (secOrbitY μ 0 c) = secOrbitY μ 0 ((μ : L) * Fr c) := by
  have h3 : (μ : L) ^ 3 = 1 := by grind
  rw [secOrbitY, twistHom_neg_triple, secOrbitY, secKappa_zero]
  have e0 : Fr ((μ : L) * c) = (μ : L) * Fr c := by rw [map_mul, hFr]
  have e1 : (μ : L) ^ 2 * ((μ : L) * Fr c) = Fr c := by grind
  have e2 : (μ : L) * ((μ : L) * Fr c) = Fr ((μ : L) ^ 2 * c) := by
    rw [map_mul, map_pow, hFr]; grind
  rw [e0, e1, e2]

theorem twistHom_secOrbitY_one (c : L) :
    twistHom TwistTag.D4 L Fr (secOrbitY μ 1 c) = secOrbitY μ 1 ((μ : L) ^ 2 * Fr c) := by
  have h3 : (μ : L) ^ 3 = 1 := by grind
  rw [secOrbitY, twistHom_neg_triple, secOrbitY, secKappa_one]
  have e0 : Fr ((μ : L) ^ 2 * c) = (μ : L) ^ 2 * Fr c := by rw [map_mul, map_pow, hFr]
  have e1 : ((μ : L) ^ 2) ^ 2 * ((μ : L) ^ 2 * Fr c) = Fr c := by grind
  have e2 : (μ : L) ^ 2 * ((μ : L) ^ 2 * Fr c) = Fr (((μ : L) ^ 2) ^ 2 * c) := by
    rw [map_mul, map_pow, map_pow, hFr]; grind
  rw [e0, e1, e2]

theorem twistHom_secOrbitY_two (c : L) :
    twistHom TwistTag.D4 L Fr (secOrbitY μ 2 c) = secOrbitY μ 2 (Fr c) := by
  have hμ3 : μ ^ 3 = 1 := pow_three_of_sq_add hμ
  rw [secOrbitY, twistHom_neg_triple, secOrbitY, secKappa_two hμ3]
  simp only [one_pow, one_mul]

end Orbits


theorem twistHom_rootDiagUnit (Fr : L →+* L) {a : Fin TwistTag.D4.tag.rank → Lˣ}
    (ha1 : a 1 = a 0) (ha3 : a 3 = a 0) :
    twistHom TwistTag.D4 L Fr (rootDiagUnit TwistTag.D4.tag a) =
      rootDiagUnit TwistTag.D4.tag (fun i => Units.map Fr.toMonoidHom (a i)) := by
  rw [twistHom_rootDiagUnit_eq]
  congr 1
  funext i
  rcases d4_cases i with rfl | rfl | rfl | rfl
  · rw [show TwistTag.D4.perm.symm 0 = 3 by decide, ha3]
  · rw [show TwistTag.D4.perm.symm 1 = 0 by decide, ha1]
  · rw [show TwistTag.D4.perm.symm 2 = 2 by decide]
  · rw [show TwistTag.D4.perm.symm 3 = 1 by decide, ha1, ha3]

@[expose] def evenD (μ : Lˣ) : GL (Fin 3) L where
  val := Matrix.diagonal ![1, (μ : L), 1]
  inv := Matrix.diagonal ![1, (μ : L)⁻¹, 1]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    fin_cases k <;> simp [Units.ne_zero μ]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    fin_cases k <;> simp [Units.ne_zero μ]

@[expose] def evenFrobGL (μ : Lˣ) (Fr : L →+* L) : GL (Fin 3) L →* GL (Fin 3) L :=
  (MulAut.conj (evenD μ)).toMonoidHom.comp (Matrix.GeneralLinearGroup.map Fr)

theorem coe_evenFrobGL (μ : Lˣ) (Fr : L →+* L) (g : GL (Fin 3) L) :
    ((evenFrobGL μ Fr g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal ![1, (μ : L), 1] * (g : Matrix (Fin 3) (Fin 3) L).map Fr *
        Matrix.diagonal ![1, (μ : L)⁻¹, 1] := by
  simp only [evenFrobGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Units.val_mul, Matrix.GeneralLinearGroup.val_map_apply]
  rfl

theorem evenFrobGL_center (μ : Lˣ) (Fr : L →+* L) :
    Subgroup.center (GL (Fin 3) L) ≤ (Subgroup.center (GL (Fin 3) L)).comap (evenFrobGL μ Fr) := by
  intro g hg
  rw [Subgroup.mem_comap]
  have h1 : Matrix.GeneralLinearGroup.map Fr g ∈ Subgroup.center (GL (Fin 3) L) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg ⊢
    obtain ⟨c, rfl⟩ := hg
    refine ⟨Units.map Fr.toMonoidHom c, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.val_map_apply, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.scalar_apply,
      Matrix.diagonal_map (map_zero Fr)]
    rfl
  change evenD μ * Matrix.GeneralLinearGroup.map Fr g * (evenD μ)⁻¹ ∈ _
  rw [Subgroup.mem_center_iff.mp h1 (evenD μ), mul_inv_cancel_right]
  exact h1

@[expose] def evenFrobPGL (μ : Lˣ) (Fr : L →+* L) : PGL(3, L) →* PGL(3, L) :=
  QuotientGroup.map _ _ (evenFrobGL μ Fr) (evenFrobGL_center μ Fr)

theorem evenFrobPGL_mk (μ : Lˣ) (Fr : L →+* L) (g : GL (Fin 3) L) :
    evenFrobPGL μ Fr (ProjGenLinGroup.mk g) = ProjGenLinGroup.mk (evenFrobGL μ Fr g) := rfl

section Partners

variable {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) (Fr : L →+* L)

include hμ

theorem evenFrobGL_tv01 (c : L) :
    evenFrobGL μ Fr (tvGL (i := 0) (j := 1) (by decide) c) =
      tvGL (i := 0) (j := 1) (by decide) ((μ : L) ^ 2 * Fr c) := by
  refine Units.ext ?_
  rw [coe_evenFrobGL, coe_tvGL, coe_tvGL]
  have hinv := inv_eq_sq_of_sq_add hμ
  have h3 : (μ : L) ^ 3 = 1 := by linear_combination ((μ : L) - 1) * hμ
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.single_apply, hinv, Matrix.map_apply, Matrix.diagonal_apply]
  all_goals grind

theorem evenFrobGL_tv12 (c : L) :
    evenFrobGL μ Fr (tvGL (i := 1) (j := 2) (by decide) c) =
      tvGL (i := 1) (j := 2) (by decide) ((μ : L) * Fr c) := by
  refine Units.ext ?_
  rw [coe_evenFrobGL, coe_tvGL, coe_tvGL]
  have hinv := inv_eq_sq_of_sq_add hμ
  have h3 : (μ : L) ^ 3 = 1 := by linear_combination ((μ : L) - 1) * hμ
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.single_apply, hinv, Matrix.map_apply, Matrix.diagonal_apply]
  all_goals grind

theorem evenFrobGL_tv02 (c : L) :
    evenFrobGL μ Fr (tvGL (i := 0) (j := 2) (by decide) c) =
      tvGL (i := 0) (j := 2) (by decide) (Fr c) := by
  refine Units.ext ?_
  rw [coe_evenFrobGL, coe_tvGL, coe_tvGL]
  have hinv := inv_eq_sq_of_sq_add hμ
  have h3 : (μ : L) ^ 3 = 1 := by linear_combination ((μ : L) - 1) * hμ
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.single_apply, hinv, Matrix.map_apply, Matrix.diagonal_apply]
  all_goals grind

theorem evenFrobGL_tv10 (c : L) :
    evenFrobGL μ Fr (tvGL (i := 1) (j := 0) (by decide) c) =
      tvGL (i := 1) (j := 0) (by decide) ((μ : L) * Fr c) := by
  refine Units.ext ?_
  rw [coe_evenFrobGL, coe_tvGL, coe_tvGL]
  have hinv := inv_eq_sq_of_sq_add hμ
  have h3 : (μ : L) ^ 3 = 1 := by linear_combination ((μ : L) - 1) * hμ
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.single_apply, hinv, Matrix.map_apply, Matrix.diagonal_apply]
  all_goals grind

theorem evenFrobGL_tv21 (c : L) :
    evenFrobGL μ Fr (tvGL (i := 2) (j := 1) (by decide) c) =
      tvGL (i := 2) (j := 1) (by decide) ((μ : L) ^ 2 * Fr c) := by
  refine Units.ext ?_
  rw [coe_evenFrobGL, coe_tvGL, coe_tvGL]
  have hinv := inv_eq_sq_of_sq_add hμ
  have h3 : (μ : L) ^ 3 = 1 := by linear_combination ((μ : L) - 1) * hμ
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.single_apply, hinv, Matrix.map_apply, Matrix.diagonal_apply]
  all_goals grind

theorem evenFrobGL_tv20 (c : L) :
    evenFrobGL μ Fr (tvGL (i := 2) (j := 0) (by decide) c) =
      tvGL (i := 2) (j := 0) (by decide) (Fr c) := by
  refine Units.ext ?_
  rw [coe_evenFrobGL, coe_tvGL, coe_tvGL]
  have hinv := inv_eq_sq_of_sq_add hμ
  have h3 : (μ : L) ^ 3 = 1 := by linear_combination ((μ : L) - 1) * hμ
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.single_apply, hinv, Matrix.map_apply, Matrix.diagonal_apply]
  all_goals grind

end Partners

theorem evenFrobGL_dgGL (μ : Lˣ) (Fr : L →+* L) (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    evenFrobGL μ Fr (dgGL a) = dgGL (fun i => Units.map Fr.toMonoidHom (a i)) := by
  refine Units.ext ?_
  rw [coe_evenFrobGL]
  change Matrix.diagonal ![1, (μ : L), 1] * (secTorD a).map Fr *
    Matrix.diagonal ![1, (μ : L)⁻¹, 1] = secTorD (fun i => Units.map Fr.toMonoidHom (a i))
  have hμ0 : (μ : L) ≠ 0 := Units.ne_zero μ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [secTorD, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply,
      Matrix.map_apply, hμ0]
  field_simp


theorem secGraph_twistHom [IsAlgClosed L] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {Fr : L →+* L} (hFr : Fr (μ : L) = (μ : L)) {m : ModGL TwistTag.D4.tag L}
    (hm : m ∈ secM μ) :
    ∀ P, (m, P) ∈ secGraph μ →
      (twistHom TwistTag.D4 L Fr m, evenFrobPGL μ Fr P) ∈ secGraph μ := by
  induction hm using Subgroup.iSup_induction' with
  | hp o x hx =>
    intro P hP
    rcases o with _ | ⟨j, _ | _⟩
    · obtain ⟨htT, htP⟩ := hx
      obtain ⟨a, ha1, ha3, rfl⟩ := exists_rootDiagUnit_of_mem_torus_fixed htT htP
      have hPa := secGraph_snd_eq hP (mem_secGraph (mem_secM_of_mem_torus μ htT htP)
        (adRel_rootDiagUnit μ ha1 ha3))
      subst hPa
      rw [evenFrobPGL_mk, evenFrobGL_dgGL, twistHom_rootDiagUnit Fr ha1 ha3]
      set a' : Fin TwistTag.D4.tag.rank → Lˣ := fun i => Units.map Fr.toMonoidHom (a i) with ha'
      have ha'1 : a' 1 = a' 0 := by
        rw [ha']
        exact congrArg (Units.map Fr.toMonoidHom) ha1
      have ha'3 : a' 3 = a' 0 := by
        rw [ha']
        exact congrArg (Units.map Fr.toMonoidHom) ha3
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
        change (twistHom TwistTag.D4 L Fr (secOrbitY μ 0 _), _) ∈ _
        rw [evenFrobPGL_mk, evenFrobGL_tv10 hμ, twistHom_secOrbitY_zero hμ Fr hFr]
        exact mem_secGraph (secOrbitY_mem_secM μ 0 _) (adRel_secOrbitY_zero μ hμ _)
      · have hPc := secGraph_snd_eq hP (mem_secGraph (secOrbitY_mem_secM μ 1 _)
          (adRel_secOrbitY_one μ hμ (Multiplicative.toAdd c)))
        subst hPc
        change (twistHom TwistTag.D4 L Fr (secOrbitY μ 1 _), _) ∈ _
        rw [evenFrobPGL_mk, evenFrobGL_tv21 hμ, twistHom_secOrbitY_one hμ Fr hFr]
        exact mem_secGraph (secOrbitY_mem_secM μ 1 _) (adRel_secOrbitY_one μ hμ _)
      · have hPc := secGraph_snd_eq hP (mem_secGraph (secOrbitY_mem_secM μ 2 _)
          (adRel_secOrbitY_two μ hμ (Multiplicative.toAdd c)))
        subst hPc
        change (twistHom TwistTag.D4 L Fr (secOrbitY μ 2 _), _) ∈ _
        rw [evenFrobPGL_mk, evenFrobGL_tv20 hμ, twistHom_secOrbitY_two hμ Fr hFr]
        exact mem_secGraph (secOrbitY_mem_secM μ 2 _) (adRel_secOrbitY_two μ hμ _)
    · obtain ⟨c, rfl⟩ := hx
      fin_cases j
      · have hPc := secGraph_snd_eq hP (mem_secGraph (secOrbitX_mem_secM μ 0 _)
          (adRel_secOrbitX_zero μ hμ (Multiplicative.toAdd c)))
        subst hPc
        change (twistHom TwistTag.D4 L Fr (secOrbitX μ 0 _), _) ∈ _
        rw [evenFrobPGL_mk, evenFrobGL_tv01 hμ, twistHom_secOrbitX_zero hμ Fr hFr]
        exact mem_secGraph (secOrbitX_mem_secM μ 0 _) (adRel_secOrbitX_zero μ hμ _)
      · have hPc := secGraph_snd_eq hP (mem_secGraph (secOrbitX_mem_secM μ 1 _)
          (adRel_secOrbitX_one μ hμ (Multiplicative.toAdd c)))
        subst hPc
        change (twistHom TwistTag.D4 L Fr (secOrbitX μ 1 _), _) ∈ _
        rw [evenFrobPGL_mk, evenFrobGL_tv12 hμ, twistHom_secOrbitX_one hμ Fr hFr]
        exact mem_secGraph (secOrbitX_mem_secM μ 1 _) (adRel_secOrbitX_one μ hμ _)
      · have hPc := secGraph_snd_eq hP (mem_secGraph (secOrbitX_mem_secM μ 2 _)
          (adRel_secOrbitX_two μ hμ (Multiplicative.toAdd c)))
        subst hPc
        change (twistHom TwistTag.D4 L Fr (secOrbitX μ 2 _), _) ∈ _
        rw [evenFrobPGL_mk, evenFrobGL_tv02 hμ, twistHom_secOrbitX_two hμ Fr hFr]
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

@[expose] def secFixEvenG (μ : Lˣ) (Fr : L →+* L) : Subgroup (ModGL TwistTag.D4.tag L) :=
  secM μ ⊓ (twistHom TwistTag.D4 L Fr).eqLocus (MonoidHom.id _)

@[expose] def pglFixEven (μ : Lˣ) (Fr : L →+* L) : Subgroup PGL(3, L) :=
  (evenFrobPGL μ Fr).eqLocus (MonoidHom.id _)

theorem secPhi_mem_pglFixEven [IsAlgClosed L] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {Fr : L →+* L} (hFr : Fr (μ : L) = (μ : L)) {m : ModGL TwistTag.D4.tag L}
    (hm : m ∈ secFixEvenG μ Fr) : secPhi μ hμ ⟨m, hm.1⟩ ∈ pglFixEven μ Fr := by
  have h1 := secPhi_mem hμ ⟨m, hm.1⟩
  have h2 := secGraph_twistHom hμ hFr hm.1 _ h1
  have hfix : twistHom TwistTag.D4 L Fr m = m := hm.2
  rw [hfix] at h2
  exact (secGraph_snd_eq h1 h2).symm

@[expose] def secFixEvenHom [IsAlgClosed L] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {Fr : L →+* L} (hFr : Fr (μ : L) = (μ : L)) : secFixEvenG μ Fr →* pglFixEven μ Fr where
  toFun m := ⟨secPhi μ hμ ⟨m.1, m.2.1⟩, secPhi_mem_pglFixEven hμ hFr m.2⟩
  map_one' := Subtype.ext (map_one (secPhi μ hμ))
  map_mul' m m' := Subtype.ext (map_mul (secPhi μ hμ) ⟨m.1, m.2.1⟩ ⟨m'.1, m'.2.1⟩)

theorem secFixEvenHom_bijective [IsAlgClosed L] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {Fr : L →+* L} (hFr : Fr (μ : L) = (μ : L)) :
    Function.Bijective (secFixEvenHom hμ hFr) := by
  refine ⟨fun m m' h => ?_, fun P => ?_⟩
  · have h' : secPhi μ hμ ⟨m.1, m.2.1⟩ = secPhi μ hμ ⟨m'.1, m'.2.1⟩ :=
      congrArg Subtype.val h
    have := (secPhi μ hμ).injective h'
    exact Subtype.ext (congrArg (fun x : secM μ => (x : ModGL TwistTag.D4.tag L)) this)
  · set m := (secPhi μ hμ).symm P.1 with hm
    have hmP : ((m : ModGL TwistTag.D4.tag L), P.1) ∈ secGraph μ := by
      have := secPhi_mem hμ m
      rwa [hm, MulEquiv.apply_symm_apply] at this
    have h2 := secGraph_twistHom hμ hFr m.2 _ hmP
    have hPfix : evenFrobPGL μ Fr P.1 = P.1 := P.2
    rw [hPfix] at h2
    have h3 := (secGraph μ).mul_mem h2 ((secGraph μ).inv_mem hmP)
    rw [Prod.inv_mk, Prod.mk_mul_mk, mul_inv_cancel] at h3
    have h4 := eq_one_of_mem_secGraph hμ h3
    have hfix : twistHom TwistTag.D4 L Fr (m : ModGL TwistTag.D4.tag L) = m := mul_inv_eq_one.1 h4
    refine ⟨⟨m, m.2, hfix⟩, Subtype.ext ?_⟩
    change secPhi μ hμ ⟨m.1, m.2⟩ = P.1
    rw [hm]
    exact MulEquiv.apply_symm_apply _ _

@[expose] def secFixEvenEquiv [IsAlgClosed L] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {Fr : L →+* L} (hFr : Fr (μ : L) = (μ : L)) : secFixEvenG μ Fr ≃* pglFixEven μ Fr :=
  MulEquiv.ofBijective _ (secFixEvenHom_bijective hμ hFr)


section Iso

@[expose] def evenB (c : Lˣ) : GL (Fin 3) L where
  val := Matrix.diagonal ![1, (c : L), 1]
  inv := Matrix.diagonal ![1, (c : L)⁻¹, 1]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    fin_cases k <;> simp [Units.ne_zero c]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    fin_cases k <;> simp [Units.ne_zero c]

theorem evenD_mul_map_evenB {μ c : Lˣ} {Fr : L →+* L} (hc : (μ : L) * Fr c = c) :
    evenD μ * Matrix.GeneralLinearGroup.map Fr (evenB c) = evenB c := by
  refine Units.ext ?_
  rw [Units.val_mul, Matrix.GeneralLinearGroup.val_map_apply]
  change Matrix.diagonal ![1, (μ : L), 1] * (Matrix.diagonal ![1, (c : L), 1]).map Fr =
    Matrix.diagonal ![1, (c : L), 1]
  rw [Matrix.diagonal_map (map_zero Fr), Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  fin_cases k <;> simp [hc]

theorem evenFrobGL_conj {μ c : Lˣ} {Fr : L →+* L} (hc : (μ : L) * Fr c = c)
    (x : GL (Fin 3) L) :
    evenFrobGL μ Fr (evenB c * x * (evenB c)⁻¹) =
      evenB c * Matrix.GeneralLinearGroup.map Fr x * (evenB c)⁻¹ := by
  have h := evenD_mul_map_evenB (Fr := Fr) hc
  have e : ∀ g, evenFrobGL μ Fr g =
      evenD μ * Matrix.GeneralLinearGroup.map Fr g * (evenD μ)⁻¹ := fun g => rfl
  rw [e, map_mul, map_mul, map_inv]
  calc evenD μ * (Matrix.GeneralLinearGroup.map Fr (evenB c) *
        Matrix.GeneralLinearGroup.map Fr x * (Matrix.GeneralLinearGroup.map Fr (evenB c))⁻¹) *
          (evenD μ)⁻¹ =
        (evenD μ * Matrix.GeneralLinearGroup.map Fr (evenB c)) *
          Matrix.GeneralLinearGroup.map Fr x *
            (evenD μ * Matrix.GeneralLinearGroup.map Fr (evenB c))⁻¹ := by group
    _ = evenB c * Matrix.GeneralLinearGroup.map Fr x * (evenB c)⁻¹ := by rw [h]

theorem exists_map_frob_fixed [IsAlgClosed L] {q : ℕ} (hq : 2 ≤ q) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ q) (y : GL (Fin 3) L)
    (hy : ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map Fr y) = ProjGenLinGroup.mk y) :
    ∃ y' : GL (Fin 3) L, ProjGenLinGroup.mk y' = ProjGenLinGroup.mk y ∧
      Matrix.GeneralLinearGroup.map Fr y' = y' := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.1 hy
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (u : L) (by omega : 0 < q - 1)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hs
    exact (Units.ne_zero u) hs.symm
  set su : Lˣ := Units.mk0 s hs0
  have hcen : ∀ g : GL (Fin 3) L, ∀ d : Lˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) d * g =
      g * Matrix.GeneralLinearGroup.scalar (Fin 3) d := fun g d => by
    have := Subgroup.mem_center_iff.1 (show Matrix.GeneralLinearGroup.scalar (Fin 3) d ∈
      Subgroup.center (GL (Fin 3) L) by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨d, rfl⟩) g
    exact this.symm
  have hmapS : ∀ d : Lˣ, Matrix.GeneralLinearGroup.map Fr (Matrix.GeneralLinearGroup.scalar
      (Fin 3) d) = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map Fr.toMonoidHom d) := by
    intro d
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_map_apply, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.scalar_apply,
      Matrix.diagonal_map (map_zero Fr)]
    rfl
  have hFy : Matrix.GeneralLinearGroup.map Fr y =
      y * (Matrix.GeneralLinearGroup.scalar (Fin 3) u)⁻¹ := eq_mul_inv_of_mul_eq hu
  have hunit : Units.map Fr.toMonoidHom su * u⁻¹ = su := by
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, su, Units.val_mk0, hFr]
    have hu0 : (u : L) ≠ 0 := Units.ne_zero u
    have hsq : s ^ q = s ^ (q - 1) * s := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hsq, hs]
    field_simp
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) su * y, ?_, ?_⟩
  · rw [map_mul, ProjGenLinGroup.mk_scalar, one_mul]
  · set S : Lˣ →* GL (Fin 3) L := Matrix.GeneralLinearGroup.scalar (Fin 3) with hS
    calc Matrix.GeneralLinearGroup.map Fr (S su * y) =
          S (Units.map Fr.toMonoidHom su) * (y * (S u)⁻¹) := by
          rw [map_mul, hmapS, hFy]
      _ = y * (S (Units.map Fr.toMonoidHom su) * S u⁻¹) := by
          rw [← mul_assoc, hcen, mul_assoc, map_inv]
      _ = y * S su := by rw [← map_mul, hunit]
      _ = S su * y := (hcen y su).symm

variable {K' : Type} [Field K'] [Fintype K'] (ι : K' →+* L) {Fr : L →+* L}
  (hFr : ∀ c, Fr c = c ^ Nat.card K')

include hFr

theorem map_map_frob_eq (M : Matrix (Fin 3) (Fin 3) K') : (M.map ι).map Fr = M.map ι := by
  ext i j
  simp only [Matrix.map_apply, hFr]
  rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

variable (μ : Lˣ) {c : Lˣ} (hc : (μ : L) * Fr c = c)

include hc

theorem pguHom_mem_pglFixEven (P : PGL(3, K')) : pguHom ι (evenB c) P ∈ pglFixEven μ Fr := by
  obtain ⟨h, rfl⟩ := ProjGenLinGroup.mk_surjective P
  change evenFrobPGL μ Fr (pguHom ι (evenB c) (ProjGenLinGroup.mk h)) =
    pguHom ι (evenB c) (ProjGenLinGroup.mk h)
  rw [pguHom_mk, evenFrobPGL_mk, evenFrobGL_conj hc]
  congr 3
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_map_apply, Matrix.GeneralLinearGroup.val_map_apply]
  exact map_map_frob_eq ι hFr _

theorem exists_pguHom_eq_even [IsAlgClosed L] {Q : PGL(3, L)} (hQ : Q ∈ pglFixEven μ Fr) :
    ∃ P : PGL(3, K'), pguHom ι (evenB c) P = Q := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective Q
  set y := (evenB c)⁻¹ * g * evenB c with hy
  have hgy : g = evenB c * y * (evenB c)⁻¹ := by rw [hy]; group
  clear_value y
  have hQ' : evenFrobPGL μ Fr (ProjGenLinGroup.mk g) = ProjGenLinGroup.mk g := hQ
  rw [evenFrobPGL_mk, hgy, evenFrobGL_conj hc] at hQ'
  rw [map_mul, map_mul, map_mul, map_mul] at hQ'
  have hy' : ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map Fr y) = ProjGenLinGroup.mk y :=
    mul_left_cancel (mul_right_cancel hQ')
  have hq : 2 ≤ Nat.card K' := Finite.one_lt_card
  obtain ⟨y', hyy', hfix⟩ := exists_map_frob_fixed hq hFr y hy'
  have hent : ∀ i j, (y' : Matrix (Fin 3) (Fin 3) L) i j ∈ ι.range := by
    intro i j
    have hx := congrArg (fun x : GL (Fin 3) L => (x : Matrix (Fin 3) (Fin 3) L) i j) hfix
    simp only [Matrix.GeneralLinearGroup.val_map_apply, Matrix.map_apply, hFr] at hx
    exact mem_range_of_pow_card_eq ι hx
  obtain ⟨h, rfl⟩ := exists_map_eq_of_mem_range ι y' hent
  refine ⟨ProjGenLinGroup.mk h, ?_⟩
  rw [pguHom_mk, map_mul, map_mul, hyy', ← map_mul, ← map_mul, ← hgy]

@[expose] def pglFixEvenHom :
    projImage (Sec4.glPi true 3 (Nat.card K') K') →* pglFixEven μ Fr where
  toFun P := ⟨pguHom ι (evenB c) P.1, pguHom_mem_pglFixEven ι hFr μ hc P.1⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

@[expose] def pglEquivPglFixEven [IsAlgClosed L] :
    projImage (Sec4.glPi true 3 (Nat.card K') K') ≃* pglFixEven μ Fr :=
  MulEquiv.ofBijective (pglFixEvenHom ι hFr μ hc)
    ⟨fun P P' h => Subtype.ext (pguHom_injective ι (evenB c) (congrArg Subtype.val h)), fun Q => by
      obtain ⟨P, hPQ⟩ := exists_pguHom_eq_even ι hFr μ hc Q.2
      obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective P
      exact ⟨⟨ProjGenLinGroup.mk g, ⟨g, Sec4.mem_glPi_true _ g, rfl⟩⟩, Subtype.ext hPQ⟩⟩

end Iso

end CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof
