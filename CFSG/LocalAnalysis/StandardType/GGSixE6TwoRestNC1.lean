module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestBasic
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoJEq
public import CFSG.LinearAlgebra.RootGroupSL.NoOuter
public import CFSG.LinearAlgebra.RootGroupSL.FpfNoCentral

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
  Matrix CFSG.LinearAlgebra.RootGroupSL

private noncomputable instance e6n1_alg : Algebra F2 F4 :=
  ((algebraMap (ZMod 2) F4).comp (GaloisField.equivZmodP (p := 2)).toRingHom).toAlgebra

private theorem e6n1_f2_cases (a : F2) : a = 0 ∨ a = 1 := by
  have hcard : Nat.card F2 = 2 := by simpa using GaloisField.card 2 1 (by norm_num)
  by_cases hz : a = 0
  · exact Or.inl hz
  · obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
    exact Or.inr ((huniq a hz).trans (huniq 1 one_ne_zero).symm)

private theorem e6n1_f4Eps_sq : f4Eps (f4Omega ^ 2) = !![1, 1; 1, 0] := by
  rw [map_pow, f4Eps_omega]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, pow_two, CharTwo.add_self_eq_zero]

private noncomputable def e6n1_f4CoordLin : F4 →ₗ[F2] (Fin 2 → F2) where
  toFun a := fun j => f4Eps a j 0
  map_add' a b := by ext j; simp [map_add]
  map_smul' c a := by
    ext j
    rcases e6n1_f2_cases c with rfl | rfl <;> simp

private theorem e6n1_f4Coord_inj : Function.Injective e6n1_f4CoordLin := by
  intro a b h
  have h0 : f4Eps a 0 0 = f4Eps b 0 0 := congrFun h 0
  have h1 : f4Eps a 1 0 = f4Eps b 1 0 := congrFun h 1
  rcases f4_cases a with rfl | rfl | rfl | rfl <;>
    rcases f4_cases b with rfl | rfl | rfl | rfl <;>
    simp_all [f4Eps_omega, e6n1_f4Eps_sq]

private theorem e6n1_f4Coord_surj : Function.Surjective e6n1_f4CoordLin := by
  intro y
  rcases e6n1_f2_cases (y 0) with h0 | h0 <;>
    rcases e6n1_f2_cases (y 1) with h1 | h1
  · refine ⟨0, ?_⟩
    ext j; fin_cases j <;> simp [e6n1_f4CoordLin, h0, h1]
  · refine ⟨f4Omega, ?_⟩
    ext j; fin_cases j <;> simp [e6n1_f4CoordLin, h0, h1, f4Eps_omega]
  · refine ⟨1, ?_⟩
    ext j; fin_cases j <;> simp [e6n1_f4CoordLin, h0, h1]
  · refine ⟨f4Omega ^ 2, ?_⟩
    ext j; fin_cases j <;> simp [e6n1_f4CoordLin, h0, h1, e6n1_f4Eps_sq]

private noncomputable def e6n1_f4Equiv : F4 ≃ₗ[F2] (Fin 2 → F2) :=
  LinearEquiv.ofBijective e6n1_f4CoordLin ⟨e6n1_f4Coord_inj, e6n1_f4Coord_surj⟩

private lemma e6n1_f4Equiv_apply (a : F4) (j : Fin 2) :
    e6n1_f4Equiv a j = f4Eps a j 0 := by
  unfold e6n1_f4Equiv
  rfl

private lemma e6n1_f4Equiv_symm_apply (y : Fin 2 → F2) (j : Fin 2) :
    f4Eps (e6n1_f4Equiv.symm y) j 0 = y j := by
  rw [← e6n1_f4Equiv_apply]
  exact congrFun (LinearEquiv.apply_symm_apply e6n1_f4Equiv y) j

private noncomputable def e6n1_Lfun (v : DSpace F4 (Fin 2 → F2)) : Fin 3 × Fin 2 → F2 :=
  fun p =>
    if p.1 = 0 then f4Eps v.1 p.2 0
    else if p.1 = 1 then v.2.1 p.2
    else f4Eps v.2.2 p.2 0

private lemma e6n1_Lfun_apply_pair (v : DSpace F4 (Fin 2 → F2)) (k : Fin 3) (j : Fin 2) :
    e6n1_Lfun v (k, j) =
      (if k = 0 then f4Eps v.1 j 0 else if k = 1 then v.2.1 j else f4Eps v.2.2 j 0) := rfl

private noncomputable def e6n1_Llin : DSpace F4 (Fin 2 → F2) →ₗ[F2] (Fin 3 × Fin 2 → F2) where
  toFun := e6n1_Lfun
  map_add' v w := by
    ext p
    obtain ⟨k, j⟩ := p
    rw [Pi.add_apply, e6n1_Lfun_apply_pair, e6n1_Lfun_apply_pair, e6n1_Lfun_apply_pair]
    fin_cases k <;> simp [f4Eps.map_add]
  map_smul' c v := by
    ext p
    obtain ⟨k, j⟩ := p
    rw [Pi.smul_apply, e6n1_Lfun_apply_pair, e6n1_Lfun_apply_pair]
    fin_cases k <;> rcases e6n1_f2_cases c with rfl | rfl <;> simp

private lemma e6n1_Llin_apply_pair (v : DSpace F4 (Fin 2 → F2)) (k : Fin 3) (j : Fin 2) :
    e6n1_Llin v (k, j) =
      (if k = 0 then f4Eps v.1 j 0 else if k = 1 then v.2.1 j else f4Eps v.2.2 j 0) :=
  e6n1_Lfun_apply_pair v k j

private theorem e6n1_Llin_inj : Function.Injective e6n1_Llin := by
  intro v w h
  have h0 : e6n1_f4Equiv v.1 = e6n1_f4Equiv w.1 := by
    ext j
    have hh := congrFun h (0, j)
    rw [e6n1_Llin_apply_pair, e6n1_Llin_apply_pair] at hh
    simpa [e6n1_f4Equiv_apply] using hh
  have h1 : v.2.1 = w.2.1 := by
    funext j
    have hh := congrFun h (1, j)
    rw [e6n1_Llin_apply_pair, e6n1_Llin_apply_pair] at hh
    simpa using hh
  have h2 : e6n1_f4Equiv v.2.2 = e6n1_f4Equiv w.2.2 := by
    ext j
    have hh := congrFun h (2, j)
    rw [e6n1_Llin_apply_pair, e6n1_Llin_apply_pair] at hh
    simpa [e6n1_f4Equiv_apply] using hh
  exact Prod.ext (e6n1_f4Equiv.injective h0)
    (Prod.ext h1 (e6n1_f4Equiv.injective h2))

private theorem e6n1_Llin_surj : Function.Surjective e6n1_Llin := by
  intro u
  refine ⟨(e6n1_f4Equiv.symm (fun j => u (0, j)),
    (fun j => u (1, j)),
    e6n1_f4Equiv.symm (fun j => u (2, j))), ?_⟩
  ext p
  obtain ⟨k, j⟩ := p
  rw [e6n1_Llin_apply_pair]
  fin_cases k <;> simp [e6n1_f4Equiv_symm_apply]

private noncomputable def e6n1_L : DSpace F4 (Fin 2 → F2) ≃ₗ[F2] (Fin 3 × Fin 2 → F2) :=
  LinearEquiv.ofBijective e6n1_Llin ⟨e6n1_Llin_inj, e6n1_Llin_surj⟩

private lemma e6n1_L_apply_pair (v : DSpace F4 (Fin 2 → F2)) (k : Fin 3) (j : Fin 2) :
    e6n1_L v (k, j) =
      (if k = 0 then f4Eps v.1 j 0 else if k = 1 then v.2.1 j else f4Eps v.2.2 j 0) := by
  unfold e6n1_L
  exact e6n1_Llin_apply_pair v k j

private lemma e6n1_coe_resSL_transvection (t : F4) :
    ((resSL 3 (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) t) :
        Matrix.SpecialLinearGroup (Fin 6) F2) : Matrix (Fin 6) (Fin 6) F2)
      = resMat 3 (1 + Matrix.single (0 : Fin 3) 2 t) := by
  rw [coe_resSL, Matrix.SpecialLinearGroup.transvection_coe]

private noncomputable def e6n1_reindex :
    Matrix.SpecialLinearGroup (Fin 6) F2 ≃* Matrix.SpecialLinearGroup (Fin 3 × Fin 2) F2 where
  toFun A := ⟨Matrix.reindexAlgEquiv F2 F2 (finProdFinEquiv (m := 3) (n := 2)).symm A.1,
    by rw [Matrix.det_reindexAlgEquiv]; exact A.2⟩
  invFun B := ⟨Matrix.reindexAlgEquiv F2 F2 (finProdFinEquiv (m := 3) (n := 2)) B.1,
    by rw [Matrix.det_reindexAlgEquiv]; exact B.2⟩
  left_inv A := by
    apply Subtype.ext
    simp [Matrix.reindexAlgEquiv_symm]
  right_inv B := by
    apply Subtype.ext
    simp [Matrix.reindexAlgEquiv_symm]
  map_mul' A B :=
    Subtype.ext (map_mul (Matrix.reindexAlgEquiv F2 F2
      (finProdFinEquiv (m := 3) (n := 2)).symm) A.1 B.1)

private lemma e6n1_reindex_coe (A : Matrix.SpecialLinearGroup (Fin 6) F2) :
    (e6n1_reindex A).1
      = Matrix.reindexAlgEquiv F2 F2 (finProdFinEquiv (m := 3) (n := 2)).symm A.1 := rfl

private noncomputable def e6n1_M (t : F4) : Matrix.SpecialLinearGroup (Fin 3 × Fin 2) F2 :=
  ⟨Matrix.reindexAlgEquiv F2 F2 (finProdFinEquiv (m := 3) (n := 2)).symm
      (resMat 3 (1 + Matrix.single (0 : Fin 3) 2 t)),
    by
      rw [Matrix.det_reindexAlgEquiv, ← e6n1_coe_resSL_transvection t]
      exact (resSL 3 (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) t)).2⟩

private lemma e6n1_M_apply (t : F4) (k l : Fin 3) (j j' : Fin 2) :
    (e6n1_M t).1 (k, j) (l, j') =
      f4Eps ((1 + Matrix.single (0 : Fin 3) 2 t) k l) j j' := by
  simp only [e6n1_M]
  rw [show (Matrix.reindexAlgEquiv F2 F2 (finProdFinEquiv (m := 3) (n := 2)).symm
      (resMat 3 (1 + Matrix.single (0 : Fin 3) 2 t))) (k, j) (l, j')
      = resMat 3 (1 + Matrix.single (0 : Fin 3) 2 t)
          (finProdFinEquiv (m := 3) (n := 2) (k, j))
          (finProdFinEquiv (m := 3) (n := 2) (l, j')) from rfl]
  exact resMat_apply 3 (1 + Matrix.single (0 : Fin 3) 2 t) k l j j'

private lemma e6n1_M_eq_reindex (t : F4) :
    e6n1_M t = e6n1_reindex
      (resSL 3 (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) t)) := by
  apply Subtype.ext
  change Matrix.reindexAlgEquiv F2 F2 (finProdFinEquiv (m := 3) (n := 2)).symm
      (resMat 3 (1 + Matrix.single (0 : Fin 3) 2 t)) = (e6n1_reindex (resSL 3
        (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) t))).1
  rw [e6n1_reindex_coe]
  rw [show (resSL 3 (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) t)).1
      = resMat 3 (1 + Matrix.single (0 : Fin 3) 2 t) from
    (e6n1_coe_resSL_transvection t)]

private lemma e6n1_L_rootEquiv (t : F4) (v : DSpace F4 (Fin 2 → F2)) :
    e6n1_L (rootEquiv F2 (Fin 2 → F2) t v) =
      (e6n1_M t).1 *ᵥ e6n1_L v := by
  ext p
  obtain ⟨k, j⟩ := p
  have hroot : rootEquiv F2 (Fin 2 → F2) t v = (v.1 + t * v.2.2, v.2.1, v.2.2) := rfl
  rw [hroot, e6n1_L_apply_pair]
  rw [show ((e6n1_M t).1 *ᵥ e6n1_L v) (k, j)
      = ∑ p' : Fin 3 × Fin 2,
          (e6n1_M t).1 (k, j) p' * e6n1_L v p'
      from rfl]
  rw [Fintype.sum_prod_type]
  rw [Fin.sum_univ_three]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases k <;> fin_cases j <;>
    simp [e6n1_M_apply, e6n1_L_apply_pair, Matrix.single_apply,
      Matrix.one_apply, f4Eps.map_add, f4Eps.map_mul, Matrix.mul_apply, Fin.sum_univ_two]

private noncomputable def e6n1_toMat :
    SpecialLinearGroup F2 (DSpace F4 (Fin 2 → F2)) ≃*
      Matrix.SpecialLinearGroup (Fin 3 × Fin 2) F2 :=
  (SpecialLinearGroup.congr_linearEquiv e6n1_L).trans
    (Matrix.SpecialLinearGroup.toLin'_equiv).symm

private lemma e6n1_toMat_rootElt (t : F4) :
    e6n1_toMat (rootElt F2 (Fin 2 → F2) t) = e6n1_M t := by
  apply (Matrix.SpecialLinearGroup.toLin'_equiv).injective
  apply SpecialLinearGroup.ext
  intro u
  rw [show (Matrix.SpecialLinearGroup.toLin'_equiv) (e6n1_toMat (rootElt F2 (Fin 2 → F2) t))
      = (SpecialLinearGroup.congr_linearEquiv e6n1_L) (rootElt F2 (Fin 2 → F2) t) from by
    simp [e6n1_toMat]]
  rw [show (Matrix.SpecialLinearGroup.toLin'_equiv) (e6n1_M t)
      = Matrix.SpecialLinearGroup.toLin' (e6n1_M t) from rfl]
  rw [show ((SpecialLinearGroup.congr_linearEquiv e6n1_L) (rootElt F2 (Fin 2 → F2) t)) u
      = e6n1_L (rootEquiv F2 (Fin 2 → F2) t (e6n1_L.symm u)) from by
    rw [SpecialLinearGroup.congr_linearEquiv_apply_apply]; rfl]
  simp only [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply']
  rw [Matrix.mulVecLin_apply]
  simpa using e6n1_L_rootEquiv t (e6n1_L.symm u)

private noncomputable def e6n1_toMatFin6 :
    SpecialLinearGroup F2 (DSpace F4 (Fin 2 → F2)) ≃*
      Matrix.SpecialLinearGroup (Fin 6) F2 :=
  e6n1_toMat.trans e6n1_reindex.symm

private lemma e6n1_toMatFin6_rootElt (t : F4) :
    e6n1_toMatFin6 (rootElt F2 (Fin 2 → F2) t) =
      resSL 3 (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) t) := by
  simp only [e6n1_toMatFin6, MulEquiv.trans_apply]
  rw [e6n1_toMat_rootElt, e6n1_M_eq_reindex]
  exact e6n1_reindex.symm_apply_apply _

private lemma e6n1_finrank_f4 : Module.finrank F2 F4 = 2 := by
  have hrank : Module.rank F2 F4 = Module.rank (ZMod 2) F4 :=
    Algebra.rank_eq_of_equiv_equiv (GaloisField.equivZmodP (p := 2)) (RingEquiv.refl F4) (by
      ext a
      rfl)
  have hfin : Module.finrank F2 F4 = Module.finrank (ZMod 2) F4 := by
    simp only [Module.finrank]
    rw [hrank]
  rw [hfin]
  exact GaloisField.finrank 2 (by norm_num)

private noncomputable instance e6n1_finite_f4 : Module.Finite F2 F4 := Module.Finite.of_finite

private theorem e6n1_rootNoCentral :
    GGRootNormNoCentral (rootSL F2 F4 (Fin 2 → F2)) := by
  exact rootNoCentral_rootSL (k := F2) (E := F4) (X := Fin 2 → F2)
    (by rw [e6n1_finrank_f4, Module.finrank_fin_fun])
    (Or.inl (by rw [e6n1_finrank_f4]))

private theorem e6n1_rootInner :
    GGRootNormInner (rootSL F2 F4 (Fin 2 → F2)) := by
  intro y hy2 hyR hymod
  have hymod' : ∀ n ∈ Subgroup.normalizer (rootSL F2 F4 (Fin 2 → F2) : Set _),
      y n * n⁻¹ ∈ QK F2 F4 (Fin 2 → F2) := by
    intro n hn
    have h := hymod n hn
    rwa [pCoreOf_normalizer_rootSL (k := F2) (E := F4) (X := Fin 2 → F2)
      (by rw [Module.finrank_fin_fun]; norm_num)] at h
  refine exists_conj_of_two_element_mem_Y (k := F2) (E := F4) (X := Fin 2 → F2)
    (by rw [e6n1_finrank_f4, Module.finrank_fin_fun])
    (Or.inl (by rw [e6n1_finrank_f4])) y hyR ?_ hy2
  intro h hh
  exact (le_sup_left : QK F2 F4 (Fin 2 → F2) ≤
    QK F2 F4 (Fin 2 → F2) ⊔ Subgroup.center (SpecialLinearGroup F2 (DSpace F4 (Fin 2 → F2))))
    (hymod' h hh)

private lemma e6n1_f4Omega_sq_eq : f4Omega ^ 2 = f4Omega + 1 := by
  have h : f4Omega ^ 2 + (f4Omega + 1) = 0 := by rw [← add_assoc]; exact f4Omega_sq
  have h2 : f4Omega ^ 2 = -(f4Omega + 1) := add_eq_zero_iff_eq_neg.mp h
  rw [h2, neg_add, CharTwo.neg_eq, CharTwo.neg_eq]

private noncomputable def e6n1_Rmat : Subgroup (Matrix.SpecialLinearGroup (Fin 6) F2) :=
  Subgroup.closure {resSL 3 (Matrix.SpecialLinearGroup.transvection
      (by decide : (0 : Fin 3) ≠ 2) (1 : F4)),
    resSL 3 (Matrix.SpecialLinearGroup.transvection
      (by decide : (0 : Fin 3) ≠ 2) f4Omega)}

private lemma e6n1_resSL_transvection_mem_Rmat (t : F4) :
    resSL 3 (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) t)
      ∈ e6n1_Rmat := by
  rcases f4_cases t with rfl | rfl | rfl | rfl
  · rw [Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one]
    exact e6n1_Rmat.one_mem
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr rfl)
  · rw [e6n1_f4Omega_sq_eq, Matrix.SpecialLinearGroup.transvection_add, map_mul]
    exact e6n1_Rmat.mul_mem (Subgroup.subset_closure (Or.inr rfl))
      (Subgroup.subset_closure (Or.inl rfl))

private lemma e6n1_mem_rootSL_iff (g : SpecialLinearGroup F2 (DSpace F4 (Fin 2 → F2))) :
    g ∈ rootSL F2 F4 (Fin 2 → F2) ↔ ∃ t : F4, rootElt F2 (Fin 2 → F2) t = g := by
  rw [mem_rootSL_iff]
  constructor
  · rintro ⟨t, ht⟩; exact ⟨t, Subtype.ext ht.symm⟩
  · rintro ⟨t, ht⟩; exact ⟨t, (congrArg Subtype.val ht).symm⟩

private lemma e6n1_map_rootSL :
    (rootSL F2 F4 (Fin 2 → F2)).map e6n1_toMatFin6.toMonoidHom = e6n1_Rmat := by
  ext g
  have key : e6n1_toMatFin6 (e6n1_toMatFin6.symm g) ∈
      (rootSL F2 F4 (Fin 2 → F2)).map e6n1_toMatFin6.toMonoidHom ↔
        e6n1_toMatFin6.symm g ∈ rootSL F2 F4 (Fin 2 → F2) :=
    Subgroup.mem_map_iff_mem e6n1_toMatFin6.injective
  rw [MulEquiv.apply_symm_apply] at key
  rw [key, e6n1_mem_rootSL_iff]
  constructor
  · rintro ⟨t, ht⟩
    have hg : g = e6n1_toMatFin6 (rootElt F2 (Fin 2 → F2) t) := by
      rw [ht]
      exact (MulEquiv.apply_symm_apply e6n1_toMatFin6 g).symm
    rw [hg, e6n1_toMatFin6_rootElt]
    exact e6n1_resSL_transvection_mem_Rmat t
  · intro hg
    have hle : e6n1_Rmat ≤
        (rootSL F2 F4 (Fin 2 → F2)).comap e6n1_toMatFin6.symm.toMonoidHom := by
      rw [e6n1_Rmat, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · change e6n1_toMatFin6.symm (resSL 3 (Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 2) (1 : F4))) ∈ rootSL F2 F4 (Fin 2 → F2)
        rw [show e6n1_toMatFin6.symm (resSL 3 (Matrix.SpecialLinearGroup.transvection
              (by decide : (0 : Fin 3) ≠ 2) (1 : F4))) =
            rootElt F2 (Fin 2 → F2) 1 from by
          rw [show resSL 3 (Matrix.SpecialLinearGroup.transvection
                (by decide : (0 : Fin 3) ≠ 2) (1 : F4)) =
              e6n1_toMatFin6 (rootElt F2 (Fin 2 → F2) 1) from
                (e6n1_toMatFin6_rootElt 1).symm,
            MulEquiv.symm_apply_apply]]
        exact rootElt_mem_rootSL 1
      · change e6n1_toMatFin6.symm (resSL 3 (Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 3) ≠ 2) f4Omega)) ∈ rootSL F2 F4 (Fin 2 → F2)
        rw [show e6n1_toMatFin6.symm (resSL 3 (Matrix.SpecialLinearGroup.transvection
              (by decide : (0 : Fin 3) ≠ 2) f4Omega)) =
            rootElt F2 (Fin 2 → F2) f4Omega from by
          rw [show resSL 3 (Matrix.SpecialLinearGroup.transvection
                (by decide : (0 : Fin 3) ≠ 2) f4Omega) =
              e6n1_toMatFin6 (rootElt F2 (Fin 2 → F2) f4Omega) from
                (e6n1_toMatFin6_rootElt f4Omega).symm,
            MulEquiv.symm_apply_apply]]
        exact rootElt_mem_rootSL f4Omega
    exact (e6n1_mem_rootSL_iff (e6n1_toMatFin6.symm g)).mp (hle hg)

private lemma e6n1_blk_eq_blk_iff {k l : Fin 3} {j j' : Fin 2} :
    blk k j = blk l j' ↔ k = l ∧ j = j' := by
  constructor
  · intro h
    have hv : 2 * (k : ℕ) + (j : ℕ) = 2 * (l : ℕ) + (j' : ℕ) := by
      simpa [blk] using congrArg Fin.val h
    constructor
    · apply Fin.ext; omega
    · apply Fin.ext; omega
  · rintro ⟨rfl, rfl⟩; rfl

private lemma e6n1_blk_ne_of_ne {k l : Fin 3} (h : k ≠ l) (j : Fin 2) :
    blk k j ≠ blk l j := fun hh => h (e6n1_blk_eq_blk_iff.mp hh).1

private lemma e6n1_blk_ne_of_ne' {k l : Fin 3} (h : k ≠ l) (j j' : Fin 2) :
    blk k j ≠ blk l j' := fun hh => h (e6n1_blk_eq_blk_iff.mp hh).1

private lemma e6n1_finProdFinEquiv_blk (k : Fin 3) (j : Fin 2) :
    finProdFinEquiv (k, j) = blk k j := by
  apply Fin.ext
  rw [finProdFinEquiv_apply_val]
  show (j : ℕ) + 2 * (k : ℕ) = 2 * (k : ℕ) + (j : ℕ)
  omega

private lemma e6n1_resMat_single (k l : Fin 3) (c : F4) :
    resMat 3 (Matrix.single k l c) =
      Matrix.single (blk k 0) (blk l 0) (f4Eps c 0 0) +
      Matrix.single (blk k 0) (blk l 1) (f4Eps c 0 1) +
      Matrix.single (blk k 1) (blk l 0) (f4Eps c 1 0) +
      Matrix.single (blk k 1) (blk l 1) (f4Eps c 1 1) := by
  ext r s
  obtain ⟨⟨i, j⟩, rfl⟩ := (finProdFinEquiv (m := 3) (n := 2)).surjective r
  obtain ⟨⟨i', j'⟩, rfl⟩ := (finProdFinEquiv (m := 3) (n := 2)).surjective s
  rw [resMat_apply]
  simp only [Matrix.add_apply, Matrix.single_apply, e6n1_finProdFinEquiv_blk,
    e6n1_blk_eq_blk_iff]
  by_cases hk : k = i <;> by_cases hl : l = i'
  · fin_cases j <;> fin_cases j' <;> simp [hk, hl]
  · simp [hk, hl]
  · simp [hk, hl]
  · simp [hk, hl]

private lemma e6n1_resMat_single_one (k l : Fin 3) :
    resMat 3 (Matrix.single k l (1 : F4)) =
      Matrix.single (blk k 0) (blk l 0) (1 : F2) +
      Matrix.single (blk k 1) (blk l 1) (1 : F2) := by
  rw [e6n1_resMat_single, map_one]
  have h01 : (1 : Matrix (Fin 2) (Fin 2) F2) 0 1 = 0 := by
    rw [Matrix.one_apply]; exact if_neg (by decide)
  have h10 : (1 : Matrix (Fin 2) (Fin 2) F2) 1 0 = 0 := by
    rw [Matrix.one_apply]; exact if_neg (by decide)
  have h00 : (1 : Matrix (Fin 2) (Fin 2) F2) 0 0 = 1 := by
    rw [Matrix.one_apply]; exact if_pos rfl
  have h11 : (1 : Matrix (Fin 2) (Fin 2) F2) 1 1 = 1 := by
    rw [Matrix.one_apply]; exact if_pos rfl
  rw [h00, h01, h10, h11, Matrix.single_zero, Matrix.single_zero]
  abel

private lemma e6n1_resMat_single_omega (k l : Fin 3) :
    resMat 3 (Matrix.single k l f4Omega) =
      Matrix.single (blk k 0) (blk l 1) (1 : F2) +
      Matrix.single (blk k 1) (blk l 0) (1 : F2) +
      Matrix.single (blk k 1) (blk l 1) (1 : F2) := by
  rw [e6n1_resMat_single, f4Eps_omega]
  have h00 : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F2) 0 0 = 0 := by simp
  have h01 : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F2) 0 1 = 1 := by simp
  have h10 : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F2) 1 0 = 1 := by simp
  have h11 : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F2) 1 1 = 1 := by simp
  rw [h00, h01, h10, h11, Matrix.single_zero]
  abel

private lemma e6n1_one_add_mul_one_add {A B : Matrix (Fin 6) (Fin 6) F2} (h : A * B = 0) :
    ((1 : Matrix (Fin 6) (Fin 6) F2) + A) * (1 + B) = 1 + (A + B) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, h, add_zero]
  abel

private lemma e6n1_one_add_single_mul_three {a b c d e f : Fin 6}
    (hbc : b ≠ c) (hbe : b ≠ e) (hde : d ≠ e) :
    ((1 + Matrix.single a b (1 : F2)) * (1 + Matrix.single c d (1 : F2))) *
        (1 + Matrix.single e f (1 : F2)) =
      1 + (Matrix.single a b (1 : F2) + Matrix.single c d (1 : F2) +
        Matrix.single e f (1 : F2)) := by
  have hAC : Matrix.single a b (1 : F2) * Matrix.single c d (1 : F2) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F2) a b c hbc (1 : F2)
  have hAE : Matrix.single a b (1 : F2) * Matrix.single e f (1 : F2) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F2) a b e hbe (1 : F2)
  have hCE : Matrix.single c d (1 : F2) * Matrix.single e f (1 : F2) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F2) c d e hde (1 : F2)
  have hACE : (Matrix.single a b (1 : F2) + Matrix.single c d (1 : F2)) *
      Matrix.single e f (1 : F2) = 0 := by
    rw [Matrix.add_mul, hAE, hCE, add_zero]
  rw [e6n1_one_add_mul_one_add hAC, e6n1_one_add_mul_one_add hACE]

private theorem e6n1_resSL_transvection_one (k l : Fin 3) (hkl : k ≠ l) :
    resSL 3 (Matrix.SpecialLinearGroup.transvection hkl (1 : F4)) =
      Matrix.SpecialLinearGroup.transvection (e6n1_blk_ne_of_ne hkl 0) (1 : F2) *
        Matrix.SpecialLinearGroup.transvection (e6n1_blk_ne_of_ne hkl 1) (1 : F2) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_resSL,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.transvection_coe, map_add, map_one, e6n1_resMat_single_one]
  have hAB : Matrix.single (blk k 0) (blk l 0) (1 : F2) *
      Matrix.single (blk k 1) (blk l 1) (1 : F2) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F2) (blk k 0) (blk l 0) (blk k 1)
      (e6n1_blk_ne_of_ne' hkl.symm 0 1) (1 : F2)
  rw [e6n1_one_add_mul_one_add hAB]

private theorem e6n1_resSL_transvection_omega (k l : Fin 3) (hkl : k ≠ l) :
    resSL 3 (Matrix.SpecialLinearGroup.transvection hkl f4Omega) =
      Matrix.SpecialLinearGroup.transvection (e6n1_blk_ne_of_ne' hkl 0 1) (1 : F2) *
        Matrix.SpecialLinearGroup.transvection (e6n1_blk_ne_of_ne' hkl 1 0) (1 : F2) *
        Matrix.SpecialLinearGroup.transvection (e6n1_blk_ne_of_ne hkl 1) (1 : F2) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_resSL,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
      map_add, map_one, e6n1_resMat_single_omega]
  exact (e6n1_one_add_single_mul_three (a := blk k 0) (b := blk l 1) (c := blk k 1)
    (d := blk l 0) (e := blk k 1) (f := blk l 1)
    (e6n1_blk_ne_of_ne hkl.symm 1) (e6n1_blk_ne_of_ne hkl.symm 1)
    (e6n1_blk_ne_of_ne' hkl.symm 0 1)).symm

theorem ggRootNorm_rE_lE :
    GGRootNormNoCentral (rE.subgroupOf lE) ∧ GGRootNormInner (rE.subgroupOf lE) := by
  have hT : ∀ (a b : Fin 6) (hab : a ≠ b),
      (E6Pilot.slToAdjointE6 F2) (Matrix.SpecialLinearGroup.transvection hab (1 : F2)) =
        xr (a5Root a b) := by
    intro a b hab
    apply Subtype.ext
    rw [E6Pilot.coe_slToAdjointE6_transvection]
    rfl
  have hPhi_one : (E6Pilot.slToAdjointE6 F2) (resSL 3 (Matrix.SpecialLinearGroup.transvection
      (by decide : (0 : Fin 3) ≠ 2) (1 : F4))) = rOne 0 2 := by
    rw [e6n1_resSL_transvection_one 0 2 (by decide), map_mul,
      hT (blk 0 0) (blk 2 0) (e6n1_blk_ne_of_ne (by decide) 0),
      hT (blk 0 1) (blk 2 1) (e6n1_blk_ne_of_ne (by decide) 1)]
    rfl
  have hPhi_omega : (E6Pilot.slToAdjointE6 F2) (resSL 3 (Matrix.SpecialLinearGroup.transvection
      (by decide : (0 : Fin 3) ≠ 2) f4Omega)) = rOmega 0 2 := by
    rw [e6n1_resSL_transvection_omega 0 2 (by decide), map_mul, map_mul,
      hT (blk 0 0) (blk 2 1) (e6n1_blk_ne_of_ne' (by decide) 0 1),
      hT (blk 0 1) (blk 2 0) (e6n1_blk_ne_of_ne' (by decide) 1 0),
      hT (blk 0 1) (blk 2 1) (e6n1_blk_ne_of_ne (by decide) 1)]
    rfl
  have hRmat : e6n1_Rmat.map (E6Pilot.slToAdjointE6 F2) = rE := by
    refine le_antisymm ?_ ?_
    · rw [e6n1_Rmat, MonoidHom.map_closure, Subgroup.closure_le]
      rintro x ⟨y, (rfl | rfl), rfl⟩
      · rw [hPhi_one]; exact Subgroup.subset_closure (Or.inl rfl)
      · rw [hPhi_omega]; exact Subgroup.subset_closure (Or.inr rfl)
    · rw [rE, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact ⟨_, Subgroup.subset_closure (Or.inl rfl), hPhi_one⟩
      · exact ⟨_, Subgroup.subset_closure (Or.inr rfl), hPhi_omega⟩
  have hNC : GGRootNormNoCentral e6n1_Rmat := by
    rw [← e6n1_map_rootSL]
    exact ggRootNormNoCentral_map_mulEquiv e6n1_toMatFin6 e6n1_rootNoCentral
  have hI : GGRootNormInner e6n1_Rmat := by
    rw [← e6n1_map_rootSL]
    exact ggRootNormInner_map_mulEquiv e6n1_toMatFin6 e6n1_rootInner
  have hsub : e6n1_Rmat.subgroupOf (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 6) F2)) =
      e6n1_Rmat.map (Subgroup.topEquiv.symm).toMonoidHom := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨x, hx, by ext; rfl⟩
    · rintro ⟨h, hh, hhx⟩
      have hval : (h : Matrix.SpecialLinearGroup (Fin 6) F2) =
          (x : Matrix.SpecialLinearGroup (Fin 6) F2) := by
        simpa using congrArg Subtype.val hhx
      rwa [hval] at hh
  have hNC' : GGRootNormNoCentral
      (e6n1_Rmat.subgroupOf (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 6) F2))) := by
    rw [hsub]
    exact ggRootNormNoCentral_map_mulEquiv (Subgroup.topEquiv.symm) hNC
  have hI' : GGRootNormInner
      (e6n1_Rmat.subgroupOf (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 6) F2))) := by
    rw [hsub]
    exact ggRootNormInner_map_mulEquiv (Subgroup.topEquiv.symm) hI
  refine ⟨?_, ?_⟩
  · refine ggRootNormNoCentral_of_map_injective (E6Pilot.slToAdjointE6 F2)
      iota_injective (K' := ⊤) (R' := e6n1_Rmat) ?_ hRmat hNC'
    rw [Subgroup.map_top, E6Pilot.range_slToAdjointE6]
    rfl
  · refine ggRootNormInner_of_map_injective (E6Pilot.slToAdjointE6 F2)
      iota_injective (K' := ⊤) (R' := e6n1_Rmat) ?_ hRmat hI'
    rw [Subgroup.map_top, E6Pilot.range_slToAdjointE6]
    rfl

theorem ggRootNorm_rE_conj_lE
    (h : EC) (hh : h ∈ Subgroup.normalizer (rE : Set EC)) :
    GGRootNormNoCentral (rE.subgroupOf (lE.map (MulAut.conj h).toMonoidHom)) ∧
      GGRootNormInner (rE.subgroupOf (lE.map (MulAut.conj h).toMonoidHom)) := by
  have hR : rE.map (MulAut.conj h).toMonoidHom = rE := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hh y).mp hy
    · intro hx
      refine ⟨h⁻¹ * x * h, ?_, by group⟩
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hh) x).mp hx
      simpa [inv_inv] using this
  have hinj : Function.Injective (MulAut.conj h).toMonoidHom := (MulAut.conj h).injective
  exact ⟨ggRootNormNoCentral_of_map_injective _ hinj rfl hR ggRootNorm_rE_lE.1,
    ggRootNormInner_of_map_injective _ hinj rfl hR ggRootNorm_rE_lE.2⟩

end CFSG.StandardType.GGSixE6Two
