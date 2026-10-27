module

public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNodeLift
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.StandardType

open Matrix CFSG.RankThree.CALinearPlane CFSG.ComponentClassification
open CFSG.LieType.Universal.SpecialLinear

section Block

variable {N : ℕ} {F : Type} [Field F]

theorem commute_transvection_of_ne {i j k l : Fin N} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hil : i ≠ l) (c d : F) :
    Commute (SpecialLinearGroup.transvection hij c) (SpecialLinearGroup.transvection hkl d) := by
  show _ = _
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
    Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    single_mul_single_of_ne c i j k hjk d, single_mul_single_of_ne d k l i hil.symm c]
  abel

theorem apply_eq_zero_of_commute_transvection_one {g : SpecialLinearGroup (Fin N) F} {i j : Fin N}
    (hij : i ≠ j) (h : Commute g (SpecialLinearGroup.transvection hij 1)) :
    (∀ k, k ≠ i → (g : Matrix (Fin N) (Fin N) F) k i = 0) ∧
      ∀ l, l ≠ j → (g : Matrix (Fin N) (Fin N) F) j l = 0 := by
  have hm : (g : Matrix (Fin N) (Fin N) F) * (1 + single i j 1) =
      (1 + single i j 1) * (g : Matrix (Fin N) (Fin N) F) := by
    have h1 := congrArg Subtype.val h.eq
    simpa only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe] using h1
  refine ⟨fun k hk => ?_, fun l hl => ?_⟩
  · have h1 := congrFun (congrFun hm k) j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply,
      mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ hk, mul_one, add_zero] at h1
    linear_combination h1
  · have h1 := congrFun (congrFun hm i) l
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.add_apply,
      single_mul_apply_same, mul_single_apply_of_ne _ _ _ _ _ hl, one_mul, add_zero] at h1
    linear_combination -h1

theorem mem_coordBlockSL_of_commute (h2 : (2 : F) = 0) {g : SpecialLinearGroup (Fin N) F}
    (hg : g * g = 1) (J : Finset (Fin N))
    (hc : ∀ i, i ∉ J → ∃ j, ∃ hij : i ≠ j, Commute g (SpecialLinearGroup.transvection hij 1) ∧
      Commute g (SpecialLinearGroup.transvection hij.symm 1)) :
    g ∈ coordBlockSL F J := by
  have hcol : ∀ i, i ∉ J → ∀ k, k ≠ i → (g : Matrix (Fin N) (Fin N) F) k i = 0 :=
    fun i hi k hk => by
      obtain ⟨j, hij, h1, -⟩ := hc i hi
      exact (apply_eq_zero_of_commute_transvection_one hij h1).1 k hk
  have hrow : ∀ i, i ∉ J → ∀ l, l ≠ i → (g : Matrix (Fin N) (Fin N) F) i l = 0 :=
    fun i hi l hl => by
      obtain ⟨j, hij, -, h1⟩ := hc i hi
      exact (apply_eq_zero_of_commute_transvection_one hij.symm h1).2 l hl
  have hdiag : ∀ i, i ∉ J → (g : Matrix (Fin N) (Fin N) F) i i = 1 := fun i hi => by
    have h1 := congrFun (congrFun (congrArg Subtype.val hg) i) i
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq, Finset.sum_eq_single i
        (fun k _ hk => by rw [hrow i hi k hk, zero_mul]) (by simp)] at h1
    exact eq_one_of_mul_self_of_two h2 h1
  rw [mem_coordBlockSL_iff]
  rintro a b (ha | hb)
  · by_cases hab : a = b
    · subst hab
      simpa using hdiag a ha
    · simpa [hab] using hrow a ha b (Ne.symm hab)
  · by_cases hab : a = b
    · subst hab
      simpa using hdiag a hb
    · simpa [hab] using hcol b hb a hab

theorem blockSLOn_transvection (J : Finset (Fin N)) {a b : Fin J.card} (hab : a ≠ b) (c : F) :
    blockSLOn F J (SpecialLinearGroup.transvection hab c) =
      SpecialLinearGroup.transvection (show (J.equivFin.symm a : Fin N) ≠ J.equivFin.symm b from
        fun h => hab (J.equivFin.symm.injective (Subtype.ext h))) c := by
  apply Subtype.ext
  rw [coe_blockSLOn, SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe]
  ext i j
  have hamem : (J.equivFin.symm a : Fin N) ∈ J := (J.equivFin.symm a).2
  have hbmem : (J.equivFin.symm b : Fin N) ∈ J := (J.equivFin.symm b).2
  by_cases hi : i ∈ J
  · by_cases hj : j ∈ J
    · rw [blockOn_apply_mem J _ hi hj]
      have e1 : (a = J.equivFin ⟨i, hi⟩) ↔ ((J.equivFin.symm a : Fin N) = i) := by
        constructor
        · rintro rfl
          simp
        · intro h
          rw [← Equiv.apply_symm_apply J.equivFin a]
          congr 1
          exact Subtype.ext h
      have e2 : (b = J.equivFin ⟨j, hj⟩) ↔ ((J.equivFin.symm b : Fin N) = j) := by
        constructor
        · rintro rfl
          simp
        · intro h
          rw [← Equiv.apply_symm_apply J.equivFin b]
          congr 1
          exact Subtype.ext h
      have e3 : (J.equivFin ⟨i, hi⟩ = J.equivFin ⟨j, hj⟩) ↔ i = j := by
        rw [J.equivFin.injective.eq_iff, Subtype.mk.injEq]
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, e1, e2, e3]
    · rw [blockOn_apply_not_mem J _ (Or.inr hj)]
      have hne : ¬ ((J.equivFin.symm a : Fin N) = i ∧ (J.equivFin.symm b : Fin N) = j) :=
        fun h => hj (h.2 ▸ hbmem)
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, hne, ↓reduceIte,
        add_zero]
  · rw [blockOn_apply_not_mem J _ (Or.inl hi)]
    have hne : ¬ ((J.equivFin.symm a : Fin N) = i ∧ (J.equivFin.symm b : Fin N) = j) :=
      fun h => hi (h.1 ▸ hamem)
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, hne, ↓reduceIte, add_zero]

theorem coordBlockSL_le_closure (J : Finset (Fin N)) :
    coordBlockSL F J ≤ Subgroup.closure {g | ∃ (i j : Fin N) (hij : i ≠ j), i ∈ J ∧ j ∈ J ∧
      ∃ c : F, g = SpecialLinearGroup.transvection hij c} := by
  rw [← range_blockSLOn, MonoidHom.range_eq_map,
    ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin J.card)
      (K := F), MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨_, ⟨⟨a, b, hab, c⟩, rfl⟩, rfl⟩
  rw [TransvectionStruct.toSpecialLinearGroup_mk, blockSLOn_transvection]
  exact ⟨_, _, _, (J.equivFin.symm a).2, (J.equivFin.symm b).2, c, rfl⟩

end Block

theorem commute_of_mem_closure {S X : Type*} [Group S] [Group X] (φ : S →* X) {t : X} {A : Set S}
    (hA : ∀ g ∈ A, Commute t (φ g)) {g : S} (hg : g ∈ Subgroup.closure A) : Commute t (φ g) := by
  have hle : Subgroup.closure A ≤ (Subgroup.centralizer ({t} : Set X)).comap φ := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact (hA a ha).symm.eq
  have h1 := hle hg
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at h1
  exact h1.symm

section Weyl

variable {F : Type} [Field F]

theorem commute_weylRep_zero_slLowerBlockHom₂ (h2 : (2 : F) = 0) {m : ℕ}
    (h : SpecialLinearGroup (Fin m) F) :
    Commute (weylRep (m + 1) F 0) (slLowerBlockHom (m + 1) F (slLowerBlockHom m F h)) := by
  have hmem : h ∈ Subgroup.closure
      (Set.range (TransvectionStruct.toSpecialLinearGroup (ι := Fin m) (F := F))) := by
    rw [SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
    exact Subgroup.mem_top h
  refine commute_of_mem_closure ((slLowerBlockHom (m + 1) F).comp (slLowerBlockHom m F)) ?_ hmem
  rintro _ ⟨⟨a, b, hab, c⟩, rfl⟩
  rw [TransvectionStruct.toSpecialLinearGroup_mk, MonoidHom.comp_apply,
    slLowerBlockHom_transvection, slLowerBlockHom_transvection]
  exact weylRep_commute_transvection_of_two h2 0 _
    (by rw [Fin.castSucc_zero]; exact Fin.succ_ne_zero _)
    (fun e => Fin.succ_ne_zero a (Fin.succ_injective _ e))
    (by rw [Fin.castSucc_zero]; exact Fin.succ_ne_zero _)
    (fun e => Fin.succ_ne_zero b (Fin.succ_injective _ e)) c

theorem commute_weylRep_last_slUpperBlockHom₂ (h2 : (2 : F) = 0) {m : ℕ}
    (h : SpecialLinearGroup (Fin m) F) :
    Commute (weylRep (m + 1) F (Fin.last m))
      (slUpperBlockHom (m + 1) F (slUpperBlockHom m F h)) := by
  have hmem : h ∈ Subgroup.closure
      (Set.range (TransvectionStruct.toSpecialLinearGroup (ι := Fin m) (F := F))) := by
    rw [SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
    exact Subgroup.mem_top h
  refine commute_of_mem_closure ((slUpperBlockHom (m + 1) F).comp (slUpperBlockHom m F)) ?_ hmem
  rintro _ ⟨⟨a, b, hab, c⟩, rfl⟩
  rw [TransvectionStruct.toSpecialLinearGroup_mk, MonoidHom.comp_apply,
    slUpperBlockHom_transvection, slUpperBlockHom_transvection]
  have ha := a.isLt
  have hb := b.isLt
  exact weylRep_commute_transvection_of_two h2 (Fin.last m) _
    (by rw [Ne, Fin.ext_iff]; simp; omega) (by rw [Ne, Fin.ext_iff]; simp; omega)
    (by rw [Ne, Fin.ext_iff]; simp; omega) (by rw [Ne, Fin.ext_iff]; simp; omega) c

end Weyl

section Conj

variable {m : ℕ} {F : Type} [Field F]

theorem diagonal_eq_slUpperBlockMat {w : Fin (m + 1) → F} (hw : w (Fin.last m) = 1) :
    Matrix.diagonal w = slUpperBlockMat m F (Matrix.diagonal fun i => w i.castSucc) := by
  ext a b
  obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective b
  rw [slUpperBlockMat_apply]
  rcases p with p | p <;> rcases q with q | q
  · simp [Matrix.diagonal_apply, slBlock_castAdd_one_eq]
  · obtain rfl : q = 0 := Subsingleton.elim _ _
    simp [slBlock_castAdd_one_eq, slBlock_natAdd_zero_eq_last, Fin.castSucc_ne_last]
  · obtain rfl : p = 0 := Subsingleton.elim _ _
    simp [slBlock_castAdd_one_eq, slBlock_natAdd_zero_eq_last, (Fin.castSucc_ne_last _).symm]
  · obtain rfl : p = 0 := Subsingleton.elim _ _
    obtain rfl : q = 0 := Subsingleton.elim _ _
    simp [slBlock_natAdd_zero_eq_last, hw]

theorem exists_sl_slConjugation_slBlocks (hm : 1 ≤ m) (A : GL (Fin (m + 1)) F) :
    ∃ (s : SpecialLinearGroup (Fin (m + 1)) F) (D : GL (Fin m) F),
      (∀ g, CatalogueBHigherLinearAction.slConjugation (m + 1) F A (slLowerBlockHom m F g) =
        s * slLowerBlockHom m F g * s⁻¹) ∧
      ∀ g, CatalogueBHigherLinearAction.slConjugation (m + 1) F A (slUpperBlockHom m F g) =
        s * slUpperBlockHom m F (CatalogueBHigherLinearAction.slConjugation m F D g) * s⁻¹ := by
  have hδ0 : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero
  set v : Fin (m + 1) → F :=
    fun i => if i = 0 then ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det)⁻¹ else 1 with hvdef
  have hv1 : ∀ i, i ≠ 0 → v i = 1 := fun i hi => by simp [hvdef, hi]
  have hv0 : ∀ i, v i ≠ 0 := fun i => by
    by_cases hi : i = 0
    · simp [hvdef, hi, hδ0]
    · rw [hv1 i hi]
      exact one_ne_zero
  have hv : (Matrix.diagonal v).det = ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det)⁻¹ := by
    rw [Matrix.det_diagonal, Fin.prod_univ_succ, Finset.prod_eq_one
      (fun i _ => hv1 _ (Fin.succ_ne_zero i)), mul_one]
    simp [hvdef]
  let s : SpecialLinearGroup (Fin (m + 1)) F :=
    ⟨(A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Matrix.diagonal v,
      by rw [Matrix.det_mul, hv, mul_inv_cancel₀ hδ0]⟩
  set w : Fin m → F := fun i => v i.castSucc with hwdef
  have hw1 : Matrix.diagonal (fun i => (w i)⁻¹) * Matrix.diagonal w = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hv0 _)
  have hw2 : Matrix.diagonal w * Matrix.diagonal (fun i => (w i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hv0 _)
  let D : GL (Fin m) F := ⟨Matrix.diagonal fun i => (w i)⁻¹, Matrix.diagonal w, hw1, hw2⟩
  have hlast : v (Fin.last m) = 1 := hv1 _ (by rw [Ne, Fin.ext_iff]; simp; omega)
  have hvU : Matrix.diagonal v = slUpperBlockMat m F (Matrix.diagonal w) :=
    diagonal_eq_slUpperBlockMat hlast
  have hAinv : ((A⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := Units.inv_mul A
  refine ⟨s, D, fun g => ?_, fun g => ?_⟩
  · rw [eq_comm, mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      CatalogueBHigherLinearAction.slConjugation_matrix, coe_slLowerBlockHom]
    change (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Matrix.diagonal v *
        slLowerBlockMat m F (g : Matrix (Fin m) (Fin m) F) =
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
          slLowerBlockMat m F (g : Matrix (Fin m) (Fin m) F) *
        ((A⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
          ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Matrix.diagonal v)
    rw [Matrix.mul_assoc (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (Matrix.diagonal v),
      diagonal_mul_slLowerBlockMat hv1, Matrix.mul_assoc _ (((A⁻¹ : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F)), ← Matrix.mul_assoc (((A⁻¹ : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F)), hAinv, Matrix.one_mul, Matrix.mul_assoc]
  · rw [eq_comm, mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      CatalogueBHigherLinearAction.slConjugation_matrix, coe_slUpperBlockHom, coe_slUpperBlockHom,
      CatalogueBHigherLinearAction.slConjugation_matrix]
    change (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Matrix.diagonal v *
        slUpperBlockMat m F (Matrix.diagonal (fun i => (w i)⁻¹) *
          (g : Matrix (Fin m) (Fin m) F) * Matrix.diagonal w) =
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
          slUpperBlockMat m F (g : Matrix (Fin m) (Fin m) F) *
        ((A⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
          ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Matrix.diagonal v)
    have key : Matrix.diagonal w * (Matrix.diagonal (fun i => (w i)⁻¹) *
        (g : Matrix (Fin m) (Fin m) F) * Matrix.diagonal w) =
        (g : Matrix (Fin m) (Fin m) F) * Matrix.diagonal w := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hw2, Matrix.one_mul]
    rw [hvU, Matrix.mul_assoc (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F), ← slUpperBlockMat_mul,
      key, slUpperBlockMat_mul, Matrix.mul_assoc _ (((A⁻¹ : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F)), ← Matrix.mul_assoc (((A⁻¹ : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F)), hAinv, Matrix.one_mul, Matrix.mul_assoc]

theorem map_range_eq_map_conj_of_apply {S T : Type*} [Group S] [Group T] (ι : S →* T)
    (α : MulAut T) (β : MulAut S) (s : T) (h : ∀ g, α (ι g) = s * ι (β g) * s⁻¹) :
    ι.range.map α.toMonoidHom = ι.range.map (MulAut.conj s).toMonoidHom := by
  ext z
  simp only [Subgroup.mem_map, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨_, ⟨β g, rfl⟩, (h g).symm⟩
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    refine ⟨_, ⟨β⁻¹ g, rfl⟩, ?_⟩
    rw [h, show β (β⁻¹ g) = g from MulEquiv.apply_symm_apply β g]

theorem exists_conj_slBlocks_of_mulAut [Finite F] (hm : 2 ≤ m)
    (β : MulAut (SpecialLinearGroup (Fin (m + 1)) F)) :
    ∃ s : SpecialLinearGroup (Fin (m + 1)) F,
      (slLowerBlockHom m F).range.map β.toMonoidHom =
        (slLowerBlockHom m F).range.map (MulAut.conj s).toMonoidHom ∧
      (slUpperBlockHom m F).range.map β.toMonoidHom =
        (slUpperBlockHom m F).range.map (MulAut.conj s).toMonoidHom := by
  obtain ⟨A, σ, ε, hε, rfl⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl (by omega : 3 ≤ m + 1) β
  obtain ⟨s, D, hsL, hsU⟩ := exists_sl_slConjugation_slBlocks (by omega : 1 ≤ m) A
  refine ⟨s, map_range_eq_map_conj_of_apply _ _
    (CatalogueBHigherLinearField.slFieldAut (Fin m) F σ * CatalogueBGraphForm.slGraphAut m F ^ ε) s
    fun g => ?_, map_range_eq_map_conj_of_apply _ _
    (CatalogueBHigherLinearAction.slConjugation m F D *
      CatalogueBHigherLinearField.slFieldAut (Fin m) F σ * CatalogueBGraphForm.slGraphAut m F ^ ε) s
    fun g => ?_⟩
  · have hγ : (CatalogueBGraphForm.slGraphAut (m + 1) F ^ ε) (slLowerBlockHom m F g) =
        slLowerBlockHom m F ((CatalogueBGraphForm.slGraphAut m F ^ ε) g) := by
      interval_cases ε
      · rfl
      · simp only [pow_one]
        exact slGraphAut_slLowerBlockHom g
    simp only [MulAut.mul_apply]
    rw [hγ, slFieldAut_slLowerBlockHom, hsL]
  · have hγ : (CatalogueBGraphForm.slGraphAut (m + 1) F ^ ε) (slUpperBlockHom m F g) =
        slUpperBlockHom m F ((CatalogueBGraphForm.slGraphAut m F ^ ε) g) := by
      interval_cases ε
      · rfl
      · simp only [pow_one]
        exact slGraphAut_slUpperBlockHom g
    simp only [MulAut.mul_apply]
    rw [hγ, slFieldAut_slUpperBlockHom, hsU]

end Conj

end CFSG.StandardType
