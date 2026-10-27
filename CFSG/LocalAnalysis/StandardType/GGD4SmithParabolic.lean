module

public import CFSG.Quasithin.Background.SmithParabolic
public import CFSG.Quasithin.Background.SmithCurtisChevType
public import CFSG.LocalAnalysis.StandardType.GGD4SmithRoots
public import CFSG.ClassicalGroups.Orthogonal.RootGroupGLEichler
public import CFSG.LocalAnalysis.StandardType.GGD4AdjointOm8
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard

public section

namespace CFSG.StandardType.TriBridge

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ClassicalGroups.Orthogonal (rootGroupGL lineStabilizer conj_mem_rootGroupGL
  mem_rootGroupGL_of_eichlerC mem_rootGroupGL_of_eichlerC_smul_right eichlerC_eq_self
  eichlerC_zero_right eichlerC_eichlerC mem_lineStabilizer_iff)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  (matrixDerived matrixDerived_le_isometries mem_matrixIsometries_iff matrixLinearEquiv_apply)
open CFSG.ClassicalGroups.Orthogonal (exists_eichlerC_of_mem_rootGroupGL)
open CFSG.Quasithin.SmithCurtis
open CFSG.Quasithin.SmithCurtis.Chev
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.StandardType.AutOm (eichlerC)
open CFSG.StandardType.Triality

theorem mem_span_pvec_of_polar_eq_zero {K : Type} [Field K] {n : ℕ} (i : Fin n)
    {w : Fin (2 * n) → K}
    (h1 : QuadraticMap.polar (coordinateQuadPlus n K) w (AutOm.pvec i true) = 0)
    (h2 : QuadraticMap.polar (coordinateQuadPlus n K) w (AutOm.pvec i false) = 0) :
    w ∈ Submodule.span K {v | ∃ k : Fin n, k ≠ i ∧ ∃ r : Bool, AutOm.pvec k r = v} := by
  classical
  obtain ⟨w', rfl⟩ := (reindexVectorEquiv (K := K) (plusIndexEquiv n)).surjective w
  have h1' : w' (.inr i) = 0 := by
    have h := h1
    rw [AutOm.pvec_true, ← AutOm.reindex_single, AutOm.polar_reindex_plus,
      CFSG.LieType.Universal.Spin.polar_quadPlus_single_inl] at h
    exact h
  have h2' : w' (.inl i) = 0 := by
    have h := h2
    rw [AutOm.pvec_false, ← AutOm.reindex_single, AutOm.polar_reindex_plus,
      CFSG.LieType.Universal.Spin.polar_quadPlus_single_inr] at h
    exact h
  have hsingle_smul : ∀ {ι : Type} [DecidableEq ι] (x : ι) (a : K),
      Pi.single x a = a • (Pi.single x 1 : ι → K) := by
    intro ι _ x a
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  have hsingle : ∀ (x : Fin n ⊕ Fin n) (a : K),
      reindexVectorEquiv (plusIndexEquiv n) (Pi.single x a) =
        Pi.single (plusIndexEquiv n x) a := by
    intro x a
    rw [hsingle_smul x a, LinearEquiv.map_smul, AutOm.reindex_single,
      ← hsingle_smul (plusIndexEquiv n x) a]
  have hw : reindexVectorEquiv (plusIndexEquiv n) w' =
      ∑ a : Fin n ⊕ Fin n, w' a • Pi.single (plusIndexEquiv n a) 1 := by
    conv_lhs => rw [← Finset.univ_sum_single w']
    rw [map_sum]
    simp only [hsingle, ← Pi.single_smul, smul_eq_mul, mul_one]
  rw [hw]
  refine Submodule.sum_mem _ fun a _ => ?_
  rcases a with k | k
  · by_cases hk : k = i
    · subst hk
      rw [h2', zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, true, by rw [AutOm.pvec_true]⟩)
  · by_cases hk : k = i
    · subst hk
      rw [h1', zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, false, by rw [AutOm.pvec_false]⟩)

theorem exists_closure_X8_eichlerC {K : Type} [Field K] [CharP K 2]
    {w : Fin (2 * 4) → K}
    (hw : w ∈ Submodule.span K
      {v : Fin (2 * 4) → K | ∃ k : Fin 4, k ≠ 1 ∧ ∃ r : Bool, AutOm.pvec k r = v})
    (c : K) :
    ∃ x ∈ Subgroup.closure
      {x : Om8 K | ∃ k : Fin 4, k ≠ 1 ∧ ∃ r : Bool, ∃ c : K,
        X8 (fromStd (lv k 1 r false)) c = x},
      ∀ y, Matrix.mulVec (((x : Om8 K) : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) y =
        eichlerC (coordinateQuadPlus 4 K) (AutOm.pvec 1 false) (c • w) y := by
  classical
  let Q := coordinateQuadPlus 4 K
  let f : Fin (2 * 4) → K := AutOm.pvec 1 false
  let S : Set (Om8 K) :=
    {x | ∃ k : Fin 4, k ≠ 1 ∧ ∃ r : Bool, ∃ c : K,
      X8 (fromStd (lv k 1 r false)) c = x}
  have hspan_polar : ∀ v ∈ Submodule.span K
      {v : Fin (2 * 4) → K | ∃ k : Fin 4, k ≠ 1 ∧ ∃ r : Bool, AutOm.pvec k r = v},
      QuadraticMap.polar Q f v = 0 := by
    intro v hv
    refine Submodule.span_induction (p := fun v _ => QuadraticMap.polar Q f v = 0) ?_ ?_ ?_ ?_ hv
    · rintro v ⟨k, hk, r, rfl⟩
      exact AutOm.polar_pvec_of_ne (Ne.symm hk) false r
    · simp
    · intro a b _ _ ha hb
      rw [QuadraticMap.polar_add_right, ha, hb, add_zero]
    · intro a v _ hv
      rw [QuadraticMap.polar_smul_right, hv, smul_zero]
  revert c
  change ∀ c : K, ∃ x ∈ Subgroup.closure S,
    ∀ y, Matrix.mulVec (((x : Om8 K) : GL (Fin (2 * 4)) K) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) y = eichlerC Q f (c • w) y
  refine Submodule.span_induction (p := fun w _ => ∀ c : K, ∃ x ∈ Subgroup.closure S,
    ∀ y, Matrix.mulVec (((x : Om8 K) : GL (Fin (2 * 4)) K) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) y = eichlerC Q f (c • w) y) ?_ ?_ ?_ ?_ hw
  · rintro v ⟨k, hk, r, rfl⟩ c
    refine ⟨X8 (fromStd (lv k 1 r false)) c,
      Subgroup.subset_closure ⟨k, hk, r, c, rfl⟩, ?_⟩
    intro y
    exact X8_mulVec (γ := fromStd (lv k 1 r false)) (i := k) (j := 1)
      (s := r) (t := false) hk (roots_check k 1 r false hk).1 c y
  · intro c
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    intro y
    rw [smul_zero, eichlerC_zero_right]
    simp
  · intro a b ha hb pa pb c
    obtain ⟨x, hx, hxact⟩ := pa c
    obtain ⟨y, hy, hyact⟩ := pb c
    refine ⟨x * y, mul_mem hx hy, ?_⟩
    intro z
    have hfa : QuadraticMap.polar Q f (c • a) = 0 := by
      rw [QuadraticMap.polar_smul_right, hspan_polar a ha, smul_zero]
    have hfb : QuadraticMap.polar Q f (c • b) = 0 := by
      rw [QuadraticMap.polar_smul_right, hspan_polar b hb, smul_zero]
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hxact, hyact,
      eichlerC_eichlerC Q (AutOm.form_pvec 1 false) hfa hfb z, smul_add]
  · intro a v hv pv c
    obtain ⟨x, hx, hxact⟩ := pv (c * a)
    refine ⟨x, hx, ?_⟩
    intro z
    rw [hxact z, smul_smul]

theorem mem_closure_X8_of_mem_rootGroupGL {K : Type} [Field K] [CharP K 2] {g : Om8 K}
    (hg : (g : GL (Fin (2 * 4)) K) ∈
      rootGroupGL (coordinateQuadPlus 4 K) (AutOm.pvec 1 false)) :
    g ∈ Subgroup.closure
      {x : Om8 K | ∃ k : Fin 4, k ≠ 1 ∧ ∃ r : Bool, ∃ c : K,
        X8 (fromStd (lv k 1 r false)) c = x} := by
  classical
  let Q := coordinateQuadPlus 4 K
  let f : Fin (2 * 4) → K := AutOm.pvec 1 false
  let S : Set (Om8 K) :=
    {x | ∃ k : Fin 4, k ≠ 1 ∧ ∃ r : Bool, ∃ c : K,
      X8 (fromStd (lv k 1 r false)) c = x}
  obtain ⟨w, hwe, hwf, hgact⟩ :=
    exists_eichlerC_of_mem_rootGroupGL Q (AutOm.form_pvec 1 true)
      (AutOm.form_pvec 1 false) (AutOm.polar_pvec_not 1 true) hg
  have hwspan : w ∈ Submodule.span K
      {v : Fin (2 * 4) → K | ∃ k : Fin 4, k ≠ 1 ∧ ∃ r : Bool, AutOm.pvec k r = v} :=
    mem_span_pvec_of_polar_eq_zero (i := 1) hwe hwf
  obtain ⟨x, hx, hxact⟩ := exists_closure_X8_eichlerC hwspan 1
  have hgx : g = x := by
    refine Subtype.ext (Units.ext (Matrix.ext_iff_mulVec.2 fun y => ?_))
    rw [hgact y, hxact y, one_smul]
  change g ∈ Subgroup.closure S
  rw [hgx]
  exact hx

theorem isometry_X8 {K : Type} [Field K] {γ : Fin 4 → ℤ} (c : K) :
    ∀ y, coordinateQuadPlus 4 K
      (Matrix.mulVec (((X8 γ c : Om8 K) : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) y) = coordinateQuadPlus 4 K y := by
  intro y
  simpa only [matrixLinearEquiv_apply] using
    (mem_matrixIsometries_iff _ _).1 (matrixDerived_le_isometries _ (X8 γ c).2) y

theorem mem_rootGroupGL_of_X8_lv_one_true {K : Type} [Field K] [CharP K 2]
    {j : Fin 4} (hj : 1 ≠ j) (t : Bool) (c : K) :
    ((X8 (fromStd (lv 1 j true t)) c : Om8 K) : GL (Fin (2 * 4)) K) ∈
      rootGroupGL (coordinateQuadPlus 4 K) (AutOm.pvec 1 true) := by
  refine mem_rootGroupGL_of_eichlerC_smul_right (Q := coordinateQuadPlus 4 K)
    (e := AutOm.pvec 1 true)
    (u := AutOm.pvec j t)
    (g := ((X8 (fromStd (lv 1 j true t)) c : Om8 K) : GL (Fin (2 * 4)) K))
    c (AutOm.form_pvec 1 true) (AutOm.form_pvec j t)
    (AutOm.polar_pvec_of_ne (Ne.symm hj) t true) (fun y => ?_)
  exact X8_mulVec (γ := fromStd (lv 1 j true t)) (i := 1) (j := j) (s := true) (t := t)
    hj (roots_check 1 j true t hj).1 c y

theorem mem_rootGroupGL_of_X8_lv_one_false {K : Type} [Field K] [CharP K 2]
    {j : Fin 4} (hj : 1 ≠ j) (t : Bool) (c : K) :
    ((X8 (fromStd (lv 1 j false t)) c : Om8 K) : GL (Fin (2 * 4)) K) ∈
      rootGroupGL (coordinateQuadPlus 4 K) (AutOm.pvec 1 false) := by
  refine mem_rootGroupGL_of_eichlerC_smul_right (Q := coordinateQuadPlus 4 K)
    (e := AutOm.pvec 1 false) (u := AutOm.pvec j t)
    (g := ((X8 (fromStd (lv 1 j false t)) c : Om8 K) : GL (Fin (2 * 4)) K))
    c (AutOm.form_pvec 1 false) (AutOm.form_pvec j t)
    (AutOm.polar_pvec_of_ne (Ne.symm hj) t false) (fun y => ?_)
  exact X8_mulVec (γ := fromStd (lv 1 j false t)) (i := 1) (j := j) (s := false) (t := t)
    hj (roots_check 1 j false t hj).1 c y

theorem mem_rootGroupGL_of_X8_lv_right_true {K : Type} [Field K] [CharP K 2]
    {i : Fin 4} (hi : i ≠ 1) (s : Bool) (c : K) :
    ((X8 (fromStd (lv i 1 s true)) c : Om8 K) : GL (Fin (2 * 4)) K) ∈
      rootGroupGL (coordinateQuadPlus 4 K) (AutOm.pvec 1 true) := by
  refine mem_rootGroupGL_of_eichlerC (Q := coordinateQuadPlus 4 K)
    (e := AutOm.pvec 1 true) (w := c • AutOm.pvec i s)
    (g := ((X8 (fromStd (lv i 1 s true)) c : Om8 K) : GL (Fin (2 * 4)) K))
    (AutOm.form_pvec 1 true) ?_ (fun y => ?_)
  · rw [QuadraticMap.polar_smul_right, AutOm.polar_pvec_of_ne (Ne.symm hi) true s, smul_zero]
  · exact X8_mulVec (γ := fromStd (lv i 1 s true)) (i := i) (j := 1) (s := s) (t := true)
      hi (roots_check i 1 s true hi).1 c y

theorem mem_rootGroupGL_of_X8_lv_right_false {K : Type} [Field K] [CharP K 2]
    {i : Fin 4} (hi : i ≠ 1) (s : Bool) (c : K) :
    ((X8 (fromStd (lv i 1 s false)) c : Om8 K) : GL (Fin (2 * 4)) K) ∈
      rootGroupGL (coordinateQuadPlus 4 K) (AutOm.pvec 1 false) := by
  refine mem_rootGroupGL_of_eichlerC (Q := coordinateQuadPlus 4 K)
    (e := AutOm.pvec 1 false) (w := c • AutOm.pvec i s)
    (g := ((X8 (fromStd (lv i 1 s false)) c : Om8 K) : GL (Fin (2 * 4)) K))
    (AutOm.form_pvec 1 false) ?_ (fun y => ?_)
  · rw [QuadraticMap.polar_smul_right, AutOm.polar_pvec_of_ne (Ne.symm hi) false s, smul_zero]
  · exact X8_mulVec (γ := fromStd (lv i 1 s false)) (i := i) (j := 1) (s := s) (t := false)
      hi (roots_check i 1 s false hi).1 c y

theorem mem_lineStabilizer_inf_of_ne {K : Type} [Field K] [CharP K 2] {i j : Fin 4}
    (hij : i ≠ j) (hi : i ≠ 1) (hj : j ≠ 1) (s t : Bool) (c : K) :
    ((X8 (fromStd (lv i j s t)) c : Om8 K) : GL (Fin (2 * 4)) K) ∈
      lineStabilizer (coordinateQuadPlus 4 K) (AutOm.pvec 1 true) ⊓
        lineStabilizer (coordinateQuadPlus 4 K) (AutOm.pvec 1 false) := by
  have he : QuadraticMap.polar (coordinateQuadPlus 4 K) (AutOm.pvec 1 true)
      (AutOm.pvec j t) = 0 := AutOm.polar_pvec_of_ne (Ne.symm hj) true t
  have hew : QuadraticMap.polar (coordinateQuadPlus 4 K) (AutOm.pvec 1 true)
      (c • AutOm.pvec i s) = 0 := by
    rw [QuadraticMap.polar_smul_right, AutOm.polar_pvec_of_ne (Ne.symm hi) true s, smul_zero]
  have hf : QuadraticMap.polar (coordinateQuadPlus 4 K) (AutOm.pvec 1 false)
      (AutOm.pvec j t) = 0 := AutOm.polar_pvec_of_ne (Ne.symm hj) false t
  have hfw : QuadraticMap.polar (coordinateQuadPlus 4 K) (AutOm.pvec 1 false)
      (c • AutOm.pvec i s) = 0 := by
    rw [QuadraticMap.polar_smul_right, AutOm.polar_pvec_of_ne (Ne.symm hi) false s, smul_zero]
  have hfixe : Matrix.mulVec (((X8 (fromStd (lv i j s t)) c : Om8 K) :
      GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)
      (AutOm.pvec 1 true) = AutOm.pvec 1 true := by
    rw [X8_mulVec (γ := fromStd (lv i j s t)) (i := i) (j := j) (s := s) (t := t) hij
      (roots_check i j s t hij).1 c (AutOm.pvec 1 true)]
    exact eichlerC_eq_self (coordinateQuadPlus 4 K) he hew
  have hfixf : Matrix.mulVec (((X8 (fromStd (lv i j s t)) c : Om8 K) :
      GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)
      (AutOm.pvec 1 false) = AutOm.pvec 1 false := by
    rw [X8_mulVec (γ := fromStd (lv i j s t)) (i := i) (j := j) (s := s) (t := t) hij
      (roots_check i j s t hij).1 c (AutOm.pvec 1 false)]
    exact eichlerC_eq_self (coordinateQuadPlus 4 K) hf hfw
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_lineStabilizer_iff (coordinateQuadPlus 4 K)]
    exact ⟨isometry_X8 c, 1, by rw [hfixe, one_smul]⟩
  · rw [mem_lineStabilizer_iff (coordinateQuadPlus 4 K)]
    exact ⟨isometry_X8 c, 1, by rw [hfixf, one_smul]⟩

theorem X8_bLinv_mem_of_pos {K : Type} [Field K] [CharP K 2]
    {β : Fin TwistTag.D4.tag.rank → ℤ} (hβ : IsRoot TwistTag.D4.tag β) (h : 0 < height β)
    (c : K) :
    ((X8 (bLinv β) c : Om8 K) : GL (Fin (2 * 4)) K) ∈
        rootGroupGL (coordinateQuadPlus 4 K) (AutOm.pvec 1 true) ∨
      ((X8 (bLinv β) c : Om8 K) : GL (Fin (2 * 4)) K) ∈
        lineStabilizer (coordinateQuadPlus 4 K) (AutOm.pvec 1 true) ⊓
          lineStabilizer (coordinateQuadPlus 4 K) (AutOm.pvec 1 false) := by
  obtain ⟨i, j, s, t, hij, hstd, hfrom⟩ := exists_eq_fromStd (bLinv_mem hβ)
  rw [hfrom]
  have hsign : 0 ≤ (lv i j s t) 1 := by
    rw [← hstd]
    exact zero_le_toStdD_bLinv_one hβ h
  by_cases hi : i = 1
  · subst hi
    have hj : j ≠ 1 := fun h' => hij h'.symm
    have hs : s = true := by
      cases s with
      | false => simp [lv, Pi.single_apply, hj, CFSG.LieType.Universal.Spin.boolSign] at hsign
      | true => rfl
    subst hs
    exact Or.inl (mem_rootGroupGL_of_X8_lv_one_true hij t c)
  · by_cases hj : j = 1
    · subst hj
      have ht : t = true := by
        cases t with
        | false => simp [lv, Pi.single_apply, hi, CFSG.LieType.Universal.Spin.boolSign] at hsign
        | true => rfl
      subst ht
      exact Or.inl (mem_rootGroupGL_of_X8_lv_right_true hi s c)
    · exact Or.inr (mem_lineStabilizer_inf_of_ne hij hi hj s t c)

theorem X8_bLinv_mem_of_neg {K : Type} [Field K] [CharP K 2]
    {β : Fin TwistTag.D4.tag.rank → ℤ} (hβ : IsRoot TwistTag.D4.tag β) (h : height β < 0)
    (c : K) :
    ((X8 (bLinv β) c : Om8 K) : GL (Fin (2 * 4)) K) ∈
        rootGroupGL (coordinateQuadPlus 4 K) (AutOm.pvec 1 false) ∨
      ((X8 (bLinv β) c : Om8 K) : GL (Fin (2 * 4)) K) ∈
        lineStabilizer (coordinateQuadPlus 4 K) (AutOm.pvec 1 true) ⊓
          lineStabilizer (coordinateQuadPlus 4 K) (AutOm.pvec 1 false) := by
  obtain ⟨i, j, s, t, hij, hstd, hfrom⟩ := exists_eq_fromStd (bLinv_mem hβ)
  rw [hfrom]
  have hsign : (lv i j s t) 1 ≤ 0 := by
    rw [← hstd]
    exact toStdD_bLinv_one_nonpos hβ h
  by_cases hi : i = 1
  · subst hi
    have hj : j ≠ 1 := fun h' => hij h'.symm
    have hs : s = false := by
      cases s with
      | true => simp [lv, Pi.single_apply, hj, CFSG.LieType.Universal.Spin.boolSign] at hsign
      | false => rfl
    subst hs
    exact Or.inl (mem_rootGroupGL_of_X8_lv_one_false hij t c)
  · by_cases hj : j = 1
    · subst hj
      have ht : t = false := by
        cases t with
        | true => simp [lv, Pi.single_apply, hi, CFSG.LieType.Universal.Spin.boolSign] at hsign
        | false => rfl
      subst ht
      exact Or.inl (mem_rootGroupGL_of_X8_lv_right_false hi s c)
    · exact Or.inr (mem_lineStabilizer_inf_of_ne hij hi hj s t c)

theorem comap_conj_mem {K : Type} [Field K] {Φ : adjointGroup .D4 K ≃* Om8 K}
    {e : Fin (2 * 4) → K} {m x : adjointGroup .D4 K}
    (hm : Φ m ∈ (lineStabilizer (coordinateQuadPlus 4 K) e).subgroupOf
      (matrixDerived (coordinateQuadPlus 4 K)))
    (hx : Φ x ∈ (rootGroupGL (coordinateQuadPlus 4 K) e).subgroupOf
      (matrixDerived (coordinateQuadPlus 4 K))) :
    Φ (m * x * m⁻¹) ∈ (rootGroupGL (coordinateQuadPlus 4 K) e).subgroupOf
      (matrixDerived (coordinateQuadPlus 4 K)) := by
  change (Φ (m * x * m⁻¹) : GL (Fin (2 * 4)) K) ∈
    rootGroupGL (coordinateQuadPlus 4 K) e
  rw [map_mul, map_mul, map_inv]
  exact conj_mem_rootGroupGL (Subgroup.mem_subgroupOf.mp hm)
    (Subgroup.mem_subgroupOf.mp hx)

theorem comap_rootGroupGL_le_negUnipotent
    {K : Type} [Field K] [CharP K 2] {Φ : adjointGroup .D4 K ≃* Om8 K}
    (hΦ : ∀ β ∈ rootFinset .D4, ∀ c : K,
      Φ ⟨pinnedX .D4 K β c, pinnedX_mem_adjointGroup β c⟩ = X8 (bLinv β) c) :
    Subgroup.comap Φ.toMonoidHom
        ((rootGroupGL (coordinateQuadPlus 4 K) (AutOm.pvec 1 false)).subgroupOf
          (matrixDerived (coordinateQuadPlus 4 K))) ≤
      (negUnipotent .D4 K).subgroupOf (adjointGroup .D4 K) := by
  let S : Set (Om8 K) :=
    {x | ∃ k : Fin 4, k ≠ 1 ∧ ∃ r : Bool, ∃ c : K,
      X8 (fromStd (lv k 1 r false)) c = x}
  intro x hx
  rw [Subgroup.mem_comap] at hx
  have hxS : Φ x ∈ Subgroup.closure S :=
    mem_closure_X8_of_mem_rootGroupGL (g := Φ x) (Subgroup.mem_subgroupOf.mp hx)
  have hcoe : ∀ (γ : Fin 4 → ℤ) (hγ : γ ∈ rootsD4) (c : K),
      Φ.symm (X8 γ c) = ⟨pinnedX .D4 K (bL γ) c, pinnedX_mem_adjointGroup _ _⟩ := by
    intro γ hγ c
    refine (Φ.symm_apply_eq).mpr ?_
    have h := hΦ (bL γ) (mem_rootFinset.2 (isRoot_bL hγ)) c
    rw [bLinv_bL] at h
    exact h.symm
  have hSle : Subgroup.closure S ≤
      ((negUnipotent .D4 K).subgroupOf (adjointGroup .D4 K)).map Φ.toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro g ⟨k, hk, r, c, rfl⟩
    refine ⟨Φ.symm (X8 (fromStd (lv k 1 r false)) c), ?_, ?_⟩
    · change (Φ.symm (X8 (fromStd (lv k 1 r false)) c) : ModGL .D4 K) ∈ negUnipotent .D4 K
      have hγ : fromStd (lv k 1 r false) ∈ rootsD4 :=
        mem_rootsD4_iff.2 ⟨k, 1, hk, r, false, (roots_check k 1 r false hk).1⟩
      rw [hcoe (fromStd (lv k 1 r false)) hγ c]
      rw [negUnipotent, rootSpan]
      exact Subgroup.mem_iSup_of_mem (bL (fromStd (lv k 1 r false)))
        (Subgroup.mem_iSup_of_mem ⟨isRoot_bL hγ, height_bL_negOne hk r⟩
          (Subgroup.subset_closure ⟨c, rfl⟩))
    · exact Φ.apply_symm_apply (X8 (fromStd (lv k 1 r false)) c)
  obtain ⟨y, hy, hyx⟩ := hSle hxS
  have hyx' : y = x := Φ.injective hyx
  rwa [hyx'] at hy

theorem pinnedX_mem_comap_sup_of_pos
    {K : Type} [Field K] [CharP K 2]
    {Φ : adjointGroup .D4 K ≃* Om8 K}
    (hΦ : ∀ β ∈ rootFinset .D4, ∀ c : K,
      Φ ⟨pinnedX .D4 K β c, pinnedX_mem_adjointGroup β c⟩ = X8 (bLinv β) c)
    {γ : Fin TwistTag.D4.tag.rank → ℤ} (hγ : IsRoot TwistTag.D4.tag γ) (h : 0 < height γ)
    (c : K) :
    (⟨pinnedX .D4 K γ c, pinnedX_mem_adjointGroup γ c⟩ : adjointGroup .D4 K) ∈
      Subgroup.comap Φ.toMonoidHom
          ((rootGroupGL (coordinateQuadPlus 4 K) (AutOm.pvec 1 true)).subgroupOf
            (matrixDerived (coordinateQuadPlus 4 K))) ⊔
        (((posUnipotent .D4 K).subgroupOf (adjointGroup .D4 K)) ⊓
          Subgroup.comap Φ.toMonoidHom
            (((lineStabilizer (coordinateQuadPlus 4 K) (AutOm.pvec 1 true)).subgroupOf
                (matrixDerived (coordinateQuadPlus 4 K))) ⊓
              ((lineStabilizer (coordinateQuadPlus 4 K) (AutOm.pvec 1 false)).subgroupOf
                (matrixDerived (coordinateQuadPlus 4 K))))) := by
  let Ue : Subgroup (Om8 K) :=
    (rootGroupGL (coordinateQuadPlus 4 K) (AutOm.pvec 1 true)).subgroupOf
      (matrixDerived (coordinateQuadPlus 4 K))
  let Pe : Subgroup (Om8 K) :=
    (lineStabilizer (coordinateQuadPlus 4 K) (AutOm.pvec 1 true)).subgroupOf
      (matrixDerived (coordinateQuadPlus 4 K))
  let Pf : Subgroup (Om8 K) :=
    (lineStabilizer (coordinateQuadPlus 4 K) (AutOm.pvec 1 false)).subgroupOf
      (matrixDerived (coordinateQuadPlus 4 K))
  change (⟨pinnedX .D4 K γ c, pinnedX_mem_adjointGroup γ c⟩ : adjointGroup .D4 K) ∈
    Subgroup.comap Φ.toMonoidHom Ue ⊔
      ((posUnipotent .D4 K).subgroupOf (adjointGroup .D4 K) ⊓
        Subgroup.comap Φ.toMonoidHom (Pe ⊓ Pf))
  have hX := X8_bLinv_mem_of_pos (K := K) hγ h c
  have hpinX : Φ ⟨pinnedX .D4 K γ c, pinnedX_mem_adjointGroup _ _⟩ = X8 (bLinv γ) c :=
    hΦ γ (mem_rootFinset.2 hγ) c
  by_cases hUe : ((X8 (bLinv γ) c : Om8 K) : GL (Fin (2 * 4)) K) ∈
      rootGroupGL (coordinateQuadPlus 4 K) (AutOm.pvec 1 true)
  · refine Subgroup.mem_sup_left ?_
    rw [Subgroup.mem_comap]
    change Φ ⟨pinnedX .D4 K γ c, pinnedX_mem_adjointGroup _ _⟩ ∈ Ue
    rw [hpinX]
    exact hUe
  · have hP := hX.resolve_left hUe
    refine Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · change ((⟨pinnedX .D4 K γ c, pinnedX_mem_adjointGroup _ _⟩ :
          adjointGroup .D4 K) : ModGL .D4 K) ∈ posUnipotent .D4 K
      rw [posUnipotent, rootSpan]
      exact Subgroup.mem_iSup_of_mem γ (Subgroup.mem_iSup_of_mem ⟨hγ, h⟩
        (Subgroup.subset_closure ⟨c, rfl⟩))
    · rw [Subgroup.mem_comap]
      change Φ ⟨pinnedX .D4 K γ c, pinnedX_mem_adjointGroup _ _⟩ ∈ Pe ⊓ Pf
      rw [hpinX]
      exact ⟨hP.1, hP.2⟩

theorem pinnedX_mem_comap_sup_of_neg
    {K : Type} [Field K] [CharP K 2]
    {Φ : adjointGroup .D4 K ≃* Om8 K}
    (hΦ : ∀ β ∈ rootFinset .D4, ∀ c : K,
      Φ ⟨pinnedX .D4 K β c, pinnedX_mem_adjointGroup β c⟩ = X8 (bLinv β) c)
    {γ : Fin TwistTag.D4.tag.rank → ℤ} (hγ : IsRoot TwistTag.D4.tag γ) (h : height γ < 0)
    (c : K) :
    (⟨pinnedX .D4 K γ c, pinnedX_mem_adjointGroup γ c⟩ : adjointGroup .D4 K) ∈
      Subgroup.comap Φ.toMonoidHom
          ((rootGroupGL (coordinateQuadPlus 4 K) (AutOm.pvec 1 false)).subgroupOf
            (matrixDerived (coordinateQuadPlus 4 K))) ⊔
        Subgroup.comap Φ.toMonoidHom
          (((lineStabilizer (coordinateQuadPlus 4 K) (AutOm.pvec 1 true)).subgroupOf
              (matrixDerived (coordinateQuadPlus 4 K))) ⊓
            ((lineStabilizer (coordinateQuadPlus 4 K) (AutOm.pvec 1 false)).subgroupOf
              (matrixDerived (coordinateQuadPlus 4 K)))) := by
  let Uf : Subgroup (Om8 K) :=
    (rootGroupGL (coordinateQuadPlus 4 K) (AutOm.pvec 1 false)).subgroupOf
      (matrixDerived (coordinateQuadPlus 4 K))
  let Pe : Subgroup (Om8 K) :=
    (lineStabilizer (coordinateQuadPlus 4 K) (AutOm.pvec 1 true)).subgroupOf
      (matrixDerived (coordinateQuadPlus 4 K))
  let Pf : Subgroup (Om8 K) :=
    (lineStabilizer (coordinateQuadPlus 4 K) (AutOm.pvec 1 false)).subgroupOf
      (matrixDerived (coordinateQuadPlus 4 K))
  change (⟨pinnedX .D4 K γ c, pinnedX_mem_adjointGroup γ c⟩ : adjointGroup .D4 K) ∈
    Subgroup.comap Φ.toMonoidHom Uf ⊔ Subgroup.comap Φ.toMonoidHom (Pe ⊓ Pf)
  have hX := X8_bLinv_mem_of_neg (K := K) hγ h c
  have hpinX : Φ ⟨pinnedX .D4 K γ c, pinnedX_mem_adjointGroup _ _⟩ = X8 (bLinv γ) c :=
    hΦ γ (mem_rootFinset.2 hγ) c
  by_cases hUf : ((X8 (bLinv γ) c : Om8 K) : GL (Fin (2 * 4)) K) ∈
      rootGroupGL (coordinateQuadPlus 4 K) (AutOm.pvec 1 false)
  · refine Subgroup.mem_sup_left ?_
    rw [Subgroup.mem_comap]
    change Φ ⟨pinnedX .D4 K γ c, pinnedX_mem_adjointGroup _ _⟩ ∈ Uf
    rw [hpinX]
    exact hUf
  · have hP := hX.resolve_left hUf
    refine Subgroup.mem_sup_right ?_
    rw [Subgroup.mem_comap]
    change Φ ⟨pinnedX .D4 K γ c, pinnedX_mem_adjointGroup _ _⟩ ∈ Pe ⊓ Pf
    rw [hpinX]
    exact ⟨hP.1, hP.2⟩

theorem eq_bot_or_fixed_le_of_rootGroupGL
    {K : Type} [Field K] [Finite K] [CharP K 2] {Y : Type*} [AddCommGroup Y] [Module K Y]
    {ρ : Representation K (Om8 K) Y} (hρ : IsSimpleRep ρ) {X : Submodule K Y}
    (hX : ∀ g : Om8 K, (g : GL (Fin (2 * 4)) K) ∈
        rootGroupGL (coordinateQuadPlus 4 K) (AutOm.pvec 1 true) → ∀ y ∈ X, ρ g y = y)
    (hXP : ∀ g : Om8 K, (g : GL (Fin (2 * 4)) K) ∈
        lineStabilizer (coordinateQuadPlus 4 K) (AutOm.pvec 1 true) → ∀ y ∈ X, ρ g y ∈ X) :
    X = ⊥ ∨ ∀ y : Y, (∀ g : Om8 K, (g : GL (Fin (2 * 4)) K) ∈
        rootGroupGL (coordinateQuadPlus 4 K) (AutOm.pvec 1 true) → ρ g y = y) → y ∈ X := by
  classical
  obtain ⟨Φ, hΦ⟩ := d4_adjoint_equiv_om8 (K := K)
  let Q := coordinateQuadPlus 4 K
  let e : Fin (2 * 4) → K := AutOm.pvec 1 true
  let f : Fin (2 * 4) → K := AutOm.pvec 1 false
  let Ue : Subgroup (Om8 K) := (rootGroupGL Q e).subgroupOf (matrixDerived Q)
  let Uf : Subgroup (Om8 K) := (rootGroupGL Q f).subgroupOf (matrixDerived Q)
  let Pe : Subgroup (Om8 K) := (lineStabilizer Q e).subgroupOf (matrixDerived Q)
  let Pf : Subgroup (Om8 K) := (lineStabilizer Q f).subgroupOf (matrixDerived Q)
  let N : Subgroup (adjointGroup .D4 K) := Ue.comap Φ.toMonoidHom
  let N' : Subgroup (adjointGroup .D4 K) := Uf.comap Φ.toMonoidHom
  let P : Subgroup (adjointGroup .D4 K) := (Pe ⊓ Pf).comap Φ.toMonoidHom
  let D : CurtisDatum (adjointGroup .D4 K) (coxeterSystem .D4) 2 :=
    chevDatum .D4 K 2 exists_weyl_neg_D4
  haveI : Finite (adjointGroup .D4 K) := Subtype.finite
  haveI : Finite (WeylGroup .D4) := inferInstance
  have hsplit : SplitOver K D.H :=
    splitOver_torus (τ := .D4) (K := K) (p := 2) (hw := exists_weyl_neg_D4) K
  have hρ' : IsSimpleRep (ρ.comp Φ.toMonoidHom) :=
    (isSimpleRep_comp_iff ρ (f := Φ.toMonoidHom) Φ.surjective).2 hρ
  have hN : ∀ m ∈ P, ∀ x ∈ N, m * x * m⁻¹ ∈ N := fun m hm x hx =>
    comap_conj_mem (Subgroup.mem_inf.mp hm).1 hx
  have hN' : ∀ m ∈ P, ∀ x ∈ N', m * x * m⁻¹ ∈ N' := fun m hm x hx =>
    comap_conj_mem (Subgroup.mem_inf.mp hm).2 hx
  have hN'L : N' ≤ D.L := comap_rootGroupGL_le_negUnipotent hΦ
  have hU : D.U ≤ N ⊔ (D.U ⊓ P) := fun u hu =>
    mem_of_mem_rootSpan_of_forall_pinnedX (τ := .D4) (K := K)
      (S := {α : Fin 4 → ℤ | IsRoot .D4 α ∧ 0 < height (τ := .D4) α})
      (H := N ⊔ (D.U ⊓ P))
      (fun γ hγ c => pinnedX_mem_comap_sup_of_pos hΦ hγ.1 hγ.2 c)
      (Subgroup.mem_subgroupOf.mp hu)
  have hL : D.L ≤ N' ⊔ P := fun u hu =>
    mem_of_mem_rootSpan_of_forall_pinnedX (τ := .D4) (K := K)
      (S := {α : Fin 4 → ℤ | IsRoot .D4 α ∧ height (τ := .D4) α < 0})
      (H := N' ⊔ P)
      (fun γ hγ c => pinnedX_mem_comap_sup_of_neg hΦ hγ.1 hγ.2 c)
      (Subgroup.mem_subgroupOf.mp hu)
  have hXfix : X ≤ fixSub (ρ.comp Φ.toMonoidHom) N := fun y hy g hg =>
    hX (Φ g) (Subgroup.mem_subgroupOf.mp hg) y hy
  have hXP' : ∀ m ∈ P, ∀ x ∈ X, (ρ.comp Φ.toMonoidHom) m x ∈ X := fun m hm x hx =>
    hXP (Φ m) (Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hm).1) x hx
  have hmain := D.eq_bot_or_fixSub_le (ρ := ρ.comp Φ.toMonoidHom) (N := N) (N' := N')
    (P := P) (X := X) hsplit hρ' hN hN' hN'L hU hL hXfix hXP'
  rcases hmain with hbot | hle
  · exact Or.inl hbot
  · exact Or.inr fun y hy => hle fun g hg =>
      hy (Φ g) (Subgroup.mem_subgroupOf.mp hg)

end CFSG.StandardType.TriBridge

end
