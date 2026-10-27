module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G6Natural
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SubrepresentationLattice
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtM22ModK

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private abbrev V22 : Type := Fin 22 → ZMod 2

private abbrev W11 : Type := Fin 11 → ZMod 2

private abbrev Q10 : Type := Fin 10 → ZMod 2

private def bitVec (x : ℕ) : V22 := fun j => if x.testBit j.val then 1 else 0

private def qVec (x : ℕ) : Q10 := fun i => if x.testBit i.val then 1 else 0

private def basisBits : Fin 11 → ℕ :=
  ![1286145, 3682306, 4057092, 4136968, 1982480, 3272736, 323648, 1136768,
    1820928, 1866240, 2821120]

private def v (i : Fin 11) : V22 := bitVec (basisBits i)

private def inc11 (i : Fin 11) : Fin 22 := ⟨i.val, by omega⟩

private def inc10 (i : Fin 10) : Fin 22 := ⟨i.val, by omega⟩

private def inc1011 (i : Fin 10) : Fin 11 := ⟨i.val, by omega⟩

private def T : W11 →ₗ[ZMod 2] V22 where
  toFun x := ∑ i : Fin 11, x i • v i
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul, smul_eq_mul]

private def proj : V22 →ₗ[ZMod 2] W11 where
  toFun x := fun i => x (inc11 i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def incl : Q10 →ₗ[ZMod 2] W11 where
  toFun x := fun i => if h : i.val < 10 then x ⟨i.val, h⟩ else 0
  map_add' x y := by
    funext i
    by_cases h : i.val < 10 <;> simp [h]
  map_smul' c x := by
    funext i
    by_cases h : i.val < 10 <;> simp [h]

private def emb : Q10 →ₗ[ZMod 2] V22 := T.comp incl

private def quo : V22 →ₗ[ZMod 2] Q10 where
  toFun x := fun i => x (inc10 i) + x ⟨10, by norm_num⟩
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    ring

private theorem w183_v_inc10 :
    ∀ i j : Fin 10, v (inc1011 j) (inc10 i) = (if i = j then 1 else 0) := by
  decide +kernel

private theorem w183_v_ten :
    ∀ j : Fin 10, v (inc1011 j) ⟨10, by norm_num⟩ = 0 := by
  decide +kernel

private theorem w183_v_inc10' :
    ∀ (i : Fin 10) (j : Fin 11), v j (inc10 i) = (if j = inc1011 i then 1 else 0) := by
  decide +kernel

private theorem w183_v_ten' :
    ∀ j : Fin 11, v j ⟨10, by norm_num⟩ = (if j = ⟨10, by norm_num⟩ then 1 else 0) := by
  decide +kernel

private theorem w183_incl_single :
    ∀ j : Fin 10, incl (Pi.single j 1) = Pi.single (inc1011 j) 1 := by
  decide +kernel

private def allOnes : V22 := fun _ => 1

private def allOnes11 : W11 := fun _ => 1

private theorem w183_T_allOnes : T allOnes11 = allOnes := by
  decide +kernel

private theorem w183_T_sum (x : W11) (t : ZMod 2) (h : ∀ i, x i = t) :
    T x = t • allOnes := by
  have h1 : T x = ∑ i : Fin 11, t • v i := by
    rw [T]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    apply Finset.sum_congr rfl
    intro i _
    rw [h i]
  rw [h1, ← w183_T_allOnes, T]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [allOnes11]

private theorem w183_emb_single (j : Fin 10) : emb (Pi.single j 1) = v (inc1011 j) := by
  rw [emb, LinearMap.comp_apply, w183_incl_single j, T]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single (inc1011 j)]
  · rw [Pi.single_eq_same, one_smul]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, zero_smul]
  · intro hi
    exact absurd (Finset.mem_univ _) hi

private theorem w183_quo_emb : quo.comp emb = LinearMap.id := by
  apply (Pi.basisFun (ZMod 2) (Fin 10)).ext
  intro j
  simp only [Pi.basisFun_apply, LinearMap.comp_apply, LinearMap.id_apply]
  rw [w183_emb_single]
  funext i
  simp only [quo, LinearMap.coe_mk, AddHom.coe_mk, w183_v_inc10 i j, w183_v_ten j, add_zero,
    Pi.single_apply]

private theorem w183_quo_emb_apply (x : Q10) : quo (emb x) = x :=
  LinearMap.congr_fun w183_quo_emb x

private def permLE (σ : Equiv.Perm (Fin 22)) : V22 ≃ₗ[ZMod 2] V22 :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) σ.symm

private theorem w183_permLE_apply (σ : Equiv.Perm (Fin 22)) (x : V22) (i : Fin 22) :
    permLE σ x i = x (σ.symm i) := by
  simp only [permLE, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

private theorem w183_permLE_one : permLE (1 : Equiv.Perm (Fin 22)) = 1 := by
  ext x i
  rw [w183_permLE_apply]
  rfl

private theorem w183_permLE_mul (σ τ : Equiv.Perm (Fin 22)) :
    permLE (σ * τ) = permLE σ * permLE τ := by
  ext x i
  simp only [permLE, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    LinearEquiv.mul_apply]
  congr 1

private theorem w183_permLE_allOnes (σ : Equiv.Perm (Fin 22)) :
    permLE σ allOnes = allOnes := by
  funext i
  simp [w183_permLE_apply, allOnes]

private def genA : Equiv.Perm (Fin 22) :=
  (List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13])

private def genB : Equiv.Perm (Fin 22) :=
  (List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18])

private theorem w183_genA_mem : genA ∈ CFSG.Blueprint.NativeSporadic.M22 := by
  rw [CFSG.Blueprint.NativeSporadic.M22]
  exact Subgroup.subset_closure (by simp [genA])

private theorem w183_genB_mem : genB ∈ CFSG.Blueprint.NativeSporadic.M22 := by
  rw [CFSG.Blueprint.NativeSporadic.M22]
  exact Subgroup.subset_closure (by simp [genB])

private def a : ↥CFSG.Blueprint.NativeSporadic.M22 := ⟨genA, w183_genA_mem⟩

private def b : ↥CFSG.Blueprint.NativeSporadic.M22 := ⟨genB, w183_genB_mem⟩

private def stabC : Subgroup (Equiv.Perm (Fin 22)) where
  carrier := {g | (LinearMap.range T).map (permLE g).toLinearMap ≤ LinearMap.range T ∧
    (LinearMap.range T).map (permLE g⁻¹).toLinearMap ≤ LinearMap.range T}
  one_mem' := by
    have h1 : (1 : Equiv.Perm (Fin 22))⁻¹ = 1 := inv_one
    constructor
    · rw [w183_permLE_one]
      exact le_of_eq (Submodule.map_id _)
    · rw [h1, w183_permLE_one]
      exact le_of_eq (Submodule.map_id _)
  mul_mem' := by
    intro g h hg hh
    obtain ⟨hg1, hg2⟩ := hg
    obtain ⟨hh1, hh2⟩ := hh
    constructor
    · rw [w183_permLE_mul]
      have hcomp : ((permLE g) * (permLE h)).toLinearMap =
          (permLE g).toLinearMap.comp (permLE h).toLinearMap := rfl
      rw [hcomp, Submodule.map_comp]
      exact (Submodule.map_mono hh1).trans hg1
    · have hinv : (g * h)⁻¹ = h⁻¹ * g⁻¹ := mul_inv_rev g h
      rw [hinv, w183_permLE_mul]
      have hcomp : ((permLE h⁻¹) * (permLE g⁻¹)).toLinearMap =
          (permLE h⁻¹).toLinearMap.comp (permLE g⁻¹).toLinearMap := rfl
      rw [hcomp, Submodule.map_comp]
      exact (Submodule.map_mono hg2).trans hh2
  inv_mem' := by
    intro g hg
    exact ⟨hg.2, by simpa using hg.1⟩

private theorem w183_inv_lin_of (σ : Equiv.Perm (Fin 22))
    (h : ∀ i : Fin 11,
      T (proj ((permLE σ).toLinearMap (T (Pi.single i 1)))) =
        (permLE σ).toLinearMap (T (Pi.single i 1))) :
    T.comp (proj.comp ((permLE σ).toLinearMap.comp T)) =
      (permLE σ).toLinearMap.comp T := by
  apply (Pi.basisFun (ZMod 2) (Fin 11)).ext
  intro i
  simpa only [Pi.basisFun_apply, LinearMap.comp_apply] using h i

private theorem w183_inv_of (σ : Equiv.Perm (Fin 22))
    (hlin : T.comp (proj.comp ((permLE σ).toLinearMap.comp T)) =
      (permLE σ).toLinearMap.comp T) :
    (LinearMap.range T).map (permLE σ).toLinearMap ≤ LinearMap.range T := by
  rw [Submodule.map_le_iff_le_comap]
  intro y hy
  rw [LinearMap.mem_range] at hy
  obtain ⟨x, rfl⟩ := hy
  rw [Submodule.mem_comap, LinearMap.mem_range]
  exact ⟨proj (permLE σ (T x)), LinearMap.congr_fun hlin x⟩

private theorem w183_inv_genA :
    (LinearMap.range T).map (permLE genA).toLinearMap ≤ LinearMap.range T :=
  w183_inv_of genA (w183_inv_lin_of genA (by decide +kernel))

private theorem w183_inv_genA_inv :
    (LinearMap.range T).map (permLE genA⁻¹).toLinearMap ≤ LinearMap.range T :=
  w183_inv_of genA⁻¹ (w183_inv_lin_of genA⁻¹ (by decide +kernel))

private theorem w183_inv_genB :
    (LinearMap.range T).map (permLE genB).toLinearMap ≤ LinearMap.range T :=
  w183_inv_of genB (w183_inv_lin_of genB (by decide +kernel))

private theorem w183_inv_genB_inv :
    (LinearMap.range T).map (permLE genB⁻¹).toLinearMap ≤ LinearMap.range T :=
  w183_inv_of genB⁻¹ (w183_inv_lin_of genB⁻¹ (by decide +kernel))

private theorem w183_M22_le_stabC :
    (CFSG.Blueprint.NativeSporadic.M22 : Subgroup (Equiv.Perm (Fin 22))) ≤ stabC := by
  rw [CFSG.Blueprint.NativeSporadic.M22, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact ⟨w183_inv_genA, w183_inv_genA_inv⟩
  · exact ⟨w183_inv_genB, w183_inv_genB_inv⟩

private def rho (g : ↥CFSG.Blueprint.NativeSporadic.M22) : Q10 →ₗ[ZMod 2] Q10 :=
  quo.comp ((permLE (g : Equiv.Perm (Fin 22))).toLinearMap.comp emb)

private theorem w183_rho_apply (g : ↥CFSG.Blueprint.NativeSporadic.M22) (x : Q10) :
    rho g x = quo (permLE (g : Equiv.Perm (Fin 22)) (emb x)) :=
  rfl

private theorem w183_T_inc10 (x : W11) (i : Fin 10) : T x (inc10 i) = x (inc1011 i) := by
  rw [T]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (inc1011 i)]
  · rw [w183_v_inc10' i (inc1011 i), if_pos rfl, mul_one]
  · intro k _ hk
    rw [w183_v_inc10' i k, if_neg hk, mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ _) hk

private theorem w183_T_last (x : W11) :
    T x ⟨10, by norm_num⟩ = x ⟨10, by norm_num⟩ := by
  rw [T]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single ⟨10, by norm_num⟩]
  · rw [w183_v_ten' ⟨10, by norm_num⟩, if_pos rfl, mul_one]
  · intro k _ hk
    rw [w183_v_ten' k, if_neg hk, mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ _) hk

private theorem w183_quo_allOnes : quo allOnes = 0 := by
  funext i
  simp only [quo, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, allOnes]
  exact CharTwo.add_self_eq_zero 1

private theorem w183_span_allOnes_le_ker :
    Submodule.span (ZMod 2) {allOnes} ≤ LinearMap.ker quo := by
  rw [Submodule.span_le]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx, SetLike.mem_coe, LinearMap.mem_ker]
  exact w183_quo_allOnes

private theorem w183_C_inter_ker :
    LinearMap.range T ⊓ LinearMap.ker quo ≤ Submodule.span (ZMod 2) {allOnes} := by
  intro y hy
  obtain ⟨hyC, hyk⟩ := Submodule.mem_inf.mp hy
  rw [LinearMap.mem_ker] at hyk
  obtain ⟨x, rfl⟩ := hyC
  have hx : ∀ i : Fin 11, x i = x ⟨10, by norm_num⟩ := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have h := congrFun hyk j
      simp only [quo, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h
      rw [w183_T_inc10 x j, w183_T_last x] at h
      exact CharTwo.add_eq_zero.mp h
    · rfl
  rw [w183_T_sum x (x ⟨10, by norm_num⟩) hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

private theorem w183_permLE_span_le (g : ↥CFSG.Blueprint.NativeSporadic.M22) :
    Submodule.span (ZMod 2) {allOnes} ≤
      (Submodule.span (ZMod 2) {allOnes}).comap
        (permLE (g : Equiv.Perm (Fin 22))).toLinearMap := by
  rw [Submodule.span_le]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx, SetLike.mem_coe, Submodule.mem_comap]
  change permLE (g : Equiv.Perm (Fin 22)) allOnes ∈ Submodule.span (ZMod 2) {allOnes}
  rw [w183_permLE_allOnes]
  exact Submodule.subset_span (Set.mem_singleton _)

private theorem w183_permLE_map_span (g : ↥CFSG.Blueprint.NativeSporadic.M22) :
    (Submodule.span (ZMod 2) {allOnes}).map
        (permLE (g : Equiv.Perm (Fin 22))).toLinearMap ≤
      Submodule.span (ZMod 2) {allOnes} :=
  Submodule.map_le_iff_le_comap.mpr (w183_permLE_span_le g)

private def rhoRep : Representation (ZMod 2) ↥CFSG.Blueprint.NativeSporadic.M22 Q10 where
  toFun := rho
  map_one' := by
    apply LinearMap.ext
    intro x
    rw [w183_rho_apply]
    rw [show ((1 : ↥CFSG.Blueprint.NativeSporadic.M22) : Equiv.Perm (Fin 22)) = 1 from rfl,
      w183_permLE_one]
    exact w183_quo_emb_apply x
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    change rho (g * h) x = rho g (rho h x)
    rw [w183_rho_apply, w183_rho_apply, w183_rho_apply]
    set y : V22 := permLE (h : Equiv.Perm (Fin 22)) (emb x) with hy
    have hemb : emb x ∈ LinearMap.range T := ⟨incl x, rfl⟩
    have hyC : y ∈ LinearMap.range T := by
      rw [hy]
      exact (w183_M22_le_stabC h.2).1 (Submodule.mem_map_of_mem hemb)
    set z : V22 := y - emb (quo y) with hz
    have hzC : z ∈ LinearMap.range T :=
      Submodule.sub_mem _ hyC ⟨incl (quo y), rfl⟩
    have hzker : z ∈ LinearMap.ker quo := by
      rw [LinearMap.mem_ker, hz, map_sub, w183_quo_emb_apply, sub_self]
    have hzspan : z ∈ Submodule.span (ZMod 2) {allOnes} :=
      w183_C_inter_ker (Submodule.mem_inf.mpr ⟨hzC, hzker⟩)
    have hPgspan : permLE (g : Equiv.Perm (Fin 22)) z ∈
        Submodule.span (ZMod 2) {allOnes} :=
      w183_permLE_map_span g (Submodule.mem_map_of_mem hzspan)
    have hPgker : quo (permLE (g : Equiv.Perm (Fin 22)) z) = 0 :=
      w183_span_allOnes_le_ker hPgspan
    have hz' : emb (quo y) = y - z := by
      rw [hz]
      abel
    have hkey : quo (permLE (g : Equiv.Perm (Fin 22)) (emb (quo y))) =
        quo (permLE (g : Equiv.Perm (Fin 22)) y) := by
      rw [hz', map_sub, map_sub, hPgker, sub_zero]
    have hgh : permLE (g : Equiv.Perm (Fin 22)) y =
        permLE (((g * h : ↥CFSG.Blueprint.NativeSporadic.M22)) :
          Equiv.Perm (Fin 22)) (emb x) := by
      rw [hy, Subgroup.coe_mul, w183_permLE_mul]
      rfl
    rw [hkey]
    exact congrArg quo hgh.symm

private def MA : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  fun i j => qVec (![955, 862, 915, 927, 16, 922, 1018, 75, 588, 758] j) i

private def MB : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  fun i j => qVec (![9, 519, 565, 525, 553, 984, 34, 51, 825, 691] j) i

private theorem w183_rho_a_pt :
    ∀ j : Fin 10, rho a (Pi.single j 1) = MA.mulVecLin (Pi.single j 1) := by
  decide +kernel

private theorem w183_rho_a : rho a = MA.mulVecLin := by
  apply (Pi.basisFun (ZMod 2) (Fin 10)).ext
  intro j
  simpa only [Pi.basisFun_apply] using w183_rho_a_pt j

private theorem w183_rho_b_pt :
    ∀ j : Fin 10, rho b (Pi.single j 1) = MB.mulVecLin (Pi.single j 1) := by
  decide +kernel

private theorem w183_rho_b : rho b = MB.mulVecLin := by
  apply (Pi.basisFun (ZMod 2) (Fin 10)).ext
  intro j
  simpa only [Pi.basisFun_apply] using w183_rho_b_pt j

private theorem w183_rhoRep_a : rhoRep a = MA.mulVecLin := w183_rho_a

private theorem w183_rhoRep_b : rhoRep b = MB.mulVecLin := w183_rho_b

private def NA : Matrix (Fin 10) (Fin 10) (ZMod 2) := 1 + MA

private def NB : Matrix (Fin 10) (Fin 10) (ZMod 2) := 1 + MB + MB ^ 2 + MB ^ 3

private def colsOf {K : ℕ} (M : Matrix (Fin 10) (Fin 10) (ZMod 2)) (c : Fin K → Fin 10) :
    Matrix (Fin 10) (Fin K) (ZMod 2) := fun i k => M i (c k)

private def colIdxA : Fin 4 → Fin 10 := ![0, 1, 2, 8]

private def yBitsA : Fin 4 → ℕ := ![609, 130, 140, 768]

private def YA : Matrix (Fin 4) (Fin 10) (ZMod 2) :=
  fun k j => if (yBitsA k).testBit j.val then 1 else 0

private def colIdxB : Fin 2 → Fin 10 := ![0, 2]

private def yBitsB : Fin 2 → ℕ := ![1009, 916]

private def YB : Matrix (Fin 2) (Fin 10) (ZMod 2) :=
  fun k j => if (yBitsB k).testBit j.val then 1 else 0

private theorem w183_fact_MA : colsOf NA colIdxA * YA = NA := by
  decide +kernel

private theorem w183_fact_MB : colsOf NB colIdxB * YB = NB := by
  decide +kernel

private theorem w183_rank_NA : NA.rank = 4 := by
  apply le_antisymm
  · calc NA.rank = (colsOf NA colIdxA * YA).rank := by rw [w183_fact_MA]
      _ ≤ (colsOf NA colIdxA).rank := Matrix.rank_mul_le_left _ _
      _ ≤ 4 := Matrix.rank_le_card_width _
  · have hli : LinearIndependent (ZMod 2) (fun k : Fin 4 => NA.col (colIdxA k)) := by
      rw [Fintype.linearIndependent_iff]
      decide +kernel
    have hspan : Submodule.span (ZMod 2)
          (Set.range (fun k : Fin 4 => NA.col (colIdxA k))) ≤
        Submodule.span (ZMod 2) (Set.range NA.col) := by
      rw [Submodule.span_le]
      rintro x ⟨k, rfl⟩
      exact Submodule.subset_span ⟨colIdxA k, rfl⟩
    have h4 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        (Set.range (fun k : Fin 4 => NA.col (colIdxA k)))) = 4 := by
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    rw [Matrix.rank_eq_finrank_span_cols]
    calc 4 = Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
          (Set.range (fun k : Fin 4 => NA.col (colIdxA k)))) := h4.symm
      _ ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range NA.col)) :=
          Submodule.finrank_mono hspan

private theorem w183_rank_NB : NB.rank = 2 := by
  apply le_antisymm
  · calc NB.rank = (colsOf NB colIdxB * YB).rank := by rw [w183_fact_MB]
      _ ≤ (colsOf NB colIdxB).rank := Matrix.rank_mul_le_left _ _
      _ ≤ 2 := Matrix.rank_le_card_width _
  · have hli : LinearIndependent (ZMod 2) (fun k : Fin 2 => NB.col (colIdxB k)) := by
      rw [Fintype.linearIndependent_iff]
      decide +kernel
    have hspan : Submodule.span (ZMod 2)
          (Set.range (fun k : Fin 2 => NB.col (colIdxB k))) ≤
        Submodule.span (ZMod 2) (Set.range NB.col) := by
      rw [Submodule.span_le]
      rintro x ⟨k, rfl⟩
      exact Submodule.subset_span ⟨colIdxB k, rfl⟩
    have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        (Set.range (fun k : Fin 2 => NB.col (colIdxB k)))) = 2 := by
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    rw [Matrix.rank_eq_finrank_span_cols]
    calc 2 = Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
          (Set.range (fun k : Fin 2 => NB.col (colIdxB k)))) := h2.symm
      _ ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range NB.col)) :=
          Submodule.finrank_mono hspan

private theorem w183_pow_b : ∀ i : ℕ, rhoRep b ^ i = (MB ^ i).mulVecLin := by
  intro i
  induction i with
  | zero => rw [pow_zero, pow_zero, Matrix.mulVecLin_one]; rfl
  | succ i ih =>
      rw [pow_succ, pow_succ, Matrix.mulVecLin_mul, ih, w183_rhoRep_b]
      rfl

private theorem w183_mulVecLin_sum (n : ℕ)
    (f : ℕ → Matrix (Fin 10) (Fin 10) (ZMod 2)) :
    (∑ i ∈ Finset.range n, (f i).mulVecLin) = (∑ i ∈ Finset.range n, f i).mulVecLin := by
  induction n with
  | zero => simp [Matrix.mulVecLin_zero]
  | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, Matrix.mulVecLin_add, ih]

private theorem w183_sum_a :
    (∑ i ∈ Finset.range 2, rhoRep a ^ i) = NA.mulVecLin := by
  rw [show (∑ i ∈ Finset.range 2, rhoRep a ^ i) =
      rhoRep a ^ 0 + rhoRep a ^ 1 from by
    rw [Finset.sum_range_succ, Finset.sum_range_one]]
  rw [pow_zero, pow_one, w183_rhoRep_a, show NA = 1 + MA from rfl, Matrix.mulVecLin_add,
    Matrix.mulVecLin_one]
  rfl

private theorem w183_sum_b :
    (∑ i ∈ Finset.range 4, rhoRep b ^ i) = NB.mulVecLin := by
  rw [show (∑ i ∈ Finset.range 4, rhoRep b ^ i) =
      ∑ i ∈ Finset.range 4, (MB ^ i).mulVecLin from by
    apply Finset.sum_congr rfl
    intro i _
    exact w183_pow_b i]
  rw [w183_mulVecLin_sum]
  have hsum : (∑ i ∈ Finset.range 4, MB ^ i) = NB := by
    rw [show NB = 1 + MB + MB ^ 2 + MB ^ 3 from rfl]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
    abel
  rw [hsum]

private theorem w183_genA_sq : genA ^ 2 = 1 := by
  ext i
  fin_cases i <;> decide +kernel

private theorem w183_genB_pow4 : genB ^ 4 = 1 := by
  ext i
  fin_cases i <;> decide +kernel

private theorem w183_a_sq : a ^ 2 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  show (a : Equiv.Perm (Fin 22)) ^ 2 = 1
  rw [show (a : Equiv.Perm (Fin 22)) = genA from rfl]
  exact w183_genA_sq

private theorem w183_b_pow4 : b ^ 4 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  show (b : Equiv.Perm (Fin 22)) ^ 4 = 1
  rw [show (b : Equiv.Perm (Fin 22)) = genB from rfl]
  exact w183_genB_pow4

private theorem w183_closure_ab : Subgroup.closure {a, b} = ⊤ := by
  rw [← Subgroup.map_subtype_inj (H := CFSG.Blueprint.NativeSporadic.M22)]
  rw [Subgroup.map_top, Subgroup.range_subtype, MonoidHom.map_closure]
  have hset : (CFSG.Blueprint.NativeSporadic.M22.subtype '' {a, b}) =
      ({genA, genB} : Set (Equiv.Perm (Fin 22))) := by
    ext x
    simp [a, b]
  rw [hset]
  rfl

private theorem w183_rho_a_ne_one : rhoRep a ≠ 1 := by
  intro h
  have h1 : MA.mulVecLin (Pi.single (0 : Fin 10) 1) = Pi.single (0 : Fin 10) 1 := by
    have hc := congrArg (fun f : Q10 →ₗ[ZMod 2] Q10 => f (Pi.single (0 : Fin 10) 1)) h
    rwa [w183_rhoRep_a, Module.End.one_apply] at hc
  exact absurd h1 (by decide +kernel)

private def w183ColsA : ℕ → ℕ
  | 0 => 955 | 1 => 862 | 2 => 915 | 3 => 927 | 4 => 16 | 5 => 922
  | 6 => 1018 | 7 => 75 | 8 => 588 | 9 => 758 | _ => 0

private def w183ColsB : ℕ → ℕ
  | 0 => 9 | 1 => 519 | 2 => 565 | 3 => 525 | 4 => 553 | 5 => 984
  | 6 => 34 | 7 => 51 | 8 => 825 | 9 => 691 | _ => 0

private def w183App (c : ℕ → ℕ) (v : ℕ) : ℕ :=
  (List.range 10).foldl (fun acc j => if v.testBit j then acc ^^^ c j else acc) 0

private def w183AppA : ℕ → ℕ := w183App w183ColsA

private def w183AppB : ℕ → ℕ := w183App w183ColsB

private def w183InsertNat (x : ℕ) (l : List ℕ) : List ℕ :=
  if x ∈ l then l else x :: l

private def w183Step (l : List ℕ) : List ℕ :=
  l.foldl (fun acc x => w183InsertNat (w183AppA x) (w183InsertNat (w183AppB x) acc)) l

private def w183OrbitGo : ℕ → List ℕ → List ℕ
  | 0, S => S
  | n + 1, S =>
      let S' := w183Step S
      if S'.length = S.length then S' else w183OrbitGo n S'

private def w183Orbit (v : ℕ) : List ℕ := w183OrbitGo 1200 [v]

private def w183SpanFold (l : List ℕ) : List ℕ :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ acc.map (fun y => y ^^^ x)) [0]

private def w183MaskOf (l : List ℕ) : ℕ :=
  l.foldl (fun m x => m ||| (1 <<< x)) 0

private def w183Check : Bool :=
  (((w183MaskOf (w183Orbit 1) ||| w183MaskOf (w183Orbit 3) |||
      w183MaskOf (w183Orbit 4)) ||| 1) == (1 <<< 1024) - 1) &&
    (w183MaskOf (w183SpanFold (w183Orbit 1)) == (1 <<< 1024) - 1) &&
    (w183MaskOf (w183SpanFold (w183Orbit 3)) == (1 <<< 1024) - 1) &&
    (w183MaskOf (w183SpanFold (w183Orbit 4)) == (1 <<< 1024) - 1)

private theorem w183Check_eq_true : w183Check = true := by
  have hA : w183AppA = S16M22K.appK 955 862 915 927 16 922 1018 75 588 758 :=
    funext fun v => S16M22K.app_eq w183ColsA v
  have hB : w183AppB = S16M22K.appK 9 519 565 525 553 984 34 51 825 691 :=
    funext fun v => S16M22K.app_eq w183ColsB v
  have hgo : ∀ n S, w183OrbitGo n S = S16M22K.goL w183AppA w183AppB n S := by
    intro n
    induction n with
    | zero => intro S; rfl
    | succ n ih =>
      intro S
      have hs : w183Step S = S16M22K.stepL w183AppA w183AppB S := rfl
      simp only [w183OrbitGo, S16M22K.goL, hs, ih]
  have h : w183Check = S16M22K.chkK w183AppA w183AppB 1 3 4 ((1 <<< 1024) - 1) := by
    have hm : ∀ l, w183MaskOf l = S16M22K.maskL l := fun _ => rfl
    have hsp : ∀ l, w183SpanFold l = S16M22K.spanL l := fun _ => rfl
    rw [S16M22K.chkK_eq]
    simp only [w183Check, w183Orbit, hgo, hm, hsp]
  rw [h, hA, hB]
  decide +kernel

private theorem w183AppA_lt : ∀ v ∈ List.range 1024, w183AppA v < 1024 := by
  have hA : w183AppA = S16M22K.appK 955 862 915 927 16 922 1018 75 588 758 :=
    funext fun v => S16M22K.app_eq w183ColsA v
  rw [hA]
  decide +kernel

private theorem w183AppB_lt : ∀ v ∈ List.range 1024, w183AppB v < 1024 := by
  have hB : w183AppB = S16M22K.appK 9 519 565 525 553 984 34 51 825 691 :=
    funext fun v => S16M22K.app_eq w183ColsB v
  rw [hB]
  decide +kernel

private theorem w183AppA_invol : ∀ v ∈ List.range 1024, w183AppA (w183AppA v) = v := by
  have hA : w183AppA = S16M22K.appK 955 862 915 927 16 922 1018 75 588 758 :=
    funext fun v => S16M22K.app_eq w183ColsA v
  rw [hA]
  decide +kernel

private theorem w183AppB_pow4 :
    ∀ v ∈ List.range 1024, w183AppB (w183AppB (w183AppB (w183AppB v))) = v := by
  have hB : w183AppB = S16M22K.appK 9 519 565 525 553 984 34 51 825 691 :=
    funext fun v => S16M22K.app_eq w183ColsB v
  rw [hB]
  decide +kernel

private theorem w183MaskOf_aux : ∀ (l : List ℕ) (acc x : ℕ),
    (l.foldl (fun m y => m ||| (1 <<< y)) acc).testBit x = true →
      acc.testBit x = true ∨ x ∈ l := by
  intro l
  induction l with
  | nil => intro acc x h; exact Or.inl (by simpa using h)
  | cons y l ih =>
      intro acc x h
      rw [List.foldl_cons] at h
      rcases ih (acc ||| (1 <<< y)) x h with h1 | h2
      · rw [Nat.testBit_or] at h1
        rcases Bool.or_eq_true_iff.mp h1 with h1 | h1
        · exact Or.inl h1
        · refine Or.inr ?_
          have h2 := h1
          rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow] at h2
          exact (of_decide_eq_true h2).symm ▸ List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem y h2)

private theorem w183mem_maskOf {l : List ℕ} {x : ℕ}
    (h : (w183MaskOf l).testBit x = true) : x ∈ l := by
  rw [w183MaskOf] at h
  rcases w183MaskOf_aux l 0 x h with h0 | hl
  · simp at h0
  · exact hl

private theorem w183SpanFold_mem_span {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (dec : ℕ → V) (hdec0 : dec 0 = 0)
    (hxor : ∀ x y, dec (x ^^^ y) = dec x + dec y) (l : List ℕ) :
    ∀ y ∈ w183SpanFold l, dec y ∈ Submodule.span (ZMod 2) (dec '' {x : ℕ | x ∈ l}) := by
  unfold w183SpanFold
  have key : ∀ (l : List ℕ) (S : Submodule (ZMod 2) V), (∀ x ∈ l, dec x ∈ S) →
      ∀ acc : List ℕ, (∀ y ∈ acc, dec y ∈ S) →
      ∀ y ∈ l.foldl (fun acc x => if x ∈ acc then acc else acc ++ acc.map (fun y => y ^^^ x)) acc,
        dec y ∈ S := by
    intro l
    induction l with
    | nil => intro S hl acc hacc y hy; simpa using hacc y hy
    | cons x l ih =>
        intro S hl acc hacc y hy
        rw [List.foldl_cons] at hy
        exact ih S (fun z hz => hl z (List.mem_cons_of_mem x hz))
          (if x ∈ acc then acc else acc ++ acc.map (fun y => y ^^^ x))
          (fun z hz => by
            by_cases hx : x ∈ acc
            · rw [if_pos hx] at hz; exact hacc z hz
            · rw [if_neg hx, List.mem_append] at hz
              rcases hz with hz | hz
              · exact hacc z hz
              · rw [List.mem_map] at hz
                obtain ⟨w, hw, rfl⟩ := hz
                rw [hxor]
                exact Submodule.add_mem _ (hacc w hw) (hl x List.mem_cons_self))
          y hy
  exact key l (Submodule.span (ZMod 2) (dec '' {x : ℕ | x ∈ l}))
    (fun x hx => Submodule.subset_span (Set.mem_image_of_mem dec hx)) [0]
    (fun y hy => by
      rw [List.mem_singleton] at hy
      rw [hy, hdec0]
      exact Submodule.zero_mem _)

private def w183Eval : List Bool → ℕ → ℕ
  | [], x => x
  | true :: w, x => w183Eval w (w183AppA x)
  | false :: w, x => w183Eval w (w183AppB x)

private def w183InvWord : List Bool → List Bool
  | [] => []
  | true :: w => w183InvWord w ++ [true]
  | false :: w => w183InvWord w ++ [false, false, false]

private theorem w183Eval_append (w₁ w₂ : List Bool) (v : ℕ) :
    w183Eval (w₁ ++ w₂) v = w183Eval w₂ (w183Eval w₁ v) := by
  induction w₁ generalizing v with
  | nil => simp [w183Eval]
  | cons b w₁ ih => cases b <;> simp [w183Eval, ih]

private theorem w183Eval_inv {w : List Bool} {v : ℕ} (hv : v < 1024) :
    w183Eval (w183InvWord w) (w183Eval w v) = v := by
  induction w generalizing v with
  | nil => simp [w183Eval, w183InvWord]
  | cons b w ih =>
      cases b
      · have hlt : w183AppB v < 1024 := w183AppB_lt v (List.mem_range.mpr hv)
        calc w183Eval (w183InvWord (false :: w)) (w183Eval (false :: w) v)
            = w183Eval (w183InvWord w ++ [false, false, false])
                (w183Eval w (w183AppB v)) := rfl
          _ = w183Eval [false, false, false]
                (w183Eval (w183InvWord w) (w183Eval w (w183AppB v))) := by
                rw [w183Eval_append]
          _ = w183Eval [false, false, false] (w183AppB v) := by rw [ih hlt]
          _ = v := by
                simp only [w183Eval]
                exact w183AppB_pow4 v (List.mem_range.mpr hv)
      · have hlt : w183AppA v < 1024 := w183AppA_lt v (List.mem_range.mpr hv)
        calc w183Eval (w183InvWord (true :: w)) (w183Eval (true :: w) v)
            = w183Eval (w183InvWord w ++ [true]) (w183Eval w (w183AppA v)) := rfl
          _ = w183Eval [true] (w183Eval (w183InvWord w) (w183Eval w (w183AppA v))) := by
                rw [w183Eval_append]
          _ = w183Eval [true] (w183AppA v) := by rw [ih hlt]
          _ = v := by
                simp only [w183Eval]
                exact w183AppA_invol v (List.mem_range.mpr hv)

private def w183Reach (v x : ℕ) : Prop := ∃ w : List Bool, x = w183Eval w v

private theorem w183Reach_appA {v x : ℕ} (h : w183Reach v x) : w183Reach v (w183AppA x) := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨w ++ [true], by rw [w183Eval_append]; simp [w183Eval]⟩

private theorem w183Reach_appB {v x : ℕ} (h : w183Reach v x) : w183Reach v (w183AppB x) := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨w ++ [false], by rw [w183Eval_append]; simp [w183Eval]⟩

private theorem w183Reach_trans {v x y : ℕ} (h1 : w183Reach v x) (h2 : w183Reach x y) :
    w183Reach v y := by
  obtain ⟨w1, rfl⟩ := h1
  obtain ⟨w2, hw2⟩ := h2
  exact ⟨w1 ++ w2, by rw [hw2, w183Eval_append]⟩

private theorem w183Reach_symm {v x : ℕ} (hv : v < 1024) (hx : x < 1024)
    (h : w183Reach v x) : w183Reach x v := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨w183InvWord w, (w183Eval_inv (w := w) hv).symm⟩

private theorem w183InsertNat_reach {v x : ℕ} {acc : List ℕ}
    (hacc : ∀ y ∈ acc, w183Reach v y) (hx : w183Reach v x) :
    ∀ y ∈ w183InsertNat x acc, w183Reach v y := by
  unfold w183InsertNat
  split
  · exact hacc
  · intro y hy
    rw [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hx
    · exact hacc y hy

private theorem w183Step_reach {v : ℕ} {S : List ℕ} (hS : ∀ y ∈ S, w183Reach v y) :
    ∀ y ∈ w183Step S, w183Reach v y := by
  unfold w183Step
  have key : ∀ (l : List ℕ), (∀ x ∈ l, w183Reach v x) → ∀ acc : List ℕ,
      (∀ y ∈ acc, w183Reach v y) →
      ∀ y ∈ l.foldl (fun acc x =>
          w183InsertNat (w183AppA x) (w183InsertNat (w183AppB x) acc)) acc,
        w183Reach v y := by
    intro l
    induction l with
    | nil => intro hl acc hacc y hy; simpa using hacc y hy
    | cons x l ih =>
        intro hl acc hacc y hy
        rw [List.foldl_cons] at hy
        exact ih (fun z hz => hl z (List.mem_cons_of_mem x hz))
          (w183InsertNat (w183AppA x) (w183InsertNat (w183AppB x) acc))
          (w183InsertNat_reach
            (w183InsertNat_reach hacc (w183Reach_appB (hl x List.mem_cons_self)))
            (w183Reach_appA (hl x List.mem_cons_self)))
          y hy
  exact key S hS S hS

private theorem w183OrbitGo_reach {v : ℕ} (n : ℕ) :
    ∀ S : List ℕ, (∀ y ∈ S, w183Reach v y) → ∀ y ∈ w183OrbitGo n S, w183Reach v y := by
  induction n with
  | zero => intro S hS y hy; exact hS y hy
  | succ n ih =>
      intro S hS y hy
      dsimp only [w183OrbitGo] at hy
      split at hy
      · exact w183Step_reach hS y hy
      · exact ih (w183Step S) (w183Step_reach hS) y hy

private theorem w183Orbit_reach {v x : ℕ} (h : x ∈ w183Orbit v) : w183Reach v x :=
  w183OrbitGo_reach 1200 [v]
    (by intro y hy; rw [List.mem_singleton] at hy; rw [hy]; exact ⟨[], rfl⟩)
    x (by simpa [w183Orbit] using h)

private theorem w183Check_cover {x : ℕ} (hx : x < 1024) (hx0 : x ≠ 0) :
    x ∈ w183Orbit 1 ∨ x ∈ w183Orbit 3 ∨ x ∈ w183Orbit 4 := by
  have h := w183Check_eq_true
  simp only [w183Check, Bool.and_eq_true_iff, beq_iff_eq] at h
  obtain ⟨⟨⟨hcover, _⟩, _⟩, _⟩ := h
  have hbit : (((w183MaskOf (w183Orbit 1) ||| w183MaskOf (w183Orbit 3) |||
      w183MaskOf (w183Orbit 4)) ||| 1).testBit x) = true := by
    rw [hcover, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow_sub_one]
    simp [hx]
  rw [Nat.testBit_or] at hbit
  rcases Bool.or_eq_true_iff.mp hbit with hbit | hbit
  · rw [Nat.testBit_or, Nat.testBit_or] at hbit
    rcases Bool.or_eq_true_iff.mp hbit with hbit | hbit
    · rcases Bool.or_eq_true_iff.mp hbit with hbit | hbit
      · exact Or.inl (w183mem_maskOf hbit)
      · exact Or.inr (Or.inl (w183mem_maskOf hbit))
    · exact Or.inr (Or.inr (w183mem_maskOf hbit))
  · exfalso
    have h1 : (2 ^ 0 : ℕ).testBit x = true := by simpa using hbit
    rw [Nat.testBit_two_pow] at h1
    exact hx0 (of_decide_eq_true h1).symm

private theorem w183Check_span (i : ℕ) (hi : i = 1 ∨ i = 3 ∨ i = 4) :
    ∀ x < 1024, x ∈ w183SpanFold (w183Orbit i) := by
  have h := w183Check_eq_true
  simp only [w183Check, Bool.and_eq_true_iff, beq_iff_eq] at h
  obtain ⟨⟨⟨_, h1⟩, h3⟩, h4⟩ := h
  have hsp : w183MaskOf (w183SpanFold (w183Orbit i)) = (1 <<< 1024) - 1 := by
    rcases hi with rfl | rfl | rfl
    · exact h1
    · exact h3
    · exact h4
  intro x hx
  apply w183mem_maskOf
  rw [hsp, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow_sub_one]
  simp [hx]

private theorem w183Reach_invariant {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (A B : V →ₗ[ZMod 2] V) (dec : ℕ → V)
    (hA : ∀ x < 1024, dec (w183AppA x) = A (dec x))
    (hB : ∀ x < 1024, dec (w183AppB x) = B (dec x))
    {U : Submodule (ZMod 2) V} (hUA : ∀ x ∈ U, A x ∈ U) (hUB : ∀ x ∈ U, B x ∈ U)
    {v x : ℕ} (hv : v < 1024) (hU : dec v ∈ U) (h : w183Reach v x) : dec x ∈ U := by
  obtain ⟨w, rfl⟩ := h
  induction w generalizing v with
  | nil => simpa [w183Eval] using hU
  | cons b w ih =>
      cases b
      · simp only [w183Eval]
        exact ih (w183AppB_lt v (List.mem_range.mpr hv))
          (by rw [hB v hv]; exact hUB _ hU)
      · simp only [w183Eval]
        exact ih (w183AppA_lt v (List.mem_range.mpr hv))
          (by rw [hA v hv]; exact hUA _ hU)

private theorem w183_qVec_zero : qVec 0 = 0 := by
  funext i
  simp [qVec]

private theorem w183_qVec_xor (x y : ℕ) : qVec (x ^^^ y) = qVec x + qVec y := by
  funext i
  simp only [qVec, Pi.add_apply, Nat.testBit_xor]
  by_cases hx : x.testBit i <;> by_cases hy : y.testBit i <;>
    simp [hx, hy, CharTwo.add_self_eq_zero]

private theorem w183_qVec_two_pow (i : Fin 10) :
    qVec (2 ^ (i : ℕ)) = Pi.single i 1 := by
  funext j
  rw [qVec, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : ¬ (i.val = j.val) := fun hv => h (Fin.ext hv)
    have h'' : ¬ (j = i) := fun hv => h hv.symm
    simp [h', h'']

private theorem w183_qVec_appA :
    ∀ v ∈ List.range 1024, qVec (w183AppA v) = MA.mulVecLin (qVec v) := by
  intro v _
  have hc : ∀ j : Fin 10, w183ColsA j = ![955, 862, 915, 927, 16, 922, 1018, 75, 588, 758] j := by
    decide
  change qVec ((List.range 10).foldl
    (fun acc j => if v.testBit j then acc ^^^ w183ColsA j else acc) 0) = _
  rw [S16M22K.dec_fold qVec w183_qVec_zero w183_qVec_xor, S16M22K.sum_range_fin]
  funext i
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.sum_apply, MA, hc]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : v.testBit j <;> simp [h, qVec]

private theorem w183_qVec_appB :
    ∀ v ∈ List.range 1024, qVec (w183AppB v) = MB.mulVecLin (qVec v) := by
  intro v _
  have hc : ∀ j : Fin 10, w183ColsB j = ![9, 519, 565, 525, 553, 984, 34, 51, 825, 691] j := by
    decide
  change qVec ((List.range 10).foldl
    (fun acc j => if v.testBit j then acc ^^^ w183ColsB j else acc) 0) = _
  rw [S16M22K.dec_fold qVec w183_qVec_zero w183_qVec_xor, S16M22K.sum_range_fin]
  funext i
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.sum_apply, MB, hc]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : v.testBit j <;> simp [h, qVec]

private theorem w183_top_of_orbit {U : Submodule (ZMod 2) Q10}
    (hUA : ∀ x ∈ U, MA.mulVecLin x ∈ U) (hUB : ∀ x ∈ U, MB.mulVecLin x ∈ U)
    {i x : ℕ} (hilt : i < 1024) (hxlt : x < 1024) (hxU : qVec x ∈ U)
    (hcover : x ∈ w183Orbit i)
    (hspan : ∀ y < 1024, y ∈ w183SpanFold (w183Orbit i)) : U = ⊤ := by
  have hreach : w183Reach x i :=
    w183Reach_symm hilt hxlt (w183Orbit_reach hcover)
  have hgen : Submodule.span (ZMod 2) (qVec '' {y : ℕ | y ∈ w183Orbit i}) ≤ U := by
    rw [Submodule.span_le]
    rintro z ⟨y, hy, rfl⟩
    exact w183Reach_invariant MA.mulVecLin MB.mulVecLin qVec
      (fun v hv => w183_qVec_appA v (List.mem_range.mpr hv))
      (fun v hv => w183_qVec_appB v (List.mem_range.mpr hv))
      hUA hUB hxlt hxU (w183Reach_trans hreach (w183Orbit_reach hy))
  have hbasis : ∀ j : Fin 10, Pi.single j (1 : ZMod 2) ∈ U := by
    intro j
    have hlt : 2 ^ (j : ℕ) < 1024 := by
      have hj : (j : ℕ) < 10 := j.isLt
      calc 2 ^ (j : ℕ) < 2 ^ 10 := Nat.pow_lt_pow_of_lt (by norm_num) hj
        _ = 1024 := by norm_num
    have hmem : qVec (2 ^ (j : ℕ)) ∈
        Submodule.span (ZMod 2) (qVec '' {y : ℕ | y ∈ w183Orbit i}) :=
      w183SpanFold_mem_span qVec w183_qVec_zero w183_qVec_xor (w183Orbit i)
        (2 ^ (j : ℕ)) (hspan _ hlt)
    have hU := hgen hmem
    rwa [w183_qVec_two_pow j] at hU
  refine le_antisymm le_top ?_
  intro v _
  have hv : v = ∑ j : Fin 10, v j • Pi.single j (1 : ZMod 2) := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj; simp [hj.symm]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  rw [hv]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbasis j)

private theorem w183_submodule_eq_bot_or_top (U : Submodule (ZMod 2) Q10)
    (hUA : ∀ x ∈ U, MA.mulVecLin x ∈ U) (hUB : ∀ x ∈ U, MB.mulVecLin x ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  · refine Or.inr ?_
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hinj : Function.Injective (fun x : Fin 1024 => qVec x.val) := by
      intro x y hxy
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < 10
      · have h := congrFun hxy ⟨i, hi⟩
        simp only [qVec] at h
        by_cases hx : x.val.testBit i <;> by_cases hy : y.val.testBit i <;>
          simp [hx, hy] at h ⊢
      · have hx10 : x.val < 2 ^ 10 := by simpa using x.isLt
        have hy10 : y.val < 2 ^ 10 := by simpa using y.isLt
        have hlt : 2 ^ 10 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx10 hlt),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hy10 hlt)]
    have hcard : Fintype.card (Fin 1024) = Fintype.card (Fin 10 → ZMod 2) := by
      rw [Fintype.card_fin, Fintype.card_pi_const, ZMod.card]
      norm_num
    have hsurj : Function.Surjective (fun x : Fin 1024 => qVec x.val) :=
      ((Fintype.bijective_iff_injective_and_card (fun x : Fin 1024 => qVec x.val)).mpr
        ⟨hinj, hcard⟩).2
    obtain ⟨x, hx⟩ := hsurj u
    have hxlt : x.val < 1024 := x.isLt
    have hx0 : x.val ≠ 0 := by
      intro h0
      apply hu0
      calc u = qVec x.val := hx.symm
        _ = qVec 0 := by rw [h0]
        _ = 0 := w183_qVec_zero
    have hxU : qVec x.val ∈ U := by
      rw [show qVec x.val = u from hx]
      exact huU
    rcases w183Check_cover hxlt hx0 with h1 | h3 | h4
    · exact w183_top_of_orbit hUA hUB (by norm_num) hxlt hxU h1 (w183Check_span 1 (Or.inl rfl))
    · exact w183_top_of_orbit hUA hUB (by norm_num) hxlt hxU h3
        (w183Check_span 3 (Or.inr (Or.inl rfl)))
    · exact w183_top_of_orbit hUA hUB (by norm_num) hxlt hxU h4
        (w183Check_span 4 (Or.inr (Or.inr rfl)))

theorem s16nt_m22_module :
    ∃ (Q : Type) (_ : AddCommGroup Q) (_ : Module (ZMod 2) Q) (_ : Finite Q)
      (ρ : Representation (ZMod 2) ↥CFSG.Blueprint.NativeSporadic.M22 Q)
      (a b : ↥CFSG.Blueprint.NativeSporadic.M22),
      ρ.IsIrreducible ∧ Module.finrank (ZMod 2) Q = 10 ∧ (∃ g, ρ g ≠ 1) ∧
        Subgroup.closure {a, b} = ⊤ ∧ a ^ 2 = 1 ∧ b ^ 4 = 1 ∧
        Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range 2, ρ a ^ i)) = 4 ∧
        Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ Finset.range 4, ρ b ^ i)) = 2 := by
  refine ⟨Q10, inferInstance, inferInstance, inferInstance, rhoRep, a, b, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · haveI : Nontrivial (Subrepresentation rhoRep) :=
      ⟨⊥, ⊤, fun h => bot_ne_top (α := Submodule (ZMod 2) Q10)
        (congrArg Subrepresentation.toSubmodule h)⟩
    refine IsSimpleOrder.of_forall_eq_top ?_
    intro W hW
    have hUA : ∀ x ∈ W.toSubmodule, MA.mulVecLin x ∈ W.toSubmodule := by
      intro x hx
      have h := W.apply_mem_toSubmodule a hx
      rwa [w183_rhoRep_a] at h
    have hUB : ∀ x ∈ W.toSubmodule, MB.mulVecLin x ∈ W.toSubmodule := by
      intro x hx
      have h := W.apply_mem_toSubmodule b hx
      rwa [w183_rhoRep_b] at h
    rcases w183_submodule_eq_bot_or_top W.toSubmodule hUA hUB with h | h
    · exact absurd (Subrepresentation.toSubmodule_injective (by rw [h]; rfl)) hW
    · exact Subrepresentation.toSubmodule_injective (by rw [h]; rfl)
  · exact Module.finrank_fin_fun (ZMod 2)
  · exact ⟨a, w183_rho_a_ne_one⟩
  · exact w183_closure_ab
  · exact w183_a_sq
  · exact w183_b_pow4
  · rw [w183_sum_a]
    change NA.rank = 4
    exact w183_rank_NA
  · rw [w183_sum_b]
    change NB.rank = 2
    exact w183_rank_NB

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
