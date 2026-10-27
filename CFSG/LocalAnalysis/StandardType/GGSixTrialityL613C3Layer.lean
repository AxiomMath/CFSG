module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613C3Levi

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL CFSG.StandardType.D4Rank CFSG.StandardType.L613KG
  CFSG.Assembly.LowTwoRank QuadraticMap
open scoped Matrix

namespace L613C3

theorem map_eq_one_of_mem_commutator {G M : Type*} [Group G] [CommMonoid M] {C : Subgroup G}
    (f : G → M) (h1 : f 1 = 1) (hmul : ∀ x ∈ C, ∀ y ∈ C, f (x * y) = f x * f y) {z : G}
    (hz : z ∈ ⁅C, C⁆) : f z = 1 := by
  have hinv : ∀ x ∈ C, f x * f x⁻¹ = 1 := fun x hx => by
    rw [← hmul x hx x⁻¹ (C.inv_mem hx), mul_inv_cancel, h1]
  let N : Subgroup G :=
    { carrier := {x | x ∈ C ∧ f x = 1}
      mul_mem' := fun {x y} hx hy =>
        ⟨C.mul_mem hx.1 hy.1, by rw [hmul x hx.1 y hy.1, hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨C.one_mem, h1⟩
      inv_mem' := fun {x} hx => ⟨C.inv_mem hx.1, by
        have h := hinv x hx.1
        rwa [hx.2, one_mul] at h⟩ }
  have hle : ⁅C, C⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxy : x * y * x⁻¹ ∈ C := C.mul_mem (C.mul_mem hx hy) (C.inv_mem hx)
    rw [commutatorElement_def]
    show x * y * x⁻¹ * y⁻¹ ∈ C ∧ f (x * y * x⁻¹ * y⁻¹) = 1
    refine ⟨C.mul_mem hxy (C.inv_mem hy), ?_⟩
    rw [hmul _ hxy _ (C.inv_mem hy), hmul _ (C.mul_mem hx hy) _ (C.inv_mem hx), hmul x hx y hy,
      mul_right_comm (f x) (f y), mul_assoc, hinv x hx, hinv y hy, one_mul]
  exact (hle hz).2

variable {K : Type} [Field K]

section Coord

theorem single_ie_apply_ie (k l : Fin 4) :
    (Pi.single (ie k) 1 : Fin (2 * 4) → K) (ie l) = if l = k then 1 else 0 := by
  by_cases h : l = k
  · subst h
    simp
  · rw [Pi.single_eq_of_ne (ie_injective.ne h), ite_eq_right h]

theorem single_ie_apply_jf (k l : Fin 4) :
    (Pi.single (ie k) 1 : Fin (2 * 4) → K) (jf l) = 0 :=
  Pi.single_eq_of_ne (fun h => ie_ne_jf k l h.symm) _

theorem single_jf_apply_jf (k l : Fin 4) :
    (Pi.single (jf k) 1 : Fin (2 * 4) → K) (jf l) = if l = k then 1 else 0 := by
  by_cases h : l = k
  · subst h
    simp
  · rw [Pi.single_eq_of_ne (jf_injective.ne h), ite_eq_right h]

theorem single_jf_apply_ie (k l : Fin 4) :
    (Pi.single (jf k) 1 : Fin (2 * 4) → K) (ie l) = 0 :=
  Pi.single_eq_of_ne (ie_ne_jf l k) _

theorem castSucc_ne_last' (l : Fin 3) : (Fin.castSucc l : Fin 4) ≠ Fin.last 3 :=
  (Fin.castSucc_lt_last l).ne

theorem polar_single_ie (k : Fin 4) (v : Fin (2 * 4) → K) :
    polar (coordinateQuadPlus 4 K) (Pi.single (ie k) 1) v = v (jf k) := by
  rw [polar, coordQ_apply, coordQ_apply, coordQ_apply, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  simp only [Pi.add_apply, single_ie_apply_ie, single_ie_apply_jf, zero_add, mul_zero, sub_zero]
  have h : ∀ m : Fin 4, ((if m = k then (1 : K) else 0) + v (ie m)) * v (jf m) -
      v (ie m) * v (jf m) = if m = k then v (jf m) else 0 := fun m => by
    split_ifs <;> ring
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem sum_ie_apply (a : Fin 3 → K) (i : Fin (2 * 4)) :
    (∑ l : Fin 3, a l • (Pi.single (ie l.castSucc) 1 : Fin (2 * 4) → K)) i =
      ∑ l : Fin 3, a l * (Pi.single (ie l.castSucc) 1 : Fin (2 * 4) → K) i := by
  rw [Finset.sum_apply]
  rfl

theorem sum_jf_apply (a : Fin 3 → K) (i : Fin (2 * 4)) :
    (∑ l : Fin 3, a l • (Pi.single (jf l.castSucc) 1 : Fin (2 * 4) → K)) i =
      ∑ l : Fin 3, a l * (Pi.single (jf l.castSucc) 1 : Fin (2 * 4) → K) i := by
  rw [Finset.sum_apply]
  rfl

theorem eq_sum_ie {v : Fin (2 * 4) → K} (h3 : v (ie (Fin.last 3)) = 0) (hf : ∀ k, v (jf k) = 0) :
    v = ∑ l : Fin 3, v (ie l.castSucc) • (Pi.single (ie l.castSucc) 1 : Fin (2 * 4) → K) := by
  refine vec_ext (fun m => ?_) ?_ (fun m => ?_) ?_ <;>
    simp only [sum_ie_apply, single_ie_apply_ie, single_ie_apply_jf, Fin.castSucc_inj,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, h3, hf,
      Finset.sum_const_zero]
  · simp only [(castSucc_ne_last' _).symm, ite_false, Finset.sum_const_zero]

theorem eq_sum_jf {v : Fin (2 * 4) → K} (h3 : v (jf (Fin.last 3)) = 0) (he : ∀ k, v (ie k) = 0) :
    v = ∑ l : Fin 3, v (jf l.castSucc) • (Pi.single (jf l.castSucc) 1 : Fin (2 * 4) → K) := by
  refine vec_ext (fun m => ?_) ?_ (fun m => ?_) ?_ <;>
    simp only [sum_jf_apply, single_jf_apply_jf, single_jf_apply_ie, Fin.castSucc_inj,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, h3, he,
      Finset.sum_const_zero]
  · simp only [(castSucc_ne_last' _).symm, ite_false, Finset.sum_const_zero]

theorem eq_V1 {v : Fin (2 * 4) → K} (he : ∀ l : Fin 3, v (ie l.castSucc) = 0)
    (hf : ∀ l : Fin 3, v (jf l.castSucc) = 0) :
    v = v (ie (Fin.last 3)) • (Pi.single (ie (Fin.last 3)) 1 : Fin (2 * 4) → K) +
      v (jf (Fin.last 3)) • (Pi.single (jf (Fin.last 3)) 1 : Fin (2 * 4) → K) := by
  refine vec_ext (fun m => ?_) ?_ (fun m => ?_) ?_ <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, single_ie_apply_ie, single_ie_apply_jf,
      single_jf_apply_jf, single_jf_apply_ie, castSucc_ne_last', ite_false, ite_true, mul_zero,
      mul_one, add_zero, zero_add, he, hf]

end Coord

section Cent

variable [Finite K] [CharP K 2] {ω : Kˣ}

omit [Finite K] [CharP K 2] in
theorem twHom_ie_castSucc (ω : Kˣ) (l : Fin 3) :
    twHom (fun k : Fin 4 => if k = 3 then (1 : Kˣ) else ω) (ie l.castSucc) = ω := by
  rw [twHom_ie, ite_eq_right (castSucc_ne_three l)]

omit [Finite K] [CharP K 2] in
theorem twHom_ie_last (ω : Kˣ) :
    twHom (fun k : Fin 4 => if k = 3 then (1 : Kˣ) else ω) (ie (Fin.last 3)) = 1 := by
  rw [twHom_ie, ite_eq_left last_eq_three]

omit [Finite K] [CharP K 2] in
theorem twHom_jf_castSucc (ω : Kˣ) (l : Fin 3) :
    twHom (fun k : Fin 4 => if k = 3 then (1 : Kˣ) else ω) (jf l.castSucc) = ω⁻¹ := by
  rw [twHom_jf, ite_eq_right (castSucc_ne_three l)]

omit [Finite K] [CharP K 2] in
theorem twHom_jf_last (ω : Kˣ) :
    twHom (fun k : Fin 4 => if k = 3 then (1 : Kˣ) else ω) (jf (Fin.last 3)) = 1 := by
  rw [twHom_jf, ite_eq_left last_eq_three, inv_one]

theorem coord_eq_zero_of_eigen {μ : Kˣ} {y : Fin (2 * 4) → K}
    (hy : act (zStd ω) y = (μ : K) • y) {i : Fin (2 * 4)}
    (hi : twHom (fun k : Fin 4 => if k = 3 then (1 : Kˣ) else ω) i ≠ μ) : y i = 0 := by
  have h := congrFun hy i
  rw [zStd, act_dg, Pi.smul_apply, smul_eq_mul] at h
  beta_reduce at h
  have h' : (((twHom (fun k : Fin 4 => if k = 3 then (1 : Kˣ) else ω) i : Kˣ) : K) - μ) * y i =
      0 := by
    rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact absurd (Units.ext (sub_eq_zero.mp h1)) hi
  · exact h1

theorem act_eigen_of_mem {x : Om8 K} (hx : x ∈ Subgroup.centralizer {zStd ω}) {μ : K}
    {v : Fin (2 * 4) → K} (hv : act (zStd ω) v = μ • v) :
    act (zStd ω) (act x v) = μ • act x v := by
  rw [← act_mul, ← Subgroup.mem_centralizer_singleton_iff.mp hx, act_mul, hv, act_smul]

theorem act_zStd_ie_castSucc (ω : Kˣ) (i : Fin 3) :
    act (zStd ω) (Pi.single (ie i.castSucc) 1) =
      (ω : K) • (Pi.single (ie i.castSucc) 1 : Fin (2 * 4) → K) := by
  rw [zStd, act_dg_single, twHom_ie_castSucc]

theorem act_zStd_jf_castSucc (ω : Kˣ) (i : Fin 3) :
    act (zStd ω) (Pi.single (jf i.castSucc) 1) =
      ((ω⁻¹ : Kˣ) : K) • (Pi.single (jf i.castSucc) 1 : Fin (2 * 4) → K) := by
  rw [zStd, act_dg_single, twHom_jf_castSucc]

theorem act_zStd_ie_last (ω : Kˣ) :
    act (zStd ω) (Pi.single (ie (Fin.last 3)) 1) =
      ((1 : Kˣ) : K) • (Pi.single (ie (Fin.last 3)) 1 : Fin (2 * 4) → K) := by
  rw [zStd, act_dg_single, twHom_ie_last]

theorem act_zStd_jf_last (ω : Kˣ) :
    act (zStd ω) (Pi.single (jf (Fin.last 3)) 1) =
      ((1 : Kˣ) : K) • (Pi.single (jf (Fin.last 3)) 1 : Fin (2 * 4) → K) := by
  rw [zStd, act_dg_single, twHom_jf_last]

@[expose] noncomputable def blkE (x : Om8 K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun l i => act x (Pi.single (ie i.castSucc) 1) (ie l.castSucc)

@[expose] noncomputable def cA (x : Om8 K) : K :=
  act x (Pi.single (ie (Fin.last 3)) 1) (ie (Fin.last 3))

@[expose] noncomputable def cB (x : Om8 K) : K :=
  act x (Pi.single (jf (Fin.last 3)) 1) (ie (Fin.last 3))

@[expose] noncomputable def cC (x : Om8 K) : K :=
  act x (Pi.single (ie (Fin.last 3)) 1) (jf (Fin.last 3))

@[expose] noncomputable def cD (x : Om8 K) : K :=
  act x (Pi.single (jf (Fin.last 3)) 1) (jf (Fin.last 3))

variable (hω : orderOf ω = 3)
include hω

theorem act_ie_castSucc_eq {x : Om8 K} (hx : x ∈ Subgroup.centralizer {zStd ω}) (i : Fin 3) :
    act x (Pi.single (ie i.castSucc) 1) =
      ∑ l : Fin 3, blkE x l i • (Pi.single (ie l.castSucc) 1 : Fin (2 * 4) → K) := by
  obtain ⟨h1, -, h3⟩ := units_facts hω
  have hv := act_eigen_of_mem hx (act_zStd_ie_castSucc ω i)
  refine eq_sum_ie (coord_eq_zero_of_eigen hv (by rw [twHom_ie_last]; exact Ne.symm h1))
    fun k => ?_
  induction k using Fin.lastCases with
  | last => exact coord_eq_zero_of_eigen hv (by rw [twHom_jf_last]; exact Ne.symm h1)
  | cast l => exact coord_eq_zero_of_eigen hv (by rw [twHom_jf_castSucc]; exact h3)

theorem act_jf_castSucc_eq {x : Om8 K} (hx : x ∈ Subgroup.centralizer {zStd ω}) (i : Fin 3) :
    act x (Pi.single (jf i.castSucc) 1) =
      ∑ l : Fin 3, act x (Pi.single (jf i.castSucc) 1) (jf l.castSucc) •
        (Pi.single (jf l.castSucc) 1 : Fin (2 * 4) → K) := by
  obtain ⟨-, h2, h3⟩ := units_facts hω
  have hv := act_eigen_of_mem hx (act_zStd_jf_castSucc ω i)
  refine eq_sum_jf (coord_eq_zero_of_eigen hv (by rw [twHom_jf_last]; exact Ne.symm h2))
    fun k => ?_
  induction k using Fin.lastCases with
  | last => exact coord_eq_zero_of_eigen hv (by rw [twHom_ie_last]; exact Ne.symm h2)
  | cast l => exact coord_eq_zero_of_eigen hv (by rw [twHom_ie_castSucc]; exact Ne.symm h3)

theorem act_ie_last_eq {x : Om8 K} (hx : x ∈ Subgroup.centralizer {zStd ω}) :
    act x (Pi.single (ie (Fin.last 3)) 1) =
      cA x • (Pi.single (ie (Fin.last 3)) 1 : Fin (2 * 4) → K) +
        cC x • (Pi.single (jf (Fin.last 3)) 1 : Fin (2 * 4) → K) := by
  obtain ⟨h1, h2, -⟩ := units_facts hω
  have hv := act_eigen_of_mem hx (act_zStd_ie_last ω)
  exact eq_V1 (fun l => coord_eq_zero_of_eigen hv (by rw [twHom_ie_castSucc]; exact h1))
    (fun l => coord_eq_zero_of_eigen hv (by rw [twHom_jf_castSucc]; exact h2))

theorem act_jf_last_eq {x : Om8 K} (hx : x ∈ Subgroup.centralizer {zStd ω}) :
    act x (Pi.single (jf (Fin.last 3)) 1) =
      cB x • (Pi.single (ie (Fin.last 3)) 1 : Fin (2 * 4) → K) +
        cD x • (Pi.single (jf (Fin.last 3)) 1 : Fin (2 * 4) → K) := by
  obtain ⟨h1, h2, -⟩ := units_facts hω
  have hv := act_eigen_of_mem hx (act_zStd_jf_last ω)
  exact eq_V1 (fun l => coord_eq_zero_of_eigen hv (by rw [twHom_ie_castSucc]; exact h1))
    (fun l => coord_eq_zero_of_eigen hv (by rw [twHom_jf_castSucc]; exact h2))

end Cent

section Blocks

variable [Finite K] [CharP K 2] {ω : Kˣ}

omit [Finite K] [CharP K 2] in
theorem blkE_one : blkE (1 : Om8 K) = 1 := by
  ext m i
  simp only [blkE, Matrix.of_apply, act_one, single_ie_apply_ie, Fin.castSucc_inj, Matrix.one_apply]

omit [Finite K] [CharP K 2] in
theorem cA_one : cA (1 : Om8 K) = 1 := by
  rw [cA, act_one, single_ie_apply_ie, ite_eq_left rfl]

omit [Finite K] [CharP K 2] in
theorem cC_one : cC (1 : Om8 K) = 0 := by
  rw [cC, act_one, single_ie_apply_jf]

omit [Finite K] [CharP K 2] in
theorem Q_single_ie (k : Fin 4) : coordinateQuadPlus 4 K (Pi.single (ie k) 1) = 0 := by
  rw [← AutOm.pvec_true]
  exact AutOm.form_pvec k true

omit [Finite K] [CharP K 2] in
theorem Q_single_jf (k : Fin 4) : coordinateQuadPlus 4 K (Pi.single (jf k) 1) = 0 := by
  rw [← AutOm.pvec_false]
  exact AutOm.form_pvec k false

omit [Finite K] [CharP K 2] in
theorem Q_comb (a c : K) :
    coordinateQuadPlus 4 K (a • (Pi.single (ie (Fin.last 3)) 1 : Fin (2 * 4) → K) +
      c • (Pi.single (jf (Fin.last 3)) 1 : Fin (2 * 4) → K)) = a * c := by
  rw [QuadraticMap.map_add (coordinateQuadPlus 4 K : (Fin (2 * 4) → K) → K),
    QuadraticMap.map_smul, QuadraticMap.map_smul, Q_single_ie,
    Q_single_jf, polar_smul_left, polar_smul_right, polar_single_ie_jf]
  simp

omit [Finite K] in
theorem polar_comb (a c b d : K) :
    polar (coordinateQuadPlus 4 K) (a • (Pi.single (ie (Fin.last 3)) 1 : Fin (2 * 4) → K) +
      c • (Pi.single (jf (Fin.last 3)) 1 : Fin (2 * 4) → K))
      (b • (Pi.single (ie (Fin.last 3)) 1 : Fin (2 * 4) → K) +
        d • (Pi.single (jf (Fin.last 3)) 1 : Fin (2 * 4) → K)) = a * d + c * b := by
  have hfe : polar (coordinateQuadPlus 4 K) (Pi.single (jf (Fin.last 3)) 1 : Fin (2 * 4) → K)
      (Pi.single (ie (Fin.last 3)) 1) = 1 := by
    rw [polar_comm, polar_single_ie_jf]
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, polar_single_ie,
    single_jf_apply_jf, ite_true, D4Rank.polar_self_zero, hfe, smul_eq_mul]
  ring

variable (hω : orderOf ω = 3)
include hω

theorem blkE_mul {x y : Om8 K} (hy : y ∈ Subgroup.centralizer {zStd ω}) :
    blkE (x * y) = blkE x * blkE y := by
  ext m i
  rw [blkE, Matrix.of_apply, act_mul, act_ie_castSucc_eq hω hy i, act_sum_smul, Finset.sum_apply,
    Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  rfl

theorem cA_mul {x y : Om8 K} (hy : y ∈ Subgroup.centralizer {zStd ω}) :
    cA (x * y) = cA y * cA x + cC y * cB x := by
  rw [cA, act_mul, act_ie_last_eq hω hy, act_add, act_smul, act_smul, Pi.add_apply, Pi.smul_apply,
    Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  rfl

theorem cC_mul {x y : Om8 K} (hy : y ∈ Subgroup.centralizer {zStd ω}) :
    cC (x * y) = cA y * cC x + cC y * cD x := by
  rw [cC, act_mul, act_ie_last_eq hω hy, act_add, act_smul, act_smul, Pi.add_apply, Pi.smul_apply,
    Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  rfl

theorem cA_mul_cC {x : Om8 K} (hx : x ∈ Subgroup.centralizer {zStd ω}) : cA x * cC x = 0 := by
  have h := Q_act x (Pi.single (ie (Fin.last 3)) 1)
  rwa [act_ie_last_eq hω hx, Q_comb, Q_single_ie] at h

theorem cB_mul_cD {x : Om8 K} (hx : x ∈ Subgroup.centralizer {zStd ω}) : cB x * cD x = 0 := by
  have h := Q_act x (Pi.single (jf (Fin.last 3)) 1)
  rwa [act_jf_last_eq hω hx, Q_comb, Q_single_jf] at h

theorem cA_cD_add {x : Om8 K} (hx : x ∈ Subgroup.centralizer {zStd ω}) :
    cA x * cD x + cC x * cB x = 1 := by
  have h := polar_act x (Pi.single (ie (Fin.last 3)) 1) (Pi.single (jf (Fin.last 3)) 1)
  rwa [act_ie_last_eq hω hx, act_jf_last_eq hω hx, polar_comb, polar_single_ie_jf] at h

omit hω in
open Classical in
@[expose] noncomputable def sgnV (x : Om8 K) : ℤ := if cC x = 0 then 1 else -1

theorem sgnV_mul {x y : Om8 K} (hx : x ∈ Subgroup.centralizer {zStd ω})
    (hy : y ∈ Subgroup.centralizer {zStd ω}) : sgnV (x * y) = sgnV x * sgnV y := by
  have h1x := cA_mul_cC hω hx
  have h1y := cA_mul_cC hω hy
  have h2x := cB_mul_cD hω hx
  have h3x := cA_cD_add hω hx
  have h3y := cA_cD_add hω hy
  have hm := cC_mul hω (x := x) hy
  unfold sgnV
  by_cases hcx : cC x = 0 <;> by_cases hcy : cC y = 0
  · have : cC (x * y) = 0 := by rw [hm, hcx, hcy]; ring
    simp [hcx, hcy, this]
  · have hAy : cA y = 0 := (mul_eq_zero.mp h1y).resolve_right hcy
    have hDx : cD x ≠ 0 := by
      intro h
      rw [h, hcx] at h3x
      simp at h3x
    have : cC (x * y) ≠ 0 := by
      rw [hm, hAy, zero_mul, zero_add]
      exact mul_ne_zero hcy hDx
    simp [hcx, hcy, this]
  · have hAx : cA x = 0 := (mul_eq_zero.mp h1x).resolve_right hcx
    have hAy : cA y ≠ 0 := by
      intro h
      rw [h, hcy] at h3y
      simp at h3y
    have : cC (x * y) ≠ 0 := by
      rw [hm, hcy, zero_mul, add_zero]
      exact mul_ne_zero hAy hcx
    simp [hcx, hcy, this]
  · have hAx : cA x = 0 := (mul_eq_zero.mp h1x).resolve_right hcx
    have hBx : cB x ≠ 0 := by
      intro h
      rw [hAx, h] at h3x
      simp at h3x
    have hDx : cD x = 0 := (mul_eq_zero.mp h2x).resolve_left hBx
    have hAy : cA y = 0 := (mul_eq_zero.mp h1y).resolve_right hcy
    have : cC (x * y) = 0 := by rw [hm, hAy, hDx]; ring
    simp [hcx, hcy, this]

theorem cC_eq_zero_of_mem_commutator {z : Om8 K}
    (hz : z ∈ ⁅Subgroup.centralizer {zStd ω}, Subgroup.centralizer {zStd ω}⁆) : cC z = 0 := by
  have h := map_eq_one_of_mem_commutator sgnV (by rw [sgnV, cC_one, ite_eq_left rfl])
    (fun x hx y hy => sgnV_mul hω hx hy) hz
  by_contra hne
  rw [sgnV, ite_eq_right hne] at h
  norm_num at h

theorem det_blkE_eq_one {z : Om8 K}
    (hz : z ∈ ⁅Subgroup.centralizer {zStd ω}, Subgroup.centralizer {zStd ω}⁆) :
    (blkE z).det = 1 :=
  map_eq_one_of_mem_commutator (fun x => (blkE x).det) (by rw [blkE_one, Matrix.det_one])
    (fun x _ y hy => by rw [blkE_mul hω hy, Matrix.det_mul]) hz

theorem cA_eq_one_of_mem_commutator {z : Om8 K}
    (hz : z ∈ ⁅⁅Subgroup.centralizer {zStd ω}, Subgroup.centralizer {zStd ω}⁆,
      ⁅Subgroup.centralizer {zStd ω}, Subgroup.centralizer {zStd ω}⁆⁆) : cA z = 1 :=
  map_eq_one_of_mem_commutator cA cA_one (fun x _ y hy => by
    rw [cA_mul hω (Subgroup.commutator_le_self _ hy), cC_eq_zero_of_mem_commutator hω hy, zero_mul,
      add_zero, mul_comm]) hz

end Blocks

section Levi

theorem last_ne_castSucc' (l : Fin 3) : (Fin.last 3 : Fin 4) ≠ Fin.castSucc l :=
  (castSucc_ne_last' l).symm

theorem ePart_single_ie (i : Fin 3) :
    ePart (Pi.single (ie i.castSucc) 1 : Fin (2 * 4) → K) = Pi.single i 1 := by
  funext j
  show (Pi.single (ie i.castSucc) 1 : Fin (2 * 4) → K) (ie j.castSucc) = _
  rw [single_ie_apply_ie, Pi.single_apply]
  exact if_congr Fin.castSucc_inj rfl rfl

theorem fPart_single_ie (k : Fin 4) : fPart (Pi.single (ie k) 1 : Fin (2 * 4) → K) = 0 := by
  funext j
  rw [fPart, single_ie_apply_jf, Pi.zero_apply]

theorem ePart_single_jf (k : Fin 4) : ePart (Pi.single (jf k) 1 : Fin (2 * 4) → K) = 0 := by
  funext j
  rw [ePart, single_jf_apply_ie, Pi.zero_apply]

theorem ePart_single_ie_last : ePart (Pi.single (ie (Fin.last 3)) 1 : Fin (2 * 4) → K) = 0 := by
  funext j
  rw [ePart, single_ie_apply_ie, ite_eq_right (castSucc_ne_last' j), Pi.zero_apply]

theorem fPart_single_jf_last : fPart (Pi.single (jf (Fin.last 3)) 1 : Fin (2 * 4) → K) = 0 := by
  funext j
  rw [fPart, single_jf_apply_jf, ite_eq_right (castSucc_ne_last' j), Pi.zero_apply]

theorem act_leviOm_ie_castSucc (A : Matrix.SpecialLinearGroup (Fin 3) K) (i : Fin 3) :
    act (leviOm A) (Pi.single (ie i.castSucc) 1) =
      ∑ l : Fin 3, (A : Matrix (Fin 3) (Fin 3) K) l i •
        (Pi.single (ie l.castSucc) 1 : Fin (2 * 4) → K) := by
  rw [act_leviOm]
  refine vec_ext (fun m => ?_) ?_ (fun m => ?_) ?_
  · rw [leviVec_ie_castSucc, ePart_single_ie, Matrix.mulVec_single_one, sum_ie_apply]
    simp only [single_ie_apply_ie, Fin.castSucc_inj, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.col_apply]
  · rw [leviVec_ie_last, sum_ie_apply]
    simp only [single_ie_apply_ie, last_ne_castSucc', ite_false, mul_zero, Finset.sum_const_zero]
  · rw [leviVec_jf_castSucc, fPart_single_ie, Matrix.zero_vecMul, Pi.zero_apply, sum_ie_apply]
    simp only [single_ie_apply_jf, mul_zero, Finset.sum_const_zero]
  · rw [leviVec_jf_last, single_ie_apply_jf, sum_ie_apply]
    simp only [single_ie_apply_jf, mul_zero, Finset.sum_const_zero]

theorem act_leviOm_ie_last (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    act (leviOm A) (Pi.single (ie (Fin.last 3)) 1) = Pi.single (ie (Fin.last 3)) 1 := by
  rw [act_leviOm]
  refine vec_ext (fun m => ?_) ?_ (fun m => ?_) ?_
  · rw [leviVec_ie_castSucc, ePart_single_ie_last, Matrix.mulVec_zero, Pi.zero_apply,
      single_ie_apply_ie, ite_eq_right (castSucc_ne_last' m)]
  · rw [leviVec_ie_last]
  · rw [leviVec_jf_castSucc, fPart_single_ie, Matrix.zero_vecMul, Pi.zero_apply, single_ie_apply_jf]
  · rw [leviVec_jf_last]

theorem act_leviOm_jf_last (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    act (leviOm A) (Pi.single (jf (Fin.last 3)) 1) = Pi.single (jf (Fin.last 3)) 1 := by
  rw [act_leviOm]
  refine vec_ext (fun m => ?_) ?_ (fun m => ?_) ?_
  · rw [leviVec_ie_castSucc, ePart_single_jf, Matrix.mulVec_zero, Pi.zero_apply, single_jf_apply_ie]
  · rw [leviVec_ie_last]
  · rw [leviVec_jf_castSucc, fPart_single_jf_last, Matrix.zero_vecMul, Pi.zero_apply,
      single_jf_apply_jf, ite_eq_right (castSucc_ne_last' m)]
  · rw [leviVec_jf_last]

variable [Finite K] [CharP K 2] {ω : Kˣ}

theorem range_leviOm_le_centralizer (hω3 : ω ^ 3 = 1) :
    (leviOm (K := K)).range ≤ Subgroup.centralizer {zStd ω} := by
  rintro _ ⟨A, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← leviOm_scalar hω3, ← map_mul, ← map_mul,
    scalarSL_comm]

omit [Finite K] [CharP K 2] in
theorem eq_one_of_act_single {y : Om8 K} (he : ∀ k, act y (Pi.single (ie k) 1) = Pi.single (ie k) 1)
    (hf : ∀ k, act y (Pi.single (jf k) 1) = Pi.single (jf k) 1) : y = 1 := by
  have hker : LinearMap.ker (omRep y - 1) = ⊤ := AutOm.eq_top_of_pvec_mem fun k r => by
    rw [mem_ker_iff_act]
    cases r
    · rw [AutOm.pvec_false]
      exact hf k
    · rw [AutOm.pvec_true]
      exact he k
  exact eq_one_of_act fun v => mem_ker_iff_act.mp (hker ▸ Submodule.mem_top)

theorem perfect_le_range_leviOm (hω : orderOf ω = 3) {X : Subgroup (Om8 K)}
    (hX : X ≤ Subgroup.centralizer {zStd ω}) (hXp : ⁅X, X⁆ = X) : X ≤ (leviOm (K := K)).range := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  set C := Subgroup.centralizer {zStd ω} with hCdef
  have h1 : X ≤ ⁅C, C⁆ := by
    rw [← hXp]
    exact Subgroup.commutator_mono hX hX
  have h2 : X ≤ ⁅⁅C, C⁆, ⁅C, C⁆⁆ := by
    rw [← hXp]
    exact Subgroup.commutator_mono h1 h1
  have hSC := range_leviOm_le_centralizer (K := K) hω3
  intro x hxX
  have hxC : x ∈ C := hX hxX
  have hc : cC x = 0 := cC_eq_zero_of_mem_commutator hω (h1 hxX)
  have ha : cA x = 1 := cA_eq_one_of_mem_commutator hω (h2 hxX)
  have hdet : (blkE x).det = 1 := det_blkE_eq_one hω (h1 hxX)
  have hd : cD x = 1 := by
    have h := cA_cD_add hω hxC
    rwa [ha, hc, one_mul, zero_mul, add_zero] at h
  have hb : cB x = 0 := by
    have h := cB_mul_cD hω hxC
    rwa [hd, mul_one] at h
  set A : Matrix.SpecialLinearGroup (Fin 3) K := ⟨blkE x, hdet⟩ with hA
  refine ⟨A, (inv_mul_eq_one.mp ?_ : leviOm A = x)⟩
  set y := (leviOm A)⁻¹ * x with hy
  have hyC : y ∈ C := C.mul_mem (C.inv_mem (hSC ⟨A, rfl⟩)) hxC
  have he3 : act y (Pi.single (ie (Fin.last 3)) 1) = Pi.single (ie (Fin.last 3)) 1 := by
    rw [hy, act_mul, act_ie_last_eq hω hxC, ha, hc, one_smul, zero_smul, add_zero]
    conv_lhs => rw [← act_leviOm_ie_last A]
    exact act_inv_act _ _
  have hf3 : act y (Pi.single (jf (Fin.last 3)) 1) = Pi.single (jf (Fin.last 3)) 1 := by
    rw [hy, act_mul, act_jf_last_eq hω hxC, hb, hd, one_smul, zero_smul, zero_add]
    conv_lhs => rw [← act_leviOm_jf_last A]
    exact act_inv_act _ _
  have hei : ∀ i : Fin 3, act y (Pi.single (ie i.castSucc) 1) = Pi.single (ie i.castSucc) 1 := by
    intro i
    have h : act x (Pi.single (ie i.castSucc) 1) =
        act (leviOm A) (Pi.single (ie i.castSucc) 1) := by
      rw [act_ie_castSucc_eq hω hxC i, act_leviOm_ie_castSucc]
    rw [hy, act_mul, h]
    exact act_inv_act _ _
  have hfi : ∀ i : Fin 3, act y (Pi.single (jf i.castSucc) 1) = Pi.single (jf i.castSucc) 1 := by
    intro i
    have hcoef : ∀ l : Fin 3, act y (Pi.single (jf i.castSucc) 1) (jf l.castSucc) =
        (Pi.single (jf i.castSucc) 1 : Fin (2 * 4) → K) (jf l.castSucc) := by
      intro l
      calc act y (Pi.single (jf i.castSucc) 1) (jf l.castSucc)
          = polar (coordinateQuadPlus 4 K) (Pi.single (ie l.castSucc) 1)
              (act y (Pi.single (jf i.castSucc) 1)) := (polar_single_ie _ _).symm
        _ = polar (coordinateQuadPlus 4 K) (act y (Pi.single (ie l.castSucc) 1))
              (act y (Pi.single (jf i.castSucc) 1)) := by rw [hei l]
        _ = polar (coordinateQuadPlus 4 K) (Pi.single (ie l.castSucc) 1)
              (Pi.single (jf i.castSucc) 1) := polar_act y _ _
        _ = (Pi.single (jf i.castSucc) 1 : Fin (2 * 4) → K) (jf l.castSucc) := polar_single_ie _ _
    rw [act_jf_castSucc_eq hω hyC i]
    conv_rhs => rw [eq_sum_jf (v := (Pi.single (jf i.castSucc) 1 : Fin (2 * 4) → K))
      (by rw [single_jf_apply_jf, ite_eq_right (last_ne_castSucc' i)])
      (fun k => single_jf_apply_ie _ _)]
    simp only [hcoef]
  refine eq_one_of_act_single (fun k => ?_) (fun k => ?_)
  · induction k using Fin.lastCases with
    | last => exact he3
    | cast i => exact hei i
  · induction k using Fin.lastCases with
    | last => exact hf3
    | cast i => exact hfi i

end Levi

end L613C3

open L613C3

theorem ggD4ClassThreeLayerStdInput_holds : GGD4ClassThreeLayerStdInput := by
  intro K _ _ _ _ ω hω
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  exact ⟨(leviOm (K := K)).range, commutator_range_leviOm, ⟨_, leviOm_scalar hω3⟩,
    range_leviOm_le_centralizer hω3, fun X hX hXp => perfect_le_range_leviOm hω hX hXp,
    card_range_leviOm_le⟩

end CFSG.StandardType
