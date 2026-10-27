module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613KGConj

public section

namespace CFSG.StandardType

namespace L613C3

open Module CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL CFSG.StandardType.D4Rank CFSG.StandardType.L613KG QuadraticMap
open scoped Matrix

variable {K : Type} [Field K]

section Omega

variable [CharP K 2] {ω : K}

omit [CharP K 2] in
theorem omega_cube (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  linear_combination (ω - 1) * hω

theorem omega_ne_one (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 1 := by
  intro h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [h] at hω
  have h1 : (1 : K) = 0 := by linear_combination hω - h2
  exact one_ne_zero h1

theorem omega_sq_ne_one (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 2 ≠ 1 := by
  intro h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h0 : ω = 0 := by linear_combination hω - h - h2
  rw [h0] at h
  norm_num at h

theorem omega_mul_self_ne_one (hω : ω ^ 2 + ω + 1 = 0) : ω * ω ≠ 1 := by
  rw [← pow_two]
  exact omega_sq_ne_one hω

theorem omega_sq_mul_sq_ne_one (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 2 * ω ^ 2 ≠ 1 := by
  intro h
  apply omega_ne_one hω
  linear_combination h - ω * omega_cube hω

omit [CharP K 2] in
theorem omega_ne_zero (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 0 := by
  intro h
  rw [h] at hω
  norm_num at hω

omit [CharP K 2] in
theorem omega_inv (hω : ω ^ 2 + ω + 1 = 0) : ω⁻¹ = ω ^ 2 :=
  inv_eq_of_mul_eq_one_right (by linear_combination omega_cube hω)

end Omega

section Eigen

variable {z : Om8 K}

theorem act_sum_smul {ι : Type*} (s : Finset ι) (c : ι → K) (v : ι → Fin (2 * 4) → K) :
    act z (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • act z (v i) := by
  simp only [act, Matrix.mulVec_sum, Matrix.mulVec_smul]

theorem polar_sum_smul_left {ι : Type*} (s : Finset ι) (c : ι → K) (v : ι → Fin (2 * 4) → K)
    (y : Fin (2 * 4) → K) :
    polar (coordinateQuadPlus 4 K) (∑ i ∈ s, c i • v i) y =
      ∑ i ∈ s, c i * polar (coordinateQuadPlus 4 K) (v i) y := by
  have h : polar (coordinateQuadPlus 4 K) (∑ i ∈ s, c i • v i) y =
      polarBilin (coordinateQuadPlus 4 K) (∑ i ∈ s, c i • v i) y := rfl
  rw [h, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply, polarBilin_apply_apply, smul_eq_mul]

theorem polar_sum_smul_right {ι : Type*} (s : Finset ι) (c : ι → K) (v : ι → Fin (2 * 4) → K)
    (y : Fin (2 * 4) → K) :
    polar (coordinateQuadPlus 4 K) y (∑ i ∈ s, c i • v i) =
      ∑ i ∈ s, c i * polar (coordinateQuadPlus 4 K) y (v i) := by
  rw [polar_comm, polar_sum_smul_left]
  simp only [polar_comm]

@[expose] noncomputable def eproj (z : Om8 K) (l : K) (v : Fin (2 * 4) → K) : Fin (2 * 4) → K :=
  v + l ^ 2 • act z v + l • act z (act z v)

theorem act_eproj (hz3 : z ^ 3 = 1) {l : K} (hl : l ^ 3 = 1) (v : Fin (2 * 4) → K) :
    act z (eproj z l v) = l • eproj z l v := by
  simp only [eproj, act_add, act_smul, act_cube hz3, smul_add, smul_smul]
  rw [show l * l ^ 2 = l ^ 3 by ring, hl, one_smul, show l * l = l ^ 2 by ring]
  abel

theorem eq_eproj_add [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (v : Fin (2 * 4) → K) :
    v = eproj z 1 v + eproj z ω v + eproj z (ω ^ 2) v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  funext i
  simp only [eproj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(v i)) * h2 - (act z v i) * (1 + ω ^ 2 - ω) * hω -
    (act z (act z v) i) * hω

theorem polar_eq_zero_of_eigen {a b : Fin (2 * 4) → K} {l m : K} (ha : act z a = l • a)
    (hb : act z b = m • b) (hlm : l * m ≠ 1) : polar (coordinateQuadPlus 4 K) a b = 0 := by
  have h := polar_act z a b
  rw [ha, hb, polar_smul_left, polar_smul_right, smul_eq_mul, smul_eq_mul] at h
  have h' : (l * m - 1) * polar (coordinateQuadPlus 4 K) a b = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hlm
  · exact h1

theorem Q_eq_zero_of_eigen {a : Fin (2 * 4) → K} {l : K} (ha : act z a = l • a)
    (hl : l * l ≠ 1) : coordinateQuadPlus 4 K a = 0 := by
  have h := Q_act z a
  rw [ha, QuadraticMap.map_smul, smul_eq_mul] at h
  have h' : (l * l - 1) * coordinateQuadPlus 4 K a = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hl
  · exact h1

end Eigen

section Triple

@[expose] def IsHypTriple (F G : Fin 3 → Fin (2 * 4) → K) : Prop :=
  (∀ i, coordinateQuadPlus 4 K (F i) = 0) ∧ (∀ i, coordinateQuadPlus 4 K (G i) = 0) ∧
    (∀ i j, polar (coordinateQuadPlus 4 K) (F i) (F j) = 0) ∧
    (∀ i j, polar (coordinateQuadPlus 4 K) (G i) (G j) = 0) ∧
    ∀ i j, polar (coordinateQuadPlus 4 K) (F i) (G j) = if i = j then 1 else 0

theorem castAdd_ne_natAdd_three (a b : Fin 3) : Fin.castAdd 3 a ≠ Fin.natAdd 3 b := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
  omega

theorem IsHypTriple.polar_dual {F G : Fin 3 → Fin (2 * 4) → K} (h : IsHypTriple F G)
    (i j : Fin (3 + 3)) :
    polar (coordinateQuadPlus 4 K) (Fin.append F G i) (Fin.append G F j) =
      if i = j then 1 else 0 := by
  obtain ⟨-, -, hFF, hGG, hFG⟩ := h
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>
    simp only [Fin.append_left, Fin.append_right]
  · rw [hFG]
    exact if_congr Fin.castAdd_inj.symm rfl rfl
  · rw [hFF, ite_eq_right (castAdd_ne_natAdd_three a b)]
  · rw [hGG, ite_eq_right (castAdd_ne_natAdd_three b a).symm]
  · rw [polar_comm, hFG]
    exact if_congr ((Fin.natAdd_inj 3).trans eq_comm).symm rfl rfl

theorem IsHypTriple.linIndep {F G : Fin 3 → Fin (2 * 4) → K} (h : IsHypTriple F G) :
    LinearIndependent K (Fin.append F G) :=
  linIndep_of_dual (w := Fin.append G F) h.polar_dual

theorem IsHypTriple.Q_append {F G : Fin 3 → Fin (2 * 4) → K} (h : IsHypTriple F G)
    (i : Fin (3 + 3)) : coordinateQuadPlus 4 K (Fin.append F G i) = 0 := by
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · rw [Fin.append_left]
    exact h.1 a
  · rw [Fin.append_right]
    exact h.2.1 a

theorem IsHypTriple.polar_append_eq {F G F' G' : Fin 3 → Fin (2 * 4) → K}
    (h : IsHypTriple F G) (h' : IsHypTriple F' G') (i j : Fin (3 + 3)) :
    polar (coordinateQuadPlus 4 K) (Fin.append F' G' i) (Fin.append F' G' j) =
      polar (coordinateQuadPlus 4 K) (Fin.append F G i) (Fin.append F G j) := by
  obtain ⟨-, -, hFF, hGG, hFG⟩ := h
  obtain ⟨-, -, hFF', hGG', hFG'⟩ := h'
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>
    simp only [Fin.append_left, Fin.append_right]
  · rw [hFF', hFF]
  · rw [hFG', hFG]
  · rw [polar_comm, hFG', polar_comm, hFG]
  · rw [hGG', hGG]

end Triple

section Frame

variable [CharP K 2] {z : Om8 K} {ω : K}

@[expose] def IsEFrame (z : Om8 K) (ω : K) {k : ℕ} (u w : Fin k → Fin (2 * 4) → K) : Prop :=
  (∀ i, act z (u i) = ω • u i) ∧ (∀ i, act z (w i) = ω ^ 2 • w i) ∧
    ∀ i j, polar (coordinateQuadPlus 4 K) (u i) (w j) = if i = j then 1 else 0

omit [CharP K 2] in
theorem omega_sq_cube (hω : ω ^ 2 + ω + 1 = 0) : (ω ^ 2) ^ 3 = 1 := by
  rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, omega_cube hω, one_pow]

theorem exists_eframe_ext [Finite K] (hz3 : z ^ 3 = 1) (hd : omFixDim z = 2)
    (hω : ω ^ 2 + ω + 1 = 0) {k : ℕ} (hk : k < 3) {u w : Fin k → Fin (2 * 4) → K}
    (hf : IsEFrame z ω u w) :
    ∃ a b : Fin (2 * 4) → K, act z a = ω • a ∧ act z b = ω ^ 2 • b ∧
      polar (coordinateQuadPlus 4 K) a b = 1 ∧
      (∀ j, polar (coordinateQuadPlus 4 K) a (w j) = 0) ∧
      ∀ i, polar (coordinateQuadPlus 4 K) (u i) b = 0 := by
  obtain ⟨hu, hw, huw⟩ := hf
  have hnd := (regular_coordinateQuadPlus 4 K (by norm_num)).1
  have h3 := omega_cube hω
  have h6 := omega_sq_cube hω
  by_contra hcon
  have key : ∀ a b : Fin (2 * 4) → K, act z a = ω • a → act z b = ω ^ 2 • b →
      (∀ j, polar (coordinateQuadPlus 4 K) a (w j) = 0) →
      (∀ i, polar (coordinateQuadPlus 4 K) (u i) b = 0) →
      polar (coordinateQuadPlus 4 K) a b = 0 := by
    intro a b ha hb haw hub
    by_contra hne
    refine hcon ⟨(polar (coordinateQuadPlus 4 K) a b)⁻¹ • a, b, ?_, hb, ?_, fun j => ?_, hub⟩
    · rw [act_smul, ha, smul_comm]
    · rw [polar_smul_left, smul_eq_mul, inv_mul_cancel₀ hne]
    · rw [polar_smul_left, haw, smul_zero]
  set A : (Fin (2 * 4) → K) → Fin (2 * 4) → K := fun y =>
    eproj z ω y - ∑ j, polar (coordinateQuadPlus 4 K) (eproj z ω y) (w j) • u j with hA
  set B : (Fin (2 * 4) → K) → Fin (2 * 4) → K := fun y =>
    eproj z (ω ^ 2) y - ∑ i, polar (coordinateQuadPlus 4 K) (u i) (eproj z (ω ^ 2) y) • w i
    with hB
  have hAe : ∀ y, act z (A y) = ω • A y := by
    intro y
    simp only [hA]
    rw [act_sub, act_sum_smul, act_eproj hz3 h3, smul_sub, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hu, smul_comm]
  have hBe : ∀ y, act z (B y) = ω ^ 2 • B y := by
    intro y
    simp only [hB]
    rw [act_sub, act_sum_smul, act_eproj hz3 h6, smul_sub, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hw, smul_comm]
  have hAw : ∀ y j, polar (coordinateQuadPlus 4 K) (A y) (w j) = 0 := by
    intro y j
    simp only [hA]
    rw [polar_sub_left, polar_sum_smul_left]
    simp only [huw, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      sub_self]
  have hBu : ∀ y i, polar (coordinateQuadPlus 4 K) (u i) (B y) = 0 := by
    intro y i
    simp only [hB]
    rw [polar_sub_right, polar_sum_smul_right]
    simp only [huw, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      sub_self]
  have hA0 : ∀ y, A y = 0 := by
    intro y
    refine hnd.1 _ fun x => ?_
    rw [polarBilin_apply_apply]
    have hBx : eproj z (ω ^ 2) x =
        B x + ∑ i, polar (coordinateQuadPlus 4 K) (u i) (eproj z (ω ^ 2) x) • w i := by
      simp only [hB, sub_add_cancel]
    rw [eq_eproj_add (z := z) hω x, polar_add_right, polar_add_right, hBx, polar_add_right,
      polar_sum_smul_right, key _ _ (hAe y) (hBe x) (hAw y) (hBu x),
      polar_eq_zero_of_eigen (hAe y) (act_eproj hz3 (one_pow 3) x)
        (by rw [mul_one]; exact omega_ne_one hω),
      polar_eq_zero_of_eigen (hAe y) (act_eproj hz3 h3 x) (omega_mul_self_ne_one hω)]
    simp only [hAw y, mul_zero, Finset.sum_const_zero, add_zero]
  have hB0 : ∀ y, B y = 0 := by
    intro y
    refine hnd.1 _ fun x => ?_
    rw [polarBilin_apply_apply]
    have hAx : eproj z ω x =
        A x + ∑ j, polar (coordinateQuadPlus 4 K) (eproj z ω x) (w j) • u j := by
      simp only [hA, sub_add_cancel]
    rw [eq_eproj_add (z := z) hω x, polar_add_right, polar_add_right, hAx, polar_add_right,
      polar_sum_smul_right, polar_comm (coordinateQuadPlus 4 K) (B y) (A x),
      key _ _ (hAe x) (hBe y) (hAw x) (hBu y),
      polar_eq_zero_of_eigen (hBe y) (act_eproj hz3 (one_pow 3) x)
        (by rw [mul_one]; exact omega_sq_ne_one hω),
      polar_eq_zero_of_eigen (hBe y) (act_eproj hz3 h6 x) (omega_sq_mul_sq_ne_one hω)]
    simp only [polar_comm (coordinateQuadPlus 4 K) (B y), hBu y, mul_zero,
      Finset.sum_const_zero, add_zero]
  have htop : (⊤ : Submodule K (Fin (2 * 4) → K)) ≤ LinearMap.ker (omRep z - 1) ⊔
      (Submodule.span K (Set.range u) ⊔ Submodule.span K (Set.range w)) := by
    intro y _
    have hmem : eproj z 1 y + eproj z ω y + eproj z (ω ^ 2) y ∈ LinearMap.ker (omRep z - 1) ⊔
        (Submodule.span K (Set.range u) ⊔ Submodule.span K (Set.range w)) := by
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left ?_)
        (Submodule.mem_sup_right (Submodule.mem_sup_left ?_)))
        (Submodule.mem_sup_right (Submodule.mem_sup_right ?_))
      · refine mem_ker_iff_act.mpr ?_
        have h1 := act_eproj hz3 (one_pow 3) y
        rwa [one_smul] at h1
      · have e : eproj z ω y =
            ∑ j, polar (coordinateQuadPlus 4 K) (eproj z ω y) (w j) • u j :=
          sub_eq_zero.mp (hA0 y)
        rw [e]
        exact Submodule.sum_mem _ fun j _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      · have e : eproj z (ω ^ 2) y =
            ∑ i, polar (coordinateQuadPlus 4 K) (u i) (eproj z (ω ^ 2) y) • w i :=
          sub_eq_zero.mp (hB0 y)
        rw [e]
        exact Submodule.sum_mem _ fun j _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    rwa [← eq_eproj_add hω y] at hmem
  have hle := Submodule.finrank_mono htop
  rw [finrank_top, Module.finrank_fin_fun] at hle
  have h1 := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.ker (omRep z - 1))
    (Submodule.span K (Set.range u) ⊔ Submodule.span K (Set.range w))
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (Submodule.span K (Set.range u))
    (Submodule.span K (Set.range w))
  have h4 := finrank_range_le_card (R := K) u
  have h5 := finrank_range_le_card (R := K) w
  rw [Set.finrank, Fintype.card_fin] at h4 h5
  have hker : finrank K (LinearMap.ker (omRep z - 1)) = 2 := hd
  omega

theorem exists_eframe [Finite K] (hz3 : z ^ 3 = 1) (hd : omFixDim z = 2)
    (hω : ω ^ 2 + ω + 1 = 0) : ∀ k, k ≤ 3 → ∃ u w : Fin k → Fin (2 * 4) → K, IsEFrame z ω u w := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨u, w, hf⟩ := ih (by omega)
    obtain ⟨a, b, ha, hb, hab, haw, hub⟩ := exists_eframe_ext hz3 hd hω (by omega) hf
    refine ⟨Fin.snoc u a, Fin.snoc w b, fun i => ?_, fun i => ?_, fun i j => ?_⟩
    · induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact ha
      | cast i => rw [Fin.snoc_castSucc]; exact hf.1 i
    · induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact hb
      | cast i => rw [Fin.snoc_castSucc]; exact hf.2.1 i
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => rw [Fin.snoc_last, Fin.snoc_last, ite_eq_left rfl]; exact hab
        | cast j =>
          rw [Fin.snoc_last, Fin.snoc_castSucc, ite_eq_right (Fin.castSucc_lt_last j).ne']
          exact haw j
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          rw [Fin.snoc_castSucc, Fin.snoc_last, ite_eq_right (Fin.castSucc_lt_last i).ne]
          exact hub i
        | cast j =>
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc, hf.2.2 i j]
          exact if_congr Fin.castSucc_inj.symm rfl rfl

theorem IsEFrame.isHypTriple (hω : ω ^ 2 + ω + 1 = 0) {u w : Fin 3 → Fin (2 * 4) → K}
    (hf : IsEFrame z ω u w) : IsHypTriple u w :=
  ⟨fun i => Q_eq_zero_of_eigen (hf.1 i) (omega_mul_self_ne_one hω),
    fun i => Q_eq_zero_of_eigen (hf.2.1 i) (omega_sq_mul_sq_ne_one hω),
    fun i j => polar_eq_zero_of_eigen (hf.1 i) (hf.1 j) (omega_mul_self_ne_one hω),
    fun i j => polar_eq_zero_of_eigen (hf.2.1 i) (hf.2.1 j) (omega_sq_mul_sq_ne_one hω), hf.2.2⟩

theorem fixed_of_orth_eframe [Finite K] (hz3 : z ^ 3 = 1) (hd : omFixDim z = 2)
    (hω : ω ^ 2 + ω + 1 = 0) {u w : Fin 3 → Fin (2 * 4) → K} (hf : IsEFrame z ω u w)
    {x : Fin (2 * 4) → K} (hxu : ∀ i, polar (coordinateQuadPlus 4 K) x (u i) = 0)
    (hxw : ∀ i, polar (coordinateQuadPlus 4 K) x (w i) = 0) : act z x = x := by
  have ht := hf.isHypTriple hω
  obtain ⟨hu, hw, -⟩ := hf
  have hω1 : ω - 1 ≠ 0 := sub_ne_zero.mpr (omega_ne_one hω)
  have hω2 : ω ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr (omega_sq_ne_one hω)
  have hrange : ∀ {a : Fin (2 * 4) → K} {l : K}, act z a = l • a → l - 1 ≠ 0 →
      a ∈ LinearMap.range (omRep z - 1) := by
    intro a l ha hl
    refine ⟨(l - 1)⁻¹ • a, ?_⟩
    change act z ((l - 1)⁻¹ • a) - (l - 1)⁻¹ • a = a
    rw [act_smul, ha, smul_smul, ← sub_smul, show (l - 1)⁻¹ * l - (l - 1)⁻¹ = (l - 1)⁻¹ * (l - 1)
      by ring, inv_mul_cancel₀ hl, one_smul]
  have hle : Submodule.span K (Set.range (Fin.append u w)) ≤ LinearMap.range (omRep z - 1) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · rw [Fin.append_left]
      exact hrange (hu a) hω1
    · rw [Fin.append_right]
      exact hrange (hw a) hω2
  have hrn := LinearMap.finrank_range_add_finrank_ker (omRep z - 1)
  rw [Module.finrank_fin_fun] at hrn
  have hsp := finrank_span_eq_card ht.linIndep
  rw [Fintype.card_fin] at hsp
  have hker : finrank K (LinearMap.ker (omRep z - 1)) = 2 := hd
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by omega)
  set c := x + act z x + act z (act z x) with hc
  have hcfix : act z c = c := act_fixPart hz3 x
  have hp : act z (act z x) - act z x ∈ LinearMap.range (omRep z - 1) := ⟨act z x, rfl⟩
  rw [← heq, Submodule.mem_span_range_iff_exists_fun] at hp
  obtain ⟨a, ha⟩ := hp
  have hx : x = c + (act z (act z x) - act z x) := decomp x
  have ha0 : ∀ j, a j = 0 := by
    intro j
    have h1 : polar (coordinateQuadPlus 4 K) (∑ i, a i • Fin.append u w i) (Fin.append w u j) =
        a j := by
      rw [polar_sum_smul_left]
      simp only [ht.polar_dual, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
    have hcj : polar (coordinateQuadPlus 4 K) c (Fin.append w u j) = 0 := by
      refine Fin.addCases (fun b => ?_) (fun b => ?_) j
      · rw [Fin.append_left]
        exact polar_eq_zero_of_eigen (l := 1) (by rw [one_smul]; exact hcfix) (hw b)
          (by rw [one_mul]; exact omega_sq_ne_one hω)
      · rw [Fin.append_right]
        exact polar_eq_zero_of_eigen (l := 1) (by rw [one_smul]; exact hcfix) (hu b)
          (by rw [one_mul]; exact omega_ne_one hω)
    have hxj : polar (coordinateQuadPlus 4 K) x (Fin.append w u j) = 0 := by
      refine Fin.addCases (fun b => ?_) (fun b => ?_) j
      · rw [Fin.append_left]
        exact hxw b
      · rw [Fin.append_right]
        exact hxu b
    rw [← h1, ha]
    have h2 := congrArg (fun y => polar (coordinateQuadPlus 4 K) y (Fin.append w u j)) hx
    simp only [polar_add_left, hcj, zero_add] at h2
    rw [← h2, hxj]
  have hzero : act z (act z x) - act z x = 0 := by
    rw [← ha]
    simp only [ha0, zero_smul, Finset.sum_const_zero]
  rw [hzero, add_zero] at hx
  rw [hx]
  exact hcfix

end Frame

end L613C3

end CFSG.StandardType
