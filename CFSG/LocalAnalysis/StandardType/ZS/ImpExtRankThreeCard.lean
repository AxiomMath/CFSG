module

public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtRankThree
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtJ34
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.RootMatrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem toMatrix_reflection_fin_four (f : Module.Basis (Fin 4) (ZMod p) U) {u : Fin 3 → U}
    {φ : Fin 3 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hfu : ∀ i : Fin 3, f i.castSucc = u i) (C : Matrix (Fin 3) (Fin 4) (ZMod p))
    (hC : ∀ i j, φ i (f j) = C i j) (i : Fin 3) :
    LinearMap.toMatrix f f (Module.reflection (hφ i) : U →ₗ[ZMod p] U) =
      1 - Matrix.of fun r c => if r = i.castSucc then C i c else 0 := by
  have hφ' : φ i (f i.castSucc) = 2 := by rw [hfu]; exact hφ i
  have hr : Module.reflection (hφ i) = Module.reflection hφ' := by
    ext x; rw [Module.reflection_apply, Module.reflection_apply, hfu]
  rw [hr]
  ext r c
  rw [toMatrix_reflection_basis f hφ' r c, Matrix.sub_apply, Matrix.of_apply]
  congr 1
  by_cases hri : r = i.castSucc
  · rw [if_pos hri, if_pos hri, hC]
  · rw [if_neg hri, if_neg hri]

private theorem range_reflections_eq {u : Fin 3 → U} {φ : Fin 3 → Module.Dual (ZMod p) U}
    {hφ : ∀ i, φ i (u i) = 2} {x y z : U ≃ₗ[ZMod p] U}
    (h0 : Module.reflection (hφ 0) = x) (h1 : Module.reflection (hφ 1) = y)
    (h2 : Module.reflection (hφ 2) = z) :
    Set.range (fun i => Module.reflection (hφ i)) = {x, y, z} := by
  rw [range_fin_three, h0, h1, h2]

private theorem exists_gauge_433_four_aux (_hp : p ≠ 2) {va vb vc : U}
    {φa φb φc : Module.Dual (ZMod p) U}
    (hφa : φa va = 2) (hφb : φb vb = 2) (hφc : φc vc = 2)
    (h1 : φa vb * φb va = 2) (h2 : φa vc * φc va = 1) (h3 : φb vc * φc vb = 1)
    (h4 : (φa vb - φa vc * φc vb) * (φb va - φc va * φb vc) = 2) :
    ∃ (θ : ZMod p) (_hθ : θ * θ = θ - 2) (u : Fin 3 → U) (φ : Fin 3 → Module.Dual (ZMod p) U)
      (hφ : ∀ i, φ i (u i) = 2),
      (∀ i j, φ i (u j) =
        (!![2, θ, -1; 1 - θ, 2, -1; -1, -1, 2] : Matrix (Fin 3) (Fin 3) (ZMod p)) i j) ∧
      Module.reflection (hφ 0) = Module.reflection hφa ∧
      Module.reflection (hφ 1) = Module.reflection hφb ∧
      Module.reflection (hφ 2) = Module.reflection hφc := by
  have hs : φa vb * φb vc * φc va + φa vc * φc vb * φb va = 1 := by
    linear_combination h1 + h2 + (φa vc * φc va) * h3 - h4
  have hkk : φa vb * φb vc * φc va * (φa vc * φc vb * φb va) = 2 := by
    linear_combination h1 + (φa vb * φb va) * h2 + (φa vb * φa vc * φb va * φc va) * h3
  have hac0 : φa vc ≠ 0 := left_ne_zero_of_mul (by rw [h2]; exact one_ne_zero)
  have hcb0 : φc vb ≠ 0 := right_ne_zero_of_mul (by rw [h3]; exact one_ne_zero)
  obtain ⟨vb', vc', φb', φc', hb', hc', hrb, hrc, e1, e2, e3, e4, e5, e6, -, -⟩ :=
    exists_starGauge (va := va) (φa := φa) hφb hφc hac0 hcb0
  set θ : ZMod p := φa vb * φb vc * φc va with hθdef
  have hθ : θ * θ = θ - 2 := by linear_combination θ * hs - hkk
  have hab' : φa vb' = θ := by rw [h2, h3] at e6; simpa using e6
  have hba' : φb' va = 1 - θ := by rw [e5]; linear_combination hs
  have hca' : φc' va = -1 := by rw [e3, h2]
  have hbc' : φb' vc' = -1 := by rw [e4, h3]
  let u : Fin 3 → U := ![va, vb', vc']
  let φ : Fin 3 → Module.Dual (ZMod p) U := ![φa, φb', φc']
  have hφ : ∀ i, φ i (u i) = 2 := by
    intro i; fin_cases i
    · exact hφa
    · exact hb'
    · exact hc'
  have hC : ∀ i j, φ i (u j) =
      (!![2, θ, -1; 1 - θ, 2, -1; -1, -1, 2] : Matrix (Fin 3) (Fin 3) (ZMod p)) i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hφa
    · exact hab'
    · exact e1
    · exact hba'
    · exact hb'
    · exact hbc'
    · exact hca'
    · exact e2
    · exact hc'
  exact ⟨θ, hθ, u, φ, hφ, hC, rfl, hrb, hrc⟩

theorem exists_gauge_433_four (hp : p ≠ 2) {va vb vc : U} {φa φb φc : Module.Dual (ZMod p) U}
    (hφa : φa va = 2) (hφb : φb vb = 2) (hφc : φc vc = 2)
    (h1 : φa vb * φb va = 2) (h2 : φa vc * φc va = 1) (h3 : φb vc * φc vb = 1)
    (h4 : (φa vb - φa vc * φc vb) * (φb va - φc va * φb vc) = 2) :
    ∃ (θ : ZMod p) (_hθ : θ * θ = θ - 2) (u : Fin 3 → U) (φ : Fin 3 → Module.Dual (ZMod p) U)
      (hφ : ∀ i, φ i (u i) = 2),
      (∀ i j, φ i (u j) =
        (!![2, θ, -1; 1 - θ, 2, -1; -1, -1, 2] : Matrix (Fin 3) (Fin 3) (ZMod p)) i j) ∧
      Set.range (fun i => Module.reflection (hφ i)) =
        {Module.reflection hφa, Module.reflection hφb, Module.reflection hφc} := by
  obtain ⟨θ, hθ, u, φ, hφ, hC, h0, hrb, hrc⟩ :=
    exists_gauge_433_four_aux hp hφa hφb hφc h1 h2 h3 h4
  exact ⟨θ, hθ, u, φ, hφ, hC, range_reflections_eq h0 hrb hrc⟩

section RankThree

variable [Module.Finite (ZMod p) U] {a b c : U ≃ₗ[ZMod p] U} {A : Subgroup (U ≃ₗ[ZMod p] U)}

private theorem card_eq_336_of_gauge_433 (hp : p ≠ 2) (hU : Module.finrank (ZMod p) U = 4)
    {θ : ZMod p} (hθ : θ * θ = θ - 2) {u : Fin 3 → U}
    {φ : Fin 3 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hC : ∀ i j, φ i (u j) =
      (!![2, θ, -1; 1 - θ, 2, -1; -1, -1, 2] : Matrix (Fin 3) (Fin 3) (ZMod p)) i j) :
    Nat.card (Subgroup.closure (Set.range fun i => Module.reflection (hφ i))) = 336 := by
  have hdet : (Matrix.of fun i j => φ i (u j)).det ≠ 0 := by
    have hmat : (Matrix.of fun i j => φ i (u j)) =
        !![2, θ, -1; 1 - θ, 2, -1; -1, -1, 2] := by
      ext i j; exact hC i j
    rw [hmat, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_fin_const]
    intro h
    have h1 : (1 : ZMod p) = 0 := by linear_combination h - 2 * hθ
    exact one_ne_zero h1
  obtain ⟨f, hfu, hf3⟩ := exists_basis_roots_fixed hU hdet
  have hC4 : ∀ i j, φ i (f j) =
      (!![2, θ, -1, 0; 1 - θ, 2, -1, 0; -1, -1, 2, 0] : Matrix (Fin 3) (Fin 4) (ZMod p)) i j := by
    intro i j
    have hc : ∀ k : Fin 3, φ i (f k.castSucc) =
        (!![2, θ, -1; 1 - θ, 2, -1; -1, -1, 2] : Matrix (Fin 3) (Fin 3) (ZMod p)) i k :=
      fun k => by rw [hfu]; exact hC i k
    fin_cases j
    · have := hc 0; fin_cases i <;> simpa using this
    · have := hc 1; fin_cases i <;> simpa using this
    · have := hc 2; fin_cases i <;> simpa using this
    · fin_cases i <;> simp [hf3]
  have hg : ∀ i, LinearMap.toMatrix f f (Module.reflection (hφ i) : U →ₗ[ZMod p] U) =
      (WJ34.gen i).map (WJ34.ev θ hθ) := fun i =>
    (toMatrix_reflection_fin_four f hφ hfu
      (!![2, θ, -1, 0; 1 - θ, 2, -1, 0; -1, -1, 2, 0] : Matrix (Fin 3) (Fin 4) (ZMod p))
      hC4 i).trans (WJ34.map_gen θ hθ i).symm
  exact WJ34.card_eq_336 (g := fun i => Module.reflection (hφ i)) hp f hθ hg

theorem card_eq_of_433 (hp : p ≠ 2) (hU : Module.finrank (ZMod p) U = 4)
    (ha : IsRefl p a) (hb : IsRefl p b) (hc : IsRefl p c) (hA : A = Subgroup.closure {a, b, c})
    (_hAt : QTwoLin.TransvectionFree A)
    (_hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace A) = 3)
    (_hd : DMax p A 4) (hab : orderOf (a * b) = 4) (hac : orderOf (a * c) = 3)
    (hbc : orderOf (b * c) = 3) (hm : orderOf (c * a * c * b) = 4) :
    SplitSupport A 3 ∧ Nat.card A = 336 := by
  obtain ⟨va, φa, hφa, rfl⟩ := (isRefl_iff hp a).mp ha
  obtain ⟨vb, φb, hφb, rfl⟩ := (isRefl_iff hp b).mp hb
  obtain ⟨vc, φc, hφc, rfl⟩ := (isRefl_iff hp c).mp hc
  have h1 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφa hφb hab
  have h2 := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφa hφc hac
  have h3 := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφb hφc hbc
  rw [reflection_conj_reflection hφc hφa] at hm
  have h4 := apply_mul_apply_eq_two_of_orderOf_eq_four hp _ hφb hm
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul] at h4
  have hs : φa vb * φb vc * φc va + φa vc * φc vb * φb va = 1 := by
    linear_combination h1 + h2 + (φa vc * φc va) * h3 - h4
  have h2' : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  refine ⟨?_, ?_⟩
  · rw [hA]
    refine splitSupport_closure_three hφa hφb hφc (by rw [h1]; exact h2')
      (by rw [h2]; exact one_ne_zero) (by rw [h3]; exact one_ne_zero) ?_
    rw [h1, h2, h3, hs]; norm_num
  obtain ⟨θ, hθ, u, φ, hφ, hC, hrange⟩ := exists_gauge_433_four hp hφa hφb hφc h1 h2 h3 h4
  have hcard := card_eq_336_of_gauge_433 hp hU hθ hφ hC
  rw [hA, ← hrange]
  exact hcard

omit [Module.Finite (ZMod p) U] in
theorem relabel_434 (hp : p ≠ 2) {va vb vc : U}
    {φa φb φc : Module.Dual (ZMod p) U} (hφa : φa va = 2) (hφb : φb vb = 2) (hφc : φc vc = 2)
    (hab : orderOf (Module.reflection hφa * Module.reflection hφb) = 4)
    (hac : orderOf (Module.reflection hφa * Module.reflection hφc) = 3)
    (hbc : orderOf (Module.reflection hφb * Module.reflection hφc) = 4)
    (hm : orderOf (Module.reflection hφc * Module.reflection hφa * Module.reflection hφc *
      Module.reflection hφb) = 3) :
    IsRefl p (Module.reflection hφa * Module.reflection hφb * Module.reflection hφa) ∧
    orderOf (Module.reflection hφa *
      (Module.reflection hφa * Module.reflection hφb * Module.reflection hφa)) = 4 ∧
    orderOf (Module.reflection hφa * Module.reflection hφb * Module.reflection hφa *
      Module.reflection hφc) = 3 ∧
    orderOf (Module.reflection hφc * Module.reflection hφa * Module.reflection hφc *
      (Module.reflection hφa * Module.reflection hφb * Module.reflection hφa)) = 4 := by
  have h1 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφa hφb hab
  have h2 := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφa hφc hac
  have h3 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφb hφc hbc
  rw [reflection_conj_reflection hφc hφa] at hm
  have h4 := apply_mul_apply_eq_one_of_orderOf_eq_three hp _ hφb hm
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul] at h4
  have hp3 : p ≠ 3 := by
    have hq : (φa vb * φb vc * φc va) ^ 2 + ((-3 : ℤ) : ZMod p) * (φa vb * φb vc * φc va) +
        ((4 : ℤ) : ZMod p) = 0 := by
      push_cast
      linear_combination (φa vb * φb vc * φc va - 2) * h1 +
        (2 * (φa vb * φb vc * φc va) - 2 * (φa vb * φb va)) * h2 +
        (φa vb * φa vc * φb vc * φc va ^ 2 - φa vb * φa vc * φb va * φc va) * h3 +
        (-(φa vb * φb vc * φc va)) * h4
    exact ne_of_root_quadratic (-3) 4 hq (by decide)
  have ha2 : Module.reflection hφa * Module.reflection hφa = 1 :=
    mul_eq_one_iff_eq_inv.mpr (Module.reflection_inv hφa).symm
  have hb2 : Module.reflection hφb * Module.reflection hφb = 1 :=
    mul_eq_one_iff_eq_inv.mpr (Module.reflection_inv hφb).symm
  rw [reflection_conj_reflection hφa hφb]
  refine ⟨isRefl_reflection hp _, ?_, ?_, ?_⟩
  · rw [← reflection_conj_reflection hφa hφb, ← mul_assoc, ← mul_assoc, ha2, one_mul]
    rw [show Module.reflection hφb * Module.reflection hφa =
        (Module.reflection hφa * Module.reflection hφb)⁻¹ by
      rw [mul_inv_rev, Module.reflection_inv, Module.reflection_inv], orderOf_inv, hab]
  · refine orderOf_reflection_mul_eq_three hp3 _ hφc ?_
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
    linear_combination (φa vb * φb va - 2) * h2 + (-(φa vc * φc va) + 1) * h3 + h4
  · rw [reflection_conj_reflection hφc hφa]
    refine orderOf_reflection_mul_eq_four hp _ _ ?_
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul, hφa]
    linear_combination (φa vb * φa vc * φb va * φc va - φa vb * φb vc * φc va -
      φa vc * φb va * φc vb - φa vb * φb va + 2) * h2 + (φa vc * φc va) * h3

theorem closure_relabel_434 {G : Type*} [Group G] {a b c : G} (ha : a * a = 1) :
    Subgroup.closure ({a, a * b * a, c} : Set G) = Subgroup.closure {a, b, c} := by
  have hb : a * (a * b * a) * a = b := by
    rw [← mul_assoc, ← mul_assoc, ha, one_mul, mul_assoc, ha, mul_one]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact mul_mem (mul_mem (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | hxb | rfl
    · exact Subgroup.subset_closure (by simp)
    · rw [hxb]
      have h : a * (a * b * a) * a ∈ Subgroup.closure ({a, a * b * a, c} : Set G) :=
        mul_mem (mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp))
      rw [hb] at h
      exact h
    · exact Subgroup.subset_closure (by simp)

theorem card_eq_of_434 (hp : p ≠ 2) (hU : Module.finrank (ZMod p) U = 4)
    (ha : IsRefl p a) (hb : IsRefl p b) (hc : IsRefl p c) (hA : A = Subgroup.closure {a, b, c})
    (hAt : QTwoLin.TransvectionFree A)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace A) = 3)
    (hd : DMax p A 4) (hab : orderOf (a * b) = 4) (hac : orderOf (a * c) = 3)
    (hbc : orderOf (b * c) = 4) (hm : orderOf (c * a * c * b) = 3) :
    SplitSupport A 3 ∧ Nat.card A = 336 := by
  obtain ⟨va, φa, hφa, rfl⟩ := (isRefl_iff hp a).mp ha
  obtain ⟨vb, φb, hφb, rfl⟩ := (isRefl_iff hp b).mp hb
  obtain ⟨vc, φc, hφc, rfl⟩ := (isRefl_iff hp c).mp hc
  obtain ⟨hb', hab', hbc', hm'⟩ := relabel_434 hp hφa hφb hφc hab hac hbc hm
  refine card_eq_of_433 hp hU ha hb' hc ?_ hAt hdim hd hab' hac hbc' hm'
  rw [hA, closure_relabel_434 ha.1]

theorem orderOf_conj_relabel_444 {G : Type*} [Group G] {a b c : G} (ha : a * a = 1)
    (hc : c * c = 1) :
    orderOf (a * c * a * b * (a * c * a) * a) = orderOf (a * b * a * (c * a * c)) := by
  refine SemiconjBy.orderOf_eq (c * a) ?_
  have ha' : ∀ x, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  have hc' : ∀ x, c * (c * x) = x := fun x => by rw [← mul_assoc, hc, one_mul]
  simp only [SemiconjBy, mul_assoc, ha', hc']

theorem finrank_commutatorSpace_le_two_of_mem_span {va vb vc : U}
    {φa φb φc : Module.Dual (ZMod p) U} (hφa : φa va = 2) (hφb : φb vb = 2) (hφc : φc vc = 2)
    (hb : vb ∈ Submodule.span (ZMod p) {va, vc}) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure ({Module.reflection hφa, Module.reflection hφb,
        Module.reflection hφc} : Set (U ≃ₗ[ZMod p] U)))) ≤ 2 := by
  have hle : HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure ({Module.reflection hφa, Module.reflection hφb,
        Module.reflection hφc} : Set (U ≃ₗ[ZMod p] U))) ≤ Submodule.span (ZMod p) {va, vc} := by
    rw [commutatorSpace_le_iff]
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem t ht =>
      intro v
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl
      · rw [Module.reflection_apply]
        rw [show v - φa v • va - v = -(φa v • va) by abel]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      · rw [Module.reflection_apply]
        rw [show v - φb v • vb - v = -(φb v • vb) by abel]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hb)
      · rw [Module.reflection_apply]
        rw [show v - φc v • vc - v = -(φc v • vc) by abel]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    | one => intro v; simp
    | mul x y _ _ ihx ihy =>
      intro v
      rw [LinearEquiv.mul_apply, show x (y v) - v = (x (y v) - y v) + (y v - v) by abel]
      exact Submodule.add_mem _ (ihx (y v)) (ihy v)
    | inv x _ ihx =>
      intro v
      have h1 := ihx (x⁻¹ v)
      have h2 : x⁻¹ v - v = -(x (x⁻¹ v) - x⁻¹ v) := by
        have hx : x (x⁻¹ v) = v := by simp
        rw [hx]; abel
      rw [h2]; exact Submodule.neg_mem _ h1
  exact (Submodule.finrank_mono hle).trans
    (HardMathSupport.Kantor79.finrank_span_pair_le_two va vc)

omit [Module.Finite (ZMod p) U] in
theorem orderOf_cacb_ne_two_of_444 (hp : p ≠ 2) {va vb vc : U}
    {φa φb φc : Module.Dual (ZMod p) U} (hφa : φa va = 2) (hφb : φb vb = 2) (hφc : φc vc = 2)
    (hab : orderOf (Module.reflection hφa * Module.reflection hφb) = 4)
    (hac : orderOf (Module.reflection hφa * Module.reflection hφc) = 4)
    (hbc : orderOf (Module.reflection hφb * Module.reflection hφc) = 4) :
    orderOf (Module.reflection hφc * Module.reflection hφa * Module.reflection hφc *
      Module.reflection hφb) ≠ 2 := by
  intro hm
  have h1 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφa hφb hab
  have h2 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφa hφc hac
  have h3 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφb hφc hbc
  rw [reflection_conj_reflection hφc hφa] at hm
  obtain ⟨E1, E2⟩ := apply_eq_zero_of_orderOf_eq_two hp _ hφb hm
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul] at E1 E2
  have h2' : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  exact h2' (by
    linear_combination -(φb va) * E1 - (φa vc * φc vb) * E2 + h1 - (φb vc * φc vb) * h2 - 2 * h3)

private theorem finrank_le_two_of_reflection_eq (hp : p ≠ 2) {va vb vc : U}
    {φa φb φc : Module.Dual (ZMod p) U} (hφa : φa va = 2) (hφb : φb vb = 2) (hφc : φc vc = 2)
    (h1 : φa vb * φb va = 2)
    (heq : Module.reflection (conj_pairing hφb hφa) = Module.reflection (conj_pairing hφc hφa)) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure ({Module.reflection hφa, Module.reflection hφb,
        Module.reflection hφc} : Set (U ≃ₗ[ZMod p] U)))) ≤ 2 := by
  have h2' : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hb0 : φb va ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact h2' h1.symm
  have h5 := two_smul_eq_of_reflection_eq _ _ heq
  set t := (φa - φa vc • φc) (va - φb va • vb) with ht
  have h6 : (2 * φb va) • vb = (2 - t) • va + (t * φc va) • vc := by
    linear_combination (norm := module) h5
  have h7 : vb = (2 * φb va)⁻¹ • ((2 - t) • va + (t * φc va) • vc) := by
    rw [← h6, inv_smul_smul₀ (mul_ne_zero h2' hb0)]
  have hmem : vb ∈ Submodule.span (ZMod p) {va, vc} := by
    rw [h7]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
  exact finrank_commutatorSpace_le_two_of_mem_span hφa hφb hφc hmem

theorem orderOf_cacb_ne_four_of_444 (hp : p ≠ 2) {va vb vc : U}
    {φa φb φc : Module.Dual (ZMod p) U} (hφa : φa va = 2) (hφb : φb vb = 2) (hφc : φc vc = 2)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure ({Module.reflection hφa, Module.reflection hφb,
        Module.reflection hφc} : Set (U ≃ₗ[ZMod p] U)))) = 3)
    (hab : orderOf (Module.reflection hφa * Module.reflection hφb) = 4)
    (hac : orderOf (Module.reflection hφa * Module.reflection hφc) = 4)
    (hbc : orderOf (Module.reflection hφb * Module.reflection hφc) = 4)
    (hx : orderOf (Module.reflection hφb * Module.reflection hφa * Module.reflection hφb *
      (Module.reflection hφc * Module.reflection hφa * Module.reflection hφc)) ≤ 4) :
    orderOf (Module.reflection hφc * Module.reflection hφa * Module.reflection hφc *
      Module.reflection hφb) ≠ 4 := by
  intro hm
  have h1 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφa hφb hab
  have h2 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφa hφc hac
  have h3 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφb hφc hbc
  rw [reflection_conj_reflection hφc hφa] at hm
  have h4 := apply_mul_apply_eq_two_of_orderOf_eq_four hp _ hφb hm
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul] at h4
  rw [reflection_conj_reflection hφb hφa, reflection_conj_reflection hφc hφa] at hx
  have h2' : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hP : (φa - φa vb • φb) (va - φc va • vc) * (φa - φa vc • φc) (va - φb va • vb) = 4 := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul, hφa]
    linear_combination (-(φa vb) * φb vc * φc va - φa vc * φb va * φc vb + φa vb * φb va + 4) * h1 +
      (-(φa vb) * φb vc * φc va - φa vc * φb va * φc vb + 4 * (φa vb * φb va) + φa vc * φc va -
        6) * h2 + (φa vb * φa vc * φb va * φc va - 2 * (φa vc * φc va)) * h3 + 2 * h4
  have hp3 : p ≠ 3 := by
    have hq : (φa vb * φb vc * φc va) ^ 2 + ((-4 : ℤ) : ZMod p) * (φa vb * φb vc * φc va) +
        ((8 : ℤ) : ZMod p) = 0 := by
      push_cast
      linear_combination (φa vb * φb vc * φc va - 4) * h1 +
        (2 * (φa vb * φb vc * φc va) - 2 * (φa vb * φb va)) * h2 +
        (φa vb * φa vc * φb vc * φc va ^ 2 - φa vb * φa vc * φb va * φc va) * h3 +
        (-(φa vb * φb vc * φc va)) * h4
    exact ne_of_root_quadratic (-4) 8 hq (by decide)
  rcases eta_cases_of_orderOf_le_four hp _ _ hx with ⟨z1, -⟩ | h | h | ⟨heq, -⟩
  · rw [z1, zero_mul] at hP
    have h22 : (2 : ZMod p) * 2 = 0 := by linear_combination -hP
    exact h2' (mul_self_eq_zero.mp h22)
  · have h3' : (3 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 3 hp3
    exact h3' (by linear_combination h - hP)
  · exact h2' (by linear_combination h - hP)
  · have hle := finrank_le_two_of_reflection_eq hp hφa hφb hφc h1 heq
    omega

omit [Module.Finite (ZMod p) U] in
private theorem ne_three_of_444 {va vb vc : U}
    {φa φb φc : Module.Dual (ZMod p) U}
    (h1 : φa vb * φb va = 2) (h2 : φa vc * φc va = 2) (h3 : φb vc * φc vb = 2)
    (h4 : (φa vb - φa vc * φc vb) * (φb va - φc va * φb vc) = 1) : p ≠ 3 := by
  have hq : (φa vb * φb vc * φc va) ^ 2 + ((-5 : ℤ) : ZMod p) * (φa vb * φb vc * φc va) +
      ((8 : ℤ) : ZMod p) = 0 := by
    push_cast
    linear_combination (φa vb * φb vc * φc va - 4) * h1 +
      (2 * (φa vb * φb vc * φc va) - 2 * (φa vb * φb va)) * h2 +
      (φa vb * φa vc * φb vc * φc va ^ 2 - φa vb * φa vc * φb va * φc va) * h3 +
      (-(φa vb * φb vc * φc va)) * h4
  exact ne_of_root_quadratic (-5) 8 hq (by decide)

omit [Module.Finite (ZMod p) U] in
theorem relabel_444 (hp : p ≠ 2) {va vb vc : U}
    {φa φb φc : Module.Dual (ZMod p) U} (hφa : φa va = 2) (hφb : φb vb = 2) (hφc : φc vc = 2)
    (hab : orderOf (Module.reflection hφa * Module.reflection hφb) = 4)
    (hac : orderOf (Module.reflection hφa * Module.reflection hφc) = 4)
    (hbc : orderOf (Module.reflection hφb * Module.reflection hφc) = 4)
    (hm : orderOf (Module.reflection hφc * Module.reflection hφa * Module.reflection hφc *
      Module.reflection hφb) = 3) :
    IsRefl p (Module.reflection hφa * Module.reflection hφc * Module.reflection hφa) ∧
    orderOf (Module.reflection hφb * Module.reflection hφa) = 4 ∧
    orderOf (Module.reflection hφb *
      (Module.reflection hφa * Module.reflection hφc * Module.reflection hφa)) = 3 ∧
    orderOf (Module.reflection hφa *
      (Module.reflection hφa * Module.reflection hφc * Module.reflection hφa)) = 4 ∧
    orderOf (Module.reflection hφa * Module.reflection hφc * Module.reflection hφa *
      Module.reflection hφb * (Module.reflection hφa * Module.reflection hφc *
        Module.reflection hφa) * Module.reflection hφa) = 3 := by
  have h1 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφa hφb hab
  have h2 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφa hφc hac
  have h3 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφb hφc hbc
  rw [reflection_conj_reflection hφc hφa] at hm
  have h4 := apply_mul_apply_eq_one_of_orderOf_eq_three hp _ hφb hm
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul] at h4
  have hp3 : p ≠ 3 := ne_three_of_444 h1 h2 h3 h4
  have ha2 : Module.reflection hφa * Module.reflection hφa = 1 :=
    mul_eq_one_iff_eq_inv.mpr (Module.reflection_inv hφa).symm
  have hb2 : Module.reflection hφb * Module.reflection hφb = 1 :=
    mul_eq_one_iff_eq_inv.mpr (Module.reflection_inv hφb).symm
  have hc2 : Module.reflection hφc * Module.reflection hφc = 1 :=
    mul_eq_one_iff_eq_inv.mpr (Module.reflection_inv hφc).symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [reflection_conj_reflection hφa hφc]; exact isRefl_reflection hp _
  · rw [show Module.reflection hφb * Module.reflection hφa =
        (Module.reflection hφa * Module.reflection hφb)⁻¹ by
      rw [mul_inv_rev, Module.reflection_inv, Module.reflection_inv], orderOf_inv, hab]
  · rw [reflection_conj_reflection hφa hφc]
    refine orderOf_reflection_mul_eq_three hp3 hφb _ ?_
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
    linear_combination h1 + (φa vb * φb va - 2) * h2 + (-(φa vc * φc va) + 1) * h3 + h4
  · rw [← mul_assoc, ← mul_assoc, ha2, one_mul]
    rw [show Module.reflection hφc * Module.reflection hφa =
        (Module.reflection hφa * Module.reflection hφc)⁻¹ by
      rw [mul_inv_rev, Module.reflection_inv, Module.reflection_inv], orderOf_inv, hac]
  · rw [orderOf_conj_relabel_444 ha2 hc2, reflection_conj_reflection hφa hφb,
      reflection_conj_reflection hφc hφa]
    refine orderOf_reflection_mul_eq_three hp3 _ _ ?_
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul, hφa]
    linear_combination (φa vb * φa vc * φb va * φc va - φa vb * φb vc * φc va -
      φa vc * φb va * φc vb) * h2 + h4

theorem closure_relabel_444 {G : Type*} [Group G] {a b c : G} (ha : a * a = 1) :
    Subgroup.closure ({b, a, a * c * a} : Set G) = Subgroup.closure {a, b, c} := by
  have hc : a * (a * c * a) * a = c := by
    rw [← mul_assoc, ← mul_assoc, ha, one_mul, mul_assoc, ha, mul_one]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact mul_mem (mul_mem (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp))
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | hxc
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · rw [hxc]
      have h : a * (a * c * a) * a ∈ Subgroup.closure ({b, a, a * c * a} : Set G) :=
        mul_mem (mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp))
      rw [hc] at h
      exact h

theorem card_eq_of_444 (hp : p ≠ 2) (hU : Module.finrank (ZMod p) U = 4)
    (ha : IsRefl p a) (hb : IsRefl p b) (hc : IsRefl p c) (hA : A = Subgroup.closure {a, b, c})
    (hAt : QTwoLin.TransvectionFree A)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace A) = 3)
    (hd : DMax p A 4) (hab : orderOf (a * b) = 4) (hac : orderOf (a * c) = 4)
    (hbc : orderOf (b * c) = 4) :
    orderOf (c * a * c * b) = 3 ∧ SplitSupport A 3 ∧ Nat.card A = 336 := by
  obtain ⟨va, φa, hφa, rfl⟩ := (isRefl_iff hp a).mp ha
  obtain ⟨vb, φb, hφb, rfl⟩ := (isRefl_iff hp b).mp hb
  obtain ⟨vc, φc, hφc, rfl⟩ := (isRefl_iff hp c).mp hc
  have hma : Module.reflection hφa ∈ A := by rw [hA]; exact Subgroup.subset_closure (by simp)
  have hmb : Module.reflection hφb ∈ A := by rw [hA]; exact Subgroup.subset_closure (by simp)
  have hmc : Module.reflection hφc ∈ A := by rw [hA]; exact Subgroup.subset_closure (by simp)
  have hx := hd.1 _ (A.mul_mem (A.mul_mem hmb hma) hmb) _ (A.mul_mem (A.mul_mem hmc hma) hmc)
    (by rw [reflection_conj_reflection hφb hφa]; exact isRefl_reflection hp _)
    (by rw [reflection_conj_reflection hφc hφa]; exact isRefl_reflection hp _)
  have hm3 : orderOf (Module.reflection hφc * Module.reflection hφa * Module.reflection hφc *
      Module.reflection hφb) = 3 := by
    obtain ⟨h2le, hle4⟩ := two_le_orderOf_cacb hp hU ha hb hc hA hdim hd
    have hn2 := orderOf_cacb_ne_two_of_444 hp hφa hφb hφc hab hac hbc
    have hn4 := orderOf_cacb_ne_four_of_444 hp hφa hφb hφc (by rw [← hA]; exact hdim) hab hac
      hbc hx
    omega
  obtain ⟨hc', hba, hbc', hac', hm'⟩ := relabel_444 hp hφa hφb hφc hab hac hbc hm3
  refine ⟨hm3, card_eq_of_434 hp hU hb ha hc' ?_ hAt hdim hd hba hbc' hac' hm'⟩
  rw [hA, closure_relabel_444 ha.1]

end RankThree

end CFSG.StandardType.ZS

end
