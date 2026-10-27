module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112K
import CFSG.Mathlib.Decide.Bounded

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggQ2wisRefl {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) :
    Matrix (Fin n) (Fin n) (ZMod 3) :=
  Matrix.of fun i k => (if i = k then 1 else 0) - if i = j then ((C j k : ℤ) : ZMod 3) else 0

private lemma ggQ2wis_mul_refl_apply {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (j : Fin n)
    (P : Matrix (Fin n) (Fin n) (ZMod 3)) (i b : Fin n) :
    (P * ggQ2wisRefl C j) i b = P i b - P i j * ((C j b : ℤ) : ZMod 3) := by
  simp only [Matrix.mul_apply, ggQ2wisRefl, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem ggQ2wis_inner_of_check {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (hdiag : ∀ j, ((C j j : ℤ) : ZMod 3) = 2) (R : Fin n → Matrix (Fin n) (Fin n) (ZMod 3))
    (hR : ∀ j, ggQ2wisRefl C j = R j) (L : List (Matrix (Fin n) (Fin n) (ZMod 3)))
    (ws : List (List (Fin n))) (hLW : L = ws.map fun w => (w.map R).prod) (hone : 1 ∈ L)
    (hmul : ∀ m ∈ L, ∀ j, m * R j ∈ L)
    (Good : (Fin n → ZMod 3) → Matrix (Fin n) (Fin n) (ZMod 3) → Prop)
    (hgood : ∀ m ∈ L, ∀ c : Fin n → ZMod 3, c ≠ 0 → m *ᵥ c = -c →
      (∀ k, ∃ t : ZMod 3, ∀ i, m i k - (1 : Matrix (Fin n) (Fin n) (ZMod 3)) i k = t * c i) →
      Good c m)
    (hcheck : ∀ P : Matrix (Fin n) (Fin n) (ZMod 3), P.det ≠ 0 →
      (∀ j, ∃ m ∈ L, Good (fun i => P i j) m ∧
        ∀ k, m *ᵥ (fun i => P i k) = (fun i => P i k) - ((C j k : ℤ) : ZMod 3) • fun i => P i j) →
      P ∈ L ∨ -P ∈ L) :
    GGQ2WeylInner n C := by
  classical
  intro U _ _ h hb hspan α hα T hT
  obtain ⟨B, hB⟩ : ∃ B : Basis (Fin n) (ZMod 3) U, ∀ i, B i = h i :=
    ⟨Basis.mk hb hspan.ge, Basis.mk_apply hb hspan.ge⟩
  have hBr : ∀ k, B.repr (h k) = Finsupp.single k 1 := fun k => by rw [← hB k, B.repr_self]
  let φ : (U ≃ₗ[ZMod 3] U) → Matrix (Fin n) (Fin n) (ZMod 3) :=
    fun g => LinearMap.toMatrix B B (g : U →ₗ[ZMod 3] U)
  have hφmul : ∀ g₁ g₂, φ (g₁ * g₂) = φ g₁ * φ g₂ := fun g₁ g₂ => by
    simp only [φ, LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul]
  have hφone : φ 1 = 1 := by
    have h1 : ((1 : U ≃ₗ[ZMod 3] U) : U →ₗ[ZMod 3] U) = 1 := LinearMap.ext fun _ => rfl
    simp only [φ, h1, LinearMap.toMatrix_one]
  have hφinj : Function.Injective φ := fun g₁ g₂ hg =>
    LinearEquiv.toLinearMap_injective ((LinearMap.toMatrix B B).injective hg)
  let s : Fin n → (U ≃ₗ[ZMod 3] U) := fun j =>
    Module.reflection (show α j (h j) = 2 by rw [hα, hdiag])
  have hs : ∀ j v, s j v = v - α j v • h j := fun j v => Module.reflection_apply v _
  have hsW : ∀ j, s j ∈ ggQ2WeylOf h α := fun j => Subgroup.subset_closure ⟨j, hs j⟩
  have hφs : ∀ j, φ (s j) = R j := by
    intro j
    rw [← hR j]
    ext i k
    simp only [φ, LinearMap.toMatrix_apply, LinearEquiv.coe_coe, hB, hs, map_sub, map_smul, hBr,
      hα, ggQ2wisRefl, Matrix.of_apply, Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply,
      Pi.smul_apply, Finsupp.single_apply, smul_eq_mul]
    rcases eq_or_ne i k with rfl | hik <;> rcases eq_or_ne i j with rfl | hij <;>
      simp [*, Ne.symm]
  have hgenset : ∀ t ∈ {t : U ≃ₗ[ZMod 3] U | ∃ j, ∀ v, t v = v - α j v • h j}, ∃ j, t = s j := by
    rintro t ⟨j, hj⟩
    exact ⟨j, LinearEquiv.ext fun v => by rw [hj, hs]⟩
  have hsinv : ∀ j, (s j)⁻¹ = s j := fun j =>
    inv_eq_of_mul_eq_one_right (LinearEquiv.ext fun v => Module.involutive_reflection _ v)
  have hWL : ∀ g ∈ ggQ2WeylOf h α, φ g ∈ L := by
    intro g hg
    change g ∈ Subgroup.closure _ at hg
    induction hg using Subgroup.closure_induction_right with
    | one => rw [hφone]; exact hone
    | mul_right x _ y hy ih =>
      obtain ⟨j, rfl⟩ := hgenset y hy
      rw [hφmul, hφs]
      exact hmul _ ih j
    | mul_inv_cancel x _ y hy ih =>
      obtain ⟨j, rfl⟩ := hgenset y hy
      rw [hsinv, hφmul, hφs]
      exact hmul _ ih j
  have hword : ∀ w : List (Fin n),
      (w.map s).prod ∈ ggQ2WeylOf h α ∧ φ (w.map s).prod = (w.map R).prod := by
    intro w
    induction w with
    | nil => exact ⟨one_mem _, hφone⟩
    | cons j w ih =>
      simp only [List.map_cons, List.prod_cons]
      exact ⟨mul_mem (hsW j) ih.1, by rw [hφmul, hφs, ih.2]⟩
  have hLW' : ∀ m ∈ L, ∃ g ∈ ggQ2WeylOf h α, φ g = m := by
    intro m hm
    rw [hLW, List.mem_map] at hm
    obtain ⟨w, -, rfl⟩ := hm
    exact ⟨_, (hword w).1, (hword w).2⟩
  set P := φ T
  set Q := φ T⁻¹
  have hPQ : P * Q = 1 := by rw [← hφmul, mul_inv_cancel, hφone]
  have hQP : Q * P = 1 := by rw [← hφmul, inv_mul_cancel, hφone]
  have hdet : P.det ≠ 0 := by
    have h1 : P.det * Q.det = 1 := by rw [← Matrix.det_mul, hPQ, Matrix.det_one]
    exact left_ne_zero_of_mul_eq_one h1
  have hnorm : ∀ j, ∃ m ∈ L, Good (fun i => P i j) m ∧
      ∀ k, m *ᵥ (fun i => P i k) = (fun i => P i k) - ((C j k : ℤ) : ZMod 3) • fun i => P i j := by
    intro j
    have hmem : T * s j * T⁻¹ ∈ ggQ2WeylOf h α :=
      (Subgroup.mem_normalizer_iff.mp hT (s j)).mp (hsW j)
    set m := φ (T * s j * T⁻¹) with hmdef
    have hm : m = P * R j * Q := by rw [hmdef, hφmul, hφmul, hφs]
    have hmP : m * P = P * R j := by rw [hm, Matrix.mul_assoc, hQP, Matrix.mul_one]
    have hpair : ∀ k, m *ᵥ (fun i => P i k) =
        (fun i => P i k) - ((C j k : ℤ) : ZMod 3) • fun i => P i j := by
      intro k
      funext i
      have h1 : (m *ᵥ fun i => P i k) i = (m * P) i k := rfl
      rw [h1, hmP, ← hR j, ggQ2wis_mul_refl_apply]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    refine ⟨m, hWL _ hmem, hgood m (hWL _ hmem) _ ?_ ?_ ?_, hpair⟩
    · intro hc
      have h1 := congrFun (congrFun hQP j) j
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
      simp [show ∀ i, P i j = 0 from fun i => congrFun hc i] at h1
    · rw [hpair j, hdiag]
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      ring
    · intro k
      refine ⟨-∑ b, ((C j b : ℤ) : ZMod 3) * Q b k, fun i => ?_⟩
      have h1 : ∑ b, P i b * Q b k = (1 : Matrix (Fin n) (Fin n) (ZMod 3)) i k := by
        rw [← hPQ, Matrix.mul_apply]
      rw [hm, Matrix.mul_apply]
      simp_rw [← hR j, ggQ2wis_mul_refl_apply, sub_mul, Finset.sum_sub_distrib, h1, mul_assoc,
        ← Finset.mul_sum]
      ring
  let ν : U ≃ₗ[ZMod 3] U := LinearEquiv.neg (ZMod 3)
  have hνφ : φ ν = -1 := by
    have h1 : (ν : U →ₗ[ZMod 3] U) = -1 := LinearMap.ext fun _ => rfl
    simp only [φ, h1, map_neg, LinearMap.toMatrix_one]
  have hνc : ∀ x : U ≃ₗ[ZMod 3] U, ν * x = x * ν := fun x => LinearEquiv.ext fun v => by
    change -(x v) = x (-v)
    rw [map_neg]
  rcases hcheck P hdet hnorm with hPL | hPL
  · obtain ⟨v, hvW, hv⟩ := hLW' P hPL
    have hTv : T = v := hφinj hv.symm
    exact ⟨T, hTv ▸ hvW, fun x _ => rfl⟩
  · obtain ⟨v, hvW, hv⟩ := hLW' (-P) hPL
    have hTv : T = ν * v := hφinj (by rw [hφmul, hνφ, hv, neg_one_mul, neg_neg])
    refine ⟨v, hvW, fun x _ => ?_⟩
    rw [hTv]
    calc ν * v * x * (ν * v)⁻¹ = ν * (v * x * v⁻¹) * ν⁻¹ := by group
      _ = v * x * v⁻¹ * ν * ν⁻¹ := by rw [hνc]
      _ = v * x * v⁻¹ := by group

private def ggQ2wisCols3 (c₀ c₁ c₂ : Fin 3 → ZMod 3) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  Matrix.of fun i j => ![c₀, c₁, c₂] j i

private lemma ggQ2wis_eq_cols3 (P : Matrix (Fin 3) (Fin 3) (ZMod 3)) :
    P = ggQ2wisCols3 (fun i => P i 0) (fun i => P i 1) (fun i => P i 2) := by
  ext i j
  fin_cases j <;> rfl

private def ggQ2wisR_A1 : Fin 1 → Matrix (Fin 1) (Fin 1) (ZMod 3) :=
  ![!![2]]

private def ggQ2wisL_A1 : List (Matrix (Fin 1) (Fin 1) (ZMod 3)) :=
  [!![1], !![2]]

private def ggQ2wisW_A1 : List (List (Fin 1)) :=
  [[], [0]]

private def ggQ2wisR_A2 : Fin 2 → Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  ![!![2, 1; 0, 1], !![1, 0; 1, 2]]

private def ggQ2wisL_A2 : List (Matrix (Fin 2) (Fin 2) (ZMod 3)) :=
  [!![1, 0; 0, 1], !![2, 1; 0, 1], !![1, 0; 1, 2], !![0, 2; 1, 2], !![2, 1; 2, 0], !![0, 2; 2, 0]]

private def ggQ2wisW_A2 : List (List (Fin 2)) :=
  [[], [0], [1], [0, 1], [1, 0], [0, 1, 0]]

private def ggQ2wisR_A3 : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  ![!![2, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 1, 2, 1; 0, 0, 1], !![1, 0, 0; 0, 1, 0; 0, 1, 2]]

private def ggQ2wisL_A3 : List (Matrix (Fin 3) (Fin 3) (ZMod 3)) :=
  [!![1, 0, 0; 0, 1, 0; 0, 0, 1], !![2, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 1, 2, 1; 0, 0, 1],
    !![1, 0, 0; 0, 1, 0; 0, 1, 2], !![0, 2, 1; 1, 2, 1; 0, 0, 1], !![2, 1, 0; 0, 1, 0; 0, 1, 2],
    !![2, 1, 0; 2, 0, 1; 0, 0, 1], !![1, 0, 0; 1, 0, 2; 0, 1, 2], !![1, 0, 0; 1, 2, 1; 1, 2, 0],
    !![0, 2, 1; 2, 0, 1; 0, 0, 1], !![0, 0, 2; 1, 0, 2; 0, 1, 2], !![0, 2, 1; 1, 2, 1; 1, 2, 0],
    !![2, 1, 0; 2, 1, 2; 0, 1, 2], !![1, 0, 0; 1, 0, 2; 1, 2, 0], !![2, 1, 0; 2, 0, 1; 2, 0, 0],
    !![0, 0, 2; 2, 1, 2; 0, 1, 2], !![0, 0, 2; 1, 0, 2; 1, 2, 0], !![0, 2, 1; 2, 0, 1; 2, 0, 0],
    !![0, 2, 1; 0, 2, 0; 1, 2, 0], !![2, 1, 0; 2, 1, 2; 2, 0, 0], !![0, 0, 2; 0, 2, 0; 1, 2, 0],
    !![0, 0, 2; 2, 1, 2; 2, 0, 0], !![0, 2, 1; 0, 2, 0; 2, 0, 0], !![0, 0, 2; 0, 2, 0; 2, 0, 0]]

private def ggQ2wisW_A3 : List (List (Fin 3)) :=
  [[], [0], [1], [2], [0, 1], [0, 2], [1, 0], [1, 2], [2, 1], [0, 1, 0], [0, 1, 2], [0, 2, 1],
    [1, 0, 2], [1, 2, 1], [2, 1, 0], [0, 1, 0, 2], [0, 1, 2, 1], [0, 2, 1, 0], [1, 0, 2, 1],
    [1, 2, 1, 0], [0, 1, 0, 2, 1], [0, 1, 2, 1, 0], [1, 0, 2, 1, 0], [0, 1, 0, 2, 1, 0]]

private def ggQ2wisT_A3 : List ((Fin 3 → ZMod 3) × Matrix (Fin 3) (Fin 3) (ZMod 3)) :=
  [(![0, 0, 1], !![1, 0, 0; 0, 1, 0; 0, 1, 2]), (![0, 0, 2], !![1, 0, 0; 0, 1, 0; 0, 1, 2]),
    (![0, 1, 0], !![1, 0, 0; 1, 2, 1; 0, 0, 1]), (![0, 1, 1], !![1, 0, 0; 1, 0, 2; 1, 2, 0]),
    (![0, 2, 0], !![1, 0, 0; 1, 2, 1; 0, 0, 1]), (![0, 2, 2], !![1, 0, 0; 1, 0, 2; 1, 2, 0]),
    (![1, 0, 0], !![2, 1, 0; 0, 1, 0; 0, 0, 1]), (![1, 1, 0], !![0, 2, 1; 2, 0, 1; 0, 0, 1]),
    (![1, 1, 1], !![0, 0, 2; 2, 1, 2; 2, 0, 0]), (![2, 0, 0], !![2, 1, 0; 0, 1, 0; 0, 0, 1]),
    (![2, 2, 0], !![0, 2, 1; 2, 0, 1; 0, 0, 1]), (![2, 2, 2], !![0, 0, 2; 2, 1, 2; 2, 0, 0])]

private lemma ggQ2wis_check2 (C : Matrix (Fin 2) (Fin 2) ℤ)
    (L : List (Matrix (Fin 2) (Fin 2) (ZMod 3)))
    (h : ∀ P : Matrix (Fin 2) (Fin 2) (ZMod 3), P 0 0 * P 1 1 - P 0 1 * P 1 0 ≠ 0 →
      (∀ j, ∃ m ∈ L, ∀ k, m *ᵥ (fun i => P i k) =
        (fun i => P i k) - ((C j k : ℤ) : ZMod 3) • fun i => P i j) →
      P ∈ L ∨ -P ∈ L) :
    ∀ P : Matrix (Fin 2) (Fin 2) (ZMod 3), P.det ≠ 0 →
      (∀ j, ∃ m ∈ L, (fun _ _ => True) (fun i => P i j) m ∧ ∀ k, m *ᵥ (fun i => P i k) =
        (fun i => P i k) - ((C j k : ℤ) : ZMod 3) • fun i => P i j) →
      P ∈ L ∨ -P ∈ L := by
  intro P hP hm
  rw [Matrix.det_fin_two] at hP
  exact h P hP fun j => (hm j).imp fun _ hm => ⟨hm.1, hm.2.2⟩

open scoped CFSG.Decide.Bounded in
theorem ggQ2WeylInner_A1 : GGQ2WeylInner 1 (CartanMatrix.A 1) := by
  refine ggQ2wis_inner_of_check _ (by decide +kernel) ggQ2wisR_A1 (by decide +kernel) ggQ2wisL_A1
    ggQ2wisW_A1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun _ _ => True)
    (fun _ _ _ _ _ _ => trivial) ?_
  intro P hP hm
  rw [Matrix.det_fin_one] at hP
  revert P
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem ggQ2WeylInner_A2 : GGQ2WeylInner 2 (CartanMatrix.A 2) :=
  ggQ2wis_inner_of_check _ (by decide +kernel) ggQ2wisR_A2 (by decide +kernel) ggQ2wisL_A2
    ggQ2wisW_A2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun _ _ => True)
    (fun _ _ _ _ _ _ => trivial) (ggQ2wis_check2 _ _ (by decide +kernel))

open scoped CFSG.Decide.Bounded in
private lemma ggQ2wis_triples_A3 : ∀ p₀ ∈ ggQ2wisT_A3, ∀ p₁ ∈ ggQ2wisT_A3,
    p₀.2 *ᵥ p₁.1 = p₁.1 - ((CartanMatrix.A 3 0 1 : ℤ) : ZMod 3) • p₀.1 →
    p₁.2 *ᵥ p₀.1 = p₀.1 - ((CartanMatrix.A 3 1 0 : ℤ) : ZMod 3) • p₁.1 → ∀ p₂ ∈ ggQ2wisT_A3,
    p₀.2 *ᵥ p₂.1 = p₂.1 - ((CartanMatrix.A 3 0 2 : ℤ) : ZMod 3) • p₀.1 →
    p₂.2 *ᵥ p₀.1 = p₀.1 - ((CartanMatrix.A 3 2 0 : ℤ) : ZMod 3) • p₂.1 →
    p₁.2 *ᵥ p₂.1 = p₂.1 - ((CartanMatrix.A 3 1 2 : ℤ) : ZMod 3) • p₁.1 →
    p₂.2 *ᵥ p₁.1 = p₁.1 - ((CartanMatrix.A 3 2 1 : ℤ) : ZMod 3) • p₂.1 →
    (ggQ2wisCols3 p₀.1 p₁.1 p₂.1).det ≠ 0 →
    ggQ2wisCols3 p₀.1 p₁.1 p₂.1 ∈ ggQ2wisL_A3 ∨ -ggQ2wisCols3 p₀.1 p₁.1 p₂.1 ∈ ggQ2wisL_A3 := by
  simp only [Matrix.det_fin_three]
  decide +kernel

open scoped CFSG.Decide.Bounded in
private lemma ggQ2wis_good_A3 : ∀ m ∈ ggQ2wisL_A3, ∀ c : Fin 3 → ZMod 3, c ≠ 0 → m *ᵥ c = -c →
    (∀ k, ∃ t : ZMod 3, ∀ i, m i k - (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) i k = t * c i) →
    (c, m) ∈ ggQ2wisT_A3 := by
  decide +kernel

private lemma ggQ2wis_diag_A3 : ∀ j, ((CartanMatrix.A 3 j j : ℤ) : ZMod 3) = 2 := by
  decide +kernel

private lemma ggQ2wis_refl_A3 : ∀ j, ggQ2wisRefl (CartanMatrix.A 3) j = ggQ2wisR_A3 j := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private lemma ggQ2wis_words_A3 :
    ggQ2wisL_A3 = ggQ2wisW_A3.map fun w => (w.map ggQ2wisR_A3).prod := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private lemma ggQ2wis_one_A3 : (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ ggQ2wisL_A3 := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private lemma ggQ2wis_mul_A3 : ∀ m ∈ ggQ2wisL_A3, ∀ j, m * ggQ2wisR_A3 j ∈ ggQ2wisL_A3 := by
  decide +kernel

theorem ggQ2WeylInner_A3 : GGQ2WeylInner 3 (CartanMatrix.A 3) := by
  refine ggQ2wis_inner_of_check _ ggQ2wis_diag_A3 ggQ2wisR_A3 ggQ2wis_refl_A3 ggQ2wisL_A3
    ggQ2wisW_A3 ggQ2wis_words_A3 ggQ2wis_one_A3 ggQ2wis_mul_A3
    (fun c m => (c, m) ∈ ggQ2wisT_A3) ggQ2wis_good_A3 ?_
  intro P hdet hP
  obtain ⟨m₀, -, h₀, e₀⟩ := hP 0
  obtain ⟨m₁, -, h₁, e₁⟩ := hP 1
  obtain ⟨m₂, -, h₂, e₂⟩ := hP 2
  have key : (ggQ2wisCols3 (fun i => P i 0) (fun i => P i 1) (fun i => P i 2)).det ≠ 0 →
      ggQ2wisCols3 (fun i => P i 0) (fun i => P i 1) (fun i => P i 2) ∈ ggQ2wisL_A3 ∨
        -ggQ2wisCols3 (fun i => P i 0) (fun i => P i 1) (fun i => P i 2) ∈ ggQ2wisL_A3 :=
    ggQ2wis_triples_A3 (_, m₀) h₀ (_, m₁) h₁ (e₀ 1) (e₁ 0) (_, m₂) h₂ (e₀ 2) (e₂ 0) (e₁ 2) (e₂ 1)
  rw [← ggQ2wis_eq_cols3 P] at key
  exact key hdet

end CFSG.StandardType

end
