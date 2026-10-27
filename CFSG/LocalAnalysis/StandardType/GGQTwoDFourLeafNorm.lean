module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTBWNormAmbInner
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLineStab
public import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1
public import CFSG.LocalAnalysis.StandardType.GGQTwoAjSetting
import CFSG.LocalAnalysis.StandardType.GGQTwoWeylInnerSmall
import CFSG.Mathlib.Decide.Bounded

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGQ2WeylDiag (n : ℕ) (C : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ {U : Type} [AddCommGroup U] [Module (ZMod 3) U] (h : Fin n → U),
    LinearIndependent (ZMod 3) h → Submodule.span (ZMod 3) (Set.range h) = ⊤ →
    ∀ (α : Fin n → Module.Dual (ZMod 3) U), (∀ i j, α i (h j) = ((C i j : ℤ) : ZMod 3)) →
    ∀ T : U ≃ₗ[ZMod 3] U,
      T ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U)) →
      ∃ w ∈ ggQ2WeylOf h α, ∃ ε : ZMod 3, ε ≠ 0 ∧ ∃ π : Equiv.Perm (Fin n),
        (∀ i j, C (π i) (π j) = C i j) ∧ ∀ i, T (h i) = ε • w (h (π i))

private lemma ggQ2d4_mul_refl_apply {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (j : Fin n)
    (P : Matrix (Fin n) (Fin n) (ZMod 3)) (i b : Fin n) :
    (P * ggQ2wisRefl C j) i b = P i b - P i j * ((C j b : ℤ) : ZMod 3) := by
  simp only [Matrix.mul_apply, ggQ2wisRefl, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem ggQ2d4_diag_of_check {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (hdiag : ∀ j, ((C j j : ℤ) : ZMod 3) = 2)
    (R : Fin n → Matrix (Fin n) (Fin n) (ZMod 3)) (hR : ∀ j, ggQ2wisRefl C j = R j)
    (Inv : Matrix (Fin n) (Fin n) (ZMod 3) → Prop) (hone : Inv 1)
    (hmul : ∀ m, Inv m → ∀ j, Inv (m * R j))
    (Good : (Fin n → ZMod 3) → Matrix (Fin n) (Fin n) (ZMod 3) → Prop)
    (hgood : ∀ m, Inv m → ∀ c : Fin n → ZMod 3, c ≠ 0 → m *ᵥ c = -c →
      (∀ k, ∃ t : ZMod 3, ∀ i, m i k - (1 : Matrix (Fin n) (Fin n) (ZMod 3)) i k = t * c i) →
      Good c m)
    (j₀ : Fin n)
    (hnz : ∀ c m, Good c m → ∃ u : List (Fin n), (u.map R).prod *ᵥ c = Pi.single j₀ 1)
    (Γ : List (Equiv.Perm (Fin n))) (hΓ : ∀ π ∈ Γ, ∀ i j, C (π i) (π j) = C i j)
    (L₁ : List (Matrix (Fin n) (Fin n) (ZMod 3) × List (Fin n)))
    (hL₁ : ∀ q ∈ L₁, (q.2.map R).prod = q.1)
    (hcheck : ∀ P : Matrix (Fin n) (Fin n) (ZMod 3), (fun i => P i j₀) = Pi.single j₀ 1 →
      (∀ j, ∃ m, Good (fun i => P i j) m ∧
        ∀ k, m *ᵥ (fun i => P i k) = (fun i => P i k) - ((C j k : ℤ) : ZMod 3) • fun i => P i j) →
      ∃ q ∈ L₁, ∃ π ∈ Γ, ∀ i k, P k i = q.1 k (π i)) :
    GGQ2WeylDiag n C := by
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
  have hφapp : ∀ (g : U ≃ₗ[ZMod 3] U) (i k : Fin n), B.repr (g (h i)) k = φ g k i :=
    fun g i k => by simp only [φ, LinearMap.toMatrix_apply, LinearEquiv.coe_coe, hB]
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
  have hWI : ∀ g ∈ ggQ2WeylOf h α, Inv (φ g) := by
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
  have hnormT : ∀ T' ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U)), ∀ j,
      ∃ m, Good (fun i => φ T' i j) m ∧ ∀ k, m *ᵥ (fun i => φ T' i k) =
        (fun i => φ T' i k) - ((C j k : ℤ) : ZMod 3) • fun i => φ T' i j := by
    intro T' hT' j
    have hPQ : φ T' * φ T'⁻¹ = 1 := by rw [← hφmul, mul_inv_cancel, hφone]
    have hQP : φ T'⁻¹ * φ T' = 1 := by rw [← hφmul, inv_mul_cancel, hφone]
    have hmem : T' * s j * T'⁻¹ ∈ ggQ2WeylOf h α :=
      (Subgroup.mem_normalizer_iff.mp hT' (s j)).mp (hsW j)
    have hm : φ (T' * s j * T'⁻¹) = φ T' * R j * φ T'⁻¹ := by rw [hφmul, hφmul, hφs]
    have hmP : φ (T' * s j * T'⁻¹) * φ T' = φ T' * R j := by
      rw [hm, Matrix.mul_assoc, hQP, Matrix.mul_one]
    have hpair : ∀ k, φ (T' * s j * T'⁻¹) *ᵥ (fun i => φ T' i k) =
        (fun i => φ T' i k) - ((C j k : ℤ) : ZMod 3) • fun i => φ T' i j := by
      intro k
      funext i
      have h1 : (φ (T' * s j * T'⁻¹) *ᵥ fun i => φ T' i k) i =
          (φ (T' * s j * T'⁻¹) * φ T') i k := rfl
      rw [h1, hmP, ← hR j, ggQ2d4_mul_refl_apply]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    refine ⟨_, hgood _ (hWI _ hmem) _ ?_ ?_ ?_, hpair⟩
    · intro hc
      have h1 := congrFun (congrFun hQP j) j
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
      simp [show ∀ i, φ T' i j = 0 from fun i => congrFun hc i] at h1
    · rw [hpair j, hdiag]
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      ring
    · intro k
      refine ⟨-∑ b, ((C j b : ℤ) : ZMod 3) * φ T'⁻¹ b k, fun i => ?_⟩
      have h1 : ∑ b, φ T' i b * φ T'⁻¹ b k = (1 : Matrix (Fin n) (Fin n) (ZMod 3)) i k := by
        rw [← hPQ, Matrix.mul_apply]
      rw [hm, Matrix.mul_apply]
      simp_rw [← hR j, ggQ2d4_mul_refl_apply, sub_mul, Finset.sum_sub_distrib, h1, mul_assoc,
        ← Finset.mul_sum]
      ring
  obtain ⟨m₀, hg₀, -⟩ := hnormT T hT j₀
  obtain ⟨u, hu⟩ := hnz _ _ hg₀
  have hV := (hword u).1
  have hVT : (u.map s).prod * T ∈
      Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U)) :=
    mul_mem (Subgroup.le_normalizer hV) hT
  have hcol : (fun i => φ ((u.map s).prod * T) i j₀) = Pi.single j₀ 1 := by
    rw [← hu, hφmul, (hword u).2]
    rfl
  obtain ⟨q, hq, π, hπ, hc⟩ := hcheck _ hcol (hnormT _ hVT)
  refine ⟨((u.map s).prod)⁻¹ * (q.2.map s).prod, mul_mem (inv_mem hV) (hword q.2).1, 1,
    one_ne_zero, π, hΓ π hπ, fun i => ?_⟩
  have h1 : ((u.map s).prod * T) (h i) = (q.2.map s).prod (h (π i)) :=
    B.repr.injective (Finsupp.ext fun k => by
      rw [hφapp, hφapp, (hword q.2).2, hL₁ q hq]
      exact hc i k)
  calc T (h i) = (((u.map s).prod)⁻¹ * ((u.map s).prod * T)) (h i) := by
        rw [inv_mul_cancel_left]
    _ = (1 : ZMod 3) • (((u.map s).prod)⁻¹ * (q.2.map s).prod) (h (π i)) := by
        rw [one_smul, LinearEquiv.mul_apply, h1, LinearEquiv.mul_apply]

private def ggQ2d4Cols (c₀ c₁ c₂ c₃ : Fin 4 → ZMod 3) : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  Matrix.of fun i j => ![c₀, c₁, c₂, c₃] j i

private lemma ggQ2d4_eq_cols (P : Matrix (Fin 4) (Fin 4) (ZMod 3)) :
    P = ggQ2d4Cols (fun i => P i 0) (fun i => P i 1) (fun i => P i 2) (fun i => P i 3) := by
  ext i j
  fin_cases j <;> rfl

private def ggQ2d4M (c : ℕ) : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  Matrix.of fun i j => ((c / 3 ^ (4 * (i : ℕ) + j) % 3 : ℕ) : ZMod 3)

private def ggQ2d4V (c : ℕ) : Fin 4 → ZMod 3 := fun i => ((c / 3 ^ (i : ℕ) % 3 : ℕ) : ZMod 3)

private def ggQ2d4R : Fin 4 → Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  ![!![2, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 1, 2, 1, 1; 0, 0, 1, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, 2, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 1, 0, 2]]

private def ggQ2d4G : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![2, 2, 0, 0; 2, 2, 2, 2; 0, 2, 2, 0; 0, 2, 0, 2]

private def ggQ2d4X₁ : List (Fin 4 → ZMod 3) := [36, 42, 44, 45, 63, 72, 75, 76].map ggQ2d4V

private def ggQ2d4X₂ : List (Fin 4 → ZMod 3) := [28, 29, 34, 52, 55, 56, 59, 68].map ggQ2d4V

private abbrev ggQ2d4Xp (m : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Prop :=
  (∀ x ∈ ggQ2d4X₁, m *ᵥ x ∈ ggQ2d4X₁) ∧ ∀ x ∈ ggQ2d4X₂, m *ᵥ x ∈ ggQ2d4X₂

private abbrev ggQ2d4Inv (m : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Prop :=
  mᵀ * ggQ2d4G * m = ggQ2d4G ∧ ggQ2d4Xp m

private def ggQ2d4Rt : List ((Fin 4 → ZMod 3) × Matrix (Fin 4) (Fin 4) (ZMod 3) × List (Fin 4)) :=
  ([(1, 14408204, [0, 1]), (2, 14408204, [0, 1, 0]), (3, 14411440, []), (4, 14411076, [0]),
    (6, 14411440, [1]), (8, 14411076, [1, 0]), (9, 14486932, [2, 1]), (12, 14575708, [2]),
    (13, 14543271, [0, 2]), (18, 14486932, [1, 2, 1]), (24, 14575708, [1, 2]),
    (26, 14543271, [1, 0, 2]), (27, 30351430, [3, 1]), (30, 8567290, [3]), (31, 5910471, [0, 3]),
    (39, 10464391, [2, 3]), (40, 12616797, [0, 2, 3]), (43, 17636461, [0, 2, 3, 1]),
    (54, 30351430, [1, 3, 1]), (60, 8567290, [1, 3]), (62, 5910471, [1, 0, 3]),
    (77, 17636461, [1, 0, 2, 3, 1]), (78, 10464391, [1, 2, 3]), (80, 12616797, [1, 0, 2, 3])] :
    List (ℕ × ℕ × List (Fin 4))).map
    fun t => (ggQ2d4V t.1, ggQ2d4M t.2.1, t.2.2)

private abbrev ggQ2d4Good (c : Fin 4 → ZMod 3) (m : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Prop :=
  ∃ t ∈ ggQ2d4Rt, t.1 = c ∧ t.2.1 = m

private def ggQ2d4Mf (c : Fin 4 → ZMod 3) : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  Matrix.of fun i k => (1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) i k +
    c i * ((c ⬝ᵥ ggQ2d4G *ᵥ c) * (ggQ2d4G *ᵥ c) k)

private def ggQ2d4S : List (Matrix (Fin 4) (Fin 4) (ZMod 3) × List (Fin 4)) :=
  ([(14408200, []), (14543271, [0, 1, 2, 1, 0]), (5910471, [0, 1, 3, 1, 0]),
    (10464391, [2, 1, 3, 1, 2]), (6036446, [0, 1, 2, 3, 1, 0]), (10216494, [2, 1, 0, 3, 1, 2]),
    (29061162, [3, 1, 0, 2, 1, 3]), (28822151, [0, 1, 2, 1, 0, 3, 1, 0, 2, 1, 3])] :
    List (ℕ × List (Fin 4))).map fun t => (ggQ2d4M t.1, t.2)

private def ggQ2d4Γ : List (Equiv.Perm (Fin 4)) :=
  [1, Equiv.swap 2 3, Equiv.swap 0 2, Equiv.swap 0 3, Equiv.swap 0 2 * Equiv.swap 0 3,
    Equiv.swap 0 3 * Equiv.swap 0 2]

private def ggQ2d4Rel (j k : Fin 4)
    (pj pk : (Fin 4 → ZMod 3) × Matrix (Fin 4) (Fin 4) (ZMod 3) × List (Fin 4)) : Prop :=
  pj.2.1 *ᵥ pk.1 = pk.1 - ((CartanMatrix.D 4 j k : ℤ) : ZMod 3) • pj.1

open scoped CFSG.Decide.Bounded in
private lemma ggQ2d4_small : (∀ j, ((CartanMatrix.D 4 j j : ℤ) : ZMod 3) = 2) ∧
    (∀ j, ggQ2wisRefl (CartanMatrix.D 4) j = ggQ2d4R j) ∧
    (∀ j, (ggQ2d4R j)ᵀ * ggQ2d4G * ggQ2d4R j = ggQ2d4G) ∧ (∀ j, ggQ2d4Xp (ggQ2d4R j)) ∧
    ggQ2d4V 3 = Pi.single 1 1 ∧
    ∀ π ∈ ggQ2d4Γ, (CartanMatrix.D 4).submatrix π π = CartanMatrix.D 4 := by
  decide +kernel

private lemma ggQ2d4_gram (j : Fin 4) : (ggQ2d4R j)ᵀ * ggQ2d4G * ggQ2d4R j = ggQ2d4G :=
  ggQ2d4_small.2.2.1 j

private lemma ggQ2d4_xpR (j : Fin 4) : ggQ2d4Xp (ggQ2d4R j) := ggQ2d4_small.2.2.2.1 j

private lemma ggQ2d4_e1 : ggQ2d4V 3 = Pi.single 1 1 := ggQ2d4_small.2.2.2.2.1

private lemma ggQ2d4_Γ :
    ∀ π ∈ ggQ2d4Γ, ∀ i j, CartanMatrix.D 4 (π i) (π j) = CartanMatrix.D 4 i j :=
  fun π hπ i j => congrFun (congrFun (ggQ2d4_small.2.2.2.2.2 π hπ) i) j

private lemma ggQ2d4_inv_one : ggQ2d4Inv 1 :=
  ⟨by rw [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one],
    fun x hx => by rwa [Matrix.one_mulVec], fun x hx => by rwa [Matrix.one_mulVec]⟩

private lemma ggQ2d4_inv_mul (m : Matrix (Fin 4) (Fin 4) (ZMod 3)) (hm : ggQ2d4Inv m) (j : Fin 4) :
    ggQ2d4Inv (m * ggQ2d4R j) := by
  refine ⟨?_, fun x hx => ?_, fun x hx => ?_⟩
  · calc (m * ggQ2d4R j)ᵀ * ggQ2d4G * (m * ggQ2d4R j)
        = (ggQ2d4R j)ᵀ * (mᵀ * ggQ2d4G * m) * ggQ2d4R j := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = ggQ2d4G := by rw [hm.1, ggQ2d4_gram j]
  · rw [← Matrix.mulVec_mulVec]
    exact hm.2.1 _ ((ggQ2d4_xpR j).1 x hx)
  · rw [← Matrix.mulVec_mulVec]
    exact hm.2.2 _ ((ggQ2d4_xpR j).2 x hx)

open scoped CFSG.Decide.Bounded in
private lemma ggQ2d4_fin : ∀ c : Fin 4 → ZMod 3, c ≠ 0 → ggQ2d4G *ᵥ c ≠ 0 ∧
    (c ⬝ᵥ ggQ2d4G *ᵥ c ≠ 0 → ggQ2d4Good c (ggQ2d4Mf c) ∨ ¬ ggQ2d4Xp (ggQ2d4Mf c)) := by
  decide +kernel

private lemma ggQ2d4_good (m : Matrix (Fin 4) (Fin 4) (ZMod 3)) (hm : ggQ2d4Inv m)
    (c : Fin 4 → ZMod 3) (hc : c ≠ 0) (hmc : m *ᵥ c = -c)
    (hrk : ∀ k, ∃ t : ZMod 3, ∀ i, m i k - (1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) i k = t * c i) :
    ggQ2d4Good c m := by
  choose f hf using hrk
  have hm1 : m = 1 + vecMulVec c f := by
    ext i k
    rw [Matrix.add_apply, vecMulVec_apply]
    linear_combination hf k i
  have hg : mᵀ *ᵥ (ggQ2d4G *ᵥ c) = -(ggQ2d4G *ᵥ c) := by
    have h := congrArg (fun M => M *ᵥ c) hm.1
    simp only [← Matrix.mulVec_mulVec, hmc, Matrix.mulVec_neg] at h
    exact neg_eq_iff_eq_neg.mp h
  have h3 : (3 : ZMod 3) = 0 := rfl
  have hβ : ∀ k, (c ⬝ᵥ ggQ2d4G *ᵥ c) * f k = (ggQ2d4G *ᵥ c) k := by
    intro k
    have h := congrFun hg k
    rw [Matrix.mulVec_transpose, hm1, Matrix.vecMul_add, Matrix.vecMul_one,
      Matrix.vecMul_vecMulVec] at h
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at h
    rw [dotProduct_comm]
    linear_combination h - (ggQ2d4G *ᵥ c) k * h3
  obtain ⟨hG, hfin⟩ := ggQ2d4_fin c hc
  have hβ0 : c ⬝ᵥ ggQ2d4G *ᵥ c ≠ 0 := by
    intro h0
    refine hG (funext fun k => ?_)
    rw [← hβ k, h0, zero_mul, Pi.zero_apply]
  have hsq : ∀ b : ZMod 3, b ≠ 0 → b * b = 1 := by decide
  have hmf : m = ggQ2d4Mf c := by
    rw [hm1]
    ext i k
    rw [Matrix.add_apply, vecMulVec_apply, ggQ2d4Mf, Matrix.of_apply, ← hβ k,
      ← mul_assoc (c ⬝ᵥ ggQ2d4G *ᵥ c), hsq _ hβ0, one_mul]
  rw [hmf] at hm ⊢
  exact (hfin hβ0).resolve_right (not_not.mpr hm.2)

private lemma ggQ2d4_prod_mulVec {n : ℕ} (R : Fin n → Matrix (Fin n) (Fin n) (ZMod 3))
    (u : List (Fin n)) (c : Fin n → ZMod 3) :
    (u.map R).prod *ᵥ c = u.foldr (fun j v => R j *ᵥ v) c := by
  induction u with
  | nil => simp
  | cons j u ih => simp only [List.map_cons, List.prod_cons, List.foldr_cons, ← ih,
      Matrix.mulVec_mulVec]

open scoped CFSG.Decide.Bounded in
private lemma ggQ2d4_nz :
    ∀ t ∈ ggQ2d4Rt, t.2.2.foldr (fun j v => ggQ2d4R j *ᵥ v) t.1 = ggQ2d4V 3 := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
private lemma ggQ2d4_Scols : ∀ q ∈ ggQ2d4S, ∀ j : Fin 4,
    q.2.foldr (fun j v => ggQ2d4R j *ᵥ v) (Pi.single j 1) = fun i => q.1 i j := by
  decide +kernel

private lemma ggQ2d4_S : ∀ q ∈ ggQ2d4S, (q.2.map ggQ2d4R).prod = q.1 := by
  intro q hq
  ext i j
  have h := congrFun (ggQ2d4_Scols q hq j) i
  rw [← ggQ2d4_prod_mulVec, Matrix.mulVec_single_one] at h
  exact h

set_option synthInstance.maxSize 1024 in
open scoped CFSG.Decide.Bounded in
private lemma ggQ2d4_quads : ∀ p₁ ∈ ggQ2d4Rt, p₁.1 = ggQ2d4V 3 → ∀ p₀ ∈ ggQ2d4Rt,
    ggQ2d4Rel 0 1 p₀ p₁ → ggQ2d4Rel 1 0 p₁ p₀ → ∀ p₂ ∈ ggQ2d4Rt,
    ggQ2d4Rel 0 2 p₀ p₂ → ggQ2d4Rel 2 0 p₂ p₀ → ggQ2d4Rel 1 2 p₁ p₂ → ggQ2d4Rel 2 1 p₂ p₁ →
    ∀ p₃ ∈ ggQ2d4Rt,
    ggQ2d4Rel 0 3 p₀ p₃ → ggQ2d4Rel 3 0 p₃ p₀ → ggQ2d4Rel 1 3 p₁ p₃ → ggQ2d4Rel 3 1 p₃ p₁ →
    ggQ2d4Rel 2 3 p₂ p₃ → ggQ2d4Rel 3 2 p₃ p₂ →
    ∃ q ∈ ggQ2d4S, ∃ π ∈ ggQ2d4Γ, ∀ i k, ggQ2d4Cols p₀.1 p₁.1 p₂.1 p₃.1 k i = q.1 k (π i) := by
  unfold ggQ2d4Rel
  decide +kernel

theorem ggQ2WeylDiag_D4 : GGQ2WeylDiag 4 (CartanMatrix.D 4) := by
  refine ggQ2d4_diag_of_check _ ggQ2d4_small.1 ggQ2d4R ggQ2d4_small.2.1 ggQ2d4Inv ggQ2d4_inv_one
    ggQ2d4_inv_mul ggQ2d4Good ggQ2d4_good 1 ?_ ggQ2d4Γ ggQ2d4_Γ ggQ2d4S ?_ ?_
  · rintro c m ⟨t, ht, rfl, -⟩
    exact ⟨t.2.2, by rw [ggQ2d4_prod_mulVec, ggQ2d4_nz t ht, ggQ2d4_e1]⟩
  · exact ggQ2d4_S
  · intro P hP1 hP
    obtain ⟨m₀, ⟨t₀, h₀, c₀, rfl⟩, e₀⟩ := hP 0
    obtain ⟨m₁, ⟨t₁, h₁, c₁, rfl⟩, e₁⟩ := hP 1
    obtain ⟨m₂, ⟨t₂, h₂, c₂, rfl⟩, e₂⟩ := hP 2
    obtain ⟨m₃, ⟨t₃, h₃, c₃, rfl⟩, e₃⟩ := hP 3
    have hr : ∀ (j k : Fin 4)
        (tj tk : (Fin 4 → ZMod 3) × Matrix (Fin 4) (Fin 4) (ZMod 3) × List (Fin 4)),
        tj.1 = (fun i => P i j) → tk.1 = (fun i => P i k) →
        tj.2.1 *ᵥ (fun i => P i k) =
          (fun i => P i k) - ((CartanMatrix.D 4 j k : ℤ) : ZMod 3) • (fun i => P i j) →
        ggQ2d4Rel j k tj tk := by
      intro j k tj tk hj hk h
      unfold ggQ2d4Rel
      rw [hj, hk]
      exact h
    obtain ⟨q, hq, π, hπ, hc⟩ := ggQ2d4_quads t₁ h₁ (by rw [c₁, hP1, ggQ2d4_e1]) t₀ h₀
      (hr 0 1 _ _ c₀ c₁ (e₀ 1)) (hr 1 0 _ _ c₁ c₀ (e₁ 0)) t₂ h₂ (hr 0 2 _ _ c₀ c₂ (e₀ 2))
      (hr 2 0 _ _ c₂ c₀ (e₂ 0)) (hr 1 2 _ _ c₁ c₂ (e₁ 2)) (hr 2 1 _ _ c₂ c₁ (e₂ 1)) t₃ h₃
      (hr 0 3 _ _ c₀ c₃ (e₀ 3)) (hr 3 0 _ _ c₃ c₀ (e₃ 0)) (hr 1 3 _ _ c₁ c₃ (e₁ 3))
      (hr 3 1 _ _ c₃ c₁ (e₃ 1)) (hr 2 3 _ _ c₂ c₃ (e₂ 3)) (hr 3 2 _ _ c₃ c₂ (e₃ 2))
    refine ⟨q, hq, π, hπ, fun i k => ?_⟩
    rw [c₀, c₁, c₂, c₃, ← ggQ2d4_eq_cols P] at hc
    exact hc i k

theorem GGQ2Lin.diag_of_transport (D : GGQ2Lin 3) {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (e : Fin n ≃ {k // k ≠ D.a}) (hC : ∀ i j, D.cartan (e i) (e j) = C i j)
    (hind : LinearIndependent (ZMod 3) (fun i : {k // k ≠ D.a} => D.coroot i))
    (hW : GGQ2WeylDiag n C) (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∃ (π : {k // k ≠ D.a} ≃ {k // k ≠ D.a}) (c : ZMod 3), c ≠ 0 ∧
      (∀ i j : {k // k ≠ D.a}, D.cartan (π i) (π j) = D.cartan i j) ∧
      ∃ w ∈ D.parab {k | k ≠ D.a}, ∀ i : {k // k ≠ D.a},
        T (D.coroot i) = c • w (D.coroot (π i)) := by
  classical
  let h' : Fin n → ggQ2xKDt_U0 D := ggQ2xKDt_h' D e
  let α' : Fin n → Module.Dual (ZMod 3) (ggQ2xKDt_U0 D) := ggQ2xKDt_α' D e
  have hP' : ∀ i j, α' i (h' j) = ((C i j : ℤ) : ZMod 3) := fun i j =>
    ggQ2xKDt_α'_h' D e C hC i j
  have hli' : LinearIndependent (ZMod 3) h' := ggQ2xKDt_h'_li D e hind
  have hsp' : Submodule.span (ZMod 3) (Set.range h') = ⊤ := ggQ2xKDt_h'_span D e hind
  have hrange : (ggQ2xKDt_res D).range = ggQ2WeylOf h' α' :=
    ggQ2xKDt_range_res D e
  let T' : ggQ2xKDt_U0 D ≃ₗ[ZMod 3] ggQ2xKDt_U0 D := ggQ2xKDt_T' D T hT
  have hT'norm : T' ∈ Subgroup.normalizer (ggQ2WeylOf h' α') := by
    rw [← hrange, Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rcases MonoidHom.mem_range.mp hy with ⟨g, hg⟩
      refine MonoidHom.mem_range.mpr ⟨⟨T * g.1 * T⁻¹,
        (Subgroup.mem_normalizer_iff.mp hT g.1).mp g.2⟩, ?_⟩
      rw [← hg]
      exact (ggQ2xKDt_T'_conj D T hT g).symm
    · intro hy
      rcases MonoidHom.mem_range.mp hy with ⟨g, hg⟩
      refine MonoidHom.mem_range.mpr ⟨⟨T⁻¹ * g.1 * T,
        (Subgroup.mem_normalizer_iff''.mp hT g.1).mp g.2⟩, ?_⟩
      have h1 : T'⁻¹ * ggQ2xKDt_res D g * T' = y := by
        rw [hg]; group
      rw [← h1]
      exact (ggQ2xKDt_T'_inv_conj D T hT g).symm
  obtain ⟨w', hw'mem, ε, hε, π₀, hπ₀C, hπ₀⟩ := hW h' hli' hsp' α' hP' T' hT'norm
  have hw'range : w' ∈ (ggQ2xKDt_res D).range := by rwa [hrange]
  obtain ⟨w, hw_eq⟩ := MonoidHom.mem_range.mp hw'range
  have hlift : ∀ v : ggQ2xKDt_U0 D, ((w' v : ggQ2xKDt_U0 D) : D.V) = w.1 (v : D.V) := by
    intro v
    rw [← hw_eq]
    exact ggQ2xKDt_res_apply D w (v : D.V) v.2
  have hT'val : ∀ v : ggQ2xKDt_U0 D, ((T' v : ggQ2xKDt_U0 D) : D.V) = T (v : D.V) := fun v =>
    ggQ2xKDt_T'_apply D T hT v
  refine ⟨e.symm.trans (π₀.trans e), ε, hε, ?_, w.1, w.2, ?_⟩
  · intro i j
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [hC (π₀ a) (π₀ b), hC a b]
    exact hπ₀C a b
  · intro i
    obtain ⟨a, rfl⟩ := e.surjective i
    simpa [h', ggQ2xKDt_h', hT'val, hlift, Equiv.trans_apply] using
      congrArg (fun z : ggQ2xKDt_U0 D => (z : D.V)) (hπ₀ a)

theorem ggQ2_tbwNormAmb_of_dFourLeaf (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3) [Fact p.Prime]
    {y : G} {K : Subgroup G} (M : GGQTwoAmbModel p Bs x y L (L ⊔ K))
    (hind : LinearIndependent (ZMod p) (fun i : {k // k ≠ M.a} => M.coroot i))
    (f : Fin 4 ≃ {k // k ≠ M.a}) (hf : ∀ i j, M.cartan (f i) (f j) = CartanMatrix.D 4 i j)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hφx : ggLin (p := p) M.model φ M.xV ∈ Submodule.span (ZMod p) {M.xV}) :
    ∃ (π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}) (c : ZMod p), c ≠ 0 ∧
      (∀ i j : {k // k ≠ M.a}, M.cartan (π i) (π j) = M.cartan i j) ∧
      ∃ w ∈ M.toLin.parab {k | k ≠ M.a}, ∀ i : {k // k ≠ M.a},
        ggLin (p := p) M.model φ (M.coroot i) = c • w (M.coroot (π i)) := by
  subst hp
  classical
  have hH : GGCorFiveTwentyHyp 3 B Bs x L D J := hS.1
  have hAJS : ggAutomizer J Bs ≠ ⊥ := ggQ2_ajOfSetting hP h5 hS
  obtain ⟨c₀, hc₀⟩ := Submodule.mem_span_singleton.mp hφx
  have hφxg : φ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) :=
    ggQ2tbi_mem_zpowers_of_smul M.model φ M.hx c₀ hc₀.symm
  have hφN : φ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) :=
    ggQ2_lineStab_normalizes_L hLB hP hH hAJS M.hx hφ hφxg
  have hTnorm : (ggLin (p := 3) M.model φ : M.V ≃ₗ[ZMod 3] M.V) ∈ Subgroup.normalizer
      (M.parabL {k | k ≠ M.a} : Set (M.V ≃ₗ[ZMod 3] M.V)) := by
    rw [M.parabL_L]
    exact Subgroup.le_normalizer_map (ggLin (p := 3) M.model) (Subgroup.mem_map.mpr ⟨φ, hφN, rfl⟩)
  exact GGQ2Lin.diag_of_transport M.toLin (CartanMatrix.D 4) f hf hind ggQ2WeylDiag_D4 _ hTnorm

theorem ggQ2_tbwNormNbrAmb_of_dFourLeaf (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hI1 : GGQTwoI1 Bs D J) [Fact p.Prime] {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (M : GGQTwoAmbModel p Bs y x K (L ⊔ K))
    (hind : LinearIndependent (ZMod p) (fun i : {k // k ≠ M.a} => M.coroot i))
    (f : Fin 4 ≃ {k // k ≠ M.a}) (hf : ∀ i j, M.cartan (f i) (f j) = CartanMatrix.D 4 i j)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hφy : ggLin (p := p) M.model φ M.xV ∈ Submodule.span (ZMod p) {M.xV}) :
    ∃ (π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}) (c : ZMod p), c ≠ 0 ∧
      (∀ i j : {k // k ≠ M.a}, M.cartan (π i) (π j) = M.cartan i j) ∧
      ∃ w ∈ M.toLin.parab {k | k ≠ M.a}, ∀ i : {k // k ≠ M.a},
        ggLin (p := p) M.model φ (M.coroot i) = c • w (M.coroot (π i)) := by
  subst hp
  classical
  have hH : GGCorFiveTwentyHyp 3 B Bs x L D J := hS.1
  have hAJS : ggAutomizer J Bs ≠ ⊥ := ggQ2_ajOfSetting hP h5 hS
  have hK1 : GGQTwoK1 3 B Bs x D J := ggQ2_K1_of_I1 hLB hP hH hI1
  obtain ⟨c₀, hc₀⟩ := Submodule.mem_span_singleton.mp hφy
  have hφyg : φ ⟨y, M.hx⟩ ∈ Subgroup.zpowers (⟨y, M.hx⟩ : ↥Bs) :=
    ggQ2tbi_mem_zpowers_of_smul M.model φ M.hx c₀ hc₀.symm
  have hφN : φ ∈ Subgroup.normalizer (ggAutomizer K Bs : Set (MulAut ↥Bs)) :=
    ggQ2_nbrLineStab_normalizes hLB hP hH hAJS hK1 hnb M.hx hφ hφyg
  have hTnorm : (ggLin (p := 3) M.model φ : M.V ≃ₗ[ZMod 3] M.V) ∈ Subgroup.normalizer
      (M.parabL {k | k ≠ M.a} : Set (M.V ≃ₗ[ZMod 3] M.V)) := by
    rw [M.parabL_L]
    exact Subgroup.le_normalizer_map (ggLin (p := 3) M.model) (Subgroup.mem_map.mpr ⟨φ, hφN, rfl⟩)
  exact GGQ2Lin.diag_of_transport M.toLin (CartanMatrix.D 4) f hf hind ggQ2WeylDiag_D4 _ hTnorm

end CFSG.StandardType

end
