module

public import CFSG.RankThree.Chevalley.SteinbergBUF4A2SL3Restriction
public import CFSG.RankThree.Chevalley.SteinbergBUF4B2QuarticDescent
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix SteinbergBN

section Coboundary

variable {L : Type} [Field L]

theorem exists_sl3_coboundary (σ : L ≃+* L) {N : Matrix (Fin 3) (Fin 3) L} (hN : N.det = 1)
    {v : Fin 3 → L} (hv : Function.Injective v)
    (hNv : N * (vandermonde v).map σ = vandermonde v) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 3) L, N * (A : Matrix (Fin 3) (Fin 3) L).map σ = A := by
  set P := vandermonde v with hP
  have hδ : P.det ≠ 0 := det_vandermonde_ne_zero_iff.2 hv
  have hσδ : σ P.det = P.det := by
    have h := congrArg Matrix.det hNv
    rw [Matrix.det_mul, hN, one_mul] at h
    rw [RingEquiv.map_det, RingEquiv.mapMatrix_apply]
    exact h
  have hdet : (P * diagonal ![P.det⁻¹, 1, 1]).det = 1 := by
    rw [Matrix.det_mul, det_diagonal, Fin.prod_univ_three]
    simp [hδ]
  refine ⟨⟨P * diagonal ![P.det⁻¹, 1, 1], hdet⟩, ?_⟩
  change N * (P * diagonal ![P.det⁻¹, 1, 1]).map σ = P * diagonal ![P.det⁻¹, 1, 1]
  rw [Matrix.map_mul, ← Matrix.mul_assoc, hNv, Matrix.diagonal_map (map_zero σ)]
  congr 2
  funext k
  fin_cases k <;> simp [map_inv₀, hσδ]

variable {K : Type} [Field K] [Fintype K] [Algebra K L]

theorem exists_map_algebraMap_of_map_eq [Finite L] (σ : L ≃+* L)
    (hσ : ∀ b, σ b = b ^ Fintype.card K) {B : Matrix (Fin 3) (Fin 3) L} (hB : B.map σ = B) :
    ∃ B₀ : Matrix (Fin 3) (Fin 3) K, B₀.map (algebraMap K L) = B := by
  have h : ∀ a b, ∃ t : K, algebraMap K L t = B a b := fun a b => by
    have e := congrFun (congrFun hB a) b
    rw [Matrix.map_apply, hσ] at e
    exact EvenCubic.mem_range_of_pow_card_eq e
  choose B₀ hB₀ using h
  exact ⟨Matrix.of B₀, by ext a b; exact hB₀ a b⟩

end Coboundary

section Weyl

variable {M : Type} [Field M]

theorem weylElt_one_mem_pair (κ : F4A2Kind) :
    weylElt Tag.F4 M κ.i 1 ∈ subsystemGroup Tag.F4 M {κ.i, κ.j} ∧
      weylElt Tag.F4 M κ.j 1 ∈ subsystemGroup Tag.F4 M {κ.i, κ.j} :=
  ⟨weylElt_mem_subsystemGroup (left_mem_pair κ.i κ.j) 1,
    weylElt_mem_subsystemGroup (right_mem_pair κ.i κ.j) 1⟩

theorem f4A2_weyl_left (c : M) :
    (1 + single 0 1 c : Matrix (Fin 3) (Fin 3) M) * (1 + single 1 0 (-c⁻¹)) *
        (1 + single 0 1 c) = !![1 - c * c⁻¹, c * (2 - c * c⁻¹), 0; -c⁻¹, 1 - c * c⁻¹, 0;
          0, 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;>
    ring

theorem f4A2_weyl_right (c : M) :
    (1 + single 1 2 c : Matrix (Fin 3) (Fin 3) M) * (1 + single 2 1 (-c⁻¹)) *
        (1 + single 1 2 c) = !![1, 0, 0; 0, 1 - c * c⁻¹, c * (2 - c * c⁻¹);
          0, -c⁻¹, 1 - c * c⁻¹] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;>
    ring

variable [CharP M 2]

theorem f4A2Equiv_weylElt_one (κ : F4A2Kind) :
    ((f4A2Equiv M κ ⟨_, (weylElt_one_mem_pair (M := M) κ).1⟩ :
        Matrix.SpecialLinearGroup (Fin 3) M) : Matrix (Fin 3) (Fin 3) M) =
        !![0, 1, 0; 1, 0, 0; 0, 0, 1] ∧
      ((f4A2Equiv M κ ⟨_, (weylElt_one_mem_pair (M := M) κ).2⟩ :
        Matrix.SpecialLinearGroup (Fin 3) M) : Matrix (Fin 3) (Fin 3) M) =
        !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by
  obtain ⟨hgen, -⟩ := F4_native_long_and_short_A2_faithful_SL3_all_characteristics M κ
  have h2 : (2 : M) = 0 := CharTwo.two_eq_zero
  have hl := left_mem_pair κ.i κ.j
  have hr := right_mem_pair κ.i κ.j
  have el : (⟨_, (weylElt_one_mem_pair (M := M) κ).1⟩ : subsystemGroup Tag.F4 M {κ.i, κ.j}) =
      qx hl 1 * qy hl (-1) * qx hl 1 := by
    apply Subtype.ext
    simp [Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  have er : (⟨_, (weylElt_one_mem_pair (M := M) κ).2⟩ : subsystemGroup Tag.F4 M {κ.i, κ.j}) =
      qx hr 1 * qy hr (-1) * qx hr 1 := by
    apply Subtype.ext
    simp [Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  constructor
  · rw [el, map_mul, map_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, (hgen 1).1, (hgen (-1)).2.1]
    have e := f4A2_weyl_left (M := M) 1
    rw [inv_one] at e
    rw [e]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [h2, CharTwo.neg_eq]
  · rw [er, map_mul, map_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, (hgen 1).2.2.1, (hgen (-1)).2.2.2]
    have e := f4A2_weyl_right (M := M) 1
    rw [inv_one] at e
    rw [e]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [h2, CharTwo.neg_eq]

end Weyl

section Commutant

variable {M : Type} [Field M]

theorem subsystemTorus_le_torusGroup' {J : Set (Fin Tag.F4.rank)} :
    subsystemTorus Tag.F4 M J ≤ torusGroup Tag.F4 M := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, -, t, rfl⟩
  exact Subgroup.subset_closure ⟨(i, t), rfl⟩

theorem torusRootChar_eq_one_of_commute_pinnedX_one {h : ModGL Tag.F4 M}
    (hh : h ∈ torusGroup Tag.F4 M) {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot Tag.F4 α)
    (hc : h * pinnedX Tag.F4 M α 1 = pinnedX Tag.F4 M α 1 * h) : torusRootChar h α = 1 := by
  have e := conj_pinnedX_of_mem_torusGroup hh hα 1
  rw [hc, mul_inv_cancel_right, mul_one] at e
  exact (pinnedX_injective Tag.F4 M α e).symm

theorem mem_range_scalar_of_commute_elementary {X : Matrix (Fin 3) (Fin 3) M}
    (h01 : X * (1 + single 0 1 1) = (1 + single 0 1 1) * X)
    (h10 : X * (1 + single 1 0 1) = (1 + single 1 0 1) * X)
    (h12 : X * (1 + single 1 2 1) = (1 + single 1 2 1) * X)
    (h21 : X * (1 + single 2 1 1) = (1 + single 2 1 1) * X) :
    X ∈ Set.range (scalar (Fin 3)) := by
  have hc : ∀ {a b : Fin 3}, X * (1 + single a b 1) = (1 + single a b 1) * X →
      Commute (single a b (1 : M)) X := fun h => by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact (add_left_cancel h).symm
  have c01 := hc h01
  have c10 := hc h10
  have c12 := hc h12
  have c21 := hc h21
  have e02 : (single 0 2 1 : Matrix (Fin 3) (Fin 3) M) =
      (single 0 1 1 : Matrix (Fin 3) (Fin 3) M) * single 1 2 1 := by
    rw [Matrix.single_mul_single_same, one_mul]
  have e20 : (single 2 0 1 : Matrix (Fin 3) (Fin 3) M) =
      (single 2 1 1 : Matrix (Fin 3) (Fin 3) M) * single 1 0 1 := by
    rw [Matrix.single_mul_single_same, one_mul]
  have c02 : Commute (single 0 2 (1 : M)) X := by
    rw [e02]
    exact c01.mul_left c12
  have c20 : Commute (single 2 0 (1 : M)) X := by
    rw [e20]
    exact c21.mul_left c10
  refine Matrix.mem_range_scalar_of_commute_single fun a b hab => ?_
  fin_cases a <;> fin_cases b
  all_goals first
    | exact absurd rfl hab
    | assumption

end Commutant

section Cubic

variable {K : Type} [Field K] [Fintype K] {K₃ : Type} [Field K₃] [Algebra K K₃]
  [FiniteDimensional K K₃]

omit [FiniteDimensional K K₃] in
theorem card_cubic (h3 : Module.finrank K K₃ = 3) [Fintype K₃] :
    Fintype.card K₃ = Fintype.card K ^ 3 := by
  rw [Module.card_eq_pow_finrank (K := K) (V := K₃), h3]

theorem cubic_sigma_three (h3 : Module.finrank K K₃ = 3) (σ : K₃ ≃+* K₃)
    (hσ : ∀ b, σ b = b ^ Fintype.card K) (b : K₃) : σ (σ (σ b)) = b := by
  have : Finite K₃ := Module.finite_of_finite K
  have := Fintype.ofFinite K₃
  rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul, show Fintype.card K * (Fintype.card K * Fintype.card K) =
    Fintype.card K₃ by rw [card_cubic h3]; ring, FiniteField.pow_card]

theorem exists_sigma_ne (h3 : Module.finrank K K₃ = 3) (σ : K₃ ≃+* K₃)
    (hσ : ∀ b, σ b = b ^ Fintype.card K) : ∃ ξ : K₃, σ ξ ≠ ξ := by
  have : Finite K₃ := Module.finite_of_finite K
  have := Fintype.ofFinite K₃
  by_contra h
  push Not at h
  have hle := Fintype.card_le_of_surjective (algebraMap K K₃) fun b =>
    EvenCubic.mem_range_of_pow_card_eq (by rw [← hσ, h b])
  rw [card_cubic h3] at hle
  have h2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have : Fintype.card K < Fintype.card K ^ 3 := by
    calc Fintype.card K = Fintype.card K ^ 1 := (pow_one _).symm
      _ < Fintype.card K ^ 3 := Nat.pow_lt_pow_right h2 (by norm_num)
  omega

end Cubic

section Vandermonde

variable {L : Type} [Field L]

theorem injective_conjugates (σ : L ≃+* L) (hσ3 : ∀ b, σ (σ (σ b)) = b) {ξ : L}
    (hξ : σ ξ ≠ ξ) :
    Function.Injective ![ξ, σ ξ, σ (σ ξ)] ∧ Function.Injective ![ξ, σ (σ ξ), σ ξ] := by
  have h1 : ξ ≠ σ ξ := fun h => hξ h.symm
  have h2 : ξ ≠ σ (σ ξ) := fun h => by
    have e := congrArg σ h
    rw [hσ3] at e
    exact hξ e
  constructor
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp at h ⊢ <;>
      first
      | exact h1 h
      | exact h1 h.symm
      | exact h2 h
      | exact h2 h.symm
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp at h ⊢ <;>
      first
      | exact h1 h
      | exact h1 h.symm
      | exact h2 h
      | exact h2 h.symm

theorem perm_mul_vandermonde_map (σ : L ≃+* L) (π : Fin 3 → Fin 3)
    {N : Matrix (Fin 3) (Fin 3) L} (hN : ∀ a b, N a b = if b = π a then 1 else 0)
    {v : Fin 3 → L} (hv : ∀ a, σ (v (π a)) = v a) :
    N * (vandermonde v).map σ = vandermonde v := by
  ext a c
  rw [Matrix.mul_apply]
  simp only [hN, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Matrix.map_apply, vandermonde_apply, vandermonde_apply, map_pow, hv]

end Vandermonde

section Word

variable {M : Type} [Field M]

theorem weyl_word_mem_pair (κ : F4A2Kind) (ε : ℤ) :
    (weylElt Tag.F4 M κ.i 1 * weylElt Tag.F4 M κ.j 1) ^ ε ∈ subsystemGroup Tag.F4 M {κ.i, κ.j} :=
  zpow_mem (mul_mem (weylElt_one_mem_pair κ).1 (weylElt_one_mem_pair κ).2) ε

variable [CharP M 2]

theorem f4A2Equiv_weyl_word (κ : F4A2Kind) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∃ π : Fin 3 → Fin 3, (π = ![2, 0, 1] ∨ π = ![1, 2, 0]) ∧ ∀ a b,
      ((f4A2Equiv M κ ⟨_, weyl_word_mem_pair (M := M) κ ε⟩ :
        Matrix.SpecialLinearGroup (Fin 3) M) : Matrix (Fin 3) (Fin 3) M) a b =
          if b = π a then 1 else 0 := by
  obtain ⟨Wi, Wj⟩ := f4A2Equiv_weylElt_one (M := M) κ
  have hprod : (⟨_, weyl_word_mem_pair (M := M) κ ε⟩ : subsystemGroup Tag.F4 M {κ.i, κ.j}) =
      (⟨_, (weylElt_one_mem_pair (M := M) κ).1⟩ * ⟨_, (weylElt_one_mem_pair (M := M) κ).2⟩) ^
        ε := Subtype.ext (by simp)
  rw [hprod, map_zpow, map_mul]
  rcases hε with rfl | rfl
  · refine ⟨![2, 0, 1], Or.inl rfl, fun a b => ?_⟩
    rw [zpow_one, Matrix.SpecialLinearGroup.coe_mul, Wi, Wj]
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · refine ⟨![1, 2, 0], Or.inr rfl, fun a b => ?_⟩
    rw [_root_.zpow_neg_one, Classical2.coe_inv_eq_nonsing_inv,
      Matrix.SpecialLinearGroup.coe_mul, Wi, Wj]
    have hinv : (!![0, 1, 0; 1, 0, 0; 0, 0, 1] * !![1, 0, 0; 0, 0, 1; 0, 1, 0] :
        Matrix (Fin 3) (Fin 3) M)⁻¹ = !![0, 1, 0; 0, 0, 1; 1, 0, 0] := by
      refine Matrix.inv_eq_left_inv ?_
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    rw [hinv]
    fin_cases a <;> fin_cases b <;> simp

end Word

section Descent

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {K₃ : Type} [Field K₃] [Algebra K K₃]
  [FiniteDimensional K K₃]

theorem exists_f4A2_cubic_coboundary (h3 : Module.finrank K K₃ = 3) (σ : K₃ ≃+* K₃)
    (hσ : ∀ b, σ b = b ^ Fintype.card K) (κ : F4A2Kind) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 3) K₃,
      have : CharP K₃ 2 := charP_of_injective_algebraMap (algebraMap K K₃).injective 2
      ((f4A2Equiv K₃ κ ⟨_, weyl_word_mem_pair (M := K₃) κ ε⟩ :
        Matrix.SpecialLinearGroup (Fin 3) K₃) : Matrix (Fin 3) (Fin 3) K₃) *
          (A : Matrix (Fin 3) (Fin 3) K₃).map σ = A := by
  have : CharP K₃ 2 := charP_of_injective_algebraMap (algebraMap K K₃).injective 2
  have hσ3 := cubic_sigma_three h3 σ hσ
  obtain ⟨ξ, hξ⟩ := exists_sigma_ne h3 σ hσ
  obtain ⟨hv1, hv2⟩ := injective_conjugates σ hσ3 hξ
  obtain ⟨π, hπ, hN⟩ := f4A2Equiv_weyl_word (M := K₃) κ hε
  have hdet := Matrix.SpecialLinearGroup.det_coe
    (f4A2Equiv K₃ κ ⟨_, weyl_word_mem_pair (M := K₃) κ ε⟩)
  rcases hπ with rfl | rfl
  · exact exists_sl3_coboundary σ hdet hv1 (perm_mul_vandermonde_map σ _ hN fun a => by
      fin_cases a <;> simp [hσ3])
  · exact exists_sl3_coboundary σ hdet hv2 (perm_mul_vandermonde_map σ _ hN fun a => by
      fin_cases a <;> simp [hσ3])

theorem f4A2Equiv_baseChange_entrywise (σ : K₃ ≃+* K₃) (κ : F4A2Kind) [CharP K₃ 2]
    (x : subsystemGroup Tag.F4 K₃ {κ.i, κ.j}) :
    ((f4A2Equiv K₃ κ ⟨_, baseChangeGL_mem_subsystemGroup σ.toRingHom x.2⟩ :
      Matrix.SpecialLinearGroup (Fin 3) K₃) : Matrix (Fin 3) (Fin 3) K₃) =
      ((f4A2Equiv K₃ κ x : Matrix.SpecialLinearGroup (Fin 3) K₃) :
        Matrix (Fin 3) (Fin 3) K₃).map σ := by
  rw [coe_f4A2Equiv_eq_blockMat, coe_f4A2Equiv_eq_blockMat]
  exact blockMat_baseChangeGL σ.toRingHom (isRoot_f4A2Root κ) _

omit [Fintype K] [FiniteDimensional K K₃] in
theorem f4A2Equiv_baseChange_algebraMap (κ : F4A2Kind) [CharP K₃ 2]
    (y : subsystemGroup Tag.F4 K {κ.i, κ.j}) :
    ((f4A2Equiv K₃ κ ⟨_, baseChangeGL_mem_subsystemGroup (algebraMap K K₃) y.2⟩ :
      Matrix.SpecialLinearGroup (Fin 3) K₃) : Matrix (Fin 3) (Fin 3) K₃) =
      ((f4A2Equiv K κ y : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).map (algebraMap K K₃) := by
  rw [coe_f4A2Equiv_eq_blockMat, coe_f4A2Equiv_eq_blockMat]
  exact blockMat_baseChangeGL _ (isRoot_f4A2Root κ) _

theorem f4A2_entrywise_fixed_iff (σ : K₃ ≃+* K₃)
    (hσ : ∀ b, σ b = b ^ Fintype.card K) (κ : F4A2Kind) {g : ModGL Tag.F4 K₃}
    (hg : g ∈ subsystemGroup Tag.F4 K₃ {κ.i, κ.j}) :
    Units.map (entrywiseHom σ.toRingHom) g = g ↔
      ∃ y ∈ subsystemGroup Tag.F4 K {κ.i, κ.j}, g = baseChangeGL (algebraMap K K₃) y := by
  have : CharP K₃ 2 := charP_of_injective_algebraMap (algebraMap K K₃).injective 2
  have : Finite K₃ := Module.finite_of_finite K
  have hσK : ∀ t : K, σ (algebraMap K K₃ t) = algebraMap K K₃ t := fun t => by
    rw [hσ, ← map_pow, FiniteField.pow_card]
  constructor
  · intro hfix
    have hB : ((f4A2Equiv K₃ κ ⟨g, hg⟩ : Matrix.SpecialLinearGroup (Fin 3) K₃) :
        Matrix (Fin 3) (Fin 3) K₃).map σ =
          (f4A2Equiv K₃ κ ⟨g, hg⟩ : Matrix (Fin 3) (Fin 3) K₃) := by
      rw [← f4A2Equiv_baseChange_entrywise σ κ ⟨g, hg⟩]
      congr 3
    obtain ⟨B₀, hB₀⟩ := exists_map_algebraMap_of_map_eq σ hσ hB
    have hdet : B₀.det = 1 := by
      apply (algebraMap K K₃).injective
      rw [map_one, RingHom.map_det, RingHom.mapMatrix_apply, hB₀,
        Matrix.SpecialLinearGroup.det_coe]
    obtain ⟨y, hy⟩ := (f4A2Equiv K κ).surjective ⟨B₀, hdet⟩
    refine ⟨y, y.2, ?_⟩
    have e : (⟨_, baseChangeGL_mem_subsystemGroup (algebraMap K K₃) y.2⟩ :
        subsystemGroup Tag.F4 K₃ {κ.i, κ.j}) = ⟨g, hg⟩ := by
      apply (f4A2Equiv K₃ κ).injective
      apply Subtype.ext
      rw [f4A2Equiv_baseChange_algebraMap, hy]
      exact hB₀
    exact (congrArg Subtype.val e).symm
  · rintro ⟨y, hy, rfl⟩
    have e : (⟨_, baseChangeGL_mem_subsystemGroup σ.toRingHom hg⟩ :
        subsystemGroup Tag.F4 K₃ {κ.i, κ.j}) = ⟨_, hg⟩ := by
      apply (f4A2Equiv K₃ κ).injective
      apply Subtype.ext
      rw [f4A2Equiv_baseChange_entrywise σ κ ⟨_, hg⟩]
      have e2 := f4A2Equiv_baseChange_algebraMap (K₃ := K₃) κ ⟨y, hy⟩
      change ((f4A2Equiv K₃ κ ⟨_, hg⟩ : Matrix.SpecialLinearGroup (Fin 3) K₃) :
        Matrix (Fin 3) (Fin 3) K₃) = _ at e2
      rw [e2, Matrix.map_map]
      congr 1
      funext t
      exact hσK t
    exact congrArg Subtype.val e

theorem f4A2_cubic_descent (σ : K₃ ≃+* K₃)
    (hσ : ∀ b, σ b = b ^ Fintype.card K) (κ : F4A2Kind) {m : ModGL Tag.F4 K₃}
    (hm : m ∈ subsystemGroup Tag.F4 K₃ {κ.i, κ.j}) (a : subsystemGroup Tag.F4 K₃ {κ.i, κ.j})
    (ha : have : CharP K₃ 2 := charP_of_injective_algebraMap (algebraMap K K₃).injective 2
      ((f4A2Equiv K₃ κ ⟨m, hm⟩ : Matrix.SpecialLinearGroup (Fin 3) K₃) :
        Matrix (Fin 3) (Fin 3) K₃) *
          ((f4A2Equiv K₃ κ a : Matrix.SpecialLinearGroup (Fin 3) K₃) :
            Matrix (Fin 3) (Fin 3) K₃).map σ = (f4A2Equiv K₃ κ a : Matrix (Fin 3) (Fin 3) K₃)) :
    m = (a : ModGL Tag.F4 K₃) * (Units.map (entrywiseHom σ.toRingHom) a)⁻¹ ∧
      ∀ g ∈ subsystemGroup Tag.F4 K₃ {κ.i, κ.j},
        (m * Units.map (entrywiseHom σ.toRingHom) g * m⁻¹ = g ↔
          ∃ y ∈ subsystemGroup Tag.F4 K {κ.i, κ.j},
            g = (a : ModGL Tag.F4 K₃) * baseChangeGL (algebraMap K K₃) y *
              (a : ModGL Tag.F4 K₃)⁻¹) := by
  have : CharP K₃ 2 := charP_of_injective_algebraMap (algebraMap K K₃).injective 2
  have hAσ : IsUnit (((f4A2Equiv K₃ κ a : Matrix.SpecialLinearGroup (Fin 3) K₃) :
      Matrix (Fin 3) (Fin 3) K₃).map σ).det := by
    rw [← RingEquiv.mapMatrix_apply, ← RingEquiv.map_det, Matrix.SpecialLinearGroup.det_coe,
      map_one]
    exact isUnit_one
  have hmeq : m = (a : ModGL Tag.F4 K₃) * (Units.map (entrywiseHom σ.toRingHom) a)⁻¹ := by
    have e : (⟨m, hm⟩ : subsystemGroup Tag.F4 K₃ {κ.i, κ.j}) =
        a * ⟨_, baseChangeGL_mem_subsystemGroup σ.toRingHom a.2⟩⁻¹ := by
      apply (f4A2Equiv K₃ κ).injective
      apply Subtype.ext
      rw [map_mul, map_inv, Matrix.SpecialLinearGroup.coe_mul, Classical2.coe_inv_eq_nonsing_inv,
        f4A2Equiv_baseChange_entrywise σ κ a]
      calc ((f4A2Equiv K₃ κ ⟨m, hm⟩ : Matrix.SpecialLinearGroup (Fin 3) K₃) :
            Matrix (Fin 3) (Fin 3) K₃) =
          ((f4A2Equiv K₃ κ ⟨m, hm⟩ : Matrix.SpecialLinearGroup (Fin 3) K₃) :
            Matrix (Fin 3) (Fin 3) K₃) *
            (((f4A2Equiv K₃ κ a : Matrix.SpecialLinearGroup (Fin 3) K₃) :
              Matrix (Fin 3) (Fin 3) K₃).map σ *
              (((f4A2Equiv K₃ κ a : Matrix.SpecialLinearGroup (Fin 3) K₃) :
                Matrix (Fin 3) (Fin 3) K₃).map σ)⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ hAσ, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, ha]
    have := congrArg Subtype.val e
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    exact this
  refine ⟨hmeq, fun g hg => ?_⟩
  have hg' : (a : ModGL Tag.F4 K₃)⁻¹ * g * (a : ModGL Tag.F4 K₃) ∈
      subsystemGroup Tag.F4 K₃ {κ.i, κ.j} :=
    mul_mem (mul_mem (inv_mem a.2) hg) a.2
  have hθa : m * Units.map (entrywiseHom σ.toRingHom) g * m⁻¹ = (a : ModGL Tag.F4 K₃) *
      Units.map (entrywiseHom σ.toRingHom) ((a : ModGL Tag.F4 K₃)⁻¹ * g * (a : ModGL Tag.F4 K₃)) *
        (a : ModGL Tag.F4 K₃)⁻¹ := by
    rw [hmeq, map_mul, map_mul, map_inv]
    group
  rw [hθa]
  constructor
  · intro h
    have h' : Units.map (entrywiseHom σ.toRingHom)
        ((a : ModGL Tag.F4 K₃)⁻¹ * g * (a : ModGL Tag.F4 K₃)) =
        (a : ModGL Tag.F4 K₃)⁻¹ * g * (a : ModGL Tag.F4 K₃) := by
      calc _ = (a : ModGL Tag.F4 K₃)⁻¹ * ((a : ModGL Tag.F4 K₃) *
            Units.map (entrywiseHom σ.toRingHom)
              ((a : ModGL Tag.F4 K₃)⁻¹ * g * (a : ModGL Tag.F4 K₃)) *
              (a : ModGL Tag.F4 K₃)⁻¹) * a := by group
        _ = _ := by rw [h]
    obtain ⟨y, hy, hye⟩ := (f4A2_entrywise_fixed_iff σ hσ κ hg').1 h'
    refine ⟨y, hy, ?_⟩
    rw [← hye]
    group
  · rintro ⟨y, hy, rfl⟩
    have e : (a : ModGL Tag.F4 K₃)⁻¹ *
        ((a : ModGL Tag.F4 K₃) * baseChangeGL (algebraMap K K₃) y * (a : ModGL Tag.F4 K₃)⁻¹) *
          (a : ModGL Tag.F4 K₃) = baseChangeGL (algebraMap K K₃) y := by group
    rw [e, (f4A2_entrywise_fixed_iff σ hσ κ (baseChangeGL_mem_subsystemGroup _ hy)).2
      ⟨y, hy, rfl⟩]

end Descent

section Centralizer

variable {K : Type} [Field K] {K₃ : Type} [Field K₃] [Algebra K K₃]

theorem matrix_mul_comm_of_eq_conj {X R : Matrix (Fin 3) (Fin 3) K₃} (hX : IsUnit X.det)
    (h : R = X * R * X⁻¹) : X * R = R * X := by
  calc X * R = X * R * X⁻¹ * X := by
        rw [Matrix.mul_assoc (X * R), Matrix.nonsing_inv_mul _ hX, Matrix.mul_one]
    _ = R * X := by rw [← h]

theorem mem_char_of_commute_f4A2 (κ : F4A2Kind) {h : ModGL Tag.F4 K₃}
    (hh : h ∈ torusGroup Tag.F4 K₃) {v : ModGL Tag.F4 K₃}
    (hv : v ∈ subsystemGroup Tag.F4 K₃ {κ.i, κ.j})
    (hc : ∀ z ∈ subsystemGroup Tag.F4 K {κ.i, κ.j},
      h * v * baseChangeGL (algebraMap K K₃) z = baseChangeGL (algebraMap K K₃) z * (h * v)) :
    h * v ∈ torusGroup Tag.F4 K₃ ∧ torusRootChar (h * v) (Pi.single κ.i 1) = 1 ∧
      torusRootChar (h * v) (Pi.single κ.j 1) = 1 := by
  have hl := left_mem_pair κ.i κ.j
  have hr := right_mem_pair κ.i κ.j
  obtain ⟨hN, hconj⟩ := f4A2Equiv_torus_mul_conj κ hh hv
  set D : Matrix (Fin 3) (Fin 3) K₃ :=
    diagonal ![torusRootChar h (Pi.single κ.i 1) * torusRootChar h (Pi.single κ.j 1),
      torusRootChar h (Pi.single κ.j 1), 1] with hD
  set X := D * ((f4A2Equiv K₃ κ ⟨v, hv⟩ : Matrix.SpecialLinearGroup (Fin 3) K₃) :
    Matrix (Fin 3) (Fin 3) K₃) with hX
  have hDdet : IsUnit D.det := by
    have hdiag := torusGroup_le_diagonalGroup hh
    rw [hD, det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, mul_one]
    exact (mul_ne_zero (mul_ne_zero (torusRootChar_ne_zero hdiag _)
      (torusRootChar_ne_zero hdiag _)) (torusRootChar_ne_zero hdiag _)).isUnit
  have hXdet : IsUnit X.det := by
    rw [hX, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one]
    exact hDdet
  have hXc : ∀ z (hz : z ∈ subsystemGroup Tag.F4 K {κ.i, κ.j}),
      X * ((f4A2Equiv K₃ κ ⟨_, baseChangeGL_mem_subsystemGroup (algebraMap K K₃) hz⟩ :
        Matrix.SpecialLinearGroup (Fin 3) K₃) : Matrix (Fin 3) (Fin 3) K₃) =
      ((f4A2Equiv K₃ κ ⟨_, baseChangeGL_mem_subsystemGroup (algebraMap K K₃) hz⟩ :
        Matrix.SpecialLinearGroup (Fin 3) K₃) : Matrix (Fin 3) (Fin 3) K₃) * X := by
    intro z hz
    have hzz := hconj ⟨_, baseChangeGL_mem_subsystemGroup (algebraMap K K₃) hz⟩
    have e : (⟨h * v * baseChangeGL (algebraMap K K₃) z * (h * v)⁻¹,
        hN _ (baseChangeGL_mem_subsystemGroup (algebraMap K K₃) hz)⟩ :
          subsystemGroup Tag.F4 K₃ {κ.i, κ.j}) =
        ⟨_, baseChangeGL_mem_subsystemGroup (algebraMap K K₃) hz⟩ := by
      apply Subtype.ext
      change h * v * baseChangeGL (algebraMap K K₃) z * (h * v)⁻¹ = _
      rw [hc z hz, mul_inv_cancel_right]
    rw [e] at hzz
    exact matrix_mul_comm_of_eq_conj hXdet hzz
  obtain ⟨hgen, -⟩ := F4_native_long_and_short_A2_faithful_SL3_all_characteristics K₃ κ
  have hbx : ∀ (k : Fin Tag.F4.rank) (hk : k ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank))),
      (⟨_, baseChangeGL_mem_subsystemGroup (algebraMap K K₃)
          (xUnit_mem_subsystemGroup hk (1 : K))⟩ : subsystemGroup Tag.F4 K₃ {κ.i, κ.j}) =
        qx hk 1 ∧
      (⟨_, baseChangeGL_mem_subsystemGroup (algebraMap K K₃)
          (yUnit_mem_subsystemGroup hk (1 : K))⟩ : subsystemGroup Tag.F4 K₃ {κ.i, κ.j}) =
        qy hk 1 := fun k hk =>
    ⟨Subtype.ext (show baseChangeGL (algebraMap K K₃) (xUnit Tag.F4 K k 1) = xUnit Tag.F4 K₃ k 1 by
        rw [baseChangeGL_xUnit, map_one]),
      Subtype.ext (show baseChangeGL (algebraMap K K₃) (yUnit Tag.F4 K k 1) = yUnit Tag.F4 K₃ k 1 by
        rw [baseChangeGL_yUnit, map_one])⟩
  have h01 := hXc _ (xUnit_mem_subsystemGroup hl (1 : K))
  have h10 := hXc _ (yUnit_mem_subsystemGroup hl (1 : K))
  have h12 := hXc _ (xUnit_mem_subsystemGroup hr (1 : K))
  have h21 := hXc _ (yUnit_mem_subsystemGroup hr (1 : K))
  rw [(hbx _ hl).1, (hgen 1).1] at h01
  rw [(hbx _ hl).2, (hgen 1).2.1] at h10
  rw [(hbx _ hr).1, (hgen 1).2.2.1] at h12
  rw [(hbx _ hr).2, (hgen 1).2.2.2] at h21
  obtain ⟨μ, hμ⟩ := mem_range_scalar_of_commute_elementary h01 h10 h12 h21
  have hvdiag : (((f4A2Equiv K₃ κ ⟨v, hv⟩ : Matrix.SpecialLinearGroup (Fin 3) K₃) :
      Matrix (Fin 3) (Fin 3) K₃)).IsDiag := by
    have e : ((f4A2Equiv K₃ κ ⟨v, hv⟩ : Matrix.SpecialLinearGroup (Fin 3) K₃) :
        Matrix (Fin 3) (Fin 3) K₃) = D⁻¹ * scalar (Fin 3) μ := by
      rw [hμ, hX, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hDdet, Matrix.one_mul]
    rw [e, hD, Matrix.inv_diagonal, Matrix.scalar_apply, diagonal_mul_diagonal]
    exact isDiag_diagonal _
  obtain ⟨g₀, hg₀T, hg₀⟩ := (f4A2Equiv_torus_iff κ (f4A2Equiv K₃ κ ⟨v, hv⟩)).2 hvdiag
  have hvT : v ∈ torusGroup Tag.F4 K₃ := by
    have e := congrArg Subtype.val ((f4A2Equiv K₃ κ).injective hg₀)
    rw [← show ((⟨v, hv⟩ : subsystemGroup Tag.F4 K₃ {κ.i, κ.j}) : ModGL Tag.F4 K₃) = v from rfl,
      ← e]
    exact subsystemTorus_le_torusGroup' hg₀T
  have hyH : h * v ∈ torusGroup Tag.F4 K₃ := mul_mem hh hvT
  have hchar : ∀ k ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank)),
      torusRootChar (h * v) (Pi.single k 1) = 1 := by
    intro k hk
    refine torusRootChar_eq_one_of_commute_pinnedX_one hyH (isRoot_single _ k) ?_
    have := hc _ (xUnit_mem_subsystemGroup hk (1 : K))
    rwa [baseChangeGL_xUnit, map_one, ← pinnedX_single] at this
  exact ⟨hyH, hchar _ hl, hchar _ hr⟩

end Centralizer

section Small

variable {M : Type} [Field M]

theorem f4A2Equiv_center_iff (κ : F4A2Kind) (g : subsystemGroup Tag.F4 M {κ.i, κ.j}) :
    g ∈ Subgroup.center (subsystemGroup Tag.F4 M {κ.i, κ.j}) ↔
      ∃ l : M, l ^ 3 = 1 ∧
        ((f4A2Equiv M κ g : Matrix.SpecialLinearGroup (Fin 3) M) : Matrix (Fin 3) (Fin 3) M) =
          scalar (Fin 3) l := by
  have e : g ∈ Subgroup.center (subsystemGroup Tag.F4 M {κ.i, κ.j}) ↔
      f4A2Equiv M κ g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) M) := by
    rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
    constructor
    · intro h B
      obtain ⟨y, rfl⟩ := (f4A2Equiv M κ).surjective B
      rw [← map_mul, ← map_mul, h]
    · intro h y
      apply (f4A2Equiv M κ).injective
      rw [map_mul, map_mul, h]
  rw [e, Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]
  exact ⟨fun ⟨l, hl3, hle⟩ => ⟨l, hl3, hle.symm⟩, fun ⟨l, hl3, hle⟩ => ⟨l, hl3, hle.symm⟩⟩

theorem isQuasisimple_f4A2 (κ : F4A2Kind) :
    CFSG.IsQuasisimple (subsystemGroup Tag.F4 M {κ.i, κ.j}) :=
  CFSG.LocalCores.isQuasisimple_of_surjective
    (Classical2.isQuasisimple_specialLinearGroup (K := M) (n := 3) le_rfl)
    (f4A2Equiv M κ).symm.toMonoidHom (f4A2Equiv M κ).symm.surjective fun x hx => by
      have hx1 : x = 1 := (f4A2Equiv M κ).symm.injective (by
        rw [MonoidHom.mem_ker] at hx
        rw [map_one]
        exact hx)
      rw [hx1]
      exact one_mem _

end Small

section LeviCentralizer

variable {K : Type} [Field K] {K₃ : Type} [Field K₃] [Algebra K K₃]

theorem f4A2_levi_centralizer [Finite K₃] [CharP K₃ 2] (κ : F4A2Kind)
    {Z L QK : Subgroup (ModGL Tag.F4 K₃)}
    (hZ : ∀ h, h ∈ Z ↔ h ∈ torusGroup Tag.F4 K₃ ∧ torusRootChar h (Pi.single κ.i 1) = 1 ∧
      torusRootChar h (Pi.single κ.j 1) = 1)
    (hL : L = torusGroup Tag.F4 K₃ ⊔ subsystemGroup Tag.F4 K₃ {κ.i, κ.j})
    {a : ModGL Tag.F4 K₃} (ha : a ∈ subsystemGroup Tag.F4 K₃ {κ.i, κ.j})
    (hQK : ∀ g, g ∈ QK ↔ ∃ y ∈ subsystemGroup Tag.F4 K {κ.i, κ.j},
      g = a * baseChangeGL (algebraMap K K₃) y * a⁻¹) :
    L ⊓ Subgroup.centralizer (QK : Set (ModGL Tag.F4 K₃)) = Z ∧
      (Subgroup.center L).map L.subtype = Z ∧ Odd (Nat.card Z) := by
  have hHcomm := (triangular_borel_structure.{0, 0} Tag.F4 K₃).1
  have hZH : ∀ z ∈ Z, z ∈ torusGroup Tag.F4 K₃ := fun z hz => ((hZ z).1 hz).1
  have hZQ : ∀ z ∈ Z, ∀ x ∈ subsystemGroup Tag.F4 K₃ {κ.i, κ.j}, z * x = x * z := by
    intro z hz x hx
    obtain ⟨hzH, h1, h2⟩ := (hZ z).1 hz
    refine commute_of_mem_subsystemGroup hzH (fun k hk => ?_) hx
    rcases hk with rfl | hk
    · exact h1
    · rw [Set.mem_singleton_iff] at hk
      subst hk
      exact h2
  have hHL : torusGroup Tag.F4 K₃ ≤ L := hL ▸ le_sup_left
  have hQL : subsystemGroup Tag.F4 K₃ {κ.i, κ.j} ≤ L := hL ▸ le_sup_right
  have hQKQ : ∀ g ∈ QK, g ∈ subsystemGroup Tag.F4 K₃ {κ.i, κ.j} := by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := (hQK g).1 hg
    exact mul_mem (mul_mem ha (baseChangeGL_mem_subsystemGroup _ hy)) (inv_mem ha)
  have hZL : ∀ z ∈ Z, ∀ g ∈ L, z * g = g * z := by
    intro z hz g hg
    have hle : L ≤ Subgroup.centralizer ({z} : Set (ModGL Tag.F4 K₃)) := by
      rw [hL]
      refine sup_le (fun h hh => ?_) (fun x hx => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hHcomm h hh z (hZH z hz)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hZQ z hz x hx).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm
  have hnorm : torusGroup Tag.F4 K₃ ≤
      Subgroup.normalizer (subsystemGroup Tag.F4 K₃ {κ.i, κ.j} : Set (ModGL Tag.F4 K₃)) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro z
    obtain ⟨hN, -⟩ := f4A2Equiv_torus_mul_conj κ hh (one_mem _)
    obtain ⟨hN', -⟩ := f4A2Equiv_torus_mul_conj κ (inv_mem hh) (one_mem _)
    constructor
    · intro hz
      have := hN z hz
      rwa [mul_one] at this
    · intro hz
      have := hN' _ hz
      have e : h⁻¹ * 1 * (h * z * h⁻¹) * (h⁻¹ * 1)⁻¹ = z := by group
      rwa [e] at this
  have hcent : L ⊓ Subgroup.centralizer (QK : Set (ModGL Tag.F4 K₃)) = Z := by
    apply le_antisymm
    · intro y hy
      obtain ⟨hyL, hyc⟩ := Subgroup.mem_inf.1 hy
      rw [Subgroup.mem_centralizer_iff] at hyc
      have haL : a ∈ L := hQL ha
      have hy'L : a⁻¹ * y * a ∈ L := mul_mem (mul_mem (inv_mem haL) hyL) haL
      have hy'L' : a⁻¹ * y * a ∈ ((torusGroup Tag.F4 K₃ ⊔ subsystemGroup Tag.F4 K₃ {κ.i, κ.j} :
          Subgroup (ModGL Tag.F4 K₃)) : Set (ModGL Tag.F4 K₃)) := by rw [← hL]; exact hy'L
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hy'L'
      obtain ⟨h, hh, v, hv, hhv⟩ := hy'L'
      have hc : ∀ z ∈ subsystemGroup Tag.F4 K {κ.i, κ.j},
          h * v * baseChangeGL (algebraMap K K₃) z =
            baseChangeGL (algebraMap K K₃) z * (h * v) := by
        intro z hz
        have hm : a * baseChangeGL (algebraMap K K₃) z * a⁻¹ ∈ QK := (hQK _).2 ⟨z, hz, rfl⟩
        have e := hyc _ hm
        change h * v = a⁻¹ * y * a at hhv
        rw [hhv]
        calc a⁻¹ * y * a * baseChangeGL (algebraMap K K₃) z =
            a⁻¹ * (y * (a * baseChangeGL (algebraMap K K₃) z * a⁻¹)) * a := by group
          _ = a⁻¹ * ((a * baseChangeGL (algebraMap K K₃) z * a⁻¹) * y) * a := by rw [e]
          _ = _ := by group
      obtain ⟨hyH, h1, h2⟩ := mem_char_of_commute_f4A2 κ hh hv hc
      change h * v = a⁻¹ * y * a at hhv
      rw [hhv] at hyH h1 h2
      have hy' : a⁻¹ * y * a ∈ Z := (hZ _).2 ⟨hyH, h1, h2⟩
      have e : y = a * (a⁻¹ * y * a) * a⁻¹ := by group
      rw [e, ← hZQ _ hy' _ ha, mul_inv_cancel_right]
      exact hy'
    · intro z hz
      refine Subgroup.mem_inf.2 ⟨hHL (hZH z hz), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hZQ z hz x (hQKQ x hx)).symm
  refine ⟨hcent, ?_, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      rw [← hcent]
      refine Subgroup.mem_inf.2 ⟨g.2, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
      have hxL : x ∈ L := hQL (hQKQ x hx)
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hg) ⟨x, hxL⟩)
    · intro z hz
      refine Subgroup.mem_map.2 ⟨⟨z, hHL (hZH z hz)⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
      exact Subtype.ext (hZL z hz g g.2).symm
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := finite_modGL (τ := Tag.F4) (K := K₃)
    have hdvd : Nat.card Z ∣ Nat.card (torusGroup Tag.F4 K₃) :=
      Subgroup.card_dvd_of_le fun z hz => hZH z hz
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    exact fun h2 => not_dvd_card_torusGroup (τ := Tag.F4) (K := K₃) 2 (h2.trans hdvd)

end LeviCentralizer

theorem even_F4_native_A2_cubic_permutation_descent_including_field_two
    (K : Type) [Field K] [Fintype K] [CharP K 2] (K₃ : Type) [Field K₃] [Algebra K K₃]
    [FiniteDimensional K K₃] (h3 : Module.finrank K K₃ = 3)
    (σ : K₃ ≃+* K₃) (hσ : ∀ b, σ b = b ^ Fintype.card K) (κ : F4A2Kind)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (θ : ModGL Tag.F4 K₃ →* ModGL Tag.F4 K₃)
    (hθ : ∀ g, θ g = (weylElt Tag.F4 K₃ κ.i 1 * weylElt Tag.F4 K₃ κ.j 1) ^ ε *
      Units.map (entrywiseHom σ.toRingHom) g *
        ((weylElt Tag.F4 K₃ κ.i 1 * weylElt Tag.F4 K₃ κ.j 1) ^ ε)⁻¹)
    (Z L : Subgroup (ModGL Tag.F4 K₃))
    (hZ : ∀ h, h ∈ Z ↔ h ∈ torusGroup Tag.F4 K₃ ∧ torusRootChar h (Pi.single κ.i 1) = 1 ∧
      torusRootChar h (Pi.single κ.j 1) = 1)
    (hL : L = torusGroup Tag.F4 K₃ ⊔ subsystemGroup Tag.F4 K₃ {κ.i, κ.j}) :
    (∀ g ∈ subsystemGroup Tag.F4 K {κ.i, κ.j}, ∀ v ∈ blockSpan K (f4A2Root κ),
      (g : Module.End K (RootModule Tag.F4 K)) v ∈ blockSpan K (f4A2Root κ)) ∧
    (∀ g : subsystemGroup Tag.F4 K {κ.i, κ.j},
      ((f4A2Equiv K κ g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        blockMat (f4A2Root κ) (g : ModGL Tag.F4 K)) ∧
    (∀ g : subsystemGroup Tag.F4 K {κ.i, κ.j},
      g ∈ Subgroup.center (subsystemGroup Tag.F4 K {κ.i, κ.j}) ↔
        ∃ l : K, l ^ 3 = 1 ∧
          ((f4A2Equiv K κ g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
            scalar (Fin 3) l) ∧
    CFSG.IsQuasisimple (subsystemGroup Tag.F4 K {κ.i, κ.j}) ∧
    Group.IsPerfect (subsystemGroup Tag.F4 K {κ.i, κ.j}) ∧
    (weylElt Tag.F4 K₃ κ.i 1 * weylElt Tag.F4 K₃ κ.j 1) ^ ε ∈
      subsystemGroup Tag.F4 K₃ {κ.i, κ.j} ∧
    ∃ a ∈ subsystemGroup Tag.F4 K₃ {κ.i, κ.j},
      (weylElt Tag.F4 K₃ κ.i 1 * weylElt Tag.F4 K₃ κ.j 1) ^ ε =
        a * (Units.map (entrywiseHom σ.toRingHom) a)⁻¹ ∧
      ∃ QK : Subgroup (ModGL Tag.F4 K₃),
        (∀ g, g ∈ QK ↔ ∃ y ∈ subsystemGroup Tag.F4 K {κ.i, κ.j},
          g = a * baseChangeGL (algebraMap K K₃) y * a⁻¹) ∧
        subsystemGroup Tag.F4 K₃ {κ.i, κ.j} ⊓ θ.eqLocus (MonoidHom.id _) = QK ∧
        L ⊓ Subgroup.centralizer (QK : Set (ModGL Tag.F4 K₃)) = Z ∧
        (Subgroup.center L).map L.subtype = Z ∧ Odd (Nat.card Z) ∧
        ∀ A : SL2 K, a * rootSL2 Tag.F4 K₃ (Pi.single κ.i 1)
            (Matrix.SpecialLinearGroup.map (algebraMap K K₃) A) * a⁻¹ ∈
          subsystemGroup Tag.F4 K₃ {κ.i, κ.j} ⊓ θ.eqLocus (MonoidHom.id _) := by
  have : CharP K₃ 2 := charP_of_injective_algebraMap (algebraMap K K₃).injective 2
  have : Finite K₃ := Module.finite_of_finite K
  refine ⟨fun g hg v hv => f4A2_mem_blockSpan κ hg hv, coe_f4A2Equiv_eq_blockMat κ,
    f4A2Equiv_center_iff κ, isQuasisimple_f4A2 κ, (isQuasisimple_f4A2 κ).1,
    weyl_word_mem_pair κ ε, ?_⟩
  obtain ⟨A, hA⟩ := exists_f4A2_cubic_coboundary h3 σ hσ κ hε
  obtain ⟨a, haA⟩ := (f4A2Equiv K₃ κ).surjective A
  have ha : ((f4A2Equiv K₃ κ ⟨_, weyl_word_mem_pair (M := K₃) κ ε⟩ :
      Matrix.SpecialLinearGroup (Fin 3) K₃) : Matrix (Fin 3) (Fin 3) K₃) *
        ((f4A2Equiv K₃ κ a : Matrix.SpecialLinearGroup (Fin 3) K₃) :
          Matrix (Fin 3) (Fin 3) K₃).map σ =
        (f4A2Equiv K₃ κ a : Matrix (Fin 3) (Fin 3) K₃) := by
    rw [haA]
    exact hA
  obtain ⟨hmeq, hfixQ⟩ := f4A2_cubic_descent σ hσ κ (weyl_word_mem_pair (M := K₃) κ ε) a ha
  refine ⟨a, a.2, hmeq, ?_⟩
  set φ : ModGL Tag.F4 K →* ModGL Tag.F4 K₃ :=
    (MulAut.conj (a : ModGL Tag.F4 K₃)).toMonoidHom.comp (baseChangeGL (algebraMap K K₃)) with hφ
  have hQK : ∀ g, g ∈ (subsystemGroup Tag.F4 K {κ.i, κ.j}).map φ ↔
      ∃ y ∈ subsystemGroup Tag.F4 K {κ.i, κ.j},
        g = (a : ModGL Tag.F4 K₃) * baseChangeGL (algebraMap K K₃) y *
          (a : ModGL Tag.F4 K₃)⁻¹ := by
    intro g
    rw [Subgroup.mem_map]
    exact ⟨fun ⟨y, hy, hyg⟩ => ⟨y, hy, hyg.symm⟩, fun ⟨y, hy, hyg⟩ => ⟨y, hy, hyg.symm⟩⟩
  have hQfix : subsystemGroup Tag.F4 K₃ {κ.i, κ.j} ⊓ θ.eqLocus (MonoidHom.id _) =
      (subsystemGroup Tag.F4 K {κ.i, κ.j}).map φ := by
    ext g
    rw [Subgroup.mem_inf, show g ∈ θ.eqLocus (MonoidHom.id _) ↔ θ g = g from Iff.rfl, hQK, hθ]
    constructor
    · rintro ⟨hg, hfg⟩
      exact (hfixQ g hg).1 hfg
    · rintro ⟨y, hy, rfl⟩
      have hg : (a : ModGL Tag.F4 K₃) * baseChangeGL (algebraMap K K₃) y *
          (a : ModGL Tag.F4 K₃)⁻¹ ∈ subsystemGroup Tag.F4 K₃ {κ.i, κ.j} :=
        mul_mem (mul_mem a.2 (baseChangeGL_mem_subsystemGroup _ hy)) (inv_mem a.2)
      exact ⟨hg, (hfixQ _ hg).2 ⟨y, hy, rfl⟩⟩
  have hQKQ : (subsystemGroup Tag.F4 K {κ.i, κ.j}).map φ ≤
      subsystemGroup Tag.F4 K₃ {κ.i, κ.j} := hQfix ▸ inf_le_left
  obtain ⟨hcent, hcenter, hodd⟩ := f4A2_levi_centralizer κ hZ hL a.2 hQK
  refine ⟨_, hQK, hQfix, hcent, hcenter, hodd, fun A => ?_⟩
  rw [← baseChangeGL_rootSL2_of_charTwo (algebraMap K K₃) (isRoot_single _ κ.i), hQfix, hQK]
  exact ⟨_, rootSL2_single_mem_subsystemGroup (left_mem_pair κ.i κ.j) A, rfl⟩

end CFSG.RankThree.Chevalley
