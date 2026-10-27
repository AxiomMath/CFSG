module

public import CFSG.RankThree.PartOne.S11.PlaneData
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusCentralizers
public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections
public import CFSG.RankThree.PartOne.S11c.G2Involution

public section

namespace CFSG.RankThree.PartOne

open Matrix Matrix.ProjGenLinGroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Classical CFSG.RankThree.QuadraticSL2
open scoped MatrixGroups

section Abstract

variable {K : Type*} [Field K]

theorem mk_eq_one_of_conjSL_eq (G : GL (Fin 2) K) (h : ∀ A : SL(2, K), conjSL G A = A) :
    (mk G : PGL(2, K)) = 1 := by
  rw [mk_eq_one, Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun t => ?_
  exact (commute_of_conjSL_eq G (h ⟨t.toMatrix, t.det⟩)).symm

theorem mk_eq_of_conjSL_eq {G G' : GL (Fin 2) K} (h : ∀ A : SL(2, K), conjSL G A = conjSL G' A) :
    (mk G : PGL(2, K)) = mk G' := by
  have h1 : (mk (G'⁻¹ * G) : PGL(2, K)) = 1 := by
    apply mk_eq_one_of_conjSL_eq
    intro A
    rw [conjSL_mul, h, ← conjSL_mul, inv_mul_cancel, conjSL_one]
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

theorem exists_pgl_of_conj {M : Type*} [Group M] (X : Subgroup M) (ρ : SL(2, K) →* M)
    (hρ : Function.Injective ρ)
    (h : ∀ g ∈ X, ∃ G : GL (Fin 2) K, ∀ A, g * ρ A * g⁻¹ = ρ (conjSL G A)) :
    ∃ π : X →* PGL(2, K), ∀ (g : X) (G : GL (Fin 2) K),
      (∀ A, (g : M) * ρ A * (g : M)⁻¹ = ρ (conjSL G A)) → π g = mk G := by
  classical
  have huniq : ∀ (g : M) (G G' : GL (Fin 2) K), (∀ A, g * ρ A * g⁻¹ = ρ (conjSL G A)) →
      (∀ A, g * ρ A * g⁻¹ = ρ (conjSL G' A)) → (mk G : PGL(2, K)) = mk G' :=
    fun g G G' h1 h2 => mk_eq_of_conjSL_eq fun A => hρ (by rw [← h1, ← h2])
  let f : X → PGL(2, K) := fun g => mk (Classical.choose (h g.1 g.2))
  have hf : ∀ (g : X) (G : GL (Fin 2) K), (∀ A, (g : M) * ρ A * (g : M)⁻¹ = ρ (conjSL G A)) →
      f g = mk G := fun g G hG => huniq g.1 _ G (Classical.choose_spec (h g.1 g.2)) hG
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, hf⟩
  · refine (hf 1 1 fun A => ?_).trans (map_one _)
    rw [conjSL_one]
    simp
  · intro g₁ g₂
    have h1 := Classical.choose_spec (h g₁.1 g₁.2)
    have h2 := Classical.choose_spec (h g₂.1 g₂.2)
    change f (g₁ * g₂) = f g₁ * f g₂
    rw [← map_mul]
    refine hf _ _ fun A => ?_
    rw [Subgroup.coe_mul, conjSL_mul]
    calc (g₁ : M) * (g₂ : M) * ρ A * ((g₁ : M) * (g₂ : M))⁻¹ =
        (g₁ : M) * ((g₂ : M) * ρ A * (g₂ : M)⁻¹) * (g₁ : M)⁻¹ := by group
      _ = _ := by rw [h2 A, h1]

end Abstract

section G2

variable {K : Type} [Field K] {a : Fin Tag.G2.rank → Kˣ} {α β : Fin Tag.G2.rank → ℤ}

theorem rootChar_one' {τ : Tag} (v : Fin τ.rank → ℤ) : rootChar (1 : Fin τ.rank → Kˣ) v = 1 := by
  simp [rootChar]

theorem exists_decomp (hK : ringChar K ≠ 2) (ha : ∀ i, a i = 1 ∨ a i = -1) (h : G2SignPair α β)
    (hS : (g2Mul h K).range = rootSpan .G2 K (rootCharKernel a)) {g : ModGL .G2 K}
    (hg : g ∈ toralCentralizer .G2 K a) :
    ∃ (c : Fin Tag.G2.rank → Kˣ) (A B : SL2 K),
      g = rootDiagUnit .G2 c * (rootSL2 .G2 K α A * rootSL2 .G2 K β B) := by
  obtain ⟨x, hx, s, hs, rfl⟩ := exists_torus_mul_rootSpan hK ha hg
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  rw [← hS] at hs
  obtain ⟨⟨A, B⟩, rfl⟩ := hs
  exact ⟨c, A, B, rfl⟩

theorem conj_rootSL2_decomp {τ : Tag} {γ γ' : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hc : ∀ A B, Commute (rootSL2 τ K γ A) (rootSL2 τ K γ' B)) (c : Fin τ.rank → Kˣ)
    (A B A' : SL2 K) :
    (rootDiagUnit τ c * (rootSL2 τ K γ A * rootSL2 τ K γ' B)) * rootSL2 τ K γ A' *
        (rootDiagUnit τ c * (rootSL2 τ K γ A * rootSL2 τ K γ' B))⁻¹ =
      rootSL2 τ K γ
        (conjSL (diagUnitOne (rootChar c γ) * Matrix.SpecialLinearGroup.toGL A) A') := by
  have hbx : rootSL2 τ K γ' B * rootSL2 τ K γ A' * (rootSL2 τ K γ' B)⁻¹ = rootSL2 τ K γ A' := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (hc A' B).eq.symm
  calc rootDiagUnit τ c * (rootSL2 τ K γ A * rootSL2 τ K γ' B) * rootSL2 τ K γ A' *
        (rootDiagUnit τ c * (rootSL2 τ K γ A * rootSL2 τ K γ' B))⁻¹
      = rootDiagUnit τ c * rootSL2 τ K γ A * (rootSL2 τ K γ' B * rootSL2 τ K γ A' *
          (rootSL2 τ K γ' B)⁻¹) * (rootSL2 τ K γ A)⁻¹ * (rootDiagUnit τ c)⁻¹ := by group
    _ = rootDiagUnit τ c * rootSL2 τ K γ (A * A' * A⁻¹) * (rootDiagUnit τ c)⁻¹ := by
        rw [hbx, map_mul, map_mul, map_inv]
        group
    _ = _ := by
        rw [rootDiagUnit_conj_rootSL2 c hγ, conjSL_mul, conjSL_toGL]

theorem exists_pgl_alpha (hK : ringChar K ≠ 2) (ha : ∀ i, a i = 1 ∨ a i = -1)
    (h : G2SignPair α β) (hS : (g2Mul h K).range = rootSpan .G2 K (rootCharKernel a)) :
    ∃ π : toralCentralizer .G2 K a →* PGL(2, K),
      ∀ (g : toralCentralizer .G2 K a) (c : Fin Tag.G2.rank → Kˣ) (A B : SL2 K),
        (g : ModGL .G2 K) = rootDiagUnit .G2 c * (rootSL2 .G2 K α A * rootSL2 .G2 K β B) →
          π g = mk (diagUnitOne (rootChar c α) * Matrix.SpecialLinearGroup.toGL A) := by
  obtain ⟨hα, hβ⟩ := g2_pair_isRoot h
  obtain ⟨π, hπ⟩ := exists_pgl_of_conj (toralCentralizer .G2 K a) (rootSL2 .G2 K α)
    (rootSL2_injective_of_field α) fun g hg => by
      obtain ⟨c, A, B, rfl⟩ := exists_decomp hK ha h hS hg
      exact ⟨_, fun A' => conj_rootSL2_decomp hα (fun A B => g2_pair_commute h A B) c A B A'⟩
  refine ⟨π, fun g c A B hg => hπ g _ fun A' => ?_⟩
  rw [hg]
  exact conj_rootSL2_decomp hα (fun A B => g2_pair_commute h A B) c A B A'

theorem exists_pgl_beta (hK : ringChar K ≠ 2) (ha : ∀ i, a i = 1 ∨ a i = -1)
    (h : G2SignPair α β) (hS : (g2Mul h K).range = rootSpan .G2 K (rootCharKernel a)) :
    ∃ π : toralCentralizer .G2 K a →* PGL(2, K),
      ∀ (g : toralCentralizer .G2 K a) (c : Fin Tag.G2.rank → Kˣ) (A B : SL2 K),
        (g : ModGL .G2 K) = rootDiagUnit .G2 c * (rootSL2 .G2 K α A * rootSL2 .G2 K β B) →
          π g = mk (diagUnitOne (rootChar c β) * Matrix.SpecialLinearGroup.toGL B) := by
  obtain ⟨hα, hβ⟩ := g2_pair_isRoot h
  have hconj : ∀ (c : Fin Tag.G2.rank → Kˣ) (A B A' : SL2 K),
      (rootDiagUnit .G2 c * (rootSL2 .G2 K α A * rootSL2 .G2 K β B)) * rootSL2 .G2 K β A' *
        (rootDiagUnit .G2 c * (rootSL2 .G2 K α A * rootSL2 .G2 K β B))⁻¹ =
      rootSL2 .G2 K β (conjSL (diagUnitOne (rootChar c β) *
        Matrix.SpecialLinearGroup.toGL B) A') := fun c A B A' => by
    have := conj_rootSL2_decomp hβ (fun A' B' => (g2_pair_commute h B' A').symm) c B A A'
    rwa [← (g2_pair_commute h A B).eq] at this
  obtain ⟨π, hπ⟩ := exists_pgl_of_conj (toralCentralizer .G2 K a) (rootSL2 .G2 K β)
    (rootSL2_injective_of_field β) fun g hg => by
      obtain ⟨c, A, B, rfl⟩ := exists_decomp hK ha h hS hg
      exact ⟨_, fun A' => hconj c A B A'⟩
  refine ⟨π, fun g c A B hg => hπ g _ fun A' => ?_⟩
  rw [hg]
  exact hconj c A B A'

theorem det_diagUnitOne (χ : Kˣ) : Matrix.GeneralLinearGroup.det (diagUnitOne χ) = χ := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagUnitOne, Matrix.det_fin_two_of]
  simp

theorem exists_sq_of_mk_mem_range {χ : Kˣ} {A : SL2 K}
    (h : (mk (diagUnitOne χ * Matrix.SpecialLinearGroup.toGL A) : PGL(2, K)) ∈
      (toPGL : SL(2, K) →* PGL(2, K)).range) : ∃ lam : Kˣ, χ = lam ^ 2 := by
  obtain ⟨A₁, hA₁⟩ := h
  have h1 : (mk (Matrix.SpecialLinearGroup.toGL A₁) : PGL(2, K)) =
      mk (diagUnitOne χ * Matrix.SpecialLinearGroup.toGL A) := hA₁
  obtain ⟨u, hu⟩ := mk_eq_mk_iff.1 h1
  have hdet := congrArg Matrix.GeneralLinearGroup.det hu
  have h2 : ∀ B : SL2 K, Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL B) = 1 :=
    fun B => Units.ext (by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        Matrix.SpecialLinearGroup.det_coe, Units.val_one])
  rw [map_mul, map_mul, Matrix.GeneralLinearGroup.det_scalar, det_diagUnitOne, h2, h2,
    Fintype.card_fin] at hdet
  exact ⟨u, by simpa using hdet.symm⟩

theorem mem_range_of_pgl_alpha (hK : ringChar K ≠ 2) (ha : ∀ i, a i = 1 ∨ a i = -1)
    (h : G2SignPair α β) (hS : (g2Mul h K).range = rootSpan .G2 K (rootCharKernel a))
    {πα : toralCentralizer .G2 K a →* PGL(2, K)}
    (hπα : ∀ (g : toralCentralizer .G2 K a) (c : Fin Tag.G2.rank → Kˣ) (A B : SL2 K),
      (g : ModGL .G2 K) = rootDiagUnit .G2 c * (rootSL2 .G2 K α A * rootSL2 .G2 K β B) →
        πα g = mk (diagUnitOne (rootChar c α) * Matrix.SpecialLinearGroup.toGL A))
    {g : toralCentralizer .G2 K a} (hg : πα g ∈ (toPGL : SL(2, K) →* PGL(2, K)).range) :
    (g : ModGL .G2 K) ∈ (g2Mul h K).range := by
  obtain ⟨c, A, B, hdec⟩ := exists_decomp hK ha h hS g.2
  rw [hπα g c A B hdec] at hg
  obtain ⟨lam, hlam⟩ := exists_sq_of_mk_mem_range hg
  obtain ⟨c₁, c₂, hc⟩ := g2_pair_rootDiagUnit h c lam hlam
  rw [hdec, hc]
  exact (g2Mul h K).range.mul_mem ⟨(HSL c₁, HSL c₂), g2Mul_apply h _ _⟩
    ⟨(A, B), g2Mul_apply h A B⟩

theorem mem_range_of_pgl_beta (hK : ringChar K ≠ 2) (ha : ∀ i, a i = 1 ∨ a i = -1)
    (h : G2SignPair α β) (hS : (g2Mul h K).range = rootSpan .G2 K (rootCharKernel a))
    {πβ : toralCentralizer .G2 K a →* PGL(2, K)}
    (hπβ : ∀ (g : toralCentralizer .G2 K a) (c : Fin Tag.G2.rank → Kˣ) (A B : SL2 K),
      (g : ModGL .G2 K) = rootDiagUnit .G2 c * (rootSL2 .G2 K α A * rootSL2 .G2 K β B) →
        πβ g = mk (diagUnitOne (rootChar c β) * Matrix.SpecialLinearGroup.toGL B))
    {g : toralCentralizer .G2 K a} (hg : πβ g ∈ (toPGL : SL(2, K) →* PGL(2, K)).range) :
    (g : ModGL .G2 K) ∈ (g2Mul h K).range := by
  obtain ⟨c, A, B, hdec⟩ := exists_decomp hK ha h hS g.2
  rw [hπβ g c A B hdec] at hg
  obtain ⟨lam, hlam⟩ := exists_sq_of_mk_mem_range hg
  obtain ⟨γ, hγ⟩ := g2_pair_rootChar_sq h c
  have hα : rootChar c α = (γ * lam) ^ 2 := by
    rw [mul_pow, ← hlam, ← hγ]
    group
  obtain ⟨c₁, c₂, hc⟩ := g2_pair_rootDiagUnit h c (γ * lam) hα
  rw [hdec, hc]
  exact (g2Mul h K).range.mul_mem ⟨(HSL c₁, HSL c₂), g2Mul_apply h _ _⟩
    ⟨(A, B), g2Mul_apply h A B⟩

theorem units_eq_one_or_neg_one {u : Kˣ} (hu : u * u = 1) : u = 1 ∨ u = -1 := by
  have h : (u : K) * u = 1 := by rw [← Units.val_mul, hu, Units.val_one]
  rcases mul_self_eq_one_iff.1 h with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by simpa using h))

theorem HSL_mul_HSL' (t t' : Kˣ) : HSL t * HSL t' = HSL (t * t') := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [HSL, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem HSL_one' : HSL (1 : Kˣ) = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [HSL]

theorem HSL_neg_one_mul_self : HSL (-1 : Kˣ) * HSL (-1 : Kˣ) = 1 := by
  rw [HSL_mul_HSL']
  simp [HSL_one']

theorem rootSL2_neg_one_sq {τ : Tag} (γ : Fin τ.rank → ℤ) :
    rootSL2 τ K γ (HSL (-1)) * rootSL2 τ K γ (HSL (-1)) = 1 := by
  rw [← map_mul, HSL_neg_one_mul_self, map_one]

theorem rootSL2_of_mem_center {τ : Tag} (γ : Fin τ.rank → ℤ) {A : SL2 K}
    (hA : A ∈ Subgroup.center (SL2 K)) :
    rootSL2 τ K γ A = 1 ∨ rootSL2 τ K γ A = rootSL2 τ K γ (HSL (-1)) := by
  obtain ⟨u, hu, rfl⟩ := exists_eq_HSL_of_mem_center hA
  rcases units_eq_one_or_neg_one hu with rfl | rfl
  · left
    rw [HSL_one', map_one]
  · right
    rfl

theorem rootSL2_sq_eq_one (hK : ringChar K ≠ 2) {τ : Tag} (γ : Fin τ.rank → ℤ) {A : SL2 K}
    (hA2 : rootSL2 τ K γ A ^ 2 = 1) :
    rootSL2 τ K γ A = 1 ∨ rootSL2 τ K γ A = rootSL2 τ K γ (HSL (-1)) := by
  have hA : A ^ 2 = 1 := rootSL2_injective_of_field γ (by rw [map_pow, hA2, map_one])
  by_cases hA1 : A = 1
  · left
    rw [hA1, map_one]
  · right
    have h1 := CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq (Ring.two_ne_zero hK) A hA hA1
    have : A = HSL (-1) := Subtype.ext (by
      rw [h1, coe_HSL]
      ext i j
      fin_cases i <;> fin_cases j <;> simp)
    rw [this]

theorem eq_one_of_sq_eq_one_of_pow_odd {G : Type*} [Group G] {z : G} {m : ℕ} (hm : Odd m)
    (h2 : z ^ 2 = 1) (hz : z ^ m = 1) : z = 1 := by
  obtain ⟨k, rfl⟩ := hm
  calc z = z ^ (2 * k + 1) := by rw [pow_succ, pow_mul, h2, one_pow, one_mul]
    _ = 1 := hz

theorem involution_of_central_component (hK : ringChar K ≠ 2) (h : G2SignPair α β) {A B : SL2 K}
    (hg2 : g2Mul h K (A, B) ^ 2 = 1)
    (hAB : A ∈ Subgroup.center (SL2 K) ∨ B ∈ Subgroup.center (SL2 K)) :
    g2Mul h K (A, B) = 1 ∨ g2Mul h K (A, B) = rootSL2 .G2 K α (HSL (-1)) := by
  have hneg := g2_pair_HSL_neg_one (K := K) h
  have hc := g2_pair_commute h A B
  have hxy : (rootSL2 .G2 K α A * rootSL2 .G2 K β B) ^ 2 =
      rootSL2 .G2 K α A ^ 2 * rootSL2 .G2 K β B ^ 2 := hc.mul_pow 2
  rw [g2Mul_apply, hxy] at hg2
  have hsq : rootSL2 .G2 K α A ^ 2 = 1 ∧ rootSL2 .G2 K β B ^ 2 = 1 := by
    rcases hAB with hA | hB
    · have hx2 : rootSL2 .G2 K α A ^ 2 = 1 := by
        rcases rootSL2_of_mem_center (τ := .G2) α hA with h1 | h1
        · rw [h1, one_pow]
        · rw [sq, h1, rootSL2_neg_one_sq]
      exact ⟨hx2, by rwa [hx2, one_mul] at hg2⟩
    · have hy2 : rootSL2 .G2 K β B ^ 2 = 1 := by
        rcases rootSL2_of_mem_center (τ := .G2) β hB with h1 | h1
        · rw [h1, one_pow]
        · rw [sq, h1, rootSL2_neg_one_sq]
      exact ⟨by rwa [hy2, mul_one] at hg2, hy2⟩
  have hx := rootSL2_sq_eq_one hK α hsq.1
  have hy := rootSL2_sq_eq_one hK β hsq.2
  rw [g2Mul_apply]
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · left
    rw [hx, hy, one_mul]
  · right
    rw [hx, hy, ← hneg, one_mul]
  · right
    rw [hx, hy, mul_one]
  · left
    rw [hx, hy, ← hneg, rootSL2_neg_one_sq]

theorem odd_order_of_central_components (h : G2SignPair α β) {A B : SL2 K}
    (hA : A ∈ Subgroup.center (SL2 K)) (hB : B ∈ Subgroup.center (SL2 K)) {m : ℕ} (hm : Odd m)
    (hz : g2Mul h K (A, B) ^ m = 1) : g2Mul h K (A, B) = 1 := by
  have hc := g2_pair_commute h A B
  have hx : rootSL2 .G2 K α A ^ 2 = 1 := by
    rcases rootSL2_of_mem_center (τ := .G2) α hA with h1 | h1
    · rw [h1, one_pow]
    · rw [sq, h1, rootSL2_neg_one_sq]
  have hy : rootSL2 .G2 K β B ^ 2 = 1 := by
    rcases rootSL2_of_mem_center (τ := .G2) β hB with h1 | h1
    · rw [h1, one_pow]
    · rw [sq, h1, rootSL2_neg_one_sq]
  have hsq : g2Mul h K (A, B) ^ 2 = 1 := by
    rw [g2Mul_apply, hc.mul_pow, hx, hy, one_mul]
  exact eq_one_of_sq_eq_one_of_pow_odd hm hsq hz

theorem pgl_image_aux (hk : ringChar K ≠ 2) {M : Type*} [Group M] {X : Subgroup M} (t₀ : M)
    (π : X →* PGL(2, K))
    (hker : ∀ g : X, (g : M) ^ 2 = 1 → π g = 1 → (g : M) = 1 ∨ (g : M) = t₀)
    {R : Subgroup M} (hR : R ≤ X) [Finite R] [IsElementaryAbelian 2 R] :
    Nat.card R ≤ 8 ∧
      (Nat.card R = 8 → ∀ z : X, (∀ r ∈ R, (z : M) * r = r * (z : M)) → π z ^ 2 = 1) := by
  classical
  let f : R →* PGL(2, K) := π.comp (Subgroup.inclusion hR)
  have : IsElementaryAbelian 2 f.range := isElementaryAbelian_range inferInstance f
  obtain ⟨-, hcard4, hcent⟩ :=
    odd_projective_linear_elementary_two_subgroups_and_centralizers K hk f.range
  have hsq : ∀ r : R, (r : M) ^ 2 = 1 := fun r =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := R) (r : M) r.2
  have hker2 : Nat.card f.ker ≤ 2 := by
    let φ : f.ker → Bool := fun x => decide (((x : R) : M) = t₀)
    have hx : ∀ x : f.ker, ((x : R) : M) = 1 ∨ ((x : R) : M) = t₀ := fun x =>
      hker (Subgroup.inclusion hR x) (hsq x) x.2
    have hφ : Function.Injective φ := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      by_cases hxt : ((x : R) : M) = t₀
      · have hyt : ((y : R) : M) = t₀ := by
          by_contra hyt
          simp [φ, hxt, hyt] at hxy
        rw [hxt, hyt]
      · have hyt : ¬ ((y : R) : M) = t₀ := by
          intro hyt
          simp [φ, hxt, hyt] at hxy
        rw [(hx x).resolve_right hxt, (hx y).resolve_right hyt]
    calc Nat.card f.ker ≤ Nat.card Bool := Nat.card_le_card_of_injective φ hφ
      _ = 2 := by simp
  have hmul := Subgroup.card_ker_mul_card_range f
  refine ⟨?_, fun h8 z hz => ?_⟩
  · calc Nat.card R = Nat.card f.ker * Nat.card f.range := hmul.symm
      _ ≤ 2 * 4 := Nat.mul_le_mul hker2 hcard4
      _ = 8 := by norm_num
  · have hrange4 : Nat.card f.range = 4 := by
      have : 8 ≤ 2 * Nat.card f.range := by
        rw [← h8, ← hmul]
        exact Nat.mul_le_mul_right _ hker2
      omega
    have hz' : π z ∈ Subgroup.centralizer (f.range : Set PGL(2, K)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨r, rfl⟩
      change π (Subgroup.inclusion hR r) * π z = π z * π (Subgroup.inclusion hR r)
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hz r r.2).symm
    rw [hcent hrange4] at hz'
    obtain ⟨r, hr⟩ := hz'
    rw [← hr, ← map_pow]
    have : r ^ 2 = 1 := Subtype.ext (hsq r)
    rw [this, map_one]

theorem g2_toral_elementary_two (hK : ringChar K ≠ 2) (ha : ∀ i, a i = 1 ∨ a i = -1)
    (h : G2SignPair α β) (hS : (g2Mul h K).range = rootSpan .G2 K (rootCharKernel a))
    {R : Subgroup (ModGL .G2 K)} (hR : R ≤ toralCentralizer .G2 K a) [Finite R]
    [IsElementaryAbelian 2 R] :
    Nat.card R ≤ 8 ∧ (Nat.card R = 8 → ∀ z ∈ toralCentralizer .G2 K a,
      (∀ r ∈ R, z * r = r * z) → Odd (orderOf z) → z = 1) := by
  obtain ⟨πα, hπα⟩ := exists_pgl_alpha hK ha h hS
  obtain ⟨πβ, hπβ⟩ := exists_pgl_beta hK ha h hS
  have hαS : ∀ (g : toralCentralizer .G2 K a) (A B : SL2 K),
      (g : ModGL .G2 K) = g2Mul h K (A, B) → πα g = toPGL A := fun g A B hg => by
    rw [hπα g 1 A B (by rw [hg, g2Mul_apply, rootDiagUnit_one, one_mul]), rootChar_one',
      diagUnitOne_one, one_mul]
    rfl
  have hβS : ∀ (g : toralCentralizer .G2 K a) (A B : SL2 K),
      (g : ModGL .G2 K) = g2Mul h K (A, B) → πβ g = toPGL B := fun g A B hg => by
    rw [hπβ g 1 A B (by rw [hg, g2Mul_apply, rootDiagUnit_one, one_mul]), rootChar_one',
      diagUnitOne_one, one_mul]
    rfl
  have hkerα : ∀ g : toralCentralizer .G2 K a, (g : ModGL .G2 K) ^ 2 = 1 → πα g = 1 →
      (g : ModGL .G2 K) = 1 ∨ (g : ModGL .G2 K) = rootSL2 .G2 K α (HSL (-1)) := by
    intro g hg2 hg1
    obtain ⟨⟨A, B⟩, hAB⟩ := mem_range_of_pgl_alpha hK ha h hS hπα (g := g)
      ⟨1, by rw [map_one, hg1]⟩
    have hgAB : (g : ModGL .G2 K) = g2Mul h K (A, B) := hAB.symm
    have hA : A ∈ Subgroup.center (SL2 K) :=
      toPGL_eq_one_iff.1 (by rw [← hαS g A B hgAB, hg1])
    rw [hgAB] at hg2 ⊢
    exact involution_of_central_component hK h hg2 (Or.inl hA)
  have hkerβ : ∀ g : toralCentralizer .G2 K a, (g : ModGL .G2 K) ^ 2 = 1 → πβ g = 1 →
      (g : ModGL .G2 K) = 1 ∨ (g : ModGL .G2 K) = rootSL2 .G2 K α (HSL (-1)) := by
    intro g hg2 hg1
    obtain ⟨⟨A, B⟩, hAB⟩ := mem_range_of_pgl_beta hK ha h hS hπβ (g := g)
      ⟨1, by rw [map_one, hg1]⟩
    have hgAB : (g : ModGL .G2 K) = g2Mul h K (A, B) := hAB.symm
    have hB : B ∈ Subgroup.center (SL2 K) :=
      toPGL_eq_one_iff.1 (by rw [← hβS g A B hgAB, hg1])
    rw [hgAB] at hg2 ⊢
    exact involution_of_central_component hK h hg2 (Or.inr hB)
  obtain ⟨hcardα, hcentα⟩ :=
    pgl_image_aux hK (rootSL2 .G2 K α (HSL (-1))) πα hkerα hR
  obtain ⟨-, hcentβ⟩ := pgl_image_aux hK (rootSL2 .G2 K α (HSL (-1))) πβ hkerβ hR
  refine ⟨hcardα, fun h8 z hz hzc hodd => ?_⟩
  have hα2 := hcentα h8 ⟨z, hz⟩ hzc
  have hβ2 := hcentβ h8 ⟨z, hz⟩ hzc
  have hzm : (⟨z, hz⟩ : toralCentralizer .G2 K a) ^ orderOf z = 1 :=
    Subtype.ext (by simp)
  have hπα1 : πα ⟨z, hz⟩ = 1 :=
    eq_one_of_sq_eq_one_of_pow_odd hodd hα2 (by rw [← map_pow, hzm, map_one])
  have hπβ1 : πβ ⟨z, hz⟩ = 1 :=
    eq_one_of_sq_eq_one_of_pow_odd hodd hβ2 (by rw [← map_pow, hzm, map_one])
  obtain ⟨⟨A, B⟩, hAB⟩ := mem_range_of_pgl_alpha hK ha h hS hπα (g := ⟨z, hz⟩)
    ⟨1, by rw [map_one, hπα1]⟩
  have hgAB : z = g2Mul h K (A, B) := hAB.symm
  have hA : A ∈ Subgroup.center (SL2 K) :=
    toPGL_eq_one_iff.1 (by rw [← hαS ⟨z, hz⟩ A B hgAB, hπα1])
  have hB : B ∈ Subgroup.center (SL2 K) :=
    toPGL_eq_one_iff.1 (by rw [← hβS ⟨z, hz⟩ A B hgAB, hπβ1])
  rw [hgAB]
  exact odd_order_of_central_components h hA hB hodd (by rw [← hgAB]; exact pow_orderOf_eq_one z)

end G2

end CFSG.RankThree.PartOne
