module

public import CFSG.LocalAnalysis.StandardType.GGHypSix
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace HypSixTypeA

section Perfect

variable {S G : Type*} [Group S] [Group G]

theorem eq_of_inv_mul_comm (hperf : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤) {H : Subgroup G}
    (φ₁ φ₂ : S →* G) (h₁ : ∀ y, φ₁ y ∈ H) (h₂ : ∀ y, φ₂ y ∈ H)
    (hc : ∀ y, ∀ k ∈ H, (φ₁ y)⁻¹ * φ₂ y * k = k * ((φ₁ y)⁻¹ * φ₂ y)) : φ₁ = φ₂ := by
  have hmul : ∀ a b, (φ₁ (a * b))⁻¹ * φ₂ (a * b) =
      (φ₁ a)⁻¹ * φ₂ a * ((φ₁ b)⁻¹ * φ₂ b) := by
    intro a b
    have h := hc a (φ₁ b)⁻¹ (H.inv_mem (h₁ b))
    rw [map_mul, map_mul, _root_.mul_inv_rev]
    calc (φ₁ b)⁻¹ * (φ₁ a)⁻¹ * (φ₂ a * φ₂ b) = (φ₁ b)⁻¹ * ((φ₁ a)⁻¹ * φ₂ a) * φ₂ b := by group
      _ = (φ₁ a)⁻¹ * φ₂ a * (φ₁ b)⁻¹ * φ₂ b := by rw [h]
      _ = _ := by group
  let χ : S →* G := MonoidHom.mk' (fun y => (φ₁ y)⁻¹ * φ₂ y) hmul
  have hker : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ ≤ χ.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc a _ (H.mul_mem (H.inv_mem (h₁ b)) (h₂ b))
  ext y
  have hy : χ y = 1 := hker (by rw [hperf]; exact Subgroup.mem_top y)
  exact inv_mul_eq_one.mp hy

theorem mem_center_of_comm_mem_center (hperf : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤) {a : S}
    (ha : ∀ y : S, y⁻¹ * (a * y * a⁻¹) ∈ Subgroup.center S) : a ∈ Subgroup.center S := by
  have h := eq_of_inv_mul_comm hperf (H := ⊤) (MonoidHom.id S) (MulAut.conj a).toMonoidHom
    (fun _ => Subgroup.mem_top _) (fun _ => Subgroup.mem_top _)
    (fun y k _ => ((Subgroup.mem_center_iff.mp (ha y)) k).symm)
  rw [Subgroup.mem_center_iff]
  intro y
  have hy := congrArg (fun φ : S →* S => φ y) h
  simp only [MonoidHom.id_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hy
  calc y * a = a * y * a⁻¹ * a := by rw [← hy]
    _ = a * y := by group

end Perfect

section Lift

variable {n : ℕ} {F : Type*} [Field F] {G : Type*} [Group G]
  {ψ : SpecialLinearGroup (Fin n) F →* G}

theorem proj_eq_of_psi_eq (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F))
    {y₁ y₂ : SpecialLinearGroup (Fin n) F} (h : ψ y₁ = ψ y₂) : proj n F y₁ = proj n F y₂ := by
  rw [proj_eq_proj_iff, scalars_eq_center]
  apply hker
  rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]

theorem exists_conj_preimage {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (y : SpecialLinearGroup (Fin n) F) : ∃ y', ψ y' = c⁻¹ * ψ y * c := by
  have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hc) (ψ y)).mp ⟨y, rfl⟩
  rw [inv_inv] at h
  exact h

theorem exists_projAut [Finite F] (hn : 3 ≤ n)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F)) {c : G}
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ∃ α : MulAut (projectiveSL n F), ∀ y y' : SpecialLinearGroup (Fin n) F,
      ψ y' = c⁻¹ * ψ y * c → α (proj n F y) = proj n F y' := by
  have hperf : ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin n) F)), ⊤⁆ = ⊤ :=
    (CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hn).commutator_eq_top
  choose ρ hρ using exists_conj_preimage hc
  have hmul : ∀ a b, proj n F (ρ (a * b)) = proj n F (ρ a) * proj n F (ρ b) := by
    intro a b
    rw [← map_mul]
    apply proj_eq_of_psi_eq hker
    rw [hρ, map_mul, map_mul, hρ, hρ]
    group
  let ρh : SpecialLinearGroup (Fin n) F →* projectiveSL n F :=
    MonoidHom.mk' (fun y => proj n F (ρ y)) hmul
  have hρh : ∀ y, ρh y = proj n F (ρ y) := fun _ => rfl
  have hrange : ∀ k ∈ ψ.range, ∃ w, k = c⁻¹ * ψ w * c := by
    intro k hk
    obtain ⟨w, hw⟩ := (Subgroup.mem_normalizer_iff.mp hc k).mp hk
    exact ⟨w, by rw [hw]; group⟩
  have hle : scalars n F ≤ ρh.ker := by
    intro z hz
    rw [scalars_eq_center] at hz
    rw [MonoidHom.mem_ker, hρh, proj_eq_one_iff, scalars_eq_center]
    have hcomm : ∀ y, ψ y * ψ (ρ z) = ψ (ρ z) * ψ y := by
      intro y
      obtain ⟨w, hw⟩ := hrange (ψ y) ⟨y, rfl⟩
      have hzw := Subgroup.mem_center_iff.mp hz w
      rw [hw, hρ]
      calc c⁻¹ * ψ w * c * (c⁻¹ * ψ z * c) = c⁻¹ * ψ (w * z) * c := by rw [map_mul]; group
        _ = c⁻¹ * ψ (z * w) * c := by rw [hzw]
        _ = _ := by rw [map_mul]; group
    refine mem_center_of_comm_mem_center hperf fun y => hker ?_
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm y]
    group
  let ρbar : projectiveSL n F →* projectiveSL n F := QuotientGroup.lift (scalars n F) ρh hle
  have hρbar : ∀ y, ρbar (proj n F y) = proj n F (ρ y) := fun y => by
    change QuotientGroup.lift (scalars n F) ρh hle (QuotientGroup.mk y) = _
    rw [QuotientGroup.lift_mk, hρh]
  have hsurj : Function.Surjective ρbar := by
    intro x
    obtain ⟨y', rfl⟩ := proj_surjective n F x
    obtain ⟨y, hy⟩ := (Subgroup.mem_normalizer_iff.mp hc (ψ y')).mp ⟨y', rfl⟩
    refine ⟨proj n F y, ?_⟩
    rw [hρbar]
    apply proj_eq_of_psi_eq hker
    rw [hρ, hy]
    group
  have hinj : Function.Injective ρbar := Finite.injective_iff_surjective.mpr hsurj
  refine ⟨MulEquiv.ofBijective ρbar ⟨hinj, hsurj⟩, fun y y' h => ?_⟩
  change ρbar (proj n F y) = proj n F y'
  rw [hρbar]
  exact proj_eq_of_psi_eq hker ((hρ y).trans h.symm)

theorem projAut_pow_apply (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F))
    {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) {α : MulAut (projectiveSL n F)}
    (hα : ∀ y y' : SpecialLinearGroup (Fin n) F,
      ψ y' = c⁻¹ * ψ y * c → α (proj n F y) = proj n F y') :
    ∀ k : ℕ, ∀ y y' : SpecialLinearGroup (Fin n) F,
      ψ y' = (c ^ k)⁻¹ * ψ y * c ^ k → (α ^ k) (proj n F y) = proj n F y'
  | 0 => fun y y' h => by
      rw [pow_zero, MulAut.one_apply]
      exact proj_eq_of_psi_eq hker (by rw [h]; group)
  | k + 1 => fun y y' h => by
      obtain ⟨y'', hy''⟩ := exists_conj_preimage (Subgroup.pow_mem _ hc k) y
      rw [pow_succ', MulAut.mul_apply, projAut_pow_apply hker hc hα k y y'' hy'']
      apply hα
      rw [h, hy'', pow_succ]
      group

end Lift

section Standard

variable {n : ℕ} {F : Type*} [Field F]

theorem graph_exp_eq_zero [Finite F] (hn : 3 ≤ n) {p : ℕ} (hp : Odd p) {A : GL (Fin n) F}
    {σ : F ≃+* F} {ε : ℕ} (hε : ε ≤ 1)
    (h : (conjAut n F A * fieldAut n F σ * dualAut n F ^ ε) ^ p = 1) : ε = 0 := by
  by_contra hne
  obtain rfl : ε = 1 := by omega
  rw [pow_one] at h
  have htr := standard_automorphism_transport (K := F) (n := n)
  have hδδ : dualAut n F * dualAut n F = 1 := htr.2.2.2.1
  have hE : ∀ (B : GL (Fin n) F) (τ : F ≃+* F),
      conjAut n F B * fieldAut n F τ ∈ semilinearAutGroup n F := fun B τ =>
    mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup B))
      (fieldAut_mem_semilinearAutGroup τ)
  set α := conjAut n F A * fieldAut n F σ * dualAut n F with hα
  have hsq : α ^ 2 ∈ semilinearAutGroup n F := by
    have heq : α ^ 2 = conjAut n F A * fieldAut n F σ *
        ((dualAut n F * conjAut n F A * dualAut n F) *
          (dualAut n F * fieldAut n F σ * dualAut n F)) := by
      calc α ^ 2 = conjAut n F A * fieldAut n F σ * dualAut n F *
            (conjAut n F A * fieldAut n F σ * dualAut n F) := by rw [hα, pow_two]
        _ = conjAut n F A * fieldAut n F σ * (dualAut n F * conjAut n F A *
            (dualAut n F * dualAut n F) * fieldAut n F σ * dualAut n F) := by
          rw [hδδ]; group
        _ = _ := by group
    rw [heq, htr.2.2.2.2.1 A, htr.2.2.2.2.2.1 σ]
    exact mul_mem (hE A σ) (hE _ σ)
  obtain ⟨k, rfl⟩ := hp
  apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := F) hn
  have h1 : (α ^ 2) ^ k * (conjAut n F A * fieldAut n F σ) * dualAut n F = 1 := by
    calc (α ^ 2) ^ k * (conjAut n F A * fieldAut n F σ) * dualAut n F = (α ^ 2) ^ k * α := by
          rw [hα]; group
      _ = α ^ (2 * k + 1) := by rw [pow_succ α (2 * k), pow_mul α 2 k]
      _ = 1 := h
  rw [eq_inv_of_mul_eq_one_right h1]
  exact inv_mem (mul_mem (pow_mem hsq k) (hE A σ))

theorem transvection_mul_self [CharP F 2] {i j : Fin n} (hij : i ≠ j) (t : F) :
    SpecialLinearGroup.transvection hij t * SpecialLinearGroup.transvection hij t = 1 := by
  rw [← SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
    SpecialLinearGroup.transvection_coeff_zero]

theorem eq_one_of_mul_self_eq_one [CharP F 2] {c : F} (h : c * c = 1) : c = 1 := by
  have h2 : (c + 1) * (c + 1) = 0 := by
    calc (c + 1) * (c + 1) = c * c + (c + c) + 1 := by ring
      _ = 0 := by rw [h, CharTwo.add_self_eq_zero, add_zero, CharTwo.add_self_eq_zero]
  have h3 : c + 1 = 0 := mul_self_eq_zero.mp h2
  calc c = c + 1 + 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = 1 := by rw [h3, zero_add]

theorem mul_conj_rel {M : Type*} [Group M] {w a v t s : M}
    (e : w * t * w⁻¹ = a * (v * s * v⁻¹) * a⁻¹) : t * (w⁻¹ * a * v) = w⁻¹ * a * v * s := by
  calc t * (w⁻¹ * a * v) = w⁻¹ * (w * t * w⁻¹) * a * v := by group
    _ = w⁻¹ * (a * (v * s * v⁻¹) * a⁻¹) * a * v := by rw [e]
    _ = w⁻¹ * a * v * s := by group

theorem field_eq_one [CharP F 2] {i j : Fin n} (hij : i ≠ j) {A : GL (Fin n) F} {σ : F ≃+* F}
    {V W : SpecialLinearGroup (Fin n) F}
    (h : ∀ t : F, proj n F (W * SpecialLinearGroup.transvection hij t * W⁻¹) =
      proj n F (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A
        (SpecialLinearGroup.map σ.toRingHom (V * SpecialLinearGroup.transvection hij t * V⁻¹)))) :
    σ = 1 := by
  set c := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A
  set fσ := SpecialLinearGroup.map (n := Fin n) σ.toRingHom
  have hexact : ∀ t, W * SpecialLinearGroup.transvection hij t * W⁻¹ =
      c (fσ (V * SpecialLinearGroup.transvection hij t * V⁻¹)) := by
    intro t
    have hTT := transvection_mul_self hij t
    obtain ⟨X, hX⟩ : ∃ X, X = c (fσ (V * SpecialLinearGroup.transvection hij t * V⁻¹)) :=
      ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y, Y = W * SpecialLinearGroup.transvection hij t * W⁻¹ := ⟨_, rfl⟩
    rw [← hX, ← hY]
    have hXX : X * X = 1 := by
      rw [hX, ← map_mul, ← map_mul]
      have : V * SpecialLinearGroup.transvection hij t * V⁻¹ *
          (V * SpecialLinearGroup.transvection hij t * V⁻¹) = 1 := by
        calc _ = V * (SpecialLinearGroup.transvection hij t *
              SpecialLinearGroup.transvection hij t) * V⁻¹ := by group
          _ = 1 := by rw [hTT, mul_one, mul_inv_cancel]
      rw [this, map_one, map_one]
    have hYY : Y * Y = 1 := by
      rw [hY]
      calc _ = W * (SpecialLinearGroup.transvection hij t *
            SpecialLinearGroup.transvection hij t) * W⁻¹ := by group
        _ = 1 := by rw [hTT, mul_one, mul_inv_cancel]
    have hs : X⁻¹ * Y ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) := by
      rw [← scalars_eq_center, hX, hY]
      exact proj_eq_proj_iff.mp (h t).symm
    have hcomm : X * (X⁻¹ * Y) = X⁻¹ * Y * X := Subgroup.mem_center_iff.mp hs X
    have hss : X⁻¹ * Y * (X⁻¹ * Y) = 1 := by
      calc X⁻¹ * Y * (X⁻¹ * Y) = X * X * (X⁻¹ * Y * (X⁻¹ * Y)) := by rw [hXX, one_mul]
        _ = X * (X * (X⁻¹ * Y)) * (X⁻¹ * Y) := by group
        _ = X * (X⁻¹ * Y * X) * (X⁻¹ * Y) := by rw [hcomm]
        _ = Y * Y := by group
        _ = 1 := hYY
    rw [← scalars_eq_center] at hs
    obtain ⟨a, -, ha⟩ := mem_scalars.mp hs
    have ha1 : (a : F) = 1 := by
      apply eq_one_of_mul_self_eq_one
      have h1 : (X⁻¹ * Y).1 * (X⁻¹ * Y).1 = 1 := congrArg Subtype.val hss
      rw [show (X⁻¹ * Y).1 = scalar (Fin n) (a : F) from ha] at h1
      have h2 := congrFun (congrFun h1 i) i
      simpa [Matrix.scalar_apply, Matrix.one_apply] using h2
    have hs1 : X⁻¹ * Y = 1 := by
      apply Subtype.ext
      rw [ha, ha1, map_one]
      rfl
    exact (inv_mul_eq_one.mp hs1).symm
  have hTN : ∀ t, Matrix.transvection i j t *
      (((SpecialLinearGroup.toGL W)⁻¹ * A * SpecialLinearGroup.toGL (fσ V) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) =
      (((SpecialLinearGroup.toGL W)⁻¹ * A * SpecialLinearGroup.toGL (fσ V) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) * Matrix.transvection i j (σ t) := by
    intro t
    have e := congrArg SpecialLinearGroup.toGL (hexact t)
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation] at e
    simp only [map_mul, map_inv] at e
    have hσT : fσ (SpecialLinearGroup.transvection hij t) =
        SpecialLinearGroup.transvection hij (σ t) :=
      SpecialLinearGroup.map_transvection σ.toRingHom hij t
    rw [hσT] at e
    exact congrArg Units.val (mul_conj_rel e)
  set N := (((SpecialLinearGroup.toGL W)⁻¹ * A * SpecialLinearGroup.toGL (fσ V) : GL (Fin n) F) :
    Matrix (Fin n) (Fin n) F) with hN
  set N' := ((((SpecialLinearGroup.toGL W)⁻¹ * A * SpecialLinearGroup.toGL (fσ V))⁻¹ :
    GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have hNN' : N * N' = 1 := by
    simp only [N, N', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hsingle : ∀ t, Matrix.single i j t * N = N * Matrix.single i j (σ t) := by
    intro t
    have h1 := hTN t
    simp only [Matrix.transvection, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
      Matrix.mul_one] at h1
    exact add_left_cancel h1
  have hE : Matrix.single i j (1 : F) * N = N * Matrix.single i j 1 := by
    simpa using hsingle 1
  have hEN : Matrix.single i j (1 : F) * N ≠ 0 := by
    intro h0
    have h1 : Matrix.single i j (1 : F) = 0 := by
      calc Matrix.single i j (1 : F) = Matrix.single i j 1 * N * N' := by
            rw [Matrix.mul_assoc, hNN', Matrix.mul_one]
        _ = 0 := by rw [h0, Matrix.zero_mul]
    have h2 := congrFun (congrFun h1 i) j
    simp at h2
  have hst : ∀ s : F, Matrix.single i j s = s • Matrix.single i j (1 : F) := fun s => by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  refine RingEquiv.ext fun t => ?_
  show σ t = t
  have h1 := hsingle t
  rw [hst t, hst (σ t), Matrix.smul_mul, Matrix.mul_smul, ← hE] at h1
  have h3 : (t - σ t) • (Matrix.single i j (1 : F) * N) = 0 := by rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact (sub_eq_zero.mp h4).symm
  · exact absurd h4 hEN

end Standard

section Torus

variable {n : ℕ} {F : Type*} [Field F]

theorem diagonal_mul_transvection {e : Fin n → F} (he : ∀ l, e l ≠ 0) {i j : Fin n} (hij : i ≠ j)
    (t : F) : Matrix.diagonal e * Matrix.transvection i j t =
      Matrix.transvection i j (e i * t * (e j)⁻¹) * Matrix.diagonal e := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    have h' : ¬ (i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
    simp [h']
  · by_cases h' : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h'
      simp only [hab, ite_false, and_self, ite_true, zero_add]
      field_simp [he j]
    · simp [hab, h']

theorem gl_diag_conj_transvection {D : GL (Fin n) F} {e : Fin n → F} (he : ∀ l, e l ≠ 0)
    (hD : (D : Matrix (Fin n) (Fin n) F) = Matrix.diagonal e) {i j : Fin n} (hij : i ≠ j)
    (t : F) : D * SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij t) * D⁻¹ =
      SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij (e i * t * (e j)⁻¹)) := by
  have h1 : D * SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij t) =
      SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij (e i * t * (e j)⁻¹)) * D := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hD]
    exact diagonal_mul_transvection he hij t
  rw [h1, mul_inv_cancel_right]

theorem slConjugation_diag_transvection {D : GL (Fin n) F} {e : Fin n → F} (he : ∀ l, e l ≠ 0)
    (hD : (D : Matrix (Fin n) (Fin n) F) = Matrix.diagonal e) {i j : Fin n} (hij : i ≠ j)
    (t : F) : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F D
      (SpecialLinearGroup.transvection hij t) =
      SpecialLinearGroup.transvection hij (e i * t * (e j)⁻¹) := by
  apply SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  exact gl_diag_conj_transvection he hD hij t

theorem sl_diag_conj_transvection {h : SpecialLinearGroup (Fin n) F} {e : Fin n → F}
    (he : ∀ l, e l ≠ 0)
    (hh : ((SpecialLinearGroup.toGL h : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal e) {i j : Fin n} (hij : i ≠ j) (t : F) :
    h * SpecialLinearGroup.transvection hij t * h⁻¹ =
      SpecialLinearGroup.transvection hij (e i * t * (e j)⁻¹) := by
  apply SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, map_inv]
  exact gl_diag_conj_transvection he hh hij t

theorem mem_ggTorus_of_diagonal {m : ℕ} {F : Type} [Field F]
    {h : SpecialLinearGroup (Fin (m + 1)) F} {e : Fin (m + 1) → F} (he : ∀ l, e l ≠ 0)
    (hh : ((SpecialLinearGroup.toGL h : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Matrix.diagonal e) : h ∈ ggTorus (SpecialLinear.rootDatum m F) := by
  simp only [ggTorus, Subgroup.mem_iInf]
  intro γ hγ
  change h ∈ Subgroup.normalizer (SpecialLinear.rootGroup m F γ : Set _)
  rw [SpecialLinear.rootGroup_eq_idx m F hγ, Subgroup.mem_normalizer_iff]
  intro g
  have hij := (SpecialLinear.idx_spec m hγ).1
  constructor
  · intro hg
    obtain ⟨t, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij g).mp hg
    rw [sl_diag_conj_transvection he hh hij t]
    exact SpecialLinear.transvection_mem_rootSubgroup hij _
  · intro hg
    obtain ⟨t, ht⟩ := (SpecialLinear.mem_rootSubgroup hij _).mp hg
    have h2 := sl_diag_conj_transvection he hh hij
      ((e (SpecialLinear.idx m γ).1)⁻¹ * t * e (SpecialLinear.idx m γ).2)
    have h3 : e (SpecialLinear.idx m γ).1 *
        ((e (SpecialLinear.idx m γ).1)⁻¹ * t * e (SpecialLinear.idx m γ).2) *
          (e (SpecialLinear.idx m γ).2)⁻¹ = t := by
      field_simp [he (SpecialLinear.idx m γ).1, he (SpecialLinear.idx m γ).2]
    rw [h3, ht] at h2
    have h4 := mul_left_cancel (mul_right_cancel h2)
    rw [← h4]
    exact SpecialLinear.transvection_mem_rootSubgroup hij _

end Torus

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ} {G : Type*} [Group G]
  {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}

omit [Finite F] [CharP F 2] in
theorem conj_eq_of_conjAut (hm : 2 ≤ m) {c : G}
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) {A D : GL (Fin (m + 1)) F}
    (hα : ∀ y y' : SpecialLinearGroup (Fin (m + 1)) F,
      ψ y' = c⁻¹ * ψ y * c → conjAut (m + 1) F A (proj (m + 1) F y) = proj (m + 1) F y')
    {A₀ : SpecialLinearGroup (Fin (m + 1)) F} (hA₀ : SpecialLinearGroup.toGL A₀ = A * D⁻¹)
    (y : SpecialLinearGroup (Fin (m + 1)) F) :
    (c * ψ A₀)⁻¹ * ψ y * (c * ψ A₀) =
      ψ (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation (m + 1) F D y) := by
  have hn : 3 ≤ m + 1 := by omega
  have hperf : ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin (m + 1)) F)), ⊤⁆ = ⊤ :=
    (CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hn).commutator_eq_top
  set cD := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation (m + 1) F D
  set cA := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation (m + 1) F A
  have hkey : ∀ w, A₀⁻¹ * cA w * A₀ = cD w := by
    intro w
    apply SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, map_inv,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, hA₀]
    group
  have hratio : ∀ w, ∃ s ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F),
      (ψ (cD w))⁻¹ * ((c * ψ A₀)⁻¹ * ψ w * (c * ψ A₀)) = ψ s := by
    intro w
    obtain ⟨w', hw'⟩ := exists_conj_preimage hc w
    have hp' : proj (m + 1) F (cA w) = proj (m + 1) F w' := by
      rw [← conjAut_proj]
      exact hα w w' hw'
    have hs : (cA w)⁻¹ * w' ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F) := by
      rw [← scalars_eq_center]
      exact proj_eq_proj_iff.mp hp'
    obtain ⟨s, hsdef⟩ : ∃ s, s = (cA w)⁻¹ * w' := ⟨_, rfl⟩
    rw [← hsdef] at hs
    have hw's : w' = cA w * s := by rw [hsdef]; group
    have hs' : A₀⁻¹ * s * A₀ = s := by
      rw [mul_assoc, ← Subgroup.mem_center_iff.mp hs A₀, inv_mul_cancel_left]
    refine ⟨s, hs, ?_⟩
    calc (ψ (cD w))⁻¹ * ((c * ψ A₀)⁻¹ * ψ w * (c * ψ A₀)) =
        (ψ (cD w))⁻¹ * ((ψ A₀)⁻¹ * (c⁻¹ * ψ w * c) * ψ A₀) := by group
      _ = ψ ((cD w)⁻¹ * (A₀⁻¹ * w' * A₀)) := by
        rw [← hw', map_mul, map_mul, map_mul, map_inv, map_inv]
      _ = ψ s := by
        rw [← hkey w, hw's]
        congr 1
        calc (A₀⁻¹ * cA w * A₀)⁻¹ * (A₀⁻¹ * (cA w * s) * A₀) = A₀⁻¹ * s * A₀ := by group
          _ = s := hs'
  have heq := eq_of_inv_mul_comm hperf (H := ψ.range) (ψ.comp cD.toMonoidHom)
    ((MulAut.conj (c * ψ A₀)⁻¹).toMonoidHom.comp ψ) (fun w => ⟨_, rfl⟩)
    (fun w => by
      obtain ⟨w', hw'⟩ := exists_conj_preimage hc w
      refine ⟨A₀⁻¹ * w' * A₀, ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [map_mul, map_mul, map_inv, hw']
      group)
    (fun w k hk => by
      obtain ⟨s, hs, hsw⟩ := hratio w
      obtain ⟨v, rfl⟩ := hk
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [hsw, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hs v])
  have h1 := congrArg (fun φ : SpecialLinearGroup (Fin (m + 1)) F →* G => φ y) heq
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
  exact h1.symm

theorem ggPsiInnerDiag_sl (hm : 2 ≤ m)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {p : ℕ} (hp : Odd p)
    {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (hcp : c ^ p ∈ Subgroup.centralizer (ψ.range : Set G)) {γ : Fin m → ℤ}
    (hγ : γ ∈ (SpecialLinear.rootDatum m F).roots) {u : SpecialLinearGroup (Fin (m + 1)) F}
    (hT : GGTorusOnRoot (SpecialLinear.rootDatum m F) ψ c γ u) :
    GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ c := by
  have hn : 3 ≤ m + 1 := by omega
  obtain ⟨α, hα⟩ := exists_projAut hn hker hc
  have hαp : α ^ p = 1 := by
    ext x
    obtain ⟨y, rfl⟩ := proj_surjective (m + 1) F x
    rw [MulAut.one_apply]
    apply projAut_pow_apply hker hc hα p y y
    have hcomm := Subgroup.mem_centralizer_iff.mp hcp (ψ y) ⟨y, rfl⟩
    rw [mul_assoc, hcomm, inv_mul_cancel_left]
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := F) hn).2 α
  have hε0 : ε = 0 := graph_exp_eq_zero hn hp hε (by rw [← hαeq]; exact hαp)
  subst hε0
  rw [pow_zero, mul_one] at hαeq
  obtain ⟨g, ⟨g₀, rfl⟩, h, -, hz⟩ := hT
  have hij : (SpecialLinear.idx m γ).1 ≠ (SpecialLinear.idx m γ).2 :=
    (SpecialLinear.idx_spec m hγ).1
  have hσ : σ = 1 := by
    refine field_eq_one hij (A := A) (V := u) (W := g₀ * u * h) fun t => ?_
    have hzt := hz (SpecialLinearGroup.transvection hij t) (by
      change _ ∈ SpecialLinear.rootGroup m F γ
      rw [SpecialLinear.rootGroup_eq_idx m F hγ]
      exact SpecialLinear.transvection_mem_rootSubgroup hij t)
    have hconj : ψ (g₀ * u * h * SpecialLinearGroup.transvection hij t * (g₀ * u * h)⁻¹) =
        c⁻¹ * ψ (u * SpecialLinearGroup.transvection hij t * u⁻¹) * c := by
      calc ψ (g₀ * u * h * SpecialLinearGroup.transvection hij t * (g₀ * u * h)⁻¹) =
          ψ g₀ * ψ (u * (h * SpecialLinearGroup.transvection hij t * h⁻¹) * u⁻¹) * (ψ g₀)⁻¹ := by
            simp only [map_mul, map_inv]
            group
        _ = ψ g₀ * ((c * ψ g₀)⁻¹ * ψ (u * SpecialLinearGroup.transvection hij t * u⁻¹) *
            (c * ψ g₀)) * (ψ g₀)⁻¹ := by rw [hzt]
        _ = _ := by group
    rw [← hα _ _ hconj, hαeq, MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  rw [hσ, map_one, mul_one] at hαeq
  subst hαeq
  set d : F := (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det with hd
  have hd0 : d ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A
  set e : Fin (m + 1) → F := fun l => if l = 0 then d else 1 with he
  have he0 : ∀ l, e l ≠ 0 := fun l => by
    simp only [e]
    split_ifs
    exacts [hd0, one_ne_zero]
  have hdetD : (Matrix.diagonal e).det = d := by
    rw [Matrix.det_diagonal]
    simp [e]
  set D : GL (Fin (m + 1)) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal e)
    (by rw [hdetD]; exact hd0)
  have hDval : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.diagonal e := rfl
  have hdet1 : Matrix.GeneralLinearGroup.det (A * D⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hDval,
      hdetD]
  obtain ⟨A₀, hA₀⟩ : A * D⁻¹ ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (m + 1)) F →*
      GL (Fin (m + 1)) F).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet1
  have hlift := conj_eq_of_conjAut hm hc hα hA₀
  refine ⟨ψ A₀, ⟨A₀, rfl⟩, fun γ' hγ' => ?_⟩
  have hij' : (SpecialLinear.idx m γ').1 ≠ (SpecialLinear.idx m γ').2 :=
    (SpecialLinear.idx_spec m hγ').1
  set i' := (SpecialLinear.idx m γ').1
  set j' := (SpecialLinear.idx m γ').2
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin (m + 1), k ≠ i' ∧ k ≠ j' := by
    by_contra hcon
    simp only [not_exists] at hcon
    have h0 := hcon ⟨0, by omega⟩
    have h1 := hcon ⟨1, by omega⟩
    have h2 := hcon ⟨2, by omega⟩
    simp only [ne_eq, Fin.ext_iff] at h0 h1 h2
    omega
  set lam : F := e i' * (e j')⁻¹
  have hlam : lam ≠ 0 := mul_ne_zero (he0 i') (inv_ne_zero (he0 j'))
  set e' : Fin (m + 1) → F := fun l => (if l = i' then lam else 1) * (if l = k then lam⁻¹ else 1)
  have he'0 : ∀ l, e' l ≠ 0 := fun l => by
    simp only [e']
    refine mul_ne_zero ?_ ?_ <;> split_ifs
    exacts [hlam, one_ne_zero, inv_ne_zero hlam, one_ne_zero]
  have hdet' : (Matrix.diagonal e').det = 1 := by
    rw [Matrix.det_diagonal]
    simp only [e', Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    exact mul_inv_cancel₀ hlam
  refine ⟨⟨Matrix.diagonal e', hdet'⟩, mem_ggTorus_of_diagonal he'0 rfl, fun z hz => ?_⟩
  change z ∈ SpecialLinear.rootGroup m F γ' at hz
  rw [SpecialLinear.rootGroup_eq_idx m F hγ'] at hz
  obtain ⟨t, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij' z).mp hz
  rw [hlift, slConjugation_diag_transvection he0 hDval hij' t,
    sl_diag_conj_transvection (h := ⟨Matrix.diagonal e', hdet'⟩) he'0 rfl hij' t]
  congr 2
  have hei : e' i' = lam := by simp [e', Ne.symm hki]
  have hej : e' j' = 1 := by simp [e', Ne.symm hij', Ne.symm hkj]
  rw [hei, hej]
  simp only [lam]
  ring

end Main

end HypSixTypeA

section Family

theorem ggRootDetect_psl : GGRootDetect .PSL := by
  intro G _ _ n f ψ hadm hrk hker p hp hp2 _ c hc hcp γ hγ u hT
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  exact HypSixTypeA.ggPsiInnerDiag_sl (F := GaloisField 2 f) hrk hker (hp.odd_of_ne_two hp2) hc
    hcp hγ hT

end Family

end CFSG.StandardType
