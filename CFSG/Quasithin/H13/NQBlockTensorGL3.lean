module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Normalizer
public import CFSG.Quasithin.H13.NQBlockResidualSupplement

public section

namespace CFSG.Quasithin.H13.NQBlock

open Matrix Subgroup CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
  CFSG.QuasithinUnique.Setup.Family

@[expose] def axisT : Subgroup GL32 where
  carrier := {g | ∃ b c : ZMod 2, g = unitriGL 0 b c}
  mul_mem' := by
    rintro _ _ ⟨b, c, rfl⟩ ⟨b', c', rfl⟩
    refine ⟨b + b', c + c', Units.ext ?_⟩
    change unitri 0 b c * unitri 0 b' c' = unitri 0 (b + b') (c + c')
    rw [unitri_mul, add_zero, zero_mul, add_zero]
  one_mem' := ⟨0, 0, Units.ext unitri_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨b, c, rfl⟩
    refine ⟨b, c, Units.ext ?_⟩
    change unitri 0 (0 * c + b) c = unitri 0 b c
    rw [zero_mul, zero_add]

theorem axis_pair_T : ∀ M₁ ∈ tinvols, ∀ M₂ ∈ tinvols, M₁ ≠ M₂ → M₁ * M₂ = M₂ * M₁ →
    cntV M₁ M₂ = 4 → (∃ b c : ZMod 2, M₁ = unitri 0 b c) ∧ ∃ b c : ZMod 2, M₂ = unitri 0 b c := by
  decide +kernel

theorem le_axisT {B : Subgroup GL32} (hle : B ≤ sylowT) (hsq : ∀ a ∈ B, a ^ 2 = 1)
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (h4 : Nat.card B = 4)
    (hfix : Nat.card (fixVec3 B) = 4) : B ≤ axisT := by
  classical
  have hB : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h4
    omega
  rcases elemAbelian_cases_T hle hB hsq hcomm with ⟨b, hb, hb1, hgen⟩ |
      ⟨b₁, hb₁, b₂, hb₂, h1, h2, hne, hgen⟩
  · have := card_two hb hb1 hgen
    omega
  · have hfixeq := (fixed_eq_of_gen hb₁ hb₂ (hsq _ hb₁) (hsq _ hb₂) hgen).1
    have hcnt : cntV (b₁ : Mat3) (b₂ : Mat3) = 4 := by
      have := hfix
      rw [hfixeq, natCard_setOf_eq_card_filter] at this
      exact this
    have hm1 := val_mem_tinvols (hle hb₁) (hsq _ hb₁) h1
    have hm2 := val_mem_tinvols (hle hb₂) (hsq _ hb₂) h2
    have hmne : (b₁ : Mat3) ≠ b₂ := fun h => hne (Units.ext h)
    have hmc : (b₁ : Mat3) * b₂ = b₂ * b₁ := by
      rw [← Units.val_mul, ← Units.val_mul, hcomm _ hb₁ _ hb₂]
    obtain ⟨⟨x₁, y₁, hx₁⟩, ⟨x₂, y₂, hx₂⟩⟩ := axis_pair_T _ hm1 _ hm2 hmne hmc hcnt
    have hb₁A : b₁ ∈ axisT := ⟨x₁, y₁, Units.ext hx₁⟩
    have hb₂A : b₂ ∈ axisT := ⟨x₂, y₂, Units.ext hx₂⟩
    intro g hg
    rcases hgen g hg with h | h | h | h <;> rw [h]
    · exact one_mem _
    · exact hb₁A
    · exact hb₂A
    · exact mul_mem hb₁A hb₂A

theorem zmod_two_eq_zero_or_one : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by
  decide

theorem closure_transvecGL_eq_top :
    Subgroup.closure {g : GL32 | ∃ (i j : Fin 3) (h : i ≠ j), g = transvecGL i j h} = ⊤ := by
  classical
  rw [eq_top_iff]
  intro y _
  set S := Subgroup.closure {g : GL32 | ∃ (i j : Fin 3) (h : i ≠ j), g = transvecGL i j h} with hS
  let P : Mat3 → Prop := fun N => ∀ z : GL32, (z : Mat3) = N → z ∈ S
  have hdet : (y : Mat3).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit y)).ne_zero
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero P (y : Mat3) hdet ?_ ?_ ?_ y rfl
  · intro D hD z hz
    have hD1 : ∀ i, D i = 1 := by
      intro i
      refine (zmod_two_eq_zero_or_one (D i)).resolve_left fun h0 => hD ?_
      rw [Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) h0
    have hD1' : Matrix.diagonal D = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, hD1]
      · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    have hz1 : z = 1 := Units.ext (by rw [hz, hD1', Units.val_one])
    rw [hz1]
    exact one_mem S
  · intro t z hz
    rcases zmod_two_eq_zero_or_one t.c with hc | hc
    · have hz1 : z = 1 := Units.ext (by
        rw [hz, Matrix.TransvectionStruct.toMatrix, hc, Matrix.transvection_zero, Units.val_one])
      rw [hz1]
      exact one_mem S
    · refine Subgroup.subset_closure ⟨t.i, t.j, t.hij, Units.ext ?_⟩
      rw [hz, Matrix.TransvectionStruct.toMatrix, hc, transvecGL_val, Matrix.transvection]
  · intro A B hA hB PA PB z hz
    have hAB : z = Matrix.GeneralLinearGroup.mkOfDetNeZero A hA *
        Matrix.GeneralLinearGroup.mkOfDetNeZero B hB :=
      Units.ext (by rw [hz, Units.val_mul]; rfl)
    rw [hAB]
    exact mul_mem (PA _ rfl) (PB _ rfl)

theorem transvec_mulVec_e1 : ∀ i j : Fin 3, j ≠ 0 →
    ((1 : Mat3) + Matrix.single i j 1) *ᵥ (Pi.single 0 1 : Fin 3 → ZMod 2) = Pi.single 0 1 := by
  decide

theorem transvec10_conj_unitri : ∀ b c : ZMod 2,
    ((1 : Mat3) + Matrix.single 1 0 1) * unitri 0 b c * ((1 : Mat3) + Matrix.single 1 0 1) =
      unitri 0 b (b + c) := by
  decide

theorem transvec_commutator :
    ((1 : Mat3) + Matrix.single 2 1 1) * ((1 : Mat3) + Matrix.single 1 0 1) *
        ((1 : Mat3) + Matrix.single 2 1 1) * ((1 : Mat3) + Matrix.single 1 0 1) =
      (1 : Mat3) + Matrix.single 2 0 1 := by
  decide

theorem transvecGL10_mem_normalizer :
    transvecGL 1 0 (by decide) ∈ normalizer (axisT : Set GL32) := by
  have hfwd : ∀ a ∈ axisT, transvecGL 1 0 (by decide) * a * (transvecGL 1 0 (by decide))⁻¹ ∈
      axisT := by
    rintro _ ⟨b, c, rfl⟩
    refine ⟨b, b + c, Units.ext ?_⟩
    rw [transvecGL_inv_val, Units.val_mul, Units.val_mul, transvecGL_val]
    exact transvec10_conj_unitri b c
  exact mem_normalizer_of_conj_mem hfwd fun a ha => by
    have := hfwd a ha
    rw [transvecGL_inv_val] at this ⊢
    exact this

theorem closure_stab_union_normalizer_axisT_eq_top :
    Subgroup.closure ({g : GL32 | (g : Mat3) *ᵥ (Pi.single 0 1 : Fin 3 → ZMod 2) = Pi.single 0 1} ∪
      (normalizer (axisT : Set GL32) : Set GL32)) = ⊤ := by
  set C := Subgroup.closure ({g : GL32 |
    (g : Mat3) *ᵥ (Pi.single 0 1 : Fin 3 → ZMod 2) = Pi.single 0 1} ∪
      (normalizer (axisT : Set GL32) : Set GL32)) with hC
  have hst : ∀ i j : Fin 3, ∀ h : i ≠ j, j ≠ 0 → transvecGL i j h ∈ C := fun i j h hj =>
    Subgroup.subset_closure (Or.inl (by
      change ((transvecGL i j h : GL32) : Mat3) *ᵥ (Pi.single 0 1 : Fin 3 → ZMod 2) =
        Pi.single 0 1
      rw [transvecGL_val]
      exact transvec_mulVec_e1 i j hj))
  have h10 : transvecGL 1 0 (by decide) ∈ C :=
    Subgroup.subset_closure (Or.inr transvecGL10_mem_normalizer)
  have h20 : transvecGL 2 0 (by decide) ∈ C := by
    have e : transvecGL 2 0 (by decide) = transvecGL 2 1 (by decide) * transvecGL 1 0 (by decide) *
        (transvecGL 2 1 (by decide))⁻¹ * (transvecGL 1 0 (by decide))⁻¹ := by
      apply Units.ext
      rw [transvecGL_inv_val, transvecGL_inv_val, Units.val_mul, Units.val_mul, Units.val_mul,
        transvecGL_val, transvecGL_val, transvecGL_val]
      exact transvec_commutator.symm
    rw [e]
    exact mul_mem (mul_mem (mul_mem (hst 2 1 (by decide) (by decide)) h10)
      (inv_mem (hst 2 1 (by decide) (by decide)))) (inv_mem h10)
  rw [eq_top_iff, ← closure_transvecGL_eq_top, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, rfl⟩
  by_cases hj : j = 0
  · subst hj
    fin_cases i
    · exact absurd rfl hij
    · exact h10
    · exact h20
  · exact hst i j hij hj

theorem row_eq_zero_of_fixed_sylowT {Pm : Mat3} (h : ∀ g ∈ sylowT, (g : Mat3) * Pm = Pm)
    (i j : Fin 3) (hi : i ≠ 0) : Pm i j = 0 := by
  have h1 := congrFun (congrFun (h (unitriGL 1 0 0) ⟨1, 0, 0, rfl⟩) 0) j
  have h2 := congrFun (congrFun (h (unitriGL 0 0 1) ⟨0, 0, 1, rfl⟩) 1) j
  change (unitri 1 0 0 * Pm) 0 j = Pm 0 j at h1
  change (unitri 0 0 1 * Pm) 1 j = Pm 1 j at h2
  simp [unitri, Matrix.mul_apply, Fin.sum_univ_three] at h1 h2
  have h1' : Pm 1 j = 0 := h1
  have h2' : Pm 2 j = 0 := h2
  fin_cases i
  · exact absurd rfl hi
  · exact h1'
  · exact h2'

theorem mul_eq_of_fixed_sylowT {Pm : Mat3} (h : ∀ g ∈ sylowT, (g : Mat3) * Pm = Pm)
    {g : Mat3} (hg : g *ᵥ (Pi.single 0 1 : Fin 3 → ZMod 2) = Pi.single 0 1) : g * Pm = Pm := by
  have hcol : ∀ i, g i 0 = (Pi.single 0 1 : Fin 3 → ZMod 2) i := fun i => by
    rw [← hg, Matrix.mulVec_single_one]
    rfl
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three, row_eq_zero_of_fixed_sylowT h 1 j (by decide),
    row_eq_zero_of_fixed_sylowT h 2 j (by decide), mul_zero, mul_zero, add_zero, add_zero, hcol]
  fin_cases i
  · simp
  · simp [row_eq_zero_of_fixed_sylowT h 1 j (by decide)]
  · simp [row_eq_zero_of_fixed_sylowT h 2 j (by decide)]

theorem card_fixedMat (B : Subgroup GL32) :
    Nat.card {Pm : Mat3 | ∀ g ∈ B, (g : Mat3) * Pm = Pm} = Nat.card (fixVec3 B) ^ 3 := by
  have e : {Pm : Mat3 | ∀ g ∈ B, (g : Mat3) * Pm = Pm} ≃ (Fin 3 → fixVec3 B) :=
    { toFun := fun Pm j => ⟨fun i => Pm.1 i j, fun g hg => by
        funext i
        have h2 := congrFun (congrFun (Pm.2 g hg) i) j
        rw [Matrix.mul_apply] at h2
        exact h2⟩
      invFun := fun v => ⟨Matrix.of fun i j => (v j).1 i, fun g hg => by
        ext i j
        rw [Matrix.mul_apply]
        exact congrFun ((v j).2 g hg) i⟩
      left_inv := fun Pm => by
        ext i j
        rfl
      right_inv := fun v => by
        funext j
        apply Subtype.ext
        funext i
        rfl }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_fin]

end CFSG.Quasithin.H13.NQBlock
