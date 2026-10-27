module

public import CFSG.Walter.ReeOrder.Ward.Mult
public import CFSG.Walter.ReeOrder.Ward.BasicSet

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers

namespace WardSetup

variable {G : Type} [Group G] [Fintype G] {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ}
  {IV : Bool} (S : WardSetup G L q e IV)

@[expose] noncomputable def d1 (χ : G → ℂ) : ℤ := S.M χ 1 - e * S.M χ S.W.θ4
@[expose] noncomputable def d2 (χ : G → ℂ) : ℤ := -e * (S.M χ S.W.θ2 + S.M χ S.W.θ4)
@[expose] noncomputable def d3 (χ : G → ℂ) : ℤ := -e * (S.M χ S.W.θ3 + S.M χ S.W.θ4)
@[expose] noncomputable def dR (χ : G → ℂ) (θ : L → ℂ) : ℤ := S.M χ θ
@[expose] noncomputable def dS (χ : G → ℂ) (θ : L → ℂ) : ℤ := S.M χ θ + S.M χ (S.W.sbar θ)

theorem dS_sbar (χ : G → ℂ) {θ : L → ℂ} (hθ : θ ∈ S.W.SFam) :
    S.dS χ (S.W.sbar θ) = S.dS χ θ := by
  simp only [dS, S.W.sbar_sbar θ hθ]
  ring

theorem inner_Φ1 {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) :
    BlocksInnerProduct (S.σ χ) S.W.Φ1 = S.d1 χ := by
  rw [WardL.Φ1, blocksInnerProduct_sub_right, blocksInnerProduct_smul_right, WardL.conj_e,
    S.inner_σ hχ S.W.one_mem, S.inner_σ hχ S.W.θ4_mem, d1]
  push_cast
  ring

theorem inner_Φ2 {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) :
    BlocksInnerProduct (S.σ χ) S.W.Φ2 = S.d2 χ := by
  rw [WardL.Φ2, blocksInnerProduct_smul_right, blocksInnerProduct_add_right, map_neg,
    WardL.conj_e, S.inner_σ hχ S.W.θ2_mem, S.inner_σ hχ S.W.θ4_mem, d2]
  push_cast
  ring

theorem inner_Φ3 {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) :
    BlocksInnerProduct (S.σ χ) S.W.Φ3 = S.d3 χ := by
  rw [WardL.Φ3, blocksInnerProduct_smul_right, blocksInnerProduct_add_right, map_neg,
    WardL.conj_e, S.inner_σ hχ S.W.θ3_mem, S.inner_σ hχ S.W.θ4_mem, d3]
  push_cast
  ring

theorem inner_ΦR {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {θ : L → ℂ} (hθ : θ ∈ S.W.RFam) :
    BlocksInnerProduct (S.σ χ) θ = S.dR χ θ := S.inner_σ hχ (S.W.R_mem hθ)

theorem inner_ΦS {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {θ : L → ℂ} (hθ : θ ∈ S.W.SFam) :
    BlocksInnerProduct (S.σ χ) (S.W.ΦS θ) = S.dS χ θ := by
  rw [WardL.ΦS, blocksInnerProduct_add_right, S.inner_σ hχ (S.W.S_mem hθ),
    S.inner_σ hχ (S.W.S_mem (S.W.sbar_mem θ hθ)), dS]
  push_cast
  ring

omit [Fintype L] in
theorem class_of_conj {Φ : L → ℂ} (h : ∀ g y : L, Φ (g⁻¹ * y * g) = Φ y) :
    BlocksIsClassFunction Φ := by
  intro y g
  have := h g⁻¹ y
  rwa [inv_inv] at this

theorem Φ1_class : BlocksIsClassFunction S.W.Φ1 := class_of_conj S.W.Φ1_conj
theorem Φ2_class : BlocksIsClassFunction S.W.Φ2 := class_of_conj S.W.Φ2_conj
theorem Φ3_class : BlocksIsClassFunction S.W.Φ3 := class_of_conj S.W.Φ3_conj
theorem ΦR_class {θ : L → ℂ} (hθ : θ ∈ S.W.RFam) : BlocksIsClassFunction θ :=
  blocksVChar_isClassFunction (AddSubgroup.subset_closure (S.W.R_mem hθ))
theorem ΦS_class {θ : L → ℂ} (hθ : θ ∈ S.W.SFam) : BlocksIsClassFunction (S.W.ΦS θ) := by
  intro y g
  simp only [WardL.ΦS, Pi.add_apply]
  rw [blocksVChar_isClassFunction (AddSubgroup.subset_closure (S.W.S_mem hθ)),
    blocksVChar_isClassFunction (AddSubgroup.subset_closure (S.W.S_mem (S.W.sbar_mem θ hθ)))]

theorem gram_int {Φ Ψ : L → ℂ} (hΦ : ∀ y : L, Even (orderOf y) → Φ y = 0)
    (hΨ : ∀ y : L, Even (orderOf y) → Ψ y = 0) (hΦc : BlocksIsClassFunction Φ)
    (a b : (G → ℂ) → ℤ)
    (ha : ∀ χ ∈ BlocksIrr G, BlocksInnerProduct (S.σ χ) Φ = a χ)
    (hb : ∀ χ ∈ BlocksIrr G, BlocksInnerProduct (S.σ χ) Ψ = b χ) (c : ℤ)
    (hc : BlocksInnerProduct Ψ Φ = c) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, a χ * b χ = 2 * c := by
  have h := S.gram hΦ hΨ hΦc
  rw [hc] at h
  have h' : ∑ χ ∈ (irreducibles_finite G).toFinset, ((a χ * b χ : ℤ) : ℂ) = ((2 * c : ℤ) : ℂ) := by
    push_cast
    rw [← h]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [Set.Finite.mem_toFinset] at hχ
    rw [ha χ hχ, hb χ hχ, map_intCast]
  exact_mod_cast h'

theorem gram_principal :
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.d1 χ * S.d1 χ = 4 ∧
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.d1 χ * S.d2 χ = 2 ∧
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.d1 χ * S.d3 χ = 2 ∧
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.d2 χ * S.d2 χ = 4 ∧
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.d2 χ * S.d3 χ = 2 ∧
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.d3 χ * S.d3 χ = 4 := by
  obtain ⟨g11, g12, g13, g21, g22, g23, g31, g32, g33⟩ := S.W.gram_principal
  have h1 : ∀ χ ∈ BlocksIrr G, BlocksInnerProduct (S.σ χ) S.W.Φ1 = S.d1 χ :=
    fun _ hχ => S.inner_Φ1 hχ
  have h2 : ∀ χ ∈ BlocksIrr G, BlocksInnerProduct (S.σ χ) S.W.Φ2 = S.d2 χ :=
    fun _ hχ => S.inner_Φ2 hχ
  have h3 : ∀ χ ∈ BlocksIrr G, BlocksInnerProduct (S.σ χ) S.W.Φ3 = S.d3 χ :=
    fun _ hχ => S.inner_Φ3 hχ
  have e1 : ∀ y : L, Even (orderOf y) → S.W.Φ1 y = 0 := fun y hy => S.W.Φ1_even hy
  have e2 : ∀ y : L, Even (orderOf y) → S.W.Φ2 y = 0 := fun y hy => S.W.Φ2_even hy
  have e3 : ∀ y : L, Even (orderOf y) → S.W.Φ3 y = 0 := fun y hy => S.W.Φ3_even hy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := S.gram_int e1 e1 S.Φ1_class S.d1 S.d1 h1 h1 2 (by rw [g11]; norm_num)
    linarith
  · have := S.gram_int e1 e2 S.Φ1_class S.d1 S.d2 h1 h2 1 (by rw [g21]; norm_num)
    linarith
  · have := S.gram_int e1 e3 S.Φ1_class S.d1 S.d3 h1 h3 1 (by rw [g31]; norm_num)
    linarith
  · have := S.gram_int e2 e2 S.Φ2_class S.d2 S.d2 h2 h2 2 (by rw [g22]; norm_num)
    linarith
  · have := S.gram_int e2 e3 S.Φ2_class S.d2 S.d3 h2 h3 1 (by rw [g32]; norm_num)
    linarith
  · have := S.gram_int e3 e3 S.Φ3_class S.d3 S.d3 h3 h3 2 (by rw [g33]; norm_num)
    linarith

theorem hR_inner : ∀ θ ∈ S.W.RFam, ∀ χ ∈ BlocksIrr G, BlocksInnerProduct (S.σ χ) θ = S.dR χ θ :=
  fun _ hθ _ hχ => S.inner_ΦR hχ hθ

theorem hS_inner : ∀ θ ∈ S.W.SFam, ∀ χ ∈ BlocksIrr G,
    BlocksInnerProduct (S.σ χ) (S.W.ΦS θ) = S.dS χ θ :=
  fun _ hθ _ hχ => S.inner_ΦS hχ hθ

theorem gram_principal_R {θ : L → ℂ} (hθ : θ ∈ S.W.RFam) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.d1 χ * S.dR χ θ = 0 ∧
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.d2 χ * S.dR χ θ = 0 ∧
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.d3 χ * S.dR χ θ = 0 := by
  obtain ⟨-, -, -, g1, g2, g3⟩ := S.W.gram_principal_other (Or.inl hθ)
  have hRe : ∀ y : L, Even (orderOf y) → θ y = 0 := fun y hy => S.W.R_even hθ hy
  refine ⟨?_, ?_, ?_⟩
  · have := S.gram_int (fun y hy => S.W.Φ1_even hy) hRe S.Φ1_class S.d1 (S.dR · θ)
      (fun _ hχ => S.inner_Φ1 hχ) (fun χ hχ => S.hR_inner θ hθ χ hχ) 0 (by rw [g1]; simp)
    linarith
  · have := S.gram_int (fun y hy => S.W.Φ2_even hy) hRe S.Φ2_class S.d2 (S.dR · θ)
      (fun _ hχ => S.inner_Φ2 hχ) (fun χ hχ => S.hR_inner θ hθ χ hχ) 0 (by rw [g2]; simp)
    linarith
  · have := S.gram_int (fun y hy => S.W.Φ3_even hy) hRe S.Φ3_class S.d3 (S.dR · θ)
      (fun _ hχ => S.inner_Φ3 hχ) (fun χ hχ => S.hR_inner θ hθ χ hχ) 0 (by rw [g3]; simp)
    linarith

theorem gram_principal_S {θ : L → ℂ} (hθ : θ ∈ S.W.SFam) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.d1 χ * S.dS χ θ = 0 ∧
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.d2 χ * S.dS χ θ = 0 ∧
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.d3 χ * S.dS χ θ = 0 := by
  obtain ⟨-, -, -, g1, g2, g3⟩ := S.W.gram_principal_S hθ
  have hSe : ∀ y : L, Even (orderOf y) → S.W.ΦS θ y = 0 := fun y hy => S.W.ΦS_even hθ hy
  refine ⟨?_, ?_, ?_⟩
  · have := S.gram_int (fun y hy => S.W.Φ1_even hy) hSe S.Φ1_class S.d1 (S.dS · θ)
      (fun _ hχ => S.inner_Φ1 hχ) (fun χ hχ => S.hS_inner θ hθ χ hχ) 0 (by rw [g1]; simp)
    linarith
  · have := S.gram_int (fun y hy => S.W.Φ2_even hy) hSe S.Φ2_class S.d2 (S.dS · θ)
      (fun _ hχ => S.inner_Φ2 hχ) (fun χ hχ => S.hS_inner θ hθ χ hχ) 0 (by rw [g2]; simp)
    linarith
  · have := S.gram_int (fun y hy => S.W.Φ3_even hy) hSe S.Φ3_class S.d3 (S.dS · θ)
      (fun _ hχ => S.inner_Φ3 hχ) (fun χ hχ => S.hS_inner θ hθ χ hχ) 0 (by rw [g3]; simp)
    linarith

theorem gram_R {θ θ' : L → ℂ} (hθ : θ ∈ S.W.RFam) (hθ' : θ' ∈ S.W.RFam) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.dR χ θ * S.dR χ θ' =
      if θ = θ' then 2 else 0 := by
  have := S.gram_int (fun y hy => S.W.R_even hθ hy) (fun y hy => S.W.R_even hθ' hy)
    (S.ΦR_class hθ) (S.dR · θ) (S.dR · θ') (fun χ hχ => S.hR_inner θ hθ χ hχ)
    (fun χ hχ => S.hR_inner θ' hθ' χ hχ) (if θ' = θ then 1 else 0) (by
      rw [S.W.inner_RS (Or.inl hθ') (Or.inl hθ)]
      split_ifs <;> simp)
  rw [this]
  by_cases h : θ = θ'
  · simp [h]
  · simp [h, Ne.symm h]

theorem gram_R_S {θ θ' : L → ℂ} (hθ : θ ∈ S.W.RFam) (hθ' : θ' ∈ S.W.SFam) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.dR χ θ * S.dS χ θ' = 0 := by
  have := S.gram_int (fun y hy => S.W.R_even hθ hy) (fun y hy => S.W.ΦS_even hθ' hy)
    (S.ΦR_class hθ) (S.dR · θ) (S.dS · θ') (fun χ hχ => S.hR_inner θ hθ χ hχ)
    (fun χ hχ => S.hS_inner θ' hθ' χ hχ) 0 (by rw [(S.W.gram_R_S hθ hθ').2]; simp)
  linarith

theorem gram_S {θ θ' : L → ℂ} (hθ : θ ∈ S.W.SFam) (hθ' : θ' ∈ S.W.SFam) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.dS χ θ * S.dS χ θ' =
      if θ' = θ ∨ θ' = S.W.sbar θ then 4 else 0 := by
  have hcond : (θ = θ' ∨ θ = S.W.sbar θ') ↔ (θ' = θ ∨ θ' = S.W.sbar θ) := by
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · right
        rw [h, S.W.sbar_sbar θ' hθ']
    · rintro (h | h)
      · exact Or.inl h.symm
      · right
        rw [h, S.W.sbar_sbar θ hθ]
  have := S.gram_int (fun y hy => S.W.ΦS_even hθ hy) (fun y hy => S.W.ΦS_even hθ' hy)
    (S.ΦS_class hθ) (S.dS · θ) (S.dS · θ') (fun χ hχ => S.hS_inner θ hθ χ hχ)
    (fun χ hχ => S.hS_inner θ' hθ' χ hχ) (if θ' = θ ∨ θ' = S.W.sbar θ then 2 else 0) (by
      rw [S.W.gram_S hθ' hθ, if_congr hcond rfl rfl]
      split_ifs <;> simp)
  rw [this]
  split_ifs <;> simp

theorem orth {Φ : L → ℂ} (d : (G → ℂ) → ℤ)
    (hd : ∀ χ ∈ BlocksIrr G, BlocksInnerProduct (S.σ χ) Φ = d χ) {x : G}
    (hx : Odd (orderOf x)) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, (d χ : ℂ) * starRingEnd ℂ (χ x) = 0 := by
  rw [← S.degree_orth Φ hx]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  rw [Set.Finite.mem_toFinset] at hχ
  rw [hd χ hχ]

theorem sum_S_half {χ : G → ℂ} {y : L} (hy : Odd (orderOf y)) :
    ∑ θ ∈ S.W.SFam, (S.M χ θ : ℂ) * θ y =
      (1 / 2 : ℂ) * ∑ θ ∈ S.W.SFam, (S.dS χ θ : ℂ) * θ y := by
  have hbar : ∑ θ ∈ S.W.SFam, (S.M χ (S.W.sbar θ) : ℂ) * θ y =
      ∑ θ ∈ S.W.SFam, (S.M χ θ : ℂ) * θ y := by
    refine Finset.sum_nbij' S.W.sbar S.W.sbar (fun θ hθ => S.W.sbar_mem θ hθ)
      (fun θ hθ => S.W.sbar_mem θ hθ) (fun θ hθ => S.W.sbar_sbar θ hθ)
      (fun θ hθ => S.W.sbar_sbar θ hθ) ?_
    intro θ hθ
    rw [(S.W.odd_values hy).2 θ hθ]
  have : ∑ θ ∈ S.W.SFam, (S.dS χ θ : ℂ) * θ y =
      ∑ θ ∈ S.W.SFam, (S.M χ θ : ℂ) * θ y + ∑ θ ∈ S.W.SFam, (S.M χ (S.W.sbar θ) : ℂ) * θ y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun θ _ => ?_
    simp only [dS]
    push_cast
    ring
  rw [this, hbar]
  ring

theorem σ_decomp {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {y : L} (hy : Odd (orderOf y)) :
    S.σ χ y = S.d1 χ + S.d2 χ * (-(e : ℂ) * S.W.θ2 y) + S.d3 χ * (-(e : ℂ) * S.W.θ3 y) +
      ∑ θ ∈ S.W.RFam, (S.dR χ θ : ℂ) * θ y +
        (1 / 2 : ℂ) * ∑ θ ∈ S.W.SFam, (S.dS χ θ : ℂ) * θ y := by
  rw [S.σ_expand hχ y, S.W.sum_irr, S.sum_S_half hy, (S.W.odd_values hy).1]
  simp only [d1, d2, d3, dR, Pi.one_apply]
  push_cast
  have he := S.W.e_sq_complex
  linear_combination (-(S.M χ S.W.θ2 : ℂ) * S.W.θ2 y - (S.M χ S.W.θ4 : ℂ) * S.W.θ2 y -
    (S.M χ S.W.θ3 : ℂ) * S.W.θ3 y - (S.M χ S.W.θ4 : ℂ) * S.W.θ3 y) * he

end WardSetup

end CFSG.Walter.Ward
