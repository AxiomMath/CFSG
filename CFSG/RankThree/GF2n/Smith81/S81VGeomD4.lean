module

public import CFSG.RankThree.GF2n.Smith81.S81VGeomD2b
public import CFSG.RankThree.GF2n.Smith81.S81VGeomD3c
public import CFSG.RankThree.GF2n.Smith81.S81VGeomE

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] {σ : F ≃+* F} {a b : Fin 3 → Fin 6 → F} {θ : F}

private theorem d4_herm_ba (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (i j : Fin 3) :
    herm σ (b i) (a j) = if i = j then 1 else 0 := by
  rw [herm_conj σ hσ (a j) (b i), hf.ab j i]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

private theorem d4_theta_ne (hσ : ∀ c, σ (σ c) = c) (hθ : θ + σ θ ≠ 0) :
    θ ≠ 0 ∧ σ θ ≠ 0 := by
  constructor
  · intro h
    apply hθ
    rw [h, map_zero, add_zero]
  · intro h
    apply hθ
    rw [h, add_zero, ← hσ θ, h, map_zero]

private theorem d4_herm_rr_right (x : Fin 6 → F) :
    herm σ x (rr a b θ) =
      herm σ x (a 0) + θ * herm σ x (b 0) + herm σ x (a 2) + θ * herm σ x (b 2) := by
  simp only [rr, herm_add_right, herm_smul_right]

private theorem d4_herm_rr_left (y : Fin 6 → F) :
    herm σ (rr a b θ) y =
      herm σ (a 0) y + σ θ * herm σ (b 0) y + herm σ (a 2) y + σ θ * herm σ (b 2) y := by
  simp only [rr, herm_add_left, herm_smul_left]

private theorem d4_herm_lc2 (x u v : Fin 6 → F) (α β : F) :
    herm σ x (α • u + β • v) = α * herm σ x u + β * herm σ x v := by
  simp only [herm_add_right, herm_smul_right]

private theorem d4_herm_lc3 (x u v w : Fin 6 → F) (α β γ : F) :
    herm σ x (α • u + β • v + γ • w) = α * herm σ x u + β * herm σ x v + γ * herm σ x w := by
  simp only [herm_add_right, herm_smul_right]

private theorem d4_rr_self [CharP F 2] (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) :
    herm σ (rr a b θ) (rr a b θ) = 0 := by
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  have hba := d4_herm_ba hσ hf
  rw [d4_herm_rr_right]
  simp only [d4_herm_rr_left]
  simp [hf.aa, hf.bb, hf.ab, hba]
  linear_combination (σ θ + θ) * two

private theorem d4_v3_self [CharP F 2] (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) :
    herm σ (v3 a b θ) (v3 a b θ) = 0 := by
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  have hba := d4_herm_ba hσ hf
  simp [v3, herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hf.aa, hf.bb,
    hf.ab, hba]
  linear_combination (σ θ + θ) * two

theorem X3_facts [CharP F 2] (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (hθ : θ + σ θ ≠ 0) :
    IsPt σ (Submodule.span F {b 1, rr a b θ, b 0 + b 2}) ∧
    IsPt σ (Submodule.span F {b 1, rr a b θ, a 0 + σ θ • b 2}) ∧
    Submodule.span F {b 1, rr a b θ, b 0 + b 2} ≠ Submodule.span F {b 1, rr a b θ, a 0 + σ θ • b 2} ∧
    LinearIndependent F ![b 1, rr a b θ] := by
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨-, hσθ0⟩ := d4_theta_ne hσ hθ
  have hba := d4_herm_ba hσ hf
  have hA1B1 : herm σ (a 1) (b 1) = 1 := by simp [hf.ab]
  have hA1r : herm σ (a 1) (rr a b θ) = 0 := by simp [d4_herm_rr_right, hf.aa, hf.ab]
  have hA1c1 : herm σ (a 1) (b 0 + b 2) = 0 := by simp [hf.ab]
  have hA1c2 : herm σ (a 1) (a 0 + σ θ • b 2) = 0 := by simp [hf.aa, hf.ab]
  have hA0B1 : herm σ (a 0) (b 1) = 0 := by simp [hf.ab]
  have hA0r : herm σ (a 0) (rr a b θ) = θ := by simp [d4_herm_rr_right, hf.aa, hf.ab]
  have hA0c1 : herm σ (a 0) (b 0 + b 2) = 1 := by simp [hf.ab]
  have hA0c2 : herm σ (a 0) (a 0 + σ θ • b 2) = 0 := by simp [hf.aa, hf.ab]
  have hA2B1 : herm σ (a 2) (b 1) = 0 := by simp [hf.ab]
  have hA2r : herm σ (a 2) (rr a b θ) = θ := by simp [d4_herm_rr_right, hf.aa, hf.ab]
  have hA2c1 : herm σ (a 2) (b 0 + b 2) = 1 := by simp [hf.ab]
  have hA2c2 : herm σ (a 2) (a 0 + σ θ • b 2) = σ θ := by simp [hf.aa, hf.ab]
  have hB0B1 : herm σ (b 0) (b 1) = 0 := by simp [hf.bb]
  have hB0r : herm σ (b 0) (rr a b θ) = 1 := by simp [d4_herm_rr_right, hf.bb, hba]
  have hB0c1 : herm σ (b 0) (b 0 + b 2) = 0 := by simp [hf.bb]
  have hB0c2 : herm σ (b 0) (a 0 + σ θ • b 2) = 1 := by simp [hf.bb, hba]
  have hB1r : herm σ (b 1) (rr a b θ) = 0 := by simp [d4_herm_rr_right, hf.bb, hba]
  have hB1c1 : herm σ (b 1) (b 0 + b 2) = 0 := by simp [hf.bb]
  have hB1c2 : herm σ (b 1) (a 0 + σ θ • b 2) = 0 := by simp [hf.bb, hba]
  have hB2B1 : herm σ (b 2) (b 1) = 0 := by simp [hf.bb]
  have hB2r : herm σ (b 2) (rr a b θ) = 1 := by simp [d4_herm_rr_right, hf.bb, hba]
  have hB2c2 : herm σ (b 2) (a 0 + σ θ • b 2) = 0 := by simp [hf.bb, hba]
  have hrB0 : herm σ (rr a b θ) (b 0) = 1 := by simp [d4_herm_rr_left, hf.bb, hf.ab, hba]
  have hrB2 : herm σ (rr a b θ) (b 2) = 1 := by simp [d4_herm_rr_left, hf.bb, hf.ab, hba]
  have hrA0 : herm σ (rr a b θ) (a 0) = σ θ := by simp [d4_herm_rr_left, hf.aa, hf.bb, hba]
  have hrr : herm σ (rr a b θ) (rr a b θ) = 0 := d4_rr_self hσ hf
  have hrc1 : herm σ (rr a b θ) (b 0 + b 2) = 0 := by
    rw [herm_add_right, hrB0, hrB2]
    linear_combination two
  have hrc2 : herm σ (rr a b θ) (a 0 + σ θ • b 2) = 0 := by
    rw [herm_add_right, herm_smul_right, hrA0, hrB2]
    linear_combination (σ θ) * two
  have hc1c1 : herm σ (b 0 + b 2) (b 0 + b 2) = 0 := by
    simp [herm_add_left, herm_add_right, hf.bb]
  have hc2c2 : herm σ (a 0 + σ θ • b 2) (a 0 + σ θ • b 2) = 0 := by
    simp [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hσ, hf.aa, hf.bb,
      hf.ab, hba]
  have hli1 : LinearIndependent F ![b 1, rr a b θ, b 0 + b 2] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons] at hg
    have e1 : g 0 = 0 := by
      have h := congrArg (herm σ (a 1)) hg
      rw [d4_herm_lc3, hA1B1, hA1r, hA1c1, herm_zero_right] at h
      linear_combination h
    have e2 : g 1 = 0 := by
      have h := congrArg (herm σ (b 0)) hg
      rw [d4_herm_lc3, hB0B1, hB0r, hB0c1, herm_zero_right] at h
      linear_combination h
    have e3 : g 2 = 0 := by
      have h := congrArg (herm σ (a 0)) hg
      rw [d4_herm_lc3, hA0B1, hA0r, hA0c1, herm_zero_right] at h
      linear_combination h - θ * e2
    intro i
    fin_cases i
    exacts [e1, e2, e3]
  have hli2 : LinearIndependent F ![b 1, rr a b θ, a 0 + σ θ • b 2] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons] at hg
    have e1 : g 0 = 0 := by
      have h := congrArg (herm σ (a 1)) hg
      rw [d4_herm_lc3, hA1B1, hA1r, hA1c2, herm_zero_right] at h
      linear_combination h
    have e2 : g 1 = 0 := by
      have h := congrArg (herm σ (b 2)) hg
      rw [d4_herm_lc3, hB2B1, hB2r, hB2c2, herm_zero_right] at h
      linear_combination h
    have e3 : g 2 = 0 := by
      have h := congrArg (herm σ (b 0)) hg
      rw [d4_herm_lc3, hB0B1, hB0r, hB0c2, herm_zero_right] at h
      linear_combination h - e2
    intro i
    fin_cases i
    exacts [e1, e2, e3]
  have hli : LinearIndependent F ![b 1, rr a b θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 : s = 0 := by
      have h := congrArg (herm σ (a 1)) hst
      rw [d4_herm_lc2, hA1B1, hA1r, herm_zero_right] at h
      linear_combination h
    have e2 : t = 0 := by
      have h := congrArg (herm σ (b 0)) hst
      rw [d4_herm_lc2, hB0B1, hB0r, herm_zero_right] at h
      linear_combination h
    exact ⟨e1, e2⟩
  have hI1 : IsPt σ (Submodule.span F {b 1, rr a b θ, b 0 + b 2}) :=
    isPt_span_triple hσ (hf.bb 1 1) hrr hc1c1 hB1r hB1c1 hrc1 hli1
  have hI2 : IsPt σ (Submodule.span F {b 1, rr a b θ, a 0 + σ θ • b 2}) :=
    isPt_span_triple hσ (hf.bb 1 1) hrr hc2c2 hB1r hB1c2 hrc2 hli2
  have hne : Submodule.span F {b 1, rr a b θ, b 0 + b 2} ≠
      Submodule.span F {b 1, rr a b θ, a 0 + σ θ • b 2} := by
    intro heq
    have hmem : b 0 + b 2 ∈ Submodule.span F {b 1, rr a b θ, a 0 + σ θ • b 2} := by
      rw [← heq]
      exact Submodule.subset_span (by simp)
    obtain ⟨α, β, γ, hcomb⟩ := Submodule.mem_span_triple.mp hmem
    have q2 := congrArg (herm σ (b 0)) hcomb
    have q3 := congrArg (herm σ (a 0)) hcomb
    have q4 := congrArg (herm σ (a 2)) hcomb
    rw [d4_herm_lc3, hB0B1, hB0r, hB0c2, hB0c1] at q2
    rw [d4_herm_lc3, hA0B1, hA0r, hA0c2, hA0c1] at q3
    rw [d4_herm_lc3, hA2B1, hA2r, hA2c2, hA2c1] at q4
    have hβθ : β * θ = 1 := by linear_combination q3
    have hβγ : β + γ = 0 := by linear_combination q2
    have hγσ : γ * σ θ = 0 := by linear_combination q4 - q3
    have hβσ : β * σ θ = 0 := by linear_combination (-1 : F) * hγσ + σ θ * hβγ
    rcases mul_eq_zero.mp hβσ with h | h
    · rw [h, zero_mul] at hβθ
      exact zero_ne_one hβθ
    · exact hσθ0 h
  exact ⟨hI1, hI2, hne, hli⟩

private theorem d4_sub_R0 :
    recipeSet σ (a 0) (a 1) (b 1) (a 2) (b 2) θ ⊆ genSet σ a b θ := by
  intro W hW
  exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ hW))

private theorem d4_sub_R1 :
    recipeSet σ (b 0) (a 1) (b 1) (a 2) (b 2) θ ⊆ genSet σ a b θ := by
  intro W hW
  exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ hW))

private theorem d4_sub_R2 :
    recipeSet σ (v3 a b θ) (a 2) (b 2) (a 0 + a 1) (b 1 + (σ θ)⁻¹ • a 0) θ ⊆
      genSet σ a b θ := by
  intro W hW
  exact Set.mem_union_left _ (Set.mem_union_right _ hW)

private theorem d4_mem_X3_1 :
    Submodule.span F {b 1, rr a b θ, b 0 + b 2} ∈ genSet σ a b θ :=
  Set.mem_union_right _ (Set.mem_insert _ _)

private theorem d4_mem_X3_2 :
    Submodule.span F {b 1, rr a b θ, a 0 + σ θ • b 2} ∈ genSet σ a b θ :=
  Set.mem_union_right _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))

private theorem d4_PU_facts [CharP F 2] (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b)
    (hθ : θ + σ θ ≠ 0) :
    (∀ u ∈ PU a b θ, herm σ (b 1) u = 0) ∧ herm σ (rr a b θ) (rr a b θ) = 0 ∧
      LinearIndependent F ![a 0, b 0, rr a b θ] := by
  obtain ⟨hθ0, -⟩ := d4_theta_ne hσ hθ
  have hba := d4_herm_ba hσ hf
  refine ⟨?_, d4_rr_self hσ hf, ?_⟩
  · intro u hu
    have hle : PU a b θ ≤ LinearMap.ker (hermL σ (b 1)) := by
      unfold PU
      rw [Submodule.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · simp [LinearMap.mem_ker, hba]
      · simp [LinearMap.mem_ker, hf.bb]
      · simp [LinearMap.mem_ker, d4_herm_rr_right, hba, hf.bb]
    have h := LinearMap.mem_ker.mp (hle hu)
    rwa [hermL_apply] at h
  · have hA0A0 : herm σ (a 0) (a 0) = 0 := hf.aa 0 0
    have hA0B0 : herm σ (a 0) (b 0) = 1 := by simp [hf.ab]
    have hA0r : herm σ (a 0) (rr a b θ) = θ := by simp [d4_herm_rr_right, hf.aa, hf.ab]
    have hB0A0 : herm σ (b 0) (a 0) = 1 := by simp [hba]
    have hB0B0 : herm σ (b 0) (b 0) = 0 := hf.bb 0 0
    have hB0r : herm σ (b 0) (rr a b θ) = 1 := by simp [d4_herm_rr_right, hf.bb, hba]
    have hA2A0 : herm σ (a 2) (a 0) = 0 := hf.aa 2 0
    have hA2B0 : herm σ (a 2) (b 0) = 0 := by simp [hf.ab]
    have hA2r : herm σ (a 2) (rr a b θ) = θ := by simp [d4_herm_rr_right, hf.aa, hf.ab]
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons] at hg
    have e3 : g 2 = 0 := by
      have h := congrArg (herm σ (a 2)) hg
      rw [d4_herm_lc3, hA2A0, hA2B0, hA2r, herm_zero_right] at h
      have h' : g 2 * θ = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_right hθ0
    have e1 : g 0 = 0 := by
      have h := congrArg (herm σ (b 0)) hg
      rw [d4_herm_lc3, hB0A0, hB0B0, hB0r, herm_zero_right] at h
      linear_combination h - e3
    have e2 : g 1 = 0 := by
      have h := congrArg (herm σ (a 0)) hg
      rw [d4_herm_lc3, hA0A0, hA0B0, hA0r, herm_zero_right] at h
      linear_combination h - θ * e3
    intro i
    fin_cases i
    exacts [e1, e2, e3]

theorem step3 [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ) (hf : Frame σ a b)
    (hθ : θ + σ θ ≠ 0) :
    ∀ G, IsPt σ G → b 1 ∈ G → GenPts σ (genSet σ a b θ) G := by
  obtain ⟨hI1, hI2, hne, hli⟩ := X3_facts hσ.invol hf hθ
  obtain ⟨hUρ, hrr, hindU⟩ := d4_PU_facts hσ.invol hf hθ
  obtain ⟨-, -, -, -, -, -, hPU3, hPUn⟩ := P_data hσ.invol hf hθ
  have hb1 : b 1 ≠ 0 := by
    intro h
    have h1 := hf.ab 1 1
    rw [h, herm_zero_right] at h1
    simp at h1
  have haU : a 0 ∈ PU a b θ := Submodule.subset_span (Set.mem_insert _ _)
  have hbU : b 0 ∈ PU a b θ :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hcU : rr a b θ ∈ PU a b θ :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hx1 : b 1 ∈ Submodule.span F {b 1, rr a b θ, b 0 + b 2} :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hy1 : rr a b θ ∈ Submodule.span F {b 1, rr a b θ, b 0 + b 2} :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hx2 : b 1 ∈ Submodule.span F {b 1, rr a b θ, a 0 + σ θ • b 2} :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hy2 : rr a b θ ∈ Submodule.span F {b 1, rr a b θ, a 0 + σ θ • b 2} :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hGa : ∀ G, IsPt σ G → b 1 ∈ G → a 0 ∈ G → GenPts σ (genSet σ a b θ) G :=
    fun G hG _ hG' =>
      genPts_mono d4_sub_R0 (Recipe.closure hσ (recipe0 hσ.invol hf hθ) G hG hG')
  have hGb : ∀ G, IsPt σ G → b 1 ∈ G → b 0 ∈ G → GenPts σ (genSet σ a b θ) G :=
    fun G hG _ hG' =>
      genPts_mono d4_sub_R1 (Recipe.closure hσ (recipe1 hσ.invol hf hθ) G hG hG')
  have hGc : ∀ G, IsPt σ G → b 1 ∈ G → rr a b θ ∈ G → GenPts σ (genSet σ a b θ) G :=
    genPts_of_two_through hli hI1 hI2 hne hx1 hy1 hx2 hy2 (GenPts.base d4_mem_X3_1)
      (GenPts.base d4_mem_X3_2)
  exact lemmaD hσ hb1 (hf.bb 1 1) hPUn hPU3 hUρ haU hbU hcU (hf.aa 0 0) (hf.bb 0 0) hrr hindU
    hGa hGb hGc

theorem dh5_generated_of_frame [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ)
    (hq : 3 ≤ Nat.card (Fσ σ)) (hf : Frame σ a b) (hθ : θ + σ θ ≠ 0) :
    ∀ G, IsPt σ G → GenPts σ (genSet σ a b θ) G := by
  obtain ⟨hP4, hn4, hP3, hn3, hP2, hn2, -, -⟩ := P_data hσ.invol hf hθ
  obtain ⟨-, hP3P4, hb1P4, hb1P3, ha0P3, hb0P3, hv3P3, hindv⟩ := P_incl hσ.invol hf hθ
  have hperp := P_perp hσ.invol hf hθ
  have ha0 : a 0 ≠ 0 := by
    intro h
    have h1 := hf.ab 0 0
    rw [h, herm_zero_left] at h1
    simp at h1
  have hb0 : b 0 ≠ 0 := by
    intro h
    have h1 := hf.ab 0 0
    rw [h, herm_zero_right] at h1
    simp at h1
  have hb1 : b 1 ≠ 0 := by
    intro h
    have h1 := hf.ab 1 1
    rw [h, herm_zero_right] at h1
    simp at h1
  have hv3 : v3 a b θ ≠ 0 := by
    intro h
    have h1 : herm σ (b 0) (v3 a b θ) = 1 := by
      simp [v3, herm_add_right, herm_smul_right, hf.aa, hf.bb, hf.ab,
        d4_herm_ba hσ.invol hf]
    rw [h, herm_zero_right] at h1
    exact zero_ne_one h1
  have hv3i : herm σ (v3 a b θ) (v3 a b θ) = 0 := d4_v3_self hσ.invol hf
  have memS : ∀ v : Fin 6 → F, v ≠ 0 → herm σ v v = 0 →
      (∀ G, IsPt σ G → v ∈ G → GenPts σ (genSet σ a b θ) G) →
      v ∈ ResSet σ (genSet σ a b θ) (⊥ : Submodule F (Fin 6 → F)) := by
    intro v hv0 hvi hvG
    refine ⟨hv0, hvi, fun r hr => ?_, fun G hG _ hvG' => hvG G hG hvG'⟩
    rw [Submodule.mem_bot] at hr
    rw [hr, herm_zero_left]
  have hS := closedPts_resSet hσ.invol (genSet σ a b θ) (⊥ : Submodule F (Fin 6 → F))
  have haS := memS (a 0) ha0 (hf.aa 0 0)
    (fun G hG hG' => genPts_mono d4_sub_R0 (Recipe.closure hσ (recipe0 hσ.invol hf hθ) G hG hG'))
  have hbS := memS (b 0) hb0 (hf.bb 0 0)
    (fun G hG hG' => genPts_mono d4_sub_R1 (Recipe.closure hσ (recipe1 hσ.invol hf hθ) G hG hG'))
  have hv3S := memS (v3 a b θ) hv3 hv3i
    (fun G hG hG' => genPts_mono d4_sub_R2 (Recipe.closure hσ (recipe2 hσ.invol hf hθ) G hG hG'))
  have hb1S := memS (b 1) hb1 (hf.bb 1 1) (fun G hG hG' => step3 hσ hf hθ G hG hG')
  have hE0 : ∀ z ∈ P3 a b θ, z ≠ 0 → herm σ z z = 0 →
      z ∈ ResSet σ (genSet σ a b θ) (⊥ : Submodule F (Fin 6 → F)) :=
    lemmaA hσ hn3 hP3 hS haS hbS hv3S ha0P3 hb0P3 hv3P3 hindv
  have hE : ∀ z ∈ P4 a b, z ≠ 0 → herm σ z z = 0 →
      z ∈ ResSet σ (genSet σ a b θ) (⊥ : Submodule F (Fin 6 → F)) :=
    lemmaE hσ hq hS hP4 hP3 hP2 hP3P4 hn4 hn3 hn2 hb1S hb1P4 hb1P3 hperp hE0
  intro G hG
  have hGti : IsTotIso σ G := hG.1
  have hGf : finrank F G = 3 := hG.2
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq G (P4 a b)
  have hle : finrank F ↥(G ⊔ P4 a b) ≤ 6 := by
    have h := Submodule.finrank_le (G ⊔ P4 a b)
    rwa [Module.finrank_fin_fun] at h
  have hinf : 1 ≤ finrank F ↥(G ⊓ P4 a b) := by omega
  have hne : G ⊓ P4 a b ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hinf
    omega
  obtain ⟨z, hzmem, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨hzG, hzP4⟩ := Submodule.mem_inf.mp hzmem
  have hzi : herm σ z z = 0 := hGti z hzG z hzG
  obtain ⟨-, -, -, hGen⟩ := hE z hzP4 hz0 hzi
  exact hGen G hG bot_le hzG

end CFSG.RankThree.GF2n.Smith81.S81V
