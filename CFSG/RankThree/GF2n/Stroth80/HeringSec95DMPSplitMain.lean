module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DMPSplitFactor

public section

namespace CFSG.RankThree.GF2n.Stroth80.HS9.MP

open scoped Matrix MatrixGroups
open CFSG.RankThree.GF2n.Stroth80.HS9.M1

section Columns

variable {K : Type} [Field K]

@[expose] def s95s_col0 : Matrix (Fin 2) (Fin 2) K →ₗ[K] (Fin 2 → K) where
  toFun A := fun i => A i 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[expose] def s95s_row0 : Matrix (Fin 2) (Fin 2) K →ₗ[K] (Fin 2 → K) where
  toFun A := fun j => A 0 j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem s95s_col0_apply (A : Matrix (Fin 2) (Fin 2) K) (i : Fin 2) :
    s95s_col0 A i = A i 0 := rfl

theorem s95s_row0_apply (A : Matrix (Fin 2) (Fin 2) K) (j : Fin 2) :
    s95s_row0 A j = A 0 j := rfl

theorem s95s_col0_mul (a : K) (A : Matrix (Fin 2) (Fin 2) K) :
    s95s_col0 (uMat a * A) = uMat a *ᵥ s95s_col0 A := by
  ext i
  simp [s95s_col0_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem s95s_row0_mul (a : K) (A : Matrix (Fin 2) (Fin 2) K) :
    s95s_row0 (A * (uMat a)ᵀ) = uMat a *ᵥ s95s_row0 A := by
  ext j
  simp [s95s_row0_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

@[expose] def s95s_post {W : Type} [AddCommGroup W] [Module K W]
    (f : Matrix (Fin 2) (Fin 2) K →ₗ[K] (Fin 2 → K)) :
    (W →ₗ[K] Matrix (Fin 2) (Fin 2) K) →+ (W →ₗ[K] (Fin 2 → K)) :=
  AddMonoidHom.mk' (fun θ => f ∘ₗ θ) fun _ _ => LinearMap.comp_add _ _ _

theorem s95s_col1_zero [CharP K 2] {A : Matrix (Fin 2) (Fin 2) K}
    (h : A = A * (uMat 1)ᵀ) (i : Fin 2) : A i 1 = 0 := by
  have := congrFun (congrFun h i) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, uMat] at this
  fin_cases i <;> simpa using this

theorem s95s_row1_zero [CharP K 2] {A : Matrix (Fin 2) (Fin 2) K}
    (h : A = uMat 1 * A) (j : Fin 2) : A 1 j = 0 := by
  have := congrFun (congrFun h 0) j
  simp [Matrix.mul_apply, Fin.sum_univ_two, uMat] at this
  fin_cases j <;> simpa using this

end Columns

section Main

theorem step95_structure_of (hF : SL2FactorStatement) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (Act : SL(2, K) × SL(2, K) →* (W ≃ₗ[K] W)) (bw : W →ₗ[K] W →ₗ[K] K)
    (hnd : ∀ w, (∀ w', bw w w' = 0) → w = 0)
    (hinv : ∀ γ w w', bw (Act γ w) (Act γ w') = bw w w')
    (X : Submodule K W)
    (hS1 : ∀ a a' : K, ∀ w, Act (uSL a, uSL a') w - w ∈ X)
    (hS2 : ∀ a a' : K, ∀ x ∈ X, Act (uSL a, uSL a') x = x)
    (hM12 : ∀ w, (∀ a a' : K, Act (uSL a, uSL a') w = w) → w ∈ X)
    (hI5 : ∃ g h : SL(2, K), (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 ∧
      (h : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 ∧
      IsCompl X (X.map ((Act (g, h) : W ≃ₗ[K] W) : W →ₗ[K] W)))
    (hM11 : ∀ w, (∀ γ, Act γ w = w) → w = 0)
    (hP1 : ∃ Θ : AddSubgroup (W →ₗ[K] Matrix (Fin 2) (Fin 2) K),
      (∀ θ ∈ Θ, ∀ (a a' : K) w,
        θ (Act (uSL a, uSL a') w) = uMat a * θ w * (uMat a')ᵀ) ∧
      ∀ x ∈ X, (∀ θ ∈ Θ, θ x = 0) → x = 0) :
    ∃ (Y₁ Y₂ : Type) (_ : AddCommGroup Y₁) (_ : Module K Y₁) (_ : AddCommGroup Y₂)
      (_ : Module K Y₂) (c : W ≃ₗ[K] (Fin 2 → Y₁) × (Fin 2 → Y₂)),
      ∀ γ w, c (Act γ w) = actW (γ.1 : Matrix (Fin 2) (Fin 2) K)
        (γ.2 : Matrix (Fin 2) (Fin 2) K) (c w) := by
  obtain ⟨g, h, hg, hh, hI⟩ := hI5
  obtain ⟨g', h', hg'0, hg'1, hh'0, hh'1, hI'⟩ := s95s_move hS2 hg hh hI
  obtain ⟨Θ, hΘ, hsep⟩ := hP1
  have S₁ := s95s_siegel_u Act X hS1 hS2 hM12
  have S₂ : s95s_Siegel Act (X.map ((Act (1, h') : W ≃ₗ[K] W) : W →ₗ[K] W))
      (Set.range uSL) (Set.range lSL) := by
    have := S₁.conj 1 h'
    rwa [show (fun p : SL(2, K) => 1 * p * 1⁻¹) '' Set.range uSL = Set.range uSL by simp,
      s95s_conj_range_uSL h' hh'0 hh'1] at this
  have S₃ : s95s_Siegel Act (X.map ((Act (g', 1) : W ≃ₗ[K] W) : W →ₗ[K] W))
      (Set.range lSL) (Set.range uSL) := by
    have := S₁.conj g' 1
    rwa [show (fun p : SL(2, K) => 1 * p * 1⁻¹) '' Set.range uSL = Set.range uSL by simp,
      s95s_conj_range_uSL g' hg'0 hg'1] at this
  have S₄ : s95s_Siegel Act (X.map ((Act (g', h') : W ≃ₗ[K] W) : W →ₗ[K] W))
      (Set.range lSL) (Set.range lSL) := by
    have := S₁.conj g' h'
    rwa [s95s_conj_range_uSL g' hg'0 hg'1, s95s_conj_range_uSL h' hh'0 hh'1] at this
  set XA := X.map ((Act (g', h') : W ≃ₗ[K] W) : W →ₗ[K] W) with hXA
  have hC : s95s_Comm Act := s95s_comm_of_four S₁ S₂ S₃ S₄
  have hsup := s95s_sup_eq_top hC bw hnd hinv hM11
  have hinf := s95s_inf_eq_bot hC hM11
  have hsplitX : ∀ x ∈ X, ∃ x₁ x₂, x₁ ∈ s95s_M1 Act ∧ x₁ ∈ X ∧ x₂ ∈ s95s_M2 Act ∧ x₂ ∈ X ∧
      x = x₁ + x₂ := fun x hx => S₁.split hC hsup hx
  have hsplitA : ∀ y ∈ XA, ∃ y₁ y₂, y₁ ∈ s95s_M1 Act ∧ y₁ ∈ XA ∧ y₂ ∈ s95s_M2 Act ∧ y₂ ∈ XA ∧
      y = y₁ + y₂ := fun y hy => S₄.split hC hsup hy
  have hhalf1 := s95s_half hI' hinf hsplitX hsplitA
  have hhalf2 := s95s_half (M₁ := s95s_M2 Act) (M₂ := s95s_M1 Act) hI'
    (by rw [inf_comm]; exact hinf)
    (fun x hx => by
      obtain ⟨x₁, x₂, h1, h2, h3, h4, h5⟩ := hsplitX x hx
      exact ⟨x₂, x₁, h3, h4, h1, h2, by rw [h5, add_comm]⟩)
    (fun y hy => by
      obtain ⟨y₁, y₂, h1, h2, h3, h4, h5⟩ := hsplitA y hy
      exact ⟨y₂, y₁, h3, h4, h1, h2, by rw [h5, add_comm]⟩)
  have hσ₁ : ∀ (g : SL(2, K)), ∀ m ∈ s95s_M1 Act, Act (g, 1) m ∈ s95s_M1 Act := by
    intro g m hm
    have e : Act (g, 1) m = m + (Act (g, 1) m - m) := by abel
    rw [e]
    exact Submodule.add_mem _ hm (s95s_sub_mem_M1 g m)
  have hσ₂ : ∀ (h : SL(2, K)), ∀ m ∈ s95s_M2 Act, Act (1, h) m ∈ s95s_M2 Act := by
    intro h m hm
    have e : Act (1, h) m = m + (Act (1, h) m - m) := by abel
    rw [e]
    exact Submodule.add_mem _ hm (s95s_sub_mem_M2 h m)
  have hC₁ : ∀ m ∈ s95s_M1 Act,
      (∀ g : SL(2, K), (Act.comp (MonoidHom.inl SL(2, K) SL(2, K))) g m = m) → m = 0 := by
    intro m hm hfix
    refine hM11 m fun γ => ?_
    obtain ⟨g, h⟩ := γ
    have hg : Act (g, 1) m = m := hfix g
    rw [s95s_act_pair' Act g h, hg]
    exact s95s_act_snd_of_mem_M1 hC hm h
  have hΘ₁ : ∀ θ ∈ Θ.map (s95s_post (s95s_col0 (K := K))), ∀ a : K, ∀ m ∈ s95s_M1 Act,
      θ ((Act.comp (MonoidHom.inl SL(2, K) SL(2, K))) (uSL a) m) = uMat a *ᵥ θ m := by
    intro θ' hθ' a m hm
    obtain ⟨θ, hθ, rfl⟩ := AddSubgroup.mem_map.1 hθ'
    have h1 := hΘ θ hθ a 0 m
    rw [s95s_uSL_zero, uMat_zero, Matrix.transpose_one, mul_one] at h1
    show s95s_col0 (θ (Act (uSL a, 1) m)) = uMat a *ᵥ s95s_col0 (θ m)
    rw [h1, s95s_col0_mul]
  have hsep₁ : ∀ x ∈ s95s_M1 Act, x ∈ X →
      (∀ θ ∈ Θ.map (s95s_post (s95s_col0 (K := K))), θ x = 0) → x = 0 := by
    intro x hxM hxX hzero
    refine hsep x hxX fun θ hθ => ?_
    have hcol : s95s_col0 (θ x) = 0 := hzero _ (AddSubgroup.mem_map.2 ⟨θ, hθ, rfl⟩)
    have h1 := hΘ θ hθ 0 1 x
    rw [s95s_uSL_zero, s95s_act_snd_of_mem_M1 hC hxM, uMat_zero, one_mul] at h1
    ext i j
    fin_cases j
    · exact congrFun hcol i
    · exact s95s_col1_zero h1 i
  obtain ⟨Y₁, i1, i2, c₁, hc₁⟩ := s95s_factor hF hK (Act.comp (MonoidHom.inl SL(2, K) SL(2, K)))
    (s95s_M1 Act) X XA hσ₁ (fun m _ h1 h2 => Submodule.disjoint_def.1 hI'.disjoint m h1 h2)
    hhalf1
    (fun a => ⟨fun m _ => S₁.mem (uSL a) ⟨a, rfl⟩ 1 S₁.one_mem_right m,
      fun x _ hx => S₁.fix (uSL a) ⟨a, rfl⟩ 1 S₁.one_mem_right x hx⟩)
    (fun b => ⟨fun m _ => S₄.mem (lSL b) ⟨b, rfl⟩ 1 S₄.one_mem_right m,
      fun x _ hx => S₄.fix (lSL b) ⟨b, rfl⟩ 1 S₄.one_mem_right x hx⟩)
    hC₁ _ hΘ₁ hsep₁
  have hC₂ : ∀ m ∈ s95s_M2 Act,
      (∀ h : SL(2, K), (Act.comp (MonoidHom.inr SL(2, K) SL(2, K))) h m = m) → m = 0 := by
    intro m hm hfix
    refine hM11 m fun γ => ?_
    obtain ⟨g, h⟩ := γ
    have hh : Act (1, h) m = m := hfix h
    rw [s95s_act_pair Act g h, hh]
    exact s95s_act_fst_of_mem_M2 hC hm g
  have hΘ₂ : ∀ θ ∈ Θ.map (s95s_post (s95s_row0 (K := K))), ∀ a : K, ∀ m ∈ s95s_M2 Act,
      θ ((Act.comp (MonoidHom.inr SL(2, K) SL(2, K))) (uSL a) m) = uMat a *ᵥ θ m := by
    intro θ' hθ' a m hm
    obtain ⟨θ, hθ, rfl⟩ := AddSubgroup.mem_map.1 hθ'
    have h1 := hΘ θ hθ 0 a m
    rw [s95s_uSL_zero, uMat_zero, one_mul] at h1
    show s95s_row0 (θ (Act (1, uSL a) m)) = uMat a *ᵥ s95s_row0 (θ m)
    rw [h1, s95s_row0_mul]
  have hsep₂ : ∀ x ∈ s95s_M2 Act, x ∈ X →
      (∀ θ ∈ Θ.map (s95s_post (s95s_row0 (K := K))), θ x = 0) → x = 0 := by
    intro x hxM hxX hzero
    refine hsep x hxX fun θ hθ => ?_
    have hrow : s95s_row0 (θ x) = 0 := hzero _ (AddSubgroup.mem_map.2 ⟨θ, hθ, rfl⟩)
    have h1 := hΘ θ hθ 1 0 x
    rw [s95s_uSL_zero, s95s_act_fst_of_mem_M2 hC hxM, uMat_zero, Matrix.transpose_one,
      mul_one] at h1
    ext i j
    fin_cases i
    · exact congrFun hrow j
    · exact s95s_row1_zero h1 j
  obtain ⟨Y₂, j1, j2, c₂, hc₂⟩ := s95s_factor hF hK (Act.comp (MonoidHom.inr SL(2, K) SL(2, K)))
    (s95s_M2 Act) X XA hσ₂ (fun m _ h1 h2 => Submodule.disjoint_def.1 hI'.disjoint m h1 h2)
    hhalf2
    (fun a => ⟨fun m _ => S₁.mem 1 S₁.one_mem_left (uSL a) ⟨a, rfl⟩ m,
      fun x _ hx => S₁.fix 1 S₁.one_mem_left (uSL a) ⟨a, rfl⟩ x hx⟩)
    (fun b => ⟨fun m _ => S₄.mem 1 S₄.one_mem_left (lSL b) ⟨b, rfl⟩ m,
      fun x _ hx => S₄.fix 1 S₄.one_mem_left (lSL b) ⟨b, rfl⟩ x hx⟩)
    hC₂ _ hΘ₂ hsep₂
  have hcompl : IsCompl (s95s_M1 Act) (s95s_M2 Act) :=
    ⟨disjoint_iff.2 hinf, codisjoint_iff.2 hsup⟩
  let e : (↥(s95s_M1 Act) × ↥(s95s_M2 Act)) ≃ₗ[K] W :=
    Submodule.prodEquivOfIsCompl _ _ hcompl
  refine ⟨Y₁, Y₂, i1, i2, j1, j2, e.symm.trans (LinearEquiv.prodCongr c₁ c₂), ?_⟩
  intro γ w
  obtain ⟨⟨m₁, m₂⟩, rfl⟩ := e.surjective w
  have hact : Act γ (e (m₁, m₂)) = e (⟨Act (γ.1, 1) m₁, hσ₁ γ.1 m₁ m₁.2⟩,
      ⟨Act (1, γ.2) m₂, hσ₂ γ.2 m₂ m₂.2⟩) := by
    obtain ⟨g, h⟩ := γ
    have e1 : Act (g, h) (m₁ : W) = Act (g, 1) m₁ := by
      rw [s95s_act_pair Act g h, s95s_act_snd_of_mem_M1 hC m₁.2]
    have e2 : Act (g, h) (m₂ : W) = Act (1, h) m₂ := by
      rw [s95s_act_pair' Act g h, s95s_act_fst_of_mem_M2 hC m₂.2]
    show Act (g, h) ((m₁ : W) + m₂) = Act (g, 1) m₁ + Act (1, h) m₂
    rw [map_add, e1, e2]
  rw [hact]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.prodCongr_apply]
  exact Prod.ext (hc₁ γ.1 m₁) (hc₂ γ.2 m₂)

end Main

end CFSG.RankThree.GF2n.Stroth80.HS9.MP
