module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DM1A

public section

namespace CFSG.RankThree.GF2n.Stroth80.HS9.MP

open scoped Matrix MatrixGroups
open CFSG.RankThree.GF2n.Stroth80.HS9.M1

section SL2

variable {K : Type} [Field K]

theorem s95s_uSL_zero : (uSL (0 : K) : SL(2, K)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL, uMat]

theorem s95s_lSL_zero : (lSL (0 : K) : SL(2, K)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lSL, lMat]

theorem s95s_lSL_add (a b : K) : lSL (a + b) = lSL a * lSL b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_lSL, lMat, Matrix.mul_apply, Fin.sum_univ_two,
      add_comm]

theorem s95s_eq_ulu (g : SL(2, K)) (hg : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    g = uSL (((g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) / (g : Matrix (Fin 2) (Fin 2) K) 1 0) *
      lSL ((g : Matrix (Fin 2) (Fin 2) K) 1 0) *
      uSL (((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) / (g : Matrix (Fin 2) (Fin 2) K) 1 0) := by
  have hdet := g.det_coe
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_lSL, uMat, lMat, Matrix.mul_apply,
      Fin.sum_univ_two] <;> field_simp <;>
    first
    | ring1
    | linear_combination -hdet
    | linear_combination hdet

theorem s95s_sl2_induction [CharP K 2] {P : SL(2, K) → Prop} (hu : ∀ a, P (uSL a))
    (hl : ∀ b, P (lSL b)) (hm : ∀ g h, P g → P h → P (g * h)) (g : SL(2, K)) : P g := by
  have key : ∀ g : SL(2, K), (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 → P g := by
    intro g hg
    rw [s95s_eq_ulu g hg]
    exact hm _ _ (hm _ _ (hu _) (hl _)) (hu _)
  by_cases h : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · have h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
      intro h0
      have hdet := g.det_coe
      rw [Matrix.det_fin_two, h0, h] at hdet
      simp at hdet
    have e : g = lSL 1 * (lSL 1 * g) := by
      rw [← mul_assoc, ← s95s_lSL_add, CharTwo.add_self_eq_zero, s95s_lSL_zero, one_mul]
    rw [e]
    exact hm _ _ (hl 1) (key _ (by simp [Matrix.SpecialLinearGroup.coe_mul, coe_lSL, lMat,
      Matrix.mul_apply, Fin.sum_univ_two, h, h00]))
  · exact key g h

end SL2

section Siegel

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]

theorem s95s_act_mul (Act : SL(2, K) × SL(2, K) →* (W ≃ₗ[K] W)) (γ δ : SL(2, K) × SL(2, K))
    (w : W) : Act (γ * δ) w = Act γ (Act δ w) := by
  rw [map_mul]
  rfl

theorem s95s_act_one (Act : SL(2, K) × SL(2, K) →* (W ≃ₗ[K] W)) (w : W) : Act 1 w = w := by
  rw [map_one]
  rfl

theorem s95s_act_inv_act (Act : SL(2, K) × SL(2, K) →* (W ≃ₗ[K] W)) (γ : SL(2, K) × SL(2, K))
    (w : W) : Act γ⁻¹ (Act γ w) = w := by
  rw [← s95s_act_mul, inv_mul_cancel, s95s_act_one]

theorem s95s_act_act_inv (Act : SL(2, K) × SL(2, K) →* (W ≃ₗ[K] W)) (γ : SL(2, K) × SL(2, K))
    (w : W) : Act γ (Act γ⁻¹ w) = w := by
  rw [← s95s_act_mul, mul_inv_cancel, s95s_act_one]

theorem s95s_act_pair (Act : SL(2, K) × SL(2, K) →* (W ≃ₗ[K] W)) (g h : SL(2, K)) (w : W) :
    Act (g, h) w = Act (g, 1) (Act (1, h) w) := by
  rw [← s95s_act_mul]
  simp

theorem s95s_act_pair' (Act : SL(2, K) × SL(2, K) →* (W ≃ₗ[K] W)) (g h : SL(2, K)) (w : W) :
    Act (g, h) w = Act (1, h) (Act (g, 1) w) := by
  rw [← s95s_act_mul]
  simp

structure s95s_Siegel (Act : SL(2, K) × SL(2, K) →* (W ≃ₗ[K] W)) (X : Submodule K W)
    (P Q : Set SL(2, K)) : Prop where
  one_mem_left : (1 : SL(2, K)) ∈ P
  one_mem_right : (1 : SL(2, K)) ∈ Q
  mem : ∀ p ∈ P, ∀ q ∈ Q, ∀ w, Act (p, q) w - w ∈ X
  fix : ∀ p ∈ P, ∀ q ∈ Q, ∀ x ∈ X, Act (p, q) x = x
  cent : ∀ w, (∀ p ∈ P, ∀ q ∈ Q, Act (p, q) w = w) → w ∈ X

theorem s95s_siegel_u (Act : SL(2, K) × SL(2, K) →* (W ≃ₗ[K] W)) (X : Submodule K W)
    (hS1 : ∀ a a' : K, ∀ w, Act (uSL a, uSL a') w - w ∈ X)
    (hS2 : ∀ a a' : K, ∀ x ∈ X, Act (uSL a, uSL a') x = x)
    (hM12 : ∀ w, (∀ a a' : K, Act (uSL a, uSL a') w = w) → w ∈ X) :
    s95s_Siegel Act X (Set.range uSL) (Set.range uSL) where
  one_mem_left := ⟨0, s95s_uSL_zero⟩
  one_mem_right := ⟨0, s95s_uSL_zero⟩
  mem := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩ w
    exact hS1 a a' w
  fix := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩ x hx
    exact hS2 a a' x hx
  cent := fun w hw => hM12 w fun a a' => hw _ ⟨a, rfl⟩ _ ⟨a', rfl⟩

variable {Act : SL(2, K) × SL(2, K) →* (W ≃ₗ[K] W)} {X : Submodule K W} {P Q : Set SL(2, K)}

theorem s95s_Siegel.comm_apply (S : s95s_Siegel Act X P Q) {p q : SL(2, K)} (hp : p ∈ P)
    (hq : q ∈ Q) (w : W) : Act (p, q) w = Act (p, 1) w + Act (1, q) w - w := by
  have h1 : Act (1, q) w - w ∈ X := S.mem 1 S.one_mem_left q hq w
  have h2 := S.fix p hp 1 S.one_mem_right _ h1
  rw [map_sub, ← s95s_act_pair] at h2
  have h3 : Act (p, q) w = Act (1, q) w - w + Act (p, 1) w := by
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at h2
    rw [← h2]
    abel
  rw [h3]
  abel

theorem s95s_Siegel.conj (S : s95s_Siegel Act X P Q) (g₀ h₀ : SL(2, K)) :
    s95s_Siegel Act (X.map ((Act (g₀, h₀) : W ≃ₗ[K] W) : W →ₗ[K] W))
      ((fun p => g₀ * p * g₀⁻¹) '' P) ((fun q => h₀ * q * h₀⁻¹) '' Q) := by
  have hconj : ∀ (p q : SL(2, K)) (w : W),
      Act (g₀ * p * g₀⁻¹, h₀ * q * h₀⁻¹) w =
        Act (g₀, h₀) (Act (p, q) (Act (g₀, h₀)⁻¹ w)) := by
    intro p q w
    have e : ((g₀ * p * g₀⁻¹, h₀ * q * h₀⁻¹) : SL(2, K) × SL(2, K)) =
        (g₀, h₀) * (p, q) * (g₀, h₀)⁻¹ := by
      simp
    rw [e, s95s_act_mul, s95s_act_mul]
  refine ⟨⟨1, S.one_mem_left, by simp⟩, ⟨1, S.one_mem_right, by simp⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ w
    refine Submodule.mem_map.2 ⟨Act (p, q) (Act (g₀, h₀)⁻¹ w) - Act (g₀, h₀)⁻¹ w,
      S.mem p hp q hq _, ?_⟩
    simp only [LinearEquiv.coe_coe, map_sub]
    rw [hconj, s95s_act_act_inv]
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ _ hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    simp only [LinearEquiv.coe_coe]
    rw [hconj, s95s_act_inv_act, S.fix p hp q hq x hx]
  · intro w hw
    refine Submodule.mem_map.2 ⟨Act (g₀, h₀)⁻¹ w, S.cent _ fun p hp q hq => ?_,
      s95s_act_act_inv Act _ w⟩
    have h := hw (g₀ * p * g₀⁻¹) ⟨p, hp, rfl⟩ (h₀ * q * h₀⁻¹) ⟨q, hq, rfl⟩
    rw [hconj] at h
    have h' := congrArg (Act (g₀, h₀)⁻¹) h
    rwa [s95s_act_inv_act] at h'

end Siegel

section Comm

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]

theorem s95s_conj_range_uSL [CharP K 2] (g : SL(2, K))
    (h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 0) (h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    (fun p => g * p * g⁻¹) '' Set.range uSL = Set.range lSL := by
  have key : ∀ s : K,
      g * uSL s * g⁻¹ = lSL (s * ((g : Matrix (Fin 2) (Fin 2) K) 1 0) ^ 2) := by
    intro s
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_uSL]
    rw [conj_uMat g s, coe_lSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nilMat, lMat, h00]
  ext x
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨_, (key s).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨_, ⟨b / ((g : Matrix (Fin 2) (Fin 2) K) 1 0) ^ 2, rfl⟩, ?_⟩
    simp only
    rw [key]
    congr 1
    field_simp

@[expose] def s95s_Comm (Act : SL(2, K) × SL(2, K) →* (W ≃ₗ[K] W)) : Prop :=
  ∀ (g h : SL(2, K)) (w : W), Act (g, h) w = Act (g, 1) w + Act (1, h) w - w

theorem s95s_comm_of_four [CharP K 2] {Act : SL(2, K) × SL(2, K) →* (W ≃ₗ[K] W)}
    {X₁ X₂ X₃ X₄ : Submodule K W}
    (S₁ : s95s_Siegel Act X₁ (Set.range uSL) (Set.range uSL))
    (S₂ : s95s_Siegel Act X₂ (Set.range uSL) (Set.range lSL))
    (S₃ : s95s_Siegel Act X₃ (Set.range lSL) (Set.range uSL))
    (S₄ : s95s_Siegel Act X₄ (Set.range lSL) (Set.range lSL)) : s95s_Comm Act := by
  have step1 : ∀ q : SL(2, K), q ∈ Set.range uSL ∨ q ∈ Set.range lSL → ∀ g w,
      Act (g, q) w = Act (g, 1) w + Act (1, q) w - w := by
    intro q hq g
    refine s95s_sl2_induction (P := fun g => ∀ w : W,
      Act (g, q) w = Act (g, 1) w + Act (1, q) w - w) ?_ ?_ ?_ g
    · intro a w
      rcases hq with hq | hq
      · exact S₁.comm_apply ⟨a, rfl⟩ hq w
      · exact S₂.comm_apply ⟨a, rfl⟩ hq w
    · intro b w
      rcases hq with hq | hq
      · exact S₃.comm_apply ⟨b, rfl⟩ hq w
      · exact S₄.comm_apply ⟨b, rfl⟩ hq w
    · intro g₁ g₂ h₁ h₂ w
      have e1 : Act (g₁ * g₂, q) w = Act (g₁, 1) (Act (g₂, q) w) := by
        rw [← s95s_act_mul]
        simp
      have e2 : Act (g₁, 1) (Act (g₂, 1) w) = Act (g₁ * g₂, 1) w := by
        rw [← s95s_act_mul]
        simp
      have e3 : Act (g₁, 1) (Act (1, q) w) = Act (g₁, q) w := (s95s_act_pair Act g₁ q w).symm
      rw [e1, h₂ w, map_sub, map_add, e2, e3, h₁ w]
      abel
  have step2 : ∀ h g w, Act (g, h) w = Act (g, 1) w + Act (1, h) w - w := by
    intro h
    refine s95s_sl2_induction (P := fun h => ∀ (g : SL(2, K)) (w : W),
      Act (g, h) w = Act (g, 1) w + Act (1, h) w - w) ?_ ?_ ?_ h
    · exact fun a g w => step1 _ (Or.inl ⟨a, rfl⟩) g w
    · exact fun b g w => step1 _ (Or.inr ⟨b, rfl⟩) g w
    · intro h₁ h₂ H₁ H₂ g w
      have e1 : Act (g, h₁ * h₂) w = Act (1, h₁) (Act (g, h₂) w) := by
        rw [← s95s_act_mul]
        simp
      have e2 : Act (1, h₁) (Act (1, h₂) w) = Act (1, h₁ * h₂) w := by
        rw [← s95s_act_mul]
        simp
      have e3 : Act (1, h₁) (Act (g, 1) w) = Act (g, h₁) w := (s95s_act_pair' Act g h₁ w).symm
      rw [e1, H₂ g w, map_sub, map_add, e2, e3, H₁ g w]
      abel
  exact fun g h w => step2 h g w

end Comm

section Split

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
  (Act : SL(2, K) × SL(2, K) →* (W ≃ₗ[K] W))

@[expose] def s95s_M1 : Submodule K W :=
  Submodule.span K {v | ∃ (g : SL(2, K)) (w : W), v = Act (g, 1) w - w}

@[expose] def s95s_M2 : Submodule K W :=
  Submodule.span K {v | ∃ (h : SL(2, K)) (w : W), v = Act (1, h) w - w}

variable {Act}

theorem s95s_sub_mem_M1 (g : SL(2, K)) (w : W) : Act (g, 1) w - w ∈ s95s_M1 Act :=
  Submodule.subset_span ⟨g, w, rfl⟩

theorem s95s_sub_mem_M2 (h : SL(2, K)) (w : W) : Act (1, h) w - w ∈ s95s_M2 Act :=
  Submodule.subset_span ⟨h, w, rfl⟩

theorem s95s_act_fst_of_mem_M2 (hC : s95s_Comm Act) {m : W} (hm : m ∈ s95s_M2 Act)
    (g : SL(2, K)) : Act (g, 1) m = m := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, w, rfl⟩ := hx
    rw [map_sub, ← s95s_act_pair, hC g h w]
    abel
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem s95s_act_snd_of_mem_M1 (hC : s95s_Comm Act) {m : W} (hm : m ∈ s95s_M1 Act)
    (h : SL(2, K)) : Act (1, h) m = m := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, w, rfl⟩ := hx
    rw [map_sub, ← s95s_act_pair', hC g h w]
    abel
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem s95s_act_sub_mem (hC : s95s_Comm Act) (γ : SL(2, K) × SL(2, K)) (w : W) :
    Act γ w - w ∈ s95s_M1 Act ⊔ s95s_M2 Act := by
  obtain ⟨g, h⟩ := γ
  have e : Act (g, h) w - w = (Act (g, 1) w - w) + (Act (1, h) w - w) := by
    rw [hC g h w]
    abel
  rw [e]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (s95s_sub_mem_M1 g w))
    (Submodule.mem_sup_right (s95s_sub_mem_M2 h w))

theorem s95s_inf_eq_bot (hC : s95s_Comm Act) (hM11 : ∀ w, (∀ γ, Act γ w = w) → w = 0) :
    s95s_M1 Act ⊓ s95s_M2 Act = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  rw [Submodule.mem_inf] at hm
  rw [Submodule.mem_bot]
  refine hM11 m ?_
  rintro ⟨g, h⟩
  rw [s95s_act_pair, s95s_act_snd_of_mem_M1 hC hm.1, s95s_act_fst_of_mem_M2 hC hm.2]

theorem s95s_sup_eq_top [FiniteDimensional K W] (hC : s95s_Comm Act) (bw : W →ₗ[K] W →ₗ[K] K)
    (hnd : ∀ w, (∀ w', bw w w' = 0) → w = 0)
    (hinv : ∀ γ w w', bw (Act γ w) (Act γ w') = bw w w')
    (hM11 : ∀ w, (∀ γ, Act γ w = w) → w = 0) : s95s_M1 Act ⊔ s95s_M2 Act = ⊤ := by
  set N := s95s_M1 Act ⊔ s95s_M2 Act with hN
  let f : W →ₗ[K] (N →ₗ[K] K) := (LinearMap.lcomp K K N.subtype) ∘ₗ bw
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h0 : ∀ n ∈ N, bw w n = 0 := fun n hn => by
      have := LinearMap.congr_fun hw ⟨n, hn⟩
      simpa [f] using this
    have key : ∀ (γ : SL(2, K) × SL(2, K)) (w' : W), bw w (Act γ w') = bw w w' := by
      intro γ w'
      have := h0 _ (s95s_act_sub_mem hC γ w')
      rw [map_sub] at this
      exact sub_eq_zero.1 this
    refine hM11 w fun γ => ?_
    have h1 : ∀ w', bw (Act γ⁻¹ w - w) w' = 0 := by
      intro w'
      have := hinv γ (Act γ⁻¹ w) w'
      rw [s95s_act_act_inv] at this
      rw [map_sub, LinearMap.sub_apply, ← this, key, sub_self]
    have h2 := sub_eq_zero.1 (hnd _ h1)
    have h3 := congrArg (Act γ) h2
    rw [s95s_act_act_inv] at h3
    exact h3.symm
  have hle : Module.finrank K W ≤ Module.finrank K (N →ₗ[K] K) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have hdual : Module.finrank K (N →ₗ[K] K) = Module.finrank K N := Subspace.dual_finrank_eq
  exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le N) (hdual ▸ hle))

variable {X : Submodule K W} {P Q : Set SL(2, K)}

theorem s95s_Siegel.split (hC : s95s_Comm Act) (hsup : s95s_M1 Act ⊔ s95s_M2 Act = ⊤)
    (S : s95s_Siegel Act X P Q) {x : W} (hx : x ∈ X) :
    ∃ x₁ x₂, x₁ ∈ s95s_M1 Act ∧ x₁ ∈ X ∧ x₂ ∈ s95s_M2 Act ∧ x₂ ∈ X ∧ x = x₁ + x₂ := by
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Submodule.mem_sup.1
    (hsup ▸ Submodule.mem_top : x ∈ s95s_M1 Act ⊔ s95s_M2 Act)
  have h1 : ∀ p ∈ P, Act (p, 1) m₁ = m₁ := by
    intro p hp
    have h := S.fix p hp 1 S.one_mem_right _ hx
    rw [map_add, s95s_act_fst_of_mem_M2 hC hm₂] at h
    exact add_right_cancel h
  have h2 : ∀ q ∈ Q, Act (1, q) m₂ = m₂ := by
    intro q hq
    have h := S.fix 1 S.one_mem_left q hq _ hx
    rw [map_add, s95s_act_snd_of_mem_M1 hC hm₁] at h
    exact add_left_cancel h
  refine ⟨m₁, m₂, hm₁, S.cent m₁ fun p hp q hq => ?_, hm₂, S.cent m₂ fun p hp q hq => ?_, rfl⟩
  · rw [s95s_act_pair' Act p q, h1 p hp, s95s_act_snd_of_mem_M1 hC hm₁]
  · rw [s95s_act_pair Act p q, h2 q hq, s95s_act_fst_of_mem_M2 hC hm₂]

theorem s95s_half {M₁ M₂ X Y : Submodule K W} (hXY : IsCompl X Y) (hM : M₁ ⊓ M₂ = ⊥)
    (hX : ∀ x ∈ X, ∃ x₁ x₂, x₁ ∈ M₁ ∧ x₁ ∈ X ∧ x₂ ∈ M₂ ∧ x₂ ∈ X ∧ x = x₁ + x₂)
    (hY : ∀ y ∈ Y, ∃ y₁ y₂, y₁ ∈ M₁ ∧ y₁ ∈ Y ∧ y₂ ∈ M₂ ∧ y₂ ∈ Y ∧ y = y₁ + y₂) :
    ∀ m ∈ M₁, ∃ x y, x ∈ M₁ ∧ x ∈ X ∧ y ∈ M₁ ∧ y ∈ Y ∧ m = x + y := by
  intro m hm
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1
    (hXY.sup_eq_top ▸ Submodule.mem_top : m ∈ X ⊔ Y)
  obtain ⟨x₁, x₂, hx₁, hx₁X, hx₂, hx₂X, rfl⟩ := hX x hx
  obtain ⟨y₁, y₂, hy₁, hy₁Y, hy₂, hy₂Y, rfl⟩ := hY y hy
  have h1 : x₂ + y₂ ∈ M₁ := by
    have := Submodule.sub_mem _ hm (Submodule.add_mem _ hx₁ hy₁)
    convert this using 1
    abel
  have h2 : x₂ + y₂ ∈ M₁ ⊓ M₂ := Submodule.mem_inf.2 ⟨h1, Submodule.add_mem _ hx₂ hy₂⟩
  rw [hM, Submodule.mem_bot] at h2
  refine ⟨x₁, y₁, hx₁, hx₁X, hy₁, hy₁Y, ?_⟩
  have : x₁ + x₂ + (y₁ + y₂) = (x₁ + y₁) + (x₂ + y₂) := by abel
  rw [this, h2, add_zero]

end Split

end CFSG.RankThree.GF2n.Stroth80.HS9.MP
