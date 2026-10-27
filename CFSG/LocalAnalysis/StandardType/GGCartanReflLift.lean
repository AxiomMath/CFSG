module

public import CFSG.LocalAnalysis.StandardType.GGReflClosedIndep

public section

namespace CFSG.StandardType

open Matrix

theorem ggRankOne_eq_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (h2 : (2 : K) ≠ 0) {h ρ : V} {α γ : Module.Dual K V} (hα : α h = 2)
    (heq : ∀ v, v - α v • h = v - γ v • ρ) :
    ∃ c : K, c ≠ 0 ∧ h = c • ρ ∧ α = c⁻¹ • γ := by
  have hh : h ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hα
    exact h2 hα.symm
  have hstep : ∀ v, α v • h = γ v • ρ := fun v => sub_right_inj.mp (heq v)
  have h2h : (2 : K) • h = γ h • ρ := by
    simpa only [hα] using hstep h
  have hγ : γ h ≠ 0 := by
    intro hγ0
    rw [hγ0, zero_smul] at h2h
    have hzero : h = 0 := by
      rcases smul_eq_zero.mp h2h with h' | h'
      · exact absurd h' h2
      · exact h'
    exact hh hzero
  set c : K := γ h / 2 with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact div_ne_zero hγ h2
  have hch : h = c • ρ := by
    rw [hc]
    calc h = (1 : K) • h := by rw [one_smul]
      _ = ((2 : K)⁻¹ * 2) • h := by rw [inv_mul_cancel₀ h2]
      _ = (2 : K)⁻¹ • ((2 : K) • h) := by rw [smul_smul]
      _ = (2 : K)⁻¹ • (γ h • ρ) := by rw [h2h]
      _ = ((2 : K)⁻¹ * γ h) • ρ := by rw [smul_smul]
      _ = (γ h / 2) • ρ := by rw [div_eq_mul_inv, mul_comm]
  refine ⟨c, hc0, hch, ?_⟩
  have hρ : ρ ≠ 0 := by
    intro hρ0
    exact hh (by rw [hch, hρ0, smul_zero])
  ext v
  have hv := hstep v
  rw [hch, smul_smul] at hv
  have hvc : α v * c = γ v := by
    have hsub : (α v * c - γ v) • ρ = 0 := by
      rw [sub_smul, hv, sub_self]
    rcases smul_eq_zero.mp hsub with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hρ
  simp only [LinearMap.smul_apply, smul_eq_mul]
  calc α v = α v * c * c⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hc0, mul_one]
    _ = γ v * c⁻¹ := by rw [hvc]
    _ = c⁻¹ * γ v := by ring

theorem ggCartanRefl_pair_apply {p : ℕ} {Λ : Type*} [Fintype Λ] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] {C : Matrix Λ Λ ℤ} (t : Λ → V) (β : Λ → Module.Dual (ZMod p) V)
    (htβ : ∀ i j, β i (t j) = (C i j : ZMod p)) (a c : Λ → ℤ) :
    (∑ l, ((a l : ℤ) : ZMod p) • β l) (∑ m, ((c m : ℤ) : ZMod p) • t m) =
      ((a ⬝ᵥ (C *ᵥ c) : ℤ) : ZMod p) := by
  have hL : (∑ l, ((a l : ℤ) : ZMod p) • β l) (∑ m, ((c m : ℤ) : ZMod p) • t m) =
      ∑ l, ∑ m, ((a l : ℤ) : ZMod p) * ((c m : ℤ) : ZMod p) * ((C l m : ℤ) : ZMod p) := by
    rw [LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro l _
    rw [LinearMap.smul_apply, map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [map_smul, htβ]
    simp only [smul_eq_mul]
    ring
  have hR : ((a ⬝ᵥ (C *ᵥ c) : ℤ) : ZMod p) =
      ∑ l, ∑ m, ((a l : ℤ) : ZMod p) * ((c m : ℤ) : ZMod p) * ((C l m : ℤ) : ZMod p) := by
    simp only [dotProduct, Matrix.mulVec]
    push_cast
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hL, hR]

private theorem ggCartanRefl_lift_sum_sub_single {p : ℕ} {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {W : Type*} [AddCommGroup W] [Module (ZMod p) W] (f : Λ → W) (i : Λ) (k : ℤ) (c : Λ → ℤ) :
      (∑ l, (((c - k • (Pi.single i (1 : ℤ) : Λ → ℤ)) l : ℤ) : ZMod p) • f l) =
      (∑ l, ((c l : ℤ) : ZMod p) • f l) - ((k : ℤ) : ZMod p) • f i := by
  have hfun : (fun l => (((c - k • (Pi.single i (1 : ℤ) : Λ → ℤ)) l : ℤ) : ZMod p) • f l) =
      fun l => ((c l : ℤ) : ZMod p) • f l -
        ((k : ZMod p) * ((Pi.single i (1 : ℤ) : Λ → ℤ) l : ZMod p)) • f l := by
    funext l
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul, sub_smul]
  rw [hfun, Finset.sum_sub_distrib]
  have hsecond : (∑ l, ((k : ZMod p) * (((Pi.single i (1 : ℤ) : Λ → ℤ)) l : ZMod p)) • f l) =
      ((k : ℤ) : ZMod p) • f i := by
    rw [← Fintype.sum_ite_eq' i (fun l => (k : ZMod p) • f l)]
    apply Finset.sum_congr rfl
    intro l _
    by_cases h : l = i
    · subst h; simp
    · rw [Pi.single_eq_of_ne h, if_neg h]
      simp
  rw [hsecond]

private theorem ggCartanRefl_lift_betaT {p : ℕ} {Λ : Type*} [Fintype Λ] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] {C : Matrix Λ Λ ℤ} (t : Λ → V)
    (β : Λ → Module.Dual (ZMod p) V) (htβ : ∀ i j, β i (t j) = (C i j : ZMod p))
    (i : Λ) (c : Λ → ℤ) :
    β i (∑ l, ((c l : ℤ) : ZMod p) • t l) = ((C *ᵥ c) i : ZMod p) := by
  simp only [map_sum, map_smul, htβ, smul_eq_mul]
  rw [Matrix.mulVec_apply_eq_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro l _
  ring

private theorem ggCartanRefl_lift_SmulVec {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (C : Matrix Λ Λ ℤ) (i : Λ) (c : Λ → ℤ) :
    (1 - Matrix.single i i 1 * C) *ᵥ c =
      c - ((C *ᵥ c) i) • Pi.single i (1 : ℤ) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, Matrix.single_mulVec_eq]
  simp [one_mul]

private theorem ggCartanRefl_lift_sT {p : ℕ} {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] {C : Matrix Λ Λ ℤ}
    (t : Λ → V) (β : Λ → Module.Dual (ZMod p) V)
    (htβ : ∀ i j, β i (t j) = (C i j : ZMod p))
    (s : Λ → (V ≃ₗ[ZMod p] V)) (hs : ∀ i v, s i v = v - β i v • t i)
    (i : Λ) (c : Λ → ℤ) :
    s i (∑ l, ((c l : ℤ) : ZMod p) • t l) =
      ∑ l, ((((1 - Matrix.single i i 1 * C) *ᵥ c) l : ℤ) : ZMod p) • t l := by
  rw [hs i, ggCartanRefl_lift_betaT t β htβ i c]
  rw [ggCartanRefl_lift_SmulVec C i c]
  exact (ggCartanRefl_lift_sum_sub_single (p := p) (Λ := Λ) (W := V) t i ((C *ᵥ c) i) c).symm

private theorem ggCartanRefl_lift_Bt {p : ℕ} {Λ : Type*} [Fintype Λ] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] {C : Matrix Λ Λ ℤ} (hCt : C.transpose = C)
    (t : Λ → V) (β : Λ → Module.Dual (ZMod p) V)
    (htβ : ∀ i j, β i (t j) = (C i j : ZMod p)) (a : Λ → ℤ) (i : Λ) :
    (∑ l, ((a l : ℤ) : ZMod p) • β l) (t i) = ((C *ᵥ a) i : ZMod p) := by
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, htβ, smul_eq_mul]
  rw [Matrix.mulVec_apply_eq_sum]
  push_cast
  have hsym : ∀ l, C l i = C i l := fun l => by
    have h := congrFun (congrFun hCt l) i
    simpa [Matrix.transpose_apply] using h.symm
  apply Finset.sum_congr rfl
  intro l _
  rw [hsym l]
  ring

private theorem ggCartanRefl_lift_Bs {p : ℕ} {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] {C : Matrix Λ Λ ℤ} (hCt : C.transpose = C)
    (t : Λ → V) (β : Λ → Module.Dual (ZMod p) V)
    (htβ : ∀ i j, β i (t j) = (C i j : ZMod p))
    (s : Λ → (V ≃ₗ[ZMod p] V)) (hs : ∀ i v, s i v = v - β i v • t i)
    (i : Λ) (a : Λ → ℤ) (v : V) :
    (∑ l, ((a l : ℤ) : ZMod p) • β l) (s i v) =
      (∑ l, ((((1 - Matrix.single i i 1 * C) *ᵥ a) l : ℤ) : ZMod p) • β l) v := by
  have hL : (∑ l, ((a l : ℤ) : ZMod p) • β l) (s i v) =
      (∑ l, ((a l : ℤ) : ZMod p) • β l) v -
        β i v * ((∑ l, ((a l : ℤ) : ZMod p) • β l) (t i)) := by
    rw [hs i, map_sub, map_smul, smul_eq_mul]
  rw [hL, ggCartanRefl_lift_Bt hCt t β htβ a i, ggCartanRefl_lift_SmulVec C i a]
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]
  rw [ggCartanRefl_lift_sum_sub_single (fun l => β l v) i ((C *ᵥ a) i) a, smul_eq_mul]
  ring

private theorem ggCartanRefl_lift_S_mul_S {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {C : Matrix Λ Λ ℤ} (hCd : ∀ i, C i i = 2) (i : Λ) :
    (1 - Matrix.single i i 1 * C) * (1 - Matrix.single i i 1 * C) = 1 := by
  have hACA : Matrix.single i i (1 : ℤ) * C * Matrix.single i i (1 : ℤ) =
      Matrix.single i i (1 : ℤ) + Matrix.single i i (1 : ℤ) := by
    have h : Matrix.single i i (1 : ℤ) * C * Matrix.single i i (1 : ℤ) =
        (C i i) • Matrix.single i i (1 : ℤ) := by
      rw [Matrix.single_mul_mul_single, Matrix.smul_single]
      simp
    rw [h, hCd i, two_smul]
  have hXX : (Matrix.single i i (1 : ℤ) * C) * (Matrix.single i i (1 : ℤ) * C) =
      (Matrix.single i i (1 : ℤ) * C) + (Matrix.single i i (1 : ℤ) * C) := by
    calc
      (Matrix.single i i (1 : ℤ) * C) * (Matrix.single i i (1 : ℤ) * C)
          = ((Matrix.single i i (1 : ℤ) * C) * Matrix.single i i (1 : ℤ)) * C :=
            (Matrix.mul_assoc _ _ _).symm
      _ = (Matrix.single i i (1 : ℤ) + Matrix.single i i (1 : ℤ)) * C := by rw [hACA]
      _ = Matrix.single i i (1 : ℤ) * C + Matrix.single i i (1 : ℤ) * C := by rw [add_mul]
  calc
    (1 - Matrix.single i i 1 * C) * (1 - Matrix.single i i 1 * C)
        = 1 - Matrix.single i i 1 * C - Matrix.single i i 1 * C +
            (Matrix.single i i 1 * C) * (Matrix.single i i 1 * C) := by noncomm_ring
    _ = 1 - Matrix.single i i 1 * C - Matrix.single i i 1 * C +
            (Matrix.single i i 1 * C + Matrix.single i i 1 * C) := by rw [hXX]
    _ = 1 := by noncomm_ring

private theorem ggCartanRefl_lift_StCS {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {C : Matrix Λ Λ ℤ} (hCt : C.transpose = C) (hCd : ∀ i, C i i = 2) (i : Λ) :
    (1 - Matrix.single i i 1 * C)ᵀ * C * (1 - Matrix.single i i 1 * C) = C := by
  have hACA : Matrix.single i i (1 : ℤ) * C * Matrix.single i i (1 : ℤ) =
      Matrix.single i i (1 : ℤ) + Matrix.single i i (1 : ℤ) := by
    have h : Matrix.single i i (1 : ℤ) * C * Matrix.single i i (1 : ℤ) =
        (C i i) • Matrix.single i i (1 : ℤ) := by
      rw [Matrix.single_mul_mul_single, Matrix.smul_single]
      simp
    rw [h, hCd i, two_smul]
  have hT : (1 - Matrix.single i i 1 * C)ᵀ = 1 - C * Matrix.single i i 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hCt,
      Matrix.transpose_single]
  rw [hT]
  have hY : (C * Matrix.single i i (1 : ℤ)) * C * (Matrix.single i i (1 : ℤ) * C) =
      (C * Matrix.single i i (1 : ℤ) * C) + (C * Matrix.single i i (1 : ℤ) * C) := by
    calc
      (C * Matrix.single i i (1 : ℤ)) * C * (Matrix.single i i (1 : ℤ) * C)
          = C * (Matrix.single i i (1 : ℤ) * C * Matrix.single i i (1 : ℤ)) * C := by
            noncomm_ring
      _ = (C * Matrix.single i i (1 : ℤ) * C) + (C * Matrix.single i i (1 : ℤ) * C) := by
            rw [hACA]; noncomm_ring
  calc
    (1 - C * Matrix.single i i 1) * C * (1 - Matrix.single i i 1 * C)
        = C - (C * Matrix.single i i 1) * C - C * (Matrix.single i i 1 * C) +
            (C * Matrix.single i i 1) * C * (Matrix.single i i 1 * C) := by noncomm_ring
    _ = C - (C * Matrix.single i i 1) * C - C * (Matrix.single i i 1 * C) +
            ((C * Matrix.single i i 1 * C) + (C * Matrix.single i i 1 * C)) := by rw [hY]
    _ = C := by noncomm_ring

theorem ggCartanRefl_lift {p : ℕ} {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] {C : Matrix Λ Λ ℤ} (hCt : C.transpose = C)
    (hCd : ∀ i, C i i = 2) (t : Λ → V) (β : Λ → Module.Dual (ZMod p) V)
    (htβ : ∀ i j, β i (t j) = (C i j : ZMod p))
    (s : Λ → (V ≃ₗ[ZMod p] V)) (hs : ∀ i v, s i v = v - β i v • t i)
    {u : V ≃ₗ[ZMod p] V} (hu : u ∈ Subgroup.closure (Set.range s)) :
    ∃ U Ui : Matrix Λ Λ ℤ, U * Ui = 1 ∧ Ui * U = 1 ∧ U.transpose * C * U = C ∧
      (∀ c : Λ → ℤ, u (∑ l, ((c l : ℤ) : ZMod p) • t l) =
        ∑ l, (((U *ᵥ c) l : ℤ) : ZMod p) • t l) ∧
      ∀ (a : Λ → ℤ) (v : V), (∑ l, ((a l : ℤ) : ZMod p) • β l) (u⁻¹ v) =
        (∑ l, (((U *ᵥ a) l : ℤ) : ZMod p) • β l) v := by
  classical
  let S : Λ → Matrix Λ Λ ℤ := fun i => 1 - Matrix.single i i 1 * C
  have hS_mul : ∀ i, S i * S i = 1 := fun i => ggCartanRefl_lift_S_mul_S hCd i
  have hS_trans : ∀ i, (S i)ᵀ * C * S i = C := fun i => ggCartanRefl_lift_StCS hCt hCd i
  have hs_inv : ∀ i, (s i)⁻¹ = s i := by
    intro i
    have hss : s i * s i = 1 := by
      apply LinearEquiv.ext
      intro v
      simp only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq, hs i, map_sub, map_smul,
        htβ, hCd i]
      module
    exact mul_eq_one_iff_inv_eq.mp hss
  let P : (V ≃ₗ[ZMod p] V) → Prop := fun u =>
    ∃ U Ui : Matrix Λ Λ ℤ, U * Ui = 1 ∧ Ui * U = 1 ∧ U.transpose * C * U = C ∧
      (∀ c : Λ → ℤ, u (∑ l, ((c l : ℤ) : ZMod p) • t l) =
        ∑ l, (((U *ᵥ c) l : ℤ) : ZMod p) • t l) ∧
      ∀ (a : Λ → ℤ) (v : V), (∑ l, ((a l : ℤ) : ZMod p) • β l) (u⁻¹ v) =
        (∑ l, (((U *ᵥ a) l : ℤ) : ZMod p) • β l) v
  have key : ∀ u ∈ Subgroup.closure (Set.range s), P u := by
    intro u hu
    refine Subgroup.closure_induction (p := fun u _ => P u) ?_ ?_ ?_ ?_ hu
    · rintro w ⟨i, rfl⟩
      exact ⟨S i, S i, hS_mul i, hS_mul i, hS_trans i,
        fun c => ggCartanRefl_lift_sT t β htβ s hs i c,
        fun a v => by rw [hs_inv i]; exact ggCartanRefl_lift_Bs hCt t β htβ s hs i a v⟩
    · exact ⟨1, 1, by simp, by simp, by simp, fun c => by simp, fun a v => by simp⟩
    · rintro u₁ u₂ _ _ ⟨U₁, Ui₁, h1, h2, h3, h4, h5⟩ ⟨U₂, Ui₂, k1, k2, k3, k4, k5⟩
      refine ⟨U₁ * U₂, Ui₂ * Ui₁, ?_, ?_, ?_, ?_, ?_⟩
      · calc U₁ * U₂ * (Ui₂ * Ui₁) = U₁ * (U₂ * Ui₂) * Ui₁ := by noncomm_ring
          _ = 1 := by rw [k1, Matrix.mul_one, h1]
      · calc Ui₂ * Ui₁ * (U₁ * U₂) = Ui₂ * (Ui₁ * U₁) * U₂ := by noncomm_ring
          _ = 1 := by rw [h2, Matrix.mul_one, k2]
      · calc (U₁ * U₂)ᵀ * C * (U₁ * U₂) = U₂ᵀ * (U₁ᵀ * C * U₁) * U₂ := by
              rw [Matrix.transpose_mul]; noncomm_ring
          _ = U₂ᵀ * C * U₂ := by rw [h3]
          _ = C := k3
      · intro c
        rw [LinearEquiv.mul_apply, k4 c, h4 (U₂ *ᵥ c), ← Matrix.mulVec_mulVec]
      · intro a v
        rw [_root_.mul_inv_rev, LinearEquiv.mul_apply, k5 a (u₁⁻¹ v), h5 (U₂ *ᵥ a) v,
          Matrix.mulVec_mulVec]
    · rintro u _ ⟨U, Ui, h1, h2, h3, h4, h5⟩
      refine ⟨Ui, U, h2, h1, ?_, ?_, ?_⟩
      · calc Uiᵀ * C * Ui = Uiᵀ * (Uᵀ * C * U) * Ui := by rw [h3]
          _ = (U * Ui)ᵀ * C * (U * Ui) := by rw [Matrix.transpose_mul]; noncomm_ring
          _ = C := by rw [h1]; simp
      · intro c
        have hthis : u (∑ l, (((Ui *ᵥ c) l : ℤ) : ZMod p) • t l) =
            ∑ l, ((c l : ℤ) : ZMod p) • t l := by
          rw [h4 (Ui *ᵥ c), Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
        rw [← hthis, ← LinearEquiv.mul_apply, inv_mul_cancel]
        simp
      · intro a v
        rw [inv_inv]
        have h := h5 (Ui *ᵥ a) (u v)
        simp only [← LinearEquiv.mul_apply, inv_mul_cancel, LinearEquiv.coe_one, id_eq] at h
        rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at h
        exact h.symm
  exact key u hu

theorem ggCartanRefl_conj_apply {p : ℕ} {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] (t : Λ → V) (β : Λ → Module.Dual (ZMod p) V)
    (s : Λ → (V ≃ₗ[ZMod p] V)) (hs : ∀ i v, s i v = v - β i v • t i)
    (u : V ≃ₗ[ZMod p] V) (U : Matrix Λ Λ ℤ)
    (hUt : ∀ c : Λ → ℤ, u (∑ l, ((c l : ℤ) : ZMod p) • t l) =
      ∑ l, (((U *ᵥ c) l : ℤ) : ZMod p) • t l)
    (hUβ : ∀ (a : Λ → ℤ) (v : V), (∑ l, ((a l : ℤ) : ZMod p) • β l) (u⁻¹ v) =
      (∑ l, (((U *ᵥ a) l : ℤ) : ZMod p) • β l) v)
    (i : Λ) (v : V) :
    (u * s i * u⁻¹) v = v - (∑ l, (((U *ᵥ Pi.single i 1) l : ℤ) : ZMod p) • β l) v •
      ∑ l, (((U *ᵥ Pi.single i 1) l : ℤ) : ZMod p) • t l := by
  have hsum_t : (∑ l, (((Pi.single i (1 : ℤ) : Λ → ℤ) l : ℤ) : ZMod p) • t l) = t i := by
    have h := Finset.sum_eq_single (s := Finset.univ)
      (f := fun l => (((Pi.single i (1 : ℤ) : Λ → ℤ) l : ℤ) : ZMod p) • t l) i
      (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp)
      (fun hi => absurd (Finset.mem_univ i) hi)
    simpa using h
  have hsum_β : (∑ l, (((Pi.single i (1 : ℤ) : Λ → ℤ) l : ℤ) : ZMod p) • β l) = β i := by
    have h := Finset.sum_eq_single (s := Finset.univ)
      (f := fun l => (((Pi.single i (1 : ℤ) : Λ → ℤ) l : ℤ) : ZMod p) • β l) i
      (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp)
      (fun hi => absurd (Finset.mem_univ i) hi)
    simpa using h
  have hti : u (t i) = ∑ l, (((U *ᵥ Pi.single i (1 : ℤ)) l : ℤ) : ZMod p) • t l := by
    rw [← hsum_t, hUt (Pi.single i (1 : ℤ))]
  have hβi : β i (u⁻¹ v) = (∑ l, (((U *ᵥ Pi.single i (1 : ℤ)) l : ℤ) : ZMod p) • β l) v := by
    rw [← hsum_β, hUβ (Pi.single i (1 : ℤ)) v]
  calc
    (u * s i * u⁻¹) v = u (s i (u⁻¹ v)) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    _ = u (u⁻¹ v - β i (u⁻¹ v) • t i) := by rw [hs]
    _ = u (u⁻¹ v) - β i (u⁻¹ v) • u (t i) := by rw [map_sub, map_smul]
    _ = v - (∑ l, (((U *ᵥ Pi.single i (1 : ℤ)) l : ℤ) : ZMod p) • β l) v •
          ∑ l, (((U *ᵥ Pi.single i (1 : ℤ)) l : ℤ) : ZMod p) • t l := by
      rw [hβi, hti]
      simp

theorem ggCartanRefl_root_data {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {Λ : Type*} [Fintype Λ]
    [DecidableEq Λ] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] {C : Matrix Λ Λ ℤ}
    (hCt : C.transpose = C) (hCd : ∀ i, C i i = 2) (t : Λ → V)
    (β : Λ → Module.Dual (ZMod p) V) (htβ : ∀ i j, β i (t j) = (C i j : ZMod p))
    (s : Λ → (V ≃ₗ[ZMod p] V)) (hs : ∀ i v, s i v = v - β i v • t i)
    {ι : Type*} (h : ι → V) (α : ι → Module.Dual (ZMod p) V) (hα : ∀ j, α j (h j) = 2)
    (r : ι → (V ≃ₗ[ZMod p] V)) (hr : ∀ j v, r j v = v - α j v • h j)
    (hconj : ∀ j, r j ∈ ggReflConj s) :
    ∃ (b : ι → Λ → ℤ) (c : ι → ZMod p), (∀ j, c j ≠ 0) ∧ (∀ j, b j ⬝ᵥ (C *ᵥ b j) = 2) ∧
      (∀ j, h j = c j • ∑ l, ((b j l : ℤ) : ZMod p) • t l) ∧
      ∀ j, α j = (c j)⁻¹ • ∑ l, ((b j l : ℤ) : ZMod p) • β l := by
  classical
  have hconj' : ∀ j, ∃ u ∈ Subgroup.closure (Set.range s), ∃ i, r j = u * s i * u⁻¹ := by
    intro j
    simpa only [ggReflConj, Set.mem_setOf_eq] using hconj j
  choose u hu i hi using hconj'
  have hlift : ∀ j, ∃ U Ui : Matrix Λ Λ ℤ, U * Ui = 1 ∧ Ui * U = 1 ∧ U.transpose * C * U = C ∧
      (∀ c : Λ → ℤ, u j (∑ l, ((c l : ℤ) : ZMod p) • t l) =
        ∑ l, (((U *ᵥ c) l : ℤ) : ZMod p) • t l) ∧
      ∀ (a : Λ → ℤ) (v : V), (∑ l, ((a l : ℤ) : ZMod p) • β l) ((u j)⁻¹ v) =
        (∑ l, (((U *ᵥ a) l : ℤ) : ZMod p) • β l) v :=
    fun j => ggCartanRefl_lift hCt hCd t β htβ s hs (hu j)
  choose U Ui hAll using hlift
  have hUCU : ∀ j, (U j).transpose * C * U j = C := fun j => (hAll j).2.2.1
  have hUt : ∀ j c, u j (∑ l, ((c l : ℤ) : ZMod p) • t l) =
      ∑ l, (((U j *ᵥ c) l : ℤ) : ZMod p) • t l := fun j => (hAll j).2.2.2.1
  have hUβ : ∀ j a v, (∑ l, ((a l : ℤ) : ZMod p) • β l) ((u j)⁻¹ v) =
      (∑ l, (((U j *ᵥ a) l : ℤ) : ZMod p) • β l) v := fun j => (hAll j).2.2.2.2
  let b : ι → Λ → ℤ := fun j => U j *ᵥ Pi.single (i j) 1
  let ρ : ι → V := fun j => ∑ l, ((b j l : ℤ) : ZMod p) • t l
  let γ : ι → Module.Dual (ZMod p) V := fun j => ∑ l, ((b j l : ℤ) : ZMod p) • β l
  have hp2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 h0
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact (Fact.out : p.Prime).ne_one h1
    · exact hp h2
  have heq : ∀ j v, v - α j v • h j = v - γ j v • ρ j := by
    intro j v
    rw [← hr j v, hi j]
    exact ggCartanRefl_conj_apply t β s hs (u j) (U j) (hUt j) (hUβ j) (i j) v
  choose c hc hch hcα using fun j => ggRankOne_eq_smul hp2 (hα j) (heq j)
  refine ⟨b, c, hc, ?_, ?_, ?_⟩
  · intro j
    have hkey : (U j *ᵥ Pi.single (i j) 1) ⬝ᵥ ((C * U j) *ᵥ Pi.single (i j) 1) =
        Pi.single (i j) 1 ⬝ᵥ ((U j).transpose *ᵥ ((C * U j) *ᵥ Pi.single (i j) 1)) := by
      rw [← dotProduct_comm ((C * U j) *ᵥ Pi.single (i j) 1)]
      exact (Matrix.dotProduct_transpose_mulVec (U j) (Pi.single (i j) 1)
        ((C * U j) *ᵥ Pi.single (i j) 1)).symm
    calc b j ⬝ᵥ (C *ᵥ b j)
        = (U j *ᵥ Pi.single (i j) 1) ⬝ᵥ (C *ᵥ (U j *ᵥ Pi.single (i j) 1)) := rfl
      _ = (U j *ᵥ Pi.single (i j) 1) ⬝ᵥ ((C * U j) *ᵥ Pi.single (i j) 1) := by
            rw [Matrix.mulVec_mulVec]
      _ = Pi.single (i j) 1 ⬝ᵥ ((U j).transpose *ᵥ ((C * U j) *ᵥ Pi.single (i j) 1)) := hkey
      _ = Pi.single (i j) 1 ⬝ᵥ (((U j).transpose * (C * U j)) *ᵥ Pi.single (i j) 1) := by
            rw [Matrix.mulVec_mulVec]
      _ = Pi.single (i j) 1 ⬝ᵥ (C *ᵥ Pi.single (i j) 1) := by
            rw [← Matrix.mul_assoc, hUCU j]
      _ = C (i j) (i j) := by
            rw [single_one_dotProduct, Matrix.mulVec_single_one]
            rfl
      _ = 2 := hCd (i j)
  · intro j
    exact hch j
  · intro j
    exact hcα j

private theorem ggPosDef_root_inner_cast {Λ : Type*} [Fintype Λ] {C : Matrix Λ Λ ℤ}
    (y : Λ → ℤ) :
    ((y ⬝ᵥ (C *ᵥ y) : ℤ) : ℚ) =
      (fun i => (y i : ℚ)) ⬝ᵥ
        ((C.map (Int.cast : ℤ → ℚ)) *ᵥ (fun i => (y i : ℚ))) := by
  rw [Matrix.dot_mulVec_eq_sum_sum, Matrix.dot_mulVec_eq_sum_sum]
  push_cast
  simp [Matrix.map_apply, mul_assoc, mul_left_comm, mul_comm]

private theorem ggPosDef_root_inner_nonneg {Λ : Type*} [Fintype Λ] {C : Matrix Λ Λ ℤ}
    (hC : (C.map (Int.cast : ℤ → ℚ)).PosDef) (y : Λ → ℤ) :
    0 ≤ y ⬝ᵥ (C *ᵥ y) := by
  have hpsd : (C.map (Int.cast : ℤ → ℚ)).PosSemidef := hC.posSemidef
  have hq := hpsd.dotProduct_mulVec_nonneg (fun i => (y i : ℚ))
  rw [star_trivial] at hq
  rw [← ggPosDef_root_inner_cast (C := C) y] at hq
  exact Int.cast_nonneg_iff.mp hq

private theorem ggPosDef_root_inner_eq_zero {Λ : Type*} [Fintype Λ] {C : Matrix Λ Λ ℤ}
    (hC : (C.map (Int.cast : ℤ → ℚ)).PosDef) {y : Λ → ℤ}
    (hy : y ⬝ᵥ (C *ᵥ y) = 0) : y = 0 := by
  by_contra hne
  have hxne : (fun i => (y i : ℚ)) ≠ 0 := by
    intro h
    apply hne
    ext i
    simpa using congr_fun h i
  have hpos := hC.dotProduct_mulVec_pos (x := fun i => (y i : ℚ)) hxne
  rw [star_trivial, ← ggPosDef_root_inner_cast (C := C) y] at hpos
  exact absurd hy (ne_of_gt (Int.cast_pos.mp hpos))

private theorem ggPosDef_root_inner_sub {Λ : Type*} [Fintype Λ] {C : Matrix Λ Λ ℤ}
    (hCt : C.transpose = C) (b b' : Λ → ℤ) :
    (b - b') ⬝ᵥ (C *ᵥ (b - b')) =
      b ⬝ᵥ (C *ᵥ b) - 2 * (b ⬝ᵥ (C *ᵥ b')) +
        b' ⬝ᵥ (C *ᵥ b') := by
  have hsymm : C.IsSymm := hCt
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [hsymm.dotProduct_mulVec_comm (x := b') (y := b)]
  ring

private theorem ggPosDef_root_inner_add {Λ : Type*} [Fintype Λ] {C : Matrix Λ Λ ℤ}
    (hCt : C.transpose = C) (b b' : Λ → ℤ) :
    (b + b') ⬝ᵥ (C *ᵥ (b + b')) =
      b ⬝ᵥ (C *ᵥ b) + 2 * (b ⬝ᵥ (C *ᵥ b')) +
        b' ⬝ᵥ (C *ᵥ b') := by
  have hsymm : C.IsSymm := hCt
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  rw [hsymm.dotProduct_mulVec_comm (x := b') (y := b)]
  ring

theorem ggPosDef_root_inner {Λ : Type*} [Fintype Λ] {C : Matrix Λ Λ ℤ} (hCt : C.transpose = C)
    (hC : (C.map (Int.cast : ℤ → ℚ)).PosDef) {b b' : Λ → ℤ} (hb : b ⬝ᵥ (C *ᵥ b) = 2)
    (hb' : b' ⬝ᵥ (C *ᵥ b') = 2) :
    -2 ≤ b ⬝ᵥ (C *ᵥ b') ∧ b ⬝ᵥ (C *ᵥ b') ≤ 2 ∧ (b ⬝ᵥ (C *ᵥ b') = 2 → b' = b) ∧
      (b ⬝ᵥ (C *ᵥ b') = -2 → b' = -b) := by
  have hsub := ggPosDef_root_inner_sub (C := C) hCt b b'
  have hadd := ggPosDef_root_inner_add (C := C) hCt b b'
  have hnsub := ggPosDef_root_inner_nonneg (C := C) hC (b - b')
  have hnadd := ggPosDef_root_inner_nonneg (C := C) hC (b + b')
  rw [hsub, hb, hb'] at hnsub
  rw [hadd, hb, hb'] at hnadd
  have hle : b ⬝ᵥ (C *ᵥ b') ≤ 2 := by linarith
  have hge : -2 ≤ b ⬝ᵥ (C *ᵥ b') := by linarith
  refine ⟨hge, hle, ?_, ?_⟩
  · intro hx
    have hzero : (b - b') ⬝ᵥ (C *ᵥ (b - b')) = 0 := by
      rw [hsub, hb, hb', hx]; ring
    exact (sub_eq_zero.mp (ggPosDef_root_inner_eq_zero (C := C) hC hzero)).symm
  · intro hx
    have hzero : (b + b') ⬝ᵥ (C *ᵥ (b + b')) = 0 := by
      rw [hadd, hb, hb', hx]; ring
    exact eq_neg_of_add_eq_zero_right (ggPosDef_root_inner_eq_zero (C := C) hC hzero)

private theorem ggReflConj_of_reflClosed_sq_aux {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] (f : Module.Dual K W) (h : W) (hf : f h = 2) (v : W) :
    (v - f v • h) - f (v - f v • h) • h = v := by
  rw [map_sub, map_smul, hf, smul_eq_mul]
  module

theorem ggReflConj_of_reflClosed {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {Λ : Type} {s : Λ → (V ≃ₗ[ZMod p] V)} (hRC : GGReflClosed s)
    {r : V ≃ₗ[ZMod p] V} {h : V} {α : Module.Dual (ZMod p) V} (hα : α h = 2)
    (hr : ∀ v, r v = v - α v • h) (hrW : r ∈ Subgroup.closure (Set.range s)) :
    r ∈ ggReflConj s := by
  have hr2 : r ^ 2 = 1 := by
    refine LinearEquiv.ext fun v => ?_
    rw [pow_two, LinearEquiv.mul_apply]
    change r (r v) = v
    rw [hr v, hr (v - α v • h)]
    exact ggReflConj_of_reflClosed_sq_aux α h hα v
  have hr1 : r ≠ 1 := by
    intro h1
    have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp
    have hh : (2 : ZMod p) • h = 0 := by
      have h3 : r h = h - (2 : ZMod p) • h := by rw [hr h, hα]
      rw [h1] at h3
      change h = h - (2 : ZMod p) • h at h3
      exact sub_eq_self.mp h3.symm
    have h0 : h = 0 := (smul_eq_zero.mp hh).resolve_left h2
    have hz : α h = 0 := by rw [h0, map_zero]
    rw [hz] at hα
    exact h2 hα.symm
  exact hRC r hrW hr2 hr1 ⟨h, α, hr⟩

end CFSG.StandardType
