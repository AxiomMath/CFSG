module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80.LA

open Module

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {E : Type} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem exists_frame_symm (B : LinearMap.BilinForm K E) (halt : ∀ e : E, B e e = 0)
    (x y : E) : B x y = B y x := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
  linear_combination h - B y x * h2

theorem exists_frame_orth (B : LinearMap.BilinForm K E) (a : K) (T : E →ₗ[K] E)
    (hTB : ∀ x y : E, B (T x) (T y) = a * B x y) (x y : E) (α β : K)
    (hx : T x = α • x) (hy : T y = β • y) : (α * β - a) * B x y = 0 := by
  have h := hTB x y
  simp only [hx, hy, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  linear_combination h

theorem exists_frame_eig_end (T : E →ₗ[K] E) (N : ℕ) (hT : T ^ N = 1) (ζ : K)
    (hζ0 : ζ ≠ 0) (hζN : ζ ^ N = 1) :
    T * (∑ j ∈ Finset.range N, (ζ • T) ^ j) = ζ⁻¹ • (∑ j ∈ Finset.range N, (ζ • T) ^ j) := by
  have hy : (ζ • T) ^ N = 1 := by rw [smul_pow, hζN, hT, one_smul]
  have hg := mul_neg_geom_sum (ζ • T) N
  rw [hy, sub_self, sub_mul, one_mul, sub_eq_zero, smul_mul_assoc] at hg
  calc T * (∑ j ∈ Finset.range N, (ζ • T) ^ j)
      = ζ⁻¹ • (ζ • (T * ∑ j ∈ Finset.range N, (ζ • T) ^ j)) := by
        rw [smul_smul, inv_mul_cancel₀ hζ0, one_smul]
    _ = ζ⁻¹ • (∑ j ∈ Finset.range N, (ζ • T) ^ j) := by rw [← hg]

theorem exists_frame_sum_proj [Fintype K] [DecidableEq K] (T : E →ₗ[K] E) :
    (∑ ζ : Kˣ, ∑ j ∈ Finset.range (Fintype.card K - 1), ((ζ : K) • T) ^ j) = -1 := by
  have hNpos : 0 < Fintype.card K - 1 := by
    have := Fintype.one_lt_card (α := K)
    omega
  simp only [smul_pow]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, FiniteField.sum_pow_units]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 hNpos)]
  · simp
  · intro j hj hj0
    rw [if_neg (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hj0) (Finset.mem_range.1 hj)),
      zero_smul]

theorem exists_frame_proj_apply [Fintype K] [DecidableEq K] (T : E →ₗ[K] E) (f : E) :
    (∑ ζ : Kˣ, (∑ j ∈ Finset.range (Fintype.card K - 1), ((ζ : K) • T) ^ j) f) = -f := by
  have h := congrArg (fun F : E →ₗ[K] E => F f) (exists_frame_sum_proj T)
  simpa only [LinearMap.sum_apply, LinearMap.neg_apply, Module.End.one_apply] using h

theorem exists_frame_eig [Fintype K] [DecidableEq K] (B : LinearMap.BilinForm K E) (a : K)
    (ha0 : a ≠ 0) (hN : ∀ e : E, (∀ f, B e f = 0) → e = 0)
    (T : E →ₗ[K] E) (hT : T ^ (Fintype.card K - 1) = 1)
    (hTB : ∀ x y : E, B (T x) (T y) = a * B x y)
    (v : E) (hv0 : v ≠ 0) (l μ : K) (hμ : μ ≠ 0) (hTv : T v = l • v) (hlμ : l * μ = a) :
    ∃ x : E, T x = μ • x ∧ B v x ≠ 0 := by
  have hl0 : l ≠ 0 := by
    intro h
    apply ha0
    rw [← hlμ, h, zero_mul]
  have hex : ∃ f, B v f ≠ 0 := by
    by_contra h
    apply hv0
    apply hN
    intro f
    by_contra hf
    exact h ⟨f, hf⟩
  obtain ⟨f, hf⟩ := hex
  obtain ⟨ζ₀, hζ₀⟩ : ∃ ζ₀ : Kˣ, (ζ₀ : K) = μ⁻¹ :=
    ⟨Units.mk0 μ⁻¹ (inv_ne_zero hμ), Units.val_mk0 (inv_ne_zero hμ)⟩
  have hterm : ∀ ζ : Kˣ, ζ ≠ ζ₀ →
      B v ((∑ j ∈ Finset.range (Fintype.card K - 1), ((ζ : K) • T) ^ j) f) = 0 := by
    intro ζ hζ
    have hζK : (ζ : K) ≠ μ⁻¹ := fun h => hζ (Units.ext (h.trans hζ₀.symm))
    have hend := exists_frame_eig_end T (Fintype.card K - 1) hT (ζ : K) ζ.ne_zero
      (FiniteField.pow_card_sub_one_eq_one _ ζ.ne_zero)
    have hx := LinearMap.congr_fun hend f
    rw [Module.End.mul_apply, LinearMap.smul_apply] at hx
    have ho := exists_frame_orth B a T hTB v _ l ((ζ : K)⁻¹) hTv hx
    have hne : l * (ζ : K)⁻¹ - a ≠ 0 := by
      intro h
      apply hζK
      have h2 : (ζ : K)⁻¹ = μ := mul_left_cancel₀ hl0 (by linear_combination h - hlμ)
      rw [← h2, inv_inv]
    exact (mul_eq_zero.1 ho).resolve_left hne
  have hBsum : B v (∑ ζ : Kˣ, (∑ j ∈ Finset.range (Fintype.card K - 1), ((ζ : K) • T) ^ j) f)
      = -B v f := by
    rw [exists_frame_proj_apply T f, map_neg]
  have hsingle : ∑ ζ : Kˣ, B v ((∑ j ∈ Finset.range (Fintype.card K - 1), ((ζ : K) • T) ^ j) f)
      = B v ((∑ j ∈ Finset.range (Fintype.card K - 1), ((ζ₀ : K) • T) ^ j) f) :=
    Finset.sum_eq_single_of_mem ζ₀ (Finset.mem_univ ζ₀) (fun ζ _ hζ => hterm ζ hζ)
  rw [map_sum, hsingle] at hBsum
  have hend₀ := exists_frame_eig_end T (Fintype.card K - 1) hT (ζ₀ : K) ζ₀.ne_zero
    (FiniteField.pow_card_sub_one_eq_one _ ζ₀.ne_zero)
  have hμζ : (ζ₀ : K)⁻¹ = μ := by rw [hζ₀, inv_inv]
  rw [hμζ] at hend₀
  refine ⟨(∑ j ∈ Finset.range (Fintype.card K - 1), ((ζ₀ : K) • T) ^ j) f, ?_, ?_⟩
  · have hx := LinearMap.congr_fun hend₀ f
    rw [Module.End.mul_apply, LinearMap.smul_apply] at hx
    exact hx
  · rw [hBsum]
    exact neg_ne_zero.2 hf

theorem exists_frame
    (B : LinearMap.BilinForm K E) (Qf : E → K)
    (hQs : ∀ (c : K) (e : E), Qf (c • e) = c ^ 2 * Qf e)
    (hQa : ∀ e f : E, Qf (e + f) = Qf e + Qf f + B e f)
    (halt : ∀ e : E, B e e = 0)
    (hN : ∀ e : E, (∀ f, B e f = 0) → e = 0)
    {a : K} (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ha2 : a ^ 2 ≠ 1)
    (T : E →ₗ[K] E) (hT : T ^ (Nat.card K - 1) = 1)
    (hTB : ∀ x y : E, B (T x) (T y) = a * B x y) (hTQ : ∀ x : E, Qf (T x) = a * Qf x)
    (b u : E) (hb0 : b ≠ 0) (hbQ : Qf b = 0) (hTb : T b = a⁻¹ • b)
    (huQ : Qf u = 0) (hub : B u b = 0) (hTu : T u = u) (hu0 : u ≠ 0) :
    ∃ u₂ c : E, T u₂ = a • u₂ ∧ T c = (a ^ 2) • c ∧ Qf u₂ = 0 ∧ Qf c = 0 ∧
      B b c = 1 ∧ B u u₂ = 1 ∧ B b u₂ = 0 ∧ B u c = 0 ∧ B u₂ c = 0 := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at hT
  have hsym : ∀ x y : E, B x y = B y x := exists_frame_symm B halt
  have hTu' : T u = (1 : K) • u := by rw [one_smul]; exact hTu
  have hlμ : a⁻¹ * a ^ 2 = a := by rw [inv_mul_eq_iff_eq_mul₀ ha0, pow_two]
  obtain ⟨x₁, hx₁T, hx₁B⟩ := exists_frame_eig B a ha0 hN T hT hTB b hb0 a⁻¹ (a ^ 2)
    (pow_ne_zero 2 ha0) hTb hlμ
  obtain ⟨c₁, hc₁T, hc₁B⟩ : ∃ c₁ : E, T c₁ = (a ^ 2) • c₁ ∧ B b c₁ = 1 :=
    ⟨(B b x₁)⁻¹ • x₁, by rw [map_smul, hx₁T, smul_comm],
      by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hx₁B]⟩
  have hQ1 : (a ^ 2) ^ 2 * Qf c₁ = a * Qf c₁ := by
    have h := hTQ c₁
    rwa [hc₁T, hQs] at h
  have hs3 : Qf c₁ * (a ^ 3 - 1) = 0 := by
    have h : a * (Qf c₁ * (a ^ 3 - 1)) = 0 := by linear_combination hQ1
    exact (mul_eq_zero.1 h).resolve_left ha0
  have hinv : a⁻¹ * a = 1 := inv_mul_cancel₀ ha0
  have hsa : Qf c₁ * (a ^ 2 - a⁻¹) = 0 := by
    linear_combination a⁻¹ * hs3 - (Qf c₁ * a ^ 2) * hinv
  have hkey : Qf c₁ * a⁻¹ = a ^ 2 * Qf c₁ := by linear_combination -hsa
  have hTc : T (c₁ + Qf c₁ • b) = (a ^ 2) • (c₁ + Qf c₁ • b) := by
    rw [map_add, map_smul, hc₁T, hTb, smul_add, smul_smul, smul_smul, hkey]
  have hQc : Qf (c₁ + Qf c₁ • b) = 0 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    rw [hQa, hQs, hbQ, map_smul, smul_eq_mul, hsym c₁ b, hc₁B]
    linear_combination (Qf c₁) * h2
  have hBbc : B b (c₁ + Qf c₁ • b) = 1 := by
    rw [map_add, map_smul, halt, smul_zero, add_zero, hc₁B]
  obtain ⟨x₂, hx₂T, hx₂B⟩ := exists_frame_eig B a ha0 hN T hT hTB u hu0 1 a ha0 hTu'
    (one_mul a)
  obtain ⟨u₂, hu₂T, hu₂B⟩ : ∃ u₂ : E, T u₂ = a • u₂ ∧ B u u₂ = 1 :=
    ⟨(B u x₂)⁻¹ • x₂, by rw [map_smul, hx₂T, smul_comm],
      by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hx₂B]⟩
  have hQu₂ : Qf u₂ = 0 := by
    have h := hTQ u₂
    rw [hu₂T, hQs] at h
    have h2 : a * ((a - 1) * Qf u₂) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 ha0
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd (sub_eq_zero.1 h4) ha1
      · exact h4
  have hBbu₂ : B b u₂ = 0 := by
    have h := exists_frame_orth B a T hTB b u₂ a⁻¹ a hTb hu₂T
    have h2 : (1 - a) * B b u₂ = 0 := by linear_combination h - B b u₂ * hinv
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (sub_eq_zero.1 h3).symm ha1
    · exact h3
  have hBuc : B u (c₁ + Qf c₁ • b) = 0 := by
    have h := exists_frame_orth B a T hTB u (c₁ + Qf c₁ • b) 1 (a ^ 2) hTu' hTc
    have hne : 1 * a ^ 2 - a ≠ 0 := by
      have e : 1 * a ^ 2 - a = a * (a - 1) := by ring
      rw [e]
      exact mul_ne_zero ha0 (sub_ne_zero.2 ha1)
    exact (mul_eq_zero.1 h).resolve_left hne
  have hBu₂c : B u₂ (c₁ + Qf c₁ • b) = 0 := by
    have h := exists_frame_orth B a T hTB u₂ (c₁ + Qf c₁ • b) a (a ^ 2) hu₂T hTc
    have hne : a * a ^ 2 - a ≠ 0 := by
      have e : a * a ^ 2 - a = a * (a ^ 2 - 1) := by ring
      rw [e]
      exact mul_ne_zero ha0 (sub_ne_zero.2 ha2)
    exact (mul_eq_zero.1 h).resolve_left hne
  exact ⟨u₂, c₁ + Qf c₁ • b, hu₂T, hTc, hQu₂, hQc, hBbc, hu₂B, hBbu₂, hBuc, hBu₂c⟩
end Frame

section Gram

variable {K : Type} [Field K]
  {E : Type} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem gram_basis (B : LinearMap.BilinForm K E) (hdim : finrank K E = 4)
    (b u u₂ c : E)
    (hbc : B b c = 1) (hcb : B c b = 1) (huu : B u u₂ = 1) (huu' : B u₂ u = 1)
    (hbb : B b b = 0) (huu0 : B u u = 0) (h22 : B u₂ u₂ = 0) (hcc : B c c = 0)
    (hbu : B b u = 0) (hub : B u b = 0) (hbu₂ : B b u₂ = 0) (hu₂b : B u₂ b = 0)
    (huc : B u c = 0) (hcu : B c u = 0) (hu₂c : B u₂ c = 0) (hcu₂ : B c u₂ = 0) :
    LinearIndependent K ![b, u, u₂, c] ∧ Submodule.span K {b, u, u₂, c} = ⊤ := by
  have hli : LinearIndependent K ![b, u, u₂, c] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp [Fin.sum_univ_four] at hg
    have e0 := congrArg (fun w => B w c) hg
    have e1 := congrArg (fun w => B w u₂) hg
    have e2 := congrArg (fun w => B w u) hg
    have e3 := congrArg (fun w => B w b) hg
    simp [hbc, hcb, huu, huu', hbb, huu0, h22, hcc, hbu, hub, hbu₂, hu₂b, huc, hcu, hu₂c,
      hcu₂] at e0 e1 e2 e3
    intro i
    fin_cases i <;> simp [e0, e1, e2, e3]
  refine ⟨hli, ?_⟩
  have hspan := hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hdim])
  have hset : Set.range ![b, u, u₂, c] = {b, u, u₂, c} := by
    simp only [Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]
  rw [hset] at hspan
  exact hspan
end Gram

section Comm

variable {K : Type} [Field K] [CharP K 2]
  {E : Type} [AddCommGroup E] [Module K E]

theorem comm_involution_trivial
    (B : LinearMap.BilinForm K E) (Qf : E → K)
    (hQs : ∀ (c : K) (e : E), Qf (c • e) = c ^ 2 * Qf e)
    (hQa : ∀ e f : E, Qf (e + f) = Qf e + Qf f + B e f)
    (b u u₂ c : E) (hli : LinearIndependent K ![b, u, u₂, c])
    (hspan : Submodule.span K {b, u, u₂, c} = ⊤)
    (hbQ : Qf b = 0) (hcQ : Qf c = 0) (hbc : B b c = 1) (hcb : B c b = 1)
    (e₁ e₂ e₃ e₄ : K) (P : E →ₗ[K] E)
    (hP1 : P b = e₁ • b) (hP2 : P u = e₂ • u) (hP3 : P u₂ = e₃ • u₂) (hP4 : P c = e₄ • c)
    (h21 : e₂ ≠ e₁) (h23 : e₂ ≠ e₃) (h24 : e₂ ≠ e₄) (h31 : e₃ ≠ e₁) (h34 : e₃ ≠ e₄)
    (S : E →ₗ[K] E) (hSQ : ∀ x : E, Qf (S x) = Qf x) (hS2 : ∀ x : E, S (S x) = x)
    (hSb : S b = b) (hSP : ∀ x : E, S (P x) = P (S x)) :
    ∀ x : E, S x = x := by
  have coords : ∀ w : E, ∃ α β γ δ : K, w = α • b + β • u + γ • u₂ + δ • c := by
    intro w
    have hw : w ∈ Submodule.span K ({b, u, u₂, c} : Set E) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨α, z, hz, rfl⟩ := Submodule.mem_span_insert.mp hw
    obtain ⟨β, z', hz', rfl⟩ := Submodule.mem_span_insert.mp hz
    obtain ⟨γ, z'', hz'', rfl⟩ := Submodule.mem_span_insert.mp hz'
    obtain ⟨δ, rfl⟩ := Submodule.mem_span_singleton.mp hz''
    exact ⟨α, β, γ, δ, by abel⟩
  have uniq : ∀ α β γ δ : K, α • b + β • u + γ • u₂ + δ • c = 0 →
      α = 0 ∧ β = 0 ∧ γ = 0 ∧ δ = 0 := by
    intro α β γ δ h
    have key := (Fintype.linearIndependent_iff.mp hli) ![α, β, γ, δ] (by
      rw [Fin.sum_univ_four]
      simpa using h)
    exact ⟨key 0, key 1, key 2, key 3⟩
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have char2_sq_one : ∀ t : K, t * t = 1 → t = 1 := by
    intro t ht
    have h4 : (t - 1) * (t - 1) = 0 := by
      linear_combination ht + (1 - t) * h2K
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h4)
  have hSu : S u = u := by
    obtain ⟨α, β, γ, δ, hw⟩ := coords (S u)
    have h1 : P (S u) = e₂ • S u := by
      rw [← hSP u, hP2, map_smul]
    rw [hw] at h1
    simp only [map_add, map_smul, hP1, hP2, hP3, hP4, smul_add, smul_smul] at h1
    have hk : (α * (e₁ - e₂)) • b + (β * (e₂ - e₂)) • u + (γ * (e₃ - e₂)) • u₂
        + (δ * (e₄ - e₂)) • c = 0 := by
      linear_combination (norm := module) h1
    obtain ⟨hα, -, hγ, hδ⟩ := uniq _ _ _ _ hk
    have hα' : α = 0 := (mul_eq_zero.mp hα).resolve_right (sub_ne_zero.mpr h21.symm)
    have hγ' : γ = 0 := (mul_eq_zero.mp hγ).resolve_right (sub_ne_zero.mpr h23.symm)
    have hδ' : δ = 0 := (mul_eq_zero.mp hδ).resolve_right (sub_ne_zero.mpr h24.symm)
    have hSu' : S u = β • u := by
      rw [hw]
      simp [hα', hγ', hδ']
    have hsq : β * β = 1 := by
      have h2 : S (S u) = u := hS2 u
      rw [hSu', map_smul, hSu', smul_smul] at h2
      have hz : (0 : K) • b + (β * β - 1) • u + (0 : K) • u₂ + (0 : K) • c = 0 := by
        linear_combination (norm := module) h2
      obtain ⟨-, h5, -, -⟩ := uniq _ _ _ _ hz
      exact sub_eq_zero.mp h5
    rw [hSu', char2_sq_one β hsq, one_smul]
  have hSu₂ : S u₂ = u₂ := by
    obtain ⟨α, β, γ, δ, hw⟩ := coords (S u₂)
    have h1 : P (S u₂) = e₃ • S u₂ := by
      rw [← hSP u₂, hP3, map_smul]
    rw [hw] at h1
    simp only [map_add, map_smul, hP1, hP2, hP3, hP4, smul_add, smul_smul] at h1
    have hk : (α * (e₁ - e₃)) • b + (β * (e₂ - e₃)) • u + (γ * (e₃ - e₃)) • u₂
        + (δ * (e₄ - e₃)) • c = 0 := by
      linear_combination (norm := module) h1
    obtain ⟨hα, hβ, -, hδ⟩ := uniq _ _ _ _ hk
    have hα' : α = 0 := (mul_eq_zero.mp hα).resolve_right (sub_ne_zero.mpr h31.symm)
    have hβ' : β = 0 := (mul_eq_zero.mp hβ).resolve_right (sub_ne_zero.mpr h23)
    have hδ' : δ = 0 := (mul_eq_zero.mp hδ).resolve_right (sub_ne_zero.mpr h34.symm)
    have hSu₂' : S u₂ = γ • u₂ := by
      rw [hw]
      simp [hα', hβ', hδ']
    have hsq : γ * γ = 1 := by
      have h2 : S (S u₂) = u₂ := hS2 u₂
      rw [hSu₂', map_smul, hSu₂', smul_smul] at h2
      have hz : (0 : K) • b + (0 : K) • u + (γ * γ - 1) • u₂ + (0 : K) • c = 0 := by
        linear_combination (norm := module) h2
      obtain ⟨-, -, h5, -⟩ := uniq _ _ _ _ hz
      exact sub_eq_zero.mp h5
    rw [hSu₂', char2_sq_one γ hsq, one_smul]
  have hSc : S c = c := by
    obtain ⟨α, β, γ, δ, hw⟩ := coords (S c)
    have h1 : P (S c) = e₄ • S c := by
      rw [← hSP c, hP4, map_smul]
    rw [hw] at h1
    simp only [map_add, map_smul, hP1, hP2, hP3, hP4, smul_add, smul_smul] at h1
    have hk : (α * (e₁ - e₄)) • b + (β * (e₂ - e₄)) • u + (γ * (e₃ - e₄)) • u₂
        + (δ * (e₄ - e₄)) • c = 0 := by
      linear_combination (norm := module) h1
    obtain ⟨-, hβ, hγ, -⟩ := uniq _ _ _ _ hk
    have hβ' : β = 0 := (mul_eq_zero.mp hβ).resolve_right (sub_ne_zero.mpr h24)
    have hγ' : γ = 0 := (mul_eq_zero.mp hγ).resolve_right (sub_ne_zero.mpr h34)
    have hSc' : S c = α • b + δ • c := by
      rw [hw]
      simp [hβ', hγ']
    have hδsq : δ * δ = 1 := by
      have h2 : S (S c) = c := hS2 c
      rw [hSc'] at h2
      simp only [map_add, map_smul, hSb, hSc', smul_add, smul_smul] at h2
      have hz : (α + δ * α) • b + (0 : K) • u + (0 : K) • u₂ + (δ * δ - 1) • c = 0 := by
        linear_combination (norm := module) h2
      obtain ⟨-, -, -, h5⟩ := uniq _ _ _ _ hz
      exact sub_eq_zero.mp h5
    have hδ1 : δ = 1 := char2_sq_one δ hδsq
    have hQc : Qf (S c) = Qf c := hSQ c
    rw [hSc'] at hQc
    simp only [hQa, hQs, hbQ, hcQ, map_smul, LinearMap.smul_apply, smul_eq_mul, hbc,
      mul_zero, zero_add, add_zero, mul_one] at hQc
    have hα0 : α = 0 := by
      simpa [hδ1] using hQc
    simp [hSc', hα0, hδ1]
  intro x
  obtain ⟨α, β, γ, δ, rfl⟩ := coords x
  simp [map_add, map_smul, hSb, hSu, hSu₂, hSc]
end Comm

end CFSG.RankThree.GF2n.Stroth80.LA
