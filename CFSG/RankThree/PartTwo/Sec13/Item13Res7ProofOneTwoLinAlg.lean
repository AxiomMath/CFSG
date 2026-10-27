module

public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofLinAlg

public section

namespace CFSG.RankThree.PartTwo.Sec13.Res7Proof

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

structure A4Data (A₁ A₂ B Ω : Module.End K V) : Prop where
  a₁ : A₁ * A₁ = 1
  a₂ : A₂ * A₂ = 1
  a₁₂ : A₁ * A₂ = A₂ * A₁
  b₁ : B * A₁ = A₁ * B
  b₂ : B * A₂ = A₂ * B
  b₃ : B * B * B = 1
  o₁ : Ω * A₁ = A₁ * A₂ * Ω
  o₂ : Ω * A₂ = A₁ * Ω
  o₃ : Ω * Ω * Ω = 1
  bo : B * Ω = Ω * B

theorem finrank_split [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) {A : Module.End K V}
    (hA : A * A = 1) (U : Submodule K V) (hU : ∀ u ∈ U, A u ∈ U) :
    Module.finrank K U = Module.finrank K ↥(U ⊓ Module.End.eigenspace A 1) +
      Module.finrank K ↥(U ⊓ Module.End.eigenspace A (-1)) := by
  have hA' : ∀ v, A (A v) = v := fun v => by
    rw [← Module.End.mul_apply, hA, Module.End.one_apply]
  have hsup : (U ⊓ Module.End.eigenspace A 1) ⊔ (U ⊓ Module.End.eigenspace A (-1)) = U := by
    apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro u hu
    rw [eq_half_smul h2 u]
    refine Submodule.smul_mem _ _ ?_
    have hrw : u + u = (u + A u) + (u - A u) := by abel
    rw [hrw]
    refine Submodule.add_mem_sup ⟨add_mem hu (hU u hu), ?_⟩ ⟨sub_mem hu (hU u hu), ?_⟩
    · rw [SetLike.mem_coe, mem_eigenspace_one_iff', map_add, hA']
      abel
    · rw [SetLike.mem_coe, mem_eigenspace_neg_one_iff', map_sub, hA']
      abel
  have hinf : (U ⊓ Module.End.eigenspace A 1) ⊓ (U ⊓ Module.End.eigenspace A (-1)) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨⟨-, h1⟩, ⟨-, h2'⟩⟩ := hv
    rw [SetLike.mem_coe, mem_eigenspace_one_iff'] at h1
    rw [SetLike.mem_coe, mem_eigenspace_neg_one_iff'] at h2'
    rw [Submodule.mem_bot]
    have h3 : (2 : K) • v = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h1]
      rw [h2', neg_add_cancel]
    exact (smul_eq_zero.mp h3).resolve_left h2
  have := Submodule.finrank_sup_add_finrank_inf_eq (U ⊓ Module.End.eigenspace A 1)
    (U ⊓ Module.End.eigenspace A (-1))
  rw [hsup, hinf, finrank_bot, add_zero] at this
  exact this

namespace A4Data

variable {A₁ A₂ B Ω : Module.End K V} (h : A4Data A₁ A₂ B Ω)
include h

theorem a₁' (v : V) : A₁ (A₁ v) = v := by
  rw [← Module.End.mul_apply, h.a₁, Module.End.one_apply]

theorem a₂' (v : V) : A₂ (A₂ v) = v := by
  rw [← Module.End.mul_apply, h.a₂, Module.End.one_apply]

theorem a₁₂' (v : V) : A₁ (A₂ v) = A₂ (A₁ v) := by
  rw [← Module.End.mul_apply, h.a₁₂, Module.End.mul_apply]

theorem b₁' (v : V) : B (A₁ v) = A₁ (B v) := by
  rw [← Module.End.mul_apply, h.b₁, Module.End.mul_apply]

theorem b₂' (v : V) : B (A₂ v) = A₂ (B v) := by
  rw [← Module.End.mul_apply, h.b₂, Module.End.mul_apply]

theorem o₁' (v : V) : Ω (A₁ v) = A₁ (A₂ (Ω v)) := by
  rw [← Module.End.mul_apply, h.o₁, Module.End.mul_apply, Module.End.mul_apply]

theorem o₂' (v : V) : Ω (A₂ v) = A₁ (Ω v) := by
  rw [← Module.End.mul_apply, h.o₂, Module.End.mul_apply]

theorem o₃' (v : V) : Ω (Ω (Ω v)) = v := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, h.o₃, Module.End.one_apply]

theorem bo' (v : V) : B (Ω v) = Ω (B v) := by
  rw [← Module.End.mul_apply, h.bo, Module.End.mul_apply]

theorem b₃' (v : V) : B (B (B v)) = v := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, h.b₃, Module.End.one_apply]

omit h in
@[expose] def eig (A₁ A₂ : Module.End K V) (s t : K) : Submodule K V :=
  Module.End.eigenspace A₁ s ⊓ Module.End.eigenspace A₂ t

omit h in
theorem mem_eig (s t : K) (v : V) : v ∈ eig A₁ A₂ s t ↔ A₁ v = s • v ∧ A₂ v = t • v := by
  rw [eig, Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff]

theorem o_V₁ {v : V} (hv : v ∈ eig A₁ A₂ 1 (-1)) : Ω v ∈ eig A₁ A₂ (-1) (-1) := by
  rw [mem_eig] at hv ⊢
  rw [one_smul] at hv
  have hA₁ : A₁ (Ω v) = -Ω v := by rw [← h.o₂', hv.2, neg_one_smul, map_neg]
  refine ⟨by rw [hA₁, neg_one_smul], ?_⟩
  have h1 : A₁ (A₂ (Ω v)) = Ω v := by rw [← h.o₁', hv.1]
  have h2 : A₂ (Ω v) = A₁ (Ω v) := by
    calc A₂ (Ω v) = A₁ (A₁ (A₂ (Ω v))) := (h.a₁' _).symm
      _ = A₁ (Ω v) := by rw [h1]
  rw [h2, hA₁, neg_one_smul]

theorem o_V₃ {v : V} (hv : v ∈ eig A₁ A₂ (-1) (-1)) : Ω v ∈ eig A₁ A₂ (-1) 1 := by
  rw [mem_eig] at hv ⊢
  rw [neg_one_smul] at hv
  have hA₁ : A₁ (Ω v) = -Ω v := by rw [← h.o₂', hv.2, map_neg]
  refine ⟨by rw [hA₁, neg_one_smul], ?_⟩
  have h1 : A₁ (A₂ (Ω v)) = -Ω v := by rw [← h.o₁', hv.1, map_neg]
  have h2 : A₂ (Ω v) = A₁ (-Ω v) := by
    calc A₂ (Ω v) = A₁ (A₁ (A₂ (Ω v))) := (h.a₁' _).symm
      _ = A₁ (-Ω v) := by rw [h1]
  rw [h2, map_neg, hA₁, neg_neg, one_smul]

theorem o_V₂ {v : V} (hv : v ∈ eig A₁ A₂ (-1) 1) : Ω v ∈ eig A₁ A₂ 1 (-1) := by
  rw [mem_eig] at hv ⊢
  rw [one_smul] at hv
  have hA₁ : A₁ (Ω v) = Ω v := by rw [← h.o₂', hv.2]
  refine ⟨by rw [hA₁, one_smul], ?_⟩
  have h1 : A₁ (A₂ (Ω v)) = -Ω v := by rw [← h.o₁', hv.1, neg_one_smul, map_neg]
  have h2 : A₂ (Ω v) = A₁ (-Ω v) := by
    calc A₂ (Ω v) = A₁ (A₁ (A₂ (Ω v))) := (h.a₁' _).symm
      _ = A₁ (-Ω v) := by rw [h1]
  rw [h2, map_neg, hA₁, neg_one_smul]

theorem b_eig {s t : K} {v : V} (hv : v ∈ eig A₁ A₂ s t) : B v ∈ eig A₁ A₂ s t := by
  rw [mem_eig] at hv ⊢
  rw [← h.b₁', hv.1, map_smul, ← h.b₂', hv.2, map_smul]
  exact ⟨rfl, rfl⟩

theorem o_injective : Function.Injective Ω := by
  intro v w hvw
  have := congrArg (fun x => Ω (Ω x)) hvw
  simp only [h.o₃'] at this
  exact this

theorem b_injective : Function.Injective B := by
  intro v w hvw
  have := congrArg (fun x => B (B x)) hvw
  simp only [h.b₃'] at this
  exact this

variable [FiniteDimensional K V]

theorem finrank_four (h2 : (2 : K) ≠ 0) (U : Submodule K V) (hU₁ : ∀ u ∈ U, A₁ u ∈ U)
    (hU₂ : ∀ u ∈ U, A₂ u ∈ U) :
    Module.finrank K U =
      Module.finrank K ↥(U ⊓ Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ 1) +
      Module.finrank K ↥(U ⊓ Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ (-1)) +
      Module.finrank K ↥(U ⊓ Module.End.eigenspace A₁ (-1) ⊓ Module.End.eigenspace A₂ 1) +
      Module.finrank K ↥(U ⊓ Module.End.eigenspace A₁ (-1) ⊓
        Module.End.eigenspace A₂ (-1)) := by
  have hs := finrank_split h2 h.a₁ U hU₁
  have hinv : ∀ s : K, ∀ u ∈ U ⊓ Module.End.eigenspace A₁ s, A₂ u ∈
      U ⊓ Module.End.eigenspace A₁ s := by
    intro s u hu
    obtain ⟨huU, hus⟩ := Submodule.mem_inf.mp hu
    refine Submodule.mem_inf.mpr ⟨hU₂ u huU, ?_⟩
    rw [Module.End.mem_eigenspace_iff] at hus ⊢
    rw [h.a₁₂', hus, map_smul]
  have hp := finrank_split h2 h.a₂ _ (hinv 1)
  have hm := finrank_split h2 h.a₂ _ (hinv (-1))
  omega

omit [FiniteDimensional K V] in
theorem o₁₂' (v : V) : Ω (A₁ (A₂ v)) = A₂ (Ω v) := by
  rw [h.o₁', h.o₂', ← h.a₁₂' (Ω v), h.a₁']

omit [FiniteDimensional K V] in
theorem a₂₁' (v : V) : A₂ (A₁ v) = A₁ (A₂ v) := (h.a₁₂' v).symm

omit h in
@[expose] noncomputable def P₀ (A₁ A₂ : Module.End K V) : Module.End K V :=
  (4 : K)⁻¹ • (1 + A₁ + A₂ + A₁ * A₂)

omit h in
@[expose] noncomputable def P₁ (A₁ A₂ : Module.End K V) : Module.End K V :=
  (4 : K)⁻¹ • (1 + A₁ - A₂ - A₁ * A₂)

omit h in
@[expose] noncomputable def P₂ (A₁ A₂ : Module.End K V) : Module.End K V :=
  (4 : K)⁻¹ • (1 - A₁ + A₂ - A₁ * A₂)

omit h in
@[expose] noncomputable def P₃ (A₁ A₂ : Module.End K V) : Module.End K V :=
  (4 : K)⁻¹ • (1 - A₁ - A₂ + A₁ * A₂)

omit h [FiniteDimensional K V] in
theorem P₀_apply (v : V) : P₀ A₁ A₂ v = (4 : K)⁻¹ • (v + A₁ v + A₂ v + A₁ (A₂ v)) := rfl

omit h [FiniteDimensional K V] in
theorem P₁_apply (v : V) : P₁ A₁ A₂ v = (4 : K)⁻¹ • (v + A₁ v - A₂ v - A₁ (A₂ v)) := rfl

omit h [FiniteDimensional K V] in
theorem P₂_apply (v : V) : P₂ A₁ A₂ v = (4 : K)⁻¹ • (v - A₁ v + A₂ v - A₁ (A₂ v)) := rfl

omit h [FiniteDimensional K V] in
theorem P₃_apply (v : V) : P₃ A₁ A₂ v = (4 : K)⁻¹ • (v - A₁ v - A₂ v + A₁ (A₂ v)) := rfl

omit h [FiniteDimensional K V] in
theorem four_ne_zero' (h2 : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  have : (4 : K) = 2 * 2 := by norm_num
  rw [this]
  exact mul_ne_zero h2 h2

omit h [FiniteDimensional K V] in
theorem sum_P (h2 : (2 : K) ≠ 0) (v : V) :
    P₀ A₁ A₂ v + P₁ A₁ A₂ v + P₂ A₁ A₂ v + P₃ A₁ A₂ v = v := by
  rw [P₀_apply, P₁_apply, P₂_apply, P₃_apply, ← smul_add, ← smul_add, ← smul_add]
  have : v + A₁ v + A₂ v + A₁ (A₂ v) + (v + A₁ v - A₂ v - A₁ (A₂ v)) +
      (v - A₁ v + A₂ v - A₁ (A₂ v)) + (v - A₁ v - A₂ v + A₁ (A₂ v)) = (4 : K) • v := by
    module
  rw [this, smul_smul, inv_mul_cancel₀ (four_ne_zero' h2), one_smul]

omit [FiniteDimensional K V] in
theorem P₀_mem (v : V) : P₀ A₁ A₂ v ∈ Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ 1 := by
  rw [Submodule.mem_inf, mem_eigenspace_one_iff', mem_eigenspace_one_iff', P₀_apply, map_smul,
    map_smul]
  have e1 : A₁ (v + A₁ v + A₂ v + A₁ (A₂ v)) = v + A₁ v + A₂ v + A₁ (A₂ v) := by
    simp only [map_add, h.a₁']
    abel
  have e2 : A₂ (v + A₁ v + A₂ v + A₁ (A₂ v)) = v + A₁ v + A₂ v + A₁ (A₂ v) := by
    simp only [map_add, h.a₂', h.a₂₁']
    abel
  rw [e1, e2]
  exact ⟨rfl, rfl⟩

omit [FiniteDimensional K V] in
theorem P₁_mem (v : V) :
    P₁ A₁ A₂ v ∈ Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ (-1) := by
  rw [Submodule.mem_inf, mem_eigenspace_one_iff', mem_eigenspace_neg_one_iff', P₁_apply,
    map_smul, map_smul]
  have e1 : A₁ (v + A₁ v - A₂ v - A₁ (A₂ v)) = v + A₁ v - A₂ v - A₁ (A₂ v) := by
    simp only [map_add, map_sub, h.a₁']
    abel
  have e2 : A₂ (v + A₁ v - A₂ v - A₁ (A₂ v)) = -(v + A₁ v - A₂ v - A₁ (A₂ v)) := by
    simp only [map_add, map_sub, h.a₂', h.a₂₁']
    abel
  rw [e1, e2, smul_neg]
  exact ⟨rfl, rfl⟩

omit [FiniteDimensional K V] in
theorem P₂_mem (v : V) :
    P₂ A₁ A₂ v ∈ Module.End.eigenspace A₁ (-1) ⊓ Module.End.eigenspace A₂ 1 := by
  rw [Submodule.mem_inf, mem_eigenspace_neg_one_iff', mem_eigenspace_one_iff', P₂_apply,
    map_smul, map_smul]
  have e1 : A₁ (v - A₁ v + A₂ v - A₁ (A₂ v)) = -(v - A₁ v + A₂ v - A₁ (A₂ v)) := by
    simp only [map_add, map_sub, h.a₁']
    abel
  have e2 : A₂ (v - A₁ v + A₂ v - A₁ (A₂ v)) = v - A₁ v + A₂ v - A₁ (A₂ v) := by
    simp only [map_add, map_sub, h.a₂', h.a₂₁']
    abel
  rw [e1, e2, smul_neg]
  exact ⟨rfl, rfl⟩

omit [FiniteDimensional K V] in
theorem P₃_mem (v : V) :
    P₃ A₁ A₂ v ∈ Module.End.eigenspace A₁ (-1) ⊓ Module.End.eigenspace A₂ (-1) := by
  rw [Submodule.mem_inf, mem_eigenspace_neg_one_iff', mem_eigenspace_neg_one_iff', P₃_apply,
    map_smul, map_smul]
  have e1 : A₁ (v - A₁ v - A₂ v + A₁ (A₂ v)) = -(v - A₁ v - A₂ v + A₁ (A₂ v)) := by
    simp only [map_add, map_sub, h.a₁']
    abel
  have e2 : A₂ (v - A₁ v - A₂ v + A₁ (A₂ v)) = -(v - A₁ v - A₂ v + A₁ (A₂ v)) := by
    simp only [map_add, map_sub, h.a₂', h.a₂₁']
    abel
  rw [e1, e2, smul_neg]
  exact ⟨rfl, rfl⟩

omit h [FiniteDimensional K V] in
theorem P₀_of_mem {s t : K} {v : V} (hv : v ∈ Module.End.eigenspace A₁ s ⊓
    Module.End.eigenspace A₂ t) : P₀ A₁ A₂ v = ((4 : K)⁻¹ * (1 + s + t + s * t)) • v := by
  rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff] at hv
  rw [P₀_apply, hv.2, map_smul, hv.1]
  module

omit h [FiniteDimensional K V] in
theorem P₁_of_mem {s t : K} {v : V} (hv : v ∈ Module.End.eigenspace A₁ s ⊓
    Module.End.eigenspace A₂ t) : P₁ A₁ A₂ v = ((4 : K)⁻¹ * (1 + s - t - s * t)) • v := by
  rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff] at hv
  rw [P₁_apply, hv.2, map_smul, hv.1]
  module

omit [FiniteDimensional K V] in
theorem o_P₀ (v : V) : Ω (P₀ A₁ A₂ v) = P₀ A₁ A₂ (Ω v) := by
  rw [P₀_apply, P₀_apply, map_smul]
  congr 1
  simp only [map_add, h.o₁₂', h.o₁', h.o₂']
  abel

omit [FiniteDimensional K V] in
theorem o_P₁ (v : V) : Ω (P₁ A₁ A₂ v) = P₃ A₁ A₂ (Ω v) := by
  rw [P₁_apply, P₃_apply, map_smul]
  congr 1
  simp only [map_add, map_sub, h.o₁₂', h.o₁', h.o₂']
  abel

omit [FiniteDimensional K V] in
theorem o_P₃ (v : V) : Ω (P₃ A₁ A₂ v) = P₂ A₁ A₂ (Ω v) := by
  rw [P₃_apply, P₂_apply, map_smul]
  congr 1
  simp only [map_add, map_sub, h.o₁₂', h.o₁', h.o₂']
  abel

omit [FiniteDimensional K V] in
theorem b_P₀ (v : V) : B (P₀ A₁ A₂ v) = P₀ A₁ A₂ (B v) := by
  rw [P₀_apply, P₀_apply, map_smul]
  simp only [map_add, h.b₁', h.b₂']

omit [FiniteDimensional K V] in
theorem b_P₁ (v : V) : B (P₁ A₁ A₂ v) = P₁ A₁ A₂ (B v) := by
  rw [P₁_apply, P₁_apply, map_smul]
  simp only [map_add, map_sub, h.b₁', h.b₂']

omit [FiniteDimensional K V] in
theorem b_P₂ (v : V) : B (P₂ A₁ A₂ v) = P₂ A₁ A₂ (B v) := by
  rw [P₂_apply, P₂_apply, map_smul]
  simp only [map_add, map_sub, h.b₁', h.b₂']

omit [FiniteDimensional K V] in
theorem b_P₃ (v : V) : B (P₃ A₁ A₂ v) = P₃ A₁ A₂ (B v) := by
  rw [P₃_apply, P₃_apply, map_smul]
  simp only [map_add, map_sub, h.b₁', h.b₂']

omit h in
theorem finrank_le_of_mapsTo {f : Module.End K V} (hf : Function.Injective f)
    {S T : Submodule K V} (hST : ∀ v ∈ S, f v ∈ T) :
    Module.finrank K S ≤ Module.finrank K T := by
  refine LinearMap.finrank_le_finrank_of_injective (f := f.restrict hST) ?_
  intro v w hvw
  apply Subtype.ext
  apply hf
  have := congrArg Subtype.val hvw
  simpa [LinearMap.restrict_apply] using this

omit h [FiniteDimensional K V] in
theorem eq_smul_of_finrank_one {W : Submodule K V} (hW : Module.finrank K W = 1) {v : V}
    (hvW : v ∈ W) (hv0 : v ≠ 0) {μ : K} (hBv : B v = μ • v) : ∀ w ∈ W, B w = μ • w := by
  intro w hw
  have hv0' : (⟨v, hvW⟩ : W) ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hvW⟩ : W) hv0').mp hW ⟨w, hw⟩
  have hc' : c • v = w := congrArg Subtype.val hc
  rw [← hc', map_smul, hBv, smul_comm]

theorem false_of_A4_three (h2 : (2 : K) ≠ 0) (hA₁1 : A₁ ≠ 1)
    (hd : Module.finrank K (Module.End.eigenspace A₁ 1) ≤ 2)
    (hBΩ : Module.finrank K (Module.End.eigenspace B 1) =
      Module.finrank K (Module.End.eigenspace Ω 1))
    (hBinv : ∀ μ : K, Module.finrank K (Module.End.eigenspace B μ) =
      Module.finrank K (Module.End.eigenspace (B * B) μ)) : False := by
  have h4 := four_ne_zero' h2
  have hinv4 : (4 : K)⁻¹ * 4 = 1 := inv_mul_cancel₀ h4
  have h13 : Module.finrank K ↥(Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ (-1)) ≤
      Module.finrank K ↥(Module.End.eigenspace A₁ (-1) ⊓ Module.End.eigenspace A₂ (-1)) :=
    finrank_le_of_mapsTo h.o_injective fun v hv => h.o_V₁ hv
  have h32 : Module.finrank K ↥(Module.End.eigenspace A₁ (-1) ⊓ Module.End.eigenspace A₂ (-1)) ≤
      Module.finrank K ↥(Module.End.eigenspace A₁ (-1) ⊓ Module.End.eigenspace A₂ 1) :=
    finrank_le_of_mapsTo h.o_injective fun v hv => h.o_V₃ hv
  have h21 : Module.finrank K ↥(Module.End.eigenspace A₁ (-1) ⊓ Module.End.eigenspace A₂ 1) ≤
      Module.finrank K ↥(Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ (-1)) :=
    finrank_le_of_mapsTo h.o_injective fun v hv => h.o_V₂ hv
  have hE1 : Module.finrank K (Module.End.eigenspace A₁ 1) =
      Module.finrank K ↥(Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ 1) +
      Module.finrank K ↥(Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ (-1)) := by
    refine finrank_split h2 h.a₂ _ fun u hu => ?_
    rw [mem_eigenspace_one_iff'] at hu ⊢
    rw [← h.a₂₁', hu]
  have he : 1 ≤ Module.finrank K ↥(Module.End.eigenspace A₁ 1 ⊓
      Module.End.eigenspace A₂ (-1)) := by
    by_contra he0
    push Not at he0
    have hall := h.finrank_four h2 ⊤ (fun _ _ => Submodule.mem_top) (fun _ _ => Submodule.mem_top)
    rw [top_inf_eq, top_inf_eq, finrank_top] at hall
    have hW₀ : Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ 1 = ⊤ :=
      Submodule.eq_of_le_of_finrank_eq le_top (by rw [finrank_top]; omega)
    apply hA₁1
    ext v
    have hv : v ∈ Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ 1 := hW₀ ▸ Submodule.mem_top
    rw [Module.End.one_apply]
    exact (mem_eigenspace_one_iff' _ v).mp (Submodule.mem_inf.mp hv).1
  set X := Module.End.eigenspace B 1 with hX
  have hX₁ : ∀ u ∈ X, A₁ u ∈ X := fun u hu => by
    rw [hX, mem_eigenspace_one_iff'] at hu ⊢
    rw [h.b₁', hu]
  have hX₂ : ∀ u ∈ X, A₂ u ∈ X := fun u hu => by
    rw [hX, mem_eigenspace_one_iff'] at hu ⊢
    rw [h.b₂', hu]
  have hXΩ : ∀ u ∈ X, Ω u ∈ X := fun u hu => by
    rw [hX, mem_eigenspace_one_iff'] at hu ⊢
    rw [h.bo', hu]
  have hXfour := h.finrank_four h2 X hX₁ hX₂
  have hx13 : Module.finrank K ↥(X ⊓ Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ (-1)) ≤
      Module.finrank K ↥(X ⊓ Module.End.eigenspace A₁ (-1) ⊓ Module.End.eigenspace A₂ (-1)) :=
    finrank_le_of_mapsTo h.o_injective fun v hv => by
      obtain ⟨⟨hvX, hv1⟩, hv2⟩ := hv
      have := h.o_V₁ (v := v) ⟨hv1, hv2⟩
      exact ⟨⟨hXΩ v hvX, this.1⟩, this.2⟩
  have hx32 : Module.finrank K
      ↥(X ⊓ Module.End.eigenspace A₁ (-1) ⊓ Module.End.eigenspace A₂ (-1)) ≤
      Module.finrank K ↥(X ⊓ Module.End.eigenspace A₁ (-1) ⊓ Module.End.eigenspace A₂ 1) :=
    finrank_le_of_mapsTo h.o_injective fun v hv => by
      obtain ⟨⟨hvX, hv1⟩, hv2⟩ := hv
      have := h.o_V₃ (v := v) ⟨hv1, hv2⟩
      exact ⟨⟨hXΩ v hvX, this.1⟩, this.2⟩
  have hx21 : Module.finrank K ↥(X ⊓ Module.End.eigenspace A₁ (-1) ⊓ Module.End.eigenspace A₂ 1) ≤
      Module.finrank K ↥(X ⊓ Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ (-1)) :=
    finrank_le_of_mapsTo h.o_injective fun v hv => by
      obtain ⟨⟨hvX, hv1⟩, hv2⟩ := hv
      have := h.o_V₂ (v := v) ⟨hv1, hv2⟩
      exact ⟨⟨hXΩ v hvX, this.1⟩, this.2⟩
  have hx0 : Module.finrank K ↥(X ⊓ Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ 1) ≤
      Module.finrank K ↥(Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ 1) :=
    Submodule.finrank_mono (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  have hx1 : Module.finrank K ↥(X ⊓ Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ (-1)) ≤
      Module.finrank K ↥(Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ (-1)) :=
    Submodule.finrank_mono (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  set Y := Module.End.eigenspace Ω 1 with hY
  set M := LinearMap.ker (P₀ A₁ A₂) with hM
  have hP₀id : ∀ v ∈ Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ 1,
      P₀ A₁ A₂ v = v := fun v hv => by
    rw [P₀_of_mem hv, show (4 : K)⁻¹ * (1 + 1 + 1 + 1 * 1) = 1 by
      rw [show (1 : K) + 1 + 1 + 1 * 1 = 4 by norm_num, hinv4], one_smul]
  have hY₀M : Module.finrank K Y = Module.finrank K ↥(Y ⊓ (Module.End.eigenspace A₁ 1 ⊓
      Module.End.eigenspace A₂ 1)) + Module.finrank K ↥(Y ⊓ M) := by
    have hsup : (Y ⊓ (Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ 1)) ⊔ (Y ⊓ M) = Y := by
      apply le_antisymm (sup_le inf_le_left inf_le_left)
      intro y hy
      have hyΩ : Ω y = y := (mem_eigenspace_one_iff' _ y).mp hy
      have hP : P₀ A₁ A₂ y ∈ Y := by
        rw [hY, mem_eigenspace_one_iff', h.o_P₀, hyΩ]
      have hdec : y = P₀ A₁ A₂ y + (y - P₀ A₁ A₂ y) := by abel
      rw [hdec]
      refine Submodule.add_mem_sup ⟨hP, h.P₀_mem y⟩ ⟨sub_mem hy hP, ?_⟩
      rw [SetLike.mem_coe, hM, LinearMap.mem_ker, map_sub, hP₀id _ (h.P₀_mem y), sub_self]
    have hinf : (Y ⊓ (Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ 1)) ⊓ (Y ⊓ M) = ⊥ := by
      rw [eq_bot_iff]
      rintro v ⟨⟨-, hv₀⟩, ⟨-, hvM⟩⟩
      rw [SetLike.mem_coe, hM, LinearMap.mem_ker, hP₀id v hv₀] at hvM
      exact (Submodule.mem_bot K).mpr hvM
    have := Submodule.finrank_sup_add_finrank_inf_eq
      (Y ⊓ (Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ 1)) (Y ⊓ M)
    rw [hsup, hinf, finrank_bot, add_zero] at this
    exact this
  have hy0 : Module.finrank K ↥(Y ⊓ (Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ 1)) ≤
      Module.finrank K ↥(Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ 1) :=
    Submodule.finrank_mono inf_le_right
  have hP₀W : ∀ {s t : K}, 1 + s + t + s * t = 0 → ∀ v ∈ Module.End.eigenspace A₁ s ⊓
      Module.End.eigenspace A₂ t, P₀ A₁ A₂ v = 0 := fun hst v hv => by
    rw [P₀_of_mem hv, hst, mul_zero, zero_smul]
  have hP₁W : ∀ {s t : K}, 1 + s - t - s * t = 0 → ∀ v ∈ Module.End.eigenspace A₁ s ⊓
      Module.End.eigenspace A₂ t, P₁ A₁ A₂ v = 0 := fun hst v hv => by
    rw [P₁_of_mem hv, hst, mul_zero, zero_smul]
  have hz1 : Module.finrank K ↥(Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ (-1)) ≤
      Module.finrank K ↥(Y ⊓ M) := by
    set φ : Module.End K V := 1 + Ω + Ω * Ω with hφ
    have hφapp : ∀ v, φ v = v + Ω v + Ω (Ω v) := fun v => rfl
    have hmaps : ∀ v ∈ Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ (-1),
        φ v ∈ Y ⊓ M := by
      intro v hv
      have h3 := h.o_V₁ hv
      have h2' := h.o_V₃ h3
      refine ⟨?_, ?_⟩
      · rw [SetLike.mem_coe, hY, mem_eigenspace_one_iff', hφapp, map_add, map_add, h.o₃']
        abel
      · rw [SetLike.mem_coe, hM, LinearMap.mem_ker, hφapp, map_add, map_add,
          hP₀W (by norm_num) v hv, hP₀W (by norm_num) _ h3, hP₀W (by norm_num) _ h2', add_zero,
          add_zero]
    refine LinearMap.finrank_le_finrank_of_injective (f := φ.restrict hmaps) ?_
    intro v w hvw
    have hsum : ∀ u ∈ Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ (-1),
        P₁ A₁ A₂ (φ u) = u := by
      intro u hu
      have h3 := h.o_V₁ hu
      have h2' := h.o_V₃ h3
      rw [hφapp, map_add, map_add, hP₁W (by norm_num) _ h3, hP₁W (by norm_num) _ h2', add_zero,
        add_zero, P₁_of_mem hu, show (4 : K)⁻¹ * (1 + 1 - -1 - 1 * -1) = 1 by
          rw [show (1 : K) + 1 - -1 - 1 * -1 = 4 by norm_num, hinv4], one_smul]
    apply Subtype.ext
    have h1 := congrArg (fun x : ↥(Y ⊓ M) => P₁ A₁ A₂ (x : V)) hvw
    simp only [LinearMap.restrict_apply] at h1
    rw [hsum v v.2, hsum w w.2] at h1
    exact h1
  have hz2 : Module.finrank K ↥(Y ⊓ M) ≤
      Module.finrank K ↥(Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ (-1)) := by
    have hmaps : ∀ v ∈ Y ⊓ M, P₁ A₁ A₂ v ∈
        Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ (-1) := fun v _ => h.P₁_mem v
    refine LinearMap.finrank_le_finrank_of_injective (f := (P₁ A₁ A₂).restrict hmaps) ?_
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨w, hwY, hwM⟩ hw
    rw [LinearMap.mem_ker] at hw
    have hw1 : P₁ A₁ A₂ w = 0 := congrArg Subtype.val hw
    have hwΩ : Ω w = w := (mem_eigenspace_one_iff' _ w).mp hwY
    have hw0 : P₀ A₁ A₂ w = 0 := hwM
    have hw3 : P₃ A₁ A₂ w = 0 := by rw [← hwΩ, ← h.o_P₁, hw1, map_zero]
    have hw2 : P₂ A₁ A₂ w = 0 := by rw [← hwΩ, ← h.o_P₃, hw3, map_zero]
    have hwsum := sum_P (A₁ := A₁) (A₂ := A₂) h2 w
    rw [hw0, hw1, hw2, hw3, add_zero, add_zero, add_zero] at hwsum
    rw [Submodule.mem_bot]
    exact Subtype.ext hwsum.symm
  have hBΩ' := hBΩ
  rw [hXfour, hY₀M] at hBΩ'
  have hx1zero : Module.finrank K ↥(X ⊓ Module.End.eigenspace A₁ 1 ⊓
      Module.End.eigenspace A₂ (-1)) = 0 := by omega
  have hx0eq : Module.finrank K ↥(X ⊓ Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ 1) =
      Module.finrank K ↥(Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ 1) := by omega
  have he1 : Module.finrank K
      ↥(Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ (-1)) = 1 := by
    omega
  have he3 : Module.finrank K
      ↥(Module.End.eigenspace A₁ (-1) ⊓ Module.End.eigenspace A₂ (-1)) = 1 := by
    omega
  have he2 : Module.finrank K
      ↥(Module.End.eigenspace A₁ (-1) ⊓ Module.End.eigenspace A₂ 1) = 1 := by
    omega
  have hB₀ : ∀ v ∈ Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ 1, B v = v := by
    have heq : X ⊓ Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ 1 =
        Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ 1 :=
      Submodule.eq_of_le_of_finrank_eq (le_inf (inf_le_left.trans inf_le_right) inf_le_right) hx0eq
    intro v hv
    rw [← heq] at hv
    exact (mem_eigenspace_one_iff' _ v).mp hv.1.1
  have hV₁ := he1
  rw [finrank_eq_one_iff'] at hV₁
  obtain ⟨⟨v₁, hv₁W⟩, hv₁0, -⟩ := hV₁
  have hv₁0' : v₁ ≠ 0 := fun hv => hv₁0 (Subtype.ext hv)
  have hBv₁ : B v₁ ∈ Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ (-1) := h.b_eig hv₁W
  have hV₁' := (finrank_eq_one_iff_of_nonzero' (⟨v₁, hv₁W⟩ :
    ↥(Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ (-1))) hv₁0).mp he1
  obtain ⟨μ, hμ⟩ := hV₁' ⟨B v₁, hBv₁⟩
  have hμ' : B v₁ = μ • v₁ := (congrArg Subtype.val hμ).symm
  have hμ1 : μ ≠ 1 := by
    intro hμ1
    rw [hμ1, one_smul] at hμ'
    have hmem : v₁ ∈ X ⊓ Module.End.eigenspace A₁ 1 ⊓ Module.End.eigenspace A₂ (-1) :=
      ⟨⟨(mem_eigenspace_one_iff' _ v₁).mpr hμ', hv₁W.1⟩, hv₁W.2⟩
    rw [Submodule.finrank_eq_zero] at hx1zero
    rw [hx1zero, Submodule.mem_bot] at hmem
    exact hv₁0' hmem
  have hμ0 : μ ≠ 0 := by
    intro hμ0
    rw [hμ0, zero_smul] at hμ'
    exact hv₁0' (h.b_injective (hμ'.trans (map_zero B).symm))
  have hB₁ := eq_smul_of_finrank_one he1 hv₁W hv₁0' hμ'
  have hΩv₁ : Ω v₁ ≠ 0 := fun h0 => hv₁0' (h.o_injective (h0.trans (map_zero Ω).symm))
  have hΩΩv₁ : Ω (Ω v₁) ≠ 0 := fun h0 => hΩv₁ (h.o_injective (h0.trans (map_zero Ω).symm))
  have hB₃ := eq_smul_of_finrank_one he3 (h.o_V₁ hv₁W) hΩv₁
    (by rw [h.bo', hμ', map_smul])
  have hB₂ := eq_smul_of_finrank_one he2 (h.o_V₃ (h.o_V₁ hv₁W)) hΩΩv₁
    (by rw [h.bo', h.bo', hμ', map_smul, map_smul])
  have hpos : Module.finrank K (Module.End.eigenspace B μ) ≠ 0 := by
    intro h0
    rw [Submodule.finrank_eq_zero] at h0
    have : v₁ ∈ Module.End.eigenspace B μ := by
      rw [Module.End.mem_eigenspace_iff]
      exact hμ'
    rw [h0, Submodule.mem_bot] at this
    exact hv₁0' this
  apply hpos
  rw [hBinv μ, Submodule.finrank_eq_zero, eq_bot_iff]
  intro w hw
  rw [Module.End.mem_eigenspace_iff, Module.End.mul_apply] at hw
  rw [Submodule.mem_bot]
  have hcomp : ∀ (P : Module.End K V), (∀ v, B (P v) = P (B v)) → B (B (P w)) = μ • P w := by
    intro P hP
    rw [hP, hP, hw, map_smul]
  have hw0 : P₀ A₁ A₂ w = 0 := by
    have h1 := hcomp _ h.b_P₀
    rw [hB₀ _ (h.P₀_mem w), hB₀ _ (h.P₀_mem w)] at h1
    have h2 : (1 - μ) • P₀ A₁ A₂ w = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hμ1))
  have hscal : ∀ (P : Module.End K V) (W : Submodule K V), (∀ v, B (P v) = P (B v)) →
      (∀ u ∈ W, B u = μ • u) → P w ∈ W → P w = 0 := by
    intro P W hP hBμ hPw
    have h1 := hcomp P hP
    rw [hBμ _ hPw, map_smul, hBμ _ hPw, smul_smul] at h1
    have h2 : (μ * μ - μ) • P w = 0 := by rw [sub_smul, h1, sub_self]
    refine (smul_eq_zero.mp h2).resolve_left ?_
    rw [show μ * μ - μ = μ * (μ - 1) by ring]
    exact mul_ne_zero hμ0 (sub_ne_zero.mpr hμ1)
  have hw1 := hscal _ _ h.b_P₁ hB₁ (h.P₁_mem w)
  have hw2 := hscal _ _ h.b_P₂ hB₂ (h.P₂_mem w)
  have hw3 := hscal _ _ h.b_P₃ hB₃ (h.P₃_mem w)
  have hwsum := sum_P (A₁ := A₁) (A₂ := A₂) h2 w
  rw [hw0, hw1, hw2, hw3, add_zero, add_zero, add_zero] at hwsum
  exact hwsum.symm

end A4Data

end CFSG.RankThree.PartTwo.Sec13.Res7Proof
