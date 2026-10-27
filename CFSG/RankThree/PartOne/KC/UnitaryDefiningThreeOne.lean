module

public import CFSG.RankThree.PartOne.KC.UnitaryDefiningHermitian
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.RankThree.PartOne.KCUnitaryHerm

open CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {V : Type} [AddCommGroup V]
  [Module K V]

section Normalize

variable {B : V →ₛₗ[h.bar] V →ₗ[K] K} {N : V →ₗ[K] V}

theorem sa_two (hN : ∀ x y, B (N x) y = -B x (N y)) (x y : V) :
    B (N (N x)) y = B x (N (N y)) := by
  rw [hN (N x) y, hN x (N y), neg_neg]

theorem normalize_step_one (hN : ∀ x y, B (N x) y = -B x (N y)) (hN3 : ∀ x, N (N (N x)) = 0)
    (v : V) (a : K) :
    B (v + a • N v) (N (N (v + a • N v))) = B v (N (N v)) ∧
      B (v + a • N v) (N (v + a • N v)) =
        B v (N v) + (a - h.bar a) * B v (N (N v)) := by
  have hz1 : B (N v) (N (N v)) = 0 := by
    rw [hN v (N (N v)), hN3 v, map_zero, neg_zero]
  have hz2 : B (N v) (N v) = -B v (N (N v)) := hN v (N v)
  have e1 : N (v + a • N v) = N v + a • N (N v) := by rw [map_add, map_smul]
  have e2 : N (N (v + a • N v)) = N (N v) := by
    rw [e1, map_add, map_smul, hN3, smul_zero, add_zero]
  rw [e2, e1]
  constructor
  · simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hz1,
      mul_zero, add_zero]
  · simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, hz1, hz2]
    ring

theorem normalize_step_two (hN : ∀ x y, B (N x) y = -B x (N y)) (hN3 : ∀ x, N (N (N x)) = 0)
    (v : V) (b : K) :
    B (v + b • N (N v)) (N (N (v + b • N (N v)))) = B v (N (N v)) ∧
      B (v + b • N (N v)) (N (v + b • N (N v))) = B v (N v) ∧
      B (v + b • N (N v)) (v + b • N (N v)) =
        B v v + (b + h.bar b) * B v (N (N v)) := by
  have hz1 : B (N (N v)) (N (N v)) = 0 := by
    rw [sa_two hN v (N (N v)), hN3 (N v), map_zero]
  have hz2 : B (N (N v)) (N v) = 0 := by
    rw [sa_two hN v (N v), hN3 v, map_zero]
  have hz3 : B (N (N v)) v = B v (N (N v)) := sa_two hN v v
  have e1 : N (v + b • N (N v)) = N v := by rw [map_add, map_smul, hN3, smul_zero, add_zero]
  have e2 : N (N (v + b • N (N v))) = N (N v) := by rw [e1]
  rw [e2, e1]
  refine ⟨?_, ?_, ?_⟩
  · simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hz1,
      mul_zero, add_zero]
  · simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hz2,
      mul_zero, add_zero]
  · simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, hz1, hz3, mul_zero, add_zero]
    ring

end Normalize

variable {B : V →ₛₗ[h.bar] V →ₗ[K] K} {N : V →ₗ[K] V}

theorem exists_normalized_vector (hp3 : 3 < p) (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hN : ∀ x y, B (N x) y = -B x (N y)) (hN3 : ∀ x, N (N (N x)) = 0)
    (hN2 : ∃ x, N (N x) ≠ 0) :
    ∃ v : V, B v (N (N v)) = 1 ∧ B v (N v) = 0 ∧ B v v = 0 := by
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  have hbar_inv : ∀ c : K, h.bar c⁻¹ = (h.bar c)⁻¹ := fun c => map_inv₀ h.bar c
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_gt_three h hp3
  obtain ⟨v₀, hv₀⟩ : ∃ v, B v (N (N v)) ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ v, B v (N (N v)) = 0 := fun v => by
      by_contra hne
      exact hcon ⟨v, hne⟩
    obtain ⟨x₀, hx₀⟩ := hN2
    have hψ := eq_zero_of_forall_diag_eq_zero h hp3 (V := V) (fun x y => B x (N (N y)))
      (fun x y z => by simp only [map_add, LinearMap.add_apply])
      (fun x y z => by simp only [map_add])
      (fun c x y => by simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul])
      (fun c x y => by simp only [map_smul, smul_eq_mul])
      (fun x y => by rw [← hsymm x (N (N y)), sa_two hN y x]) hcon'
    exact hx₀ (hBl _ fun x => by rw [hsymm x (N (N x₀)), hψ x x₀, map_zero])
  set c₀ := B v₀ (N (N v₀)) with hc₀
  set d₀ := B v₀ (N v₀) with hd₀
  have hc₀bar : h.bar c₀ = c₀ := by rw [hc₀, ← hsymm v₀ (N (N v₀)), sa_two hN v₀ v₀]
  have hd₀bar : h.bar d₀ = -d₀ := by rw [hd₀, ← hsymm v₀ (N v₀), hN v₀ v₀]
  set a : K := -d₀ / (2 * c₀) with ha
  have ha2 : a - h.bar a = -d₀ / c₀ := by
    rw [ha, map_div₀, map_neg, map_mul, hd₀bar, hc₀bar, map_ofNat h.bar 2]
    field_simp
    ring
  obtain ⟨hc₁, hd₁⟩ := normalize_step_one hN hN3 v₀ a
  set v₁ := v₀ + a • N v₀ with hv₁
  have hd₁0 : B v₁ (N v₁) = 0 := by
    rw [hd₁, ha2]
    field_simp
    ring
  set s₁ := B v₁ v₁ with hs₁
  have hs₁bar : h.bar s₁ = s₁ := (hsymm v₁ v₁).symm
  obtain ⟨b, hb⟩ := exists_add_bar_eq h (d := -s₁ / c₀)
    (by rw [map_div₀, map_neg, hs₁bar, hc₀bar])
  obtain ⟨hc₂, hd₂, hs₂⟩ := normalize_step_two hN hN3 v₁ b
  set v₂ := v₁ + b • N (N v₁) with hv₂
  have hs₂0 : B v₂ v₂ = 0 := by
    have h1 : (b + h.bar b) * c₀ = -s₁ := by
      rw [hb]
      field_simp
    rw [hs₂, ← hs₁, hc₁, ← hc₀, h1]
    ring
  obtain ⟨μ, hμ⟩ := exists_bar_mul_eq h (d := c₀⁻¹) (by rw [hbar_inv, hc₀bar])
  refine ⟨μ • v₂, ?_, ?_, ?_⟩
  · simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
    rw [hc₂, hc₁, ← hc₀]
    calc _ = (h.bar μ * μ) * c₀ := by ring
      _ = 1 := by rw [hμ]; field_simp
  · simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
    rw [hd₂, hd₁0, mul_zero, mul_zero]
  · simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
    rw [hs₂0, mul_zero, mul_zero]

theorem exists_three_one_family [FiniteDimensional K V] (hp3 : 3 < p) (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (hV : Module.finrank K V = 4)
    (hN : ∀ x y, B (N x) y = -B x (N y)) (hN3 : ∀ x, N (N (N x)) = 0)
    (hN2 : ∃ x, N (N x) ≠ 0) :
    ∃ b₀ b₁ b₂ b₃ : V, B b₀ b₀ = 0 ∧ B b₀ b₁ = 0 ∧ B b₀ b₂ = 1 ∧ B b₀ b₃ = 0 ∧
      B b₁ b₁ = -1 ∧ B b₁ b₂ = 0 ∧ B b₁ b₃ = 0 ∧ B b₂ b₂ = 0 ∧ B b₂ b₃ = 0 ∧ B b₃ b₃ = 1 ∧
      N b₀ = 0 ∧ N b₁ = b₀ ∧ N b₂ = b₁ ∧ N b₃ = 0 := by
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  have hbar_inv : ∀ c : K, h.bar c⁻¹ = (h.bar c)⁻¹ := fun c => map_inv₀ h.bar c
  obtain ⟨v, hc, hd, hs⟩ := exists_normalized_vector hp3 hB hBl hN hN3 hN2
  have g00 : B (N (N v)) (N (N v)) = 0 := by rw [sa_two hN v (N (N v)), hN3 (N v), map_zero]
  have g01 : B (N (N v)) (N v) = 0 := by rw [sa_two hN v (N v), hN3 v, map_zero]
  have g02 : B (N (N v)) v = 1 := by rw [sa_two hN v v, hc]
  have g10 : B (N v) (N (N v)) = 0 := by rw [hsymm (N (N v)) (N v), g01, map_zero]
  have g11 : B (N v) (N v) = -1 := by rw [hN v (N v), hc]
  have g12 : B (N v) v = 0 := by rw [hN v v, hd, neg_zero]
  let bb : Fin 3 → V := ![N (N v), N v, v]
  let Φ : V →ₗ[K] (Fin 3 → K) := LinearMap.pi fun j => B (bb j)
  have hPhi : ∀ t : Fin 3 → K, Φ (t 2 • N (N v) - t 1 • N v + t 0 • v) = t := by
    intro t
    funext j
    fin_cases j
    · show B (N (N v)) (t 2 • N (N v) - t 1 • N v + t 0 • v) = t 0
      simp only [map_add, map_sub, map_smul, smul_eq_mul, g00, g01, g02]
      ring
    · show B (N v) (t 2 • N (N v) - t 1 • N v + t 0 • v) = t 1
      simp only [map_add, map_sub, map_smul, smul_eq_mul, g10, g11, g12]
      ring
    · show B v (t 2 • N (N v) - t 1 • N v + t 0 • v) = t 2
      simp only [map_add, map_sub, map_smul, smul_eq_mul, hc, hd, hs]
      ring
  have hrange : LinearMap.range Φ = ⊤ := LinearMap.range_eq_top.mpr fun t => ⟨_, hPhi t⟩
  have hker : Module.finrank K (LinearMap.ker Φ) = 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hrange, finrank_top, Module.finrank_fin_fun, hV] at h1
    omega
  have hpos : 0 < Module.finrank K (LinearMap.ker Φ) := by
    rw [hker]
    exact Nat.one_pos
  obtain ⟨y, hy0⟩ : ∃ y : LinearMap.ker Φ, y ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hy1 : ∀ w : LinearMap.ker Φ, ∃ c : K, c • y = w :=
    (finrank_eq_one_iff_of_nonzero' y hy0).mp hker
  have hyB : ∀ j, B (bb j) (y : V) = 0 := fun j => by
    have := congrFun (LinearMap.mem_ker.mp y.2) j
    exact this
  have hy0' : (y : V) ≠ 0 := fun e => hy0 (Subtype.ext e)
  have hyB0 : B (N (N v)) (y : V) = 0 := hyB 0
  have hyB1 : B (N v) (y : V) = 0 := hyB 1
  have hyB2 : B v (y : V) = 0 := hyB 2
  have hyB0' : B (y : V) (N (N v)) = 0 := by rw [hsymm (N (N v)) (y : V), hyB0, map_zero]
  have hyB1' : B (y : V) (N v) = 0 := by rw [hsymm (N v) (y : V), hyB1, map_zero]
  have hyB2' : B (y : V) v = 0 := by rw [hsymm v (y : V), hyB2, map_zero]
  have hyy : B (y : V) (y : V) ≠ 0 := by
    intro hyy0
    apply hy0'
    refine hBl _ fun x => ?_
    have hmem : x - (Φ x 2 • N (N v) - Φ x 1 • N v + Φ x 0 • v) ∈ LinearMap.ker Φ := by
      rw [LinearMap.mem_ker, map_sub, hPhi (Φ x), sub_self]
    obtain ⟨c, hc'⟩ := hy1 ⟨_, hmem⟩
    have hcy : c • (y : V) = x - (Φ x 2 • N (N v) - Φ x 1 • N v + Φ x 0 • v) :=
      congrArg Subtype.val hc'
    have hx : x = (Φ x 2 • N (N v) - Φ x 1 • N v + Φ x 0 • v) + c • (y : V) := by
      rw [hcy]
      abel
    rw [hx]
    simp only [map_add, map_sub, map_smul, smul_eq_mul, hyB0', hyB1', hyB2', hyy0]
    ring
  have hBN : ∀ a, B a (N (y : V)) = -B (N a) (y : V) := fun a => by rw [hN a y, neg_neg]
  have hNy : N (y : V) ∈ LinearMap.ker Φ := by
    rw [LinearMap.mem_ker]
    funext j
    fin_cases j
    · show B (N (N v)) (N (y : V)) = 0
      rw [hBN, hN3 v, map_zero, LinearMap.zero_apply, neg_zero]
    · show B (N v) (N (y : V)) = 0
      rw [hBN, hyB0, neg_zero]
    · show B v (N (y : V)) = 0
      rw [hBN, hyB1, neg_zero]
  obtain ⟨c', hc'⟩ := hy1 ⟨N (y : V), hNy⟩
  have hNyc : N (y : V) = c' • (y : V) := (congrArg Subtype.val hc').symm
  have hNy0 : N (y : V) = 0 := by
    have h2 : N (N (y : V)) = (c' * c') • (y : V) := by rw [hNyc, map_smul, hNyc, smul_smul]
    have h3 : N (N (N (y : V))) = (c' * c' * c') • (y : V) := by
      rw [h2, map_smul, hNyc, smul_smul]
    rw [hN3 (y : V)] at h3
    have h4 : c' * c' * c' = 0 := by
      by_contra hne
      exact hy0' ((smul_eq_zero.mp h3.symm).resolve_left hne)
    have h5 : c' = 0 := by simpa using h4
    rw [hNyc, h5, zero_smul]
  have hyyF : h.bar (B (y : V) (y : V)) = B (y : V) (y : V) := (hsymm (y : V) (y : V)).symm
  obtain ⟨μ, hμ⟩ := exists_bar_mul_eq h (d := (B (y : V) (y : V))⁻¹)
    (by rw [hbar_inv, hyyF])
  refine ⟨N (N v), N v, v, μ • (y : V), g00, g01, g02, ?_, g11, g12, ?_, hs, ?_, ?_, hN3 v, rfl,
    rfl, ?_⟩
  · rw [map_smul, hyB0, smul_zero]
  · rw [map_smul, hyB1, smul_zero]
  · rw [map_smul, hyB2, smul_zero]
  · simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
    calc _ = (h.bar μ * μ) * B (y : V) (y : V) := by ring
      _ = 1 := by rw [hμ]; field_simp
  · rw [map_smul, hNy0, smul_zero]

end CFSG.RankThree.PartOne.KCUnitaryHerm
