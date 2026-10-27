module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerToralCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Triality

namespace D4Inner

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem mem_centralizer_conj_iff {s h y : Om8 K} :
    y ∈ Subgroup.centralizer ({h * s * h⁻¹} : Set (Om8 K)) ↔
      h⁻¹ * y * h ∈ Subgroup.centralizer ({s} : Set (Om8 K)) := by
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hy
    calc h⁻¹ * y * h * s = h⁻¹ * (y * (h * s * h⁻¹)) * h := by group
      _ = h⁻¹ * (h * s * h⁻¹ * y) * h := by rw [hy]
      _ = s * (h⁻¹ * y * h) := by group
  · intro hy
    calc y * (h * s * h⁻¹) = h * (h⁻¹ * y * h * s) * h⁻¹ := by group
      _ = h * (s * (h⁻¹ * y * h)) * h⁻¹ := by rw [hy]
      _ = h * s * h⁻¹ * y := by group

omit [Finite K] [CharP K 2] in
theorem centralizer_conj_eq (s h : Om8 K) :
    Subgroup.centralizer ({h * s * h⁻¹} : Set (Om8 K)) =
      (Subgroup.centralizer ({s} : Set (Om8 K))).map (MulAut.conj h).toMonoidHom := by
  ext y
  rw [mem_centralizer_conj_iff]
  constructor
  · intro hy
    exact ⟨h⁻¹ * y * h, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  · rintro ⟨w, hw, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hw

omit [Finite K] [CharP K 2] in
theorem centDer_conj_eq (s h : Om8 K) :
    centDer (h * s * h⁻¹) = (centDer s).map (MulAut.conj h).toMonoidHom := by
  rw [centDer, centDer, centralizer_conj_eq, Subgroup.map_commutator]

theorem exists_triality_centralizing_of_model
    (hconj : ∀ {x z : Om8 K}, x ^ 3 = 1 → z ^ 3 = 1 → D4Rank.omFixDim x = 2 →
      D4Rank.omFixDim z = 2 → ∃ h : Om8 K, x = h * z * h⁻¹)
    (hmodel : ∃ s₀ : Om8 K, s₀ ^ 3 = 1 ∧ D4Rank.omFixDim s₀ = 2 ∧
      (∀ y ∈ centDer s₀, theta y = y) ∧
      ∀ p ∈ Subgroup.centralizer (centDer s₀ : Set (Om8 K)), p * theta p * theta (theta p) = 1)
    {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    ∃ γ : MulAut (Om8 K), D4Bstar.IsTriPart 1 γ ∧ γ ^ 3 = 1 ∧ (∀ y ∈ centDer s, γ y = y) ∧
      ∀ p ∈ Subgroup.centralizer (centDer s : Set (Om8 K)), p * γ p * γ (γ p) = 1 := by
  obtain ⟨s₀, hs₀3, hd₀, hfix₀, hN₀⟩ := hmodel
  obtain ⟨h, rfl⟩ := hconj hs3 hs₀3 hd hd₀
  set γ : MulAut (Om8 K) := MulAut.conj h * theta * MulAut.conj h⁻¹ with hγdef
  have hγ : ∀ x, γ x = h * theta (h⁻¹ * x * h) * h⁻¹ := fun x => by
    simp [hγdef, MulAut.conj_apply]
  refine ⟨γ, ⟨h * theta h⁻¹, 1, ?_⟩, ?_, ?_, ?_⟩
  · rw [hγdef, map_one, mul_one, pow_one, mul_assoc, mulAut_mul_conj', ← mul_assoc, ← map_mul]
  · rw [hγdef, map_inv, conj_pow, theta_cube, mul_one, mul_inv_cancel]
  · intro y hy
    rw [centDer_conj_eq] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hγ, show h⁻¹ * (h * y₀ * h⁻¹) * h = y₀ by group, hfix₀ y₀ hy₀]
  · intro p hp
    have hp₀ : h⁻¹ * p * h ∈ Subgroup.centralizer (centDer s₀ : Set (Om8 K)) := by
      rw [Subgroup.mem_centralizer_iff] at hp ⊢
      intro y₀ hy₀
      have hy : h * y₀ * h⁻¹ ∈ centDer (h * s₀ * h⁻¹) := by
        rw [centDer_conj_eq]; exact ⟨y₀, hy₀, by simp [MulAut.conj_apply]⟩
      have hc := hp _ hy
      calc y₀ * (h⁻¹ * p * h) = h⁻¹ * (h * y₀ * h⁻¹ * p) * h := by group
        _ = h⁻¹ * (p * (h * y₀ * h⁻¹)) * h := by rw [hc]
        _ = h⁻¹ * p * h * y₀ := by group
    rw [hγ, hγ, show h⁻¹ * (h * theta (h⁻¹ * p * h) * h⁻¹) * h = theta (h⁻¹ * p * h) by group]
    calc p * (h * theta (h⁻¹ * p * h) * h⁻¹) * (h * theta (theta (h⁻¹ * p * h)) * h⁻¹)
        = h * ((h⁻¹ * p * h) * theta (h⁻¹ * p * h) * theta (theta (h⁻¹ * p * h))) * h⁻¹ := by
          group
      _ = 1 := by rw [hN₀ _ hp₀]; group

end D4Inner

end CFSG.StandardType

end
