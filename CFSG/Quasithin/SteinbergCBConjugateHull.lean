module

public import CFSG.Quasithin.SteinbergCBIrreducibleTI

public section

namespace CFSG.Quasithin.SteinbergCB

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem linear_conjugate_hull_normalizer_containment [Finite G] {V T : Subgroup G}
    (_hVT : V ≤ T) :
    ∀ Y : Subgroup G,
      (⨆ g : {g : G // MulAut.conj g⁻¹ • V ≤ T}, MulAut.conj (g : G)⁻¹ • V) ≤ Y → Y ≤ T →
      normalizer (Y : Set G) ≤
          normalizer (((⨆ g : {g : G // MulAut.conj g⁻¹ • V ≤ T},
            MulAut.conj (g : G)⁻¹ • V : Subgroup G)) : Set G) ∧
        (¬ (⨆ g : {g : G // MulAut.conj g⁻¹ • V ≤ T}, MulAut.conj (g : G)⁻¹ • V).Normal →
          ∀ M : Subgroup G, IsCoatom M → normalizer (Y : Set G) ≤ M →
            (∀ M' : Subgroup G, IsCoatom M' → normalizer (Y : Set G) ≤ M' → M' = M) →
            normalizer (((⨆ g : {g : G // MulAut.conj g⁻¹ • V ≤ T},
                MulAut.conj (g : G)⁻¹ • V : Subgroup G)) : Set G) ≤ M ∧
              ∀ M' : Subgroup G, IsCoatom M' →
                normalizer (((⨆ g : {g : G // MulAut.conj g⁻¹ • V ≤ T},
                  MulAut.conj (g : G)⁻¹ • V : Subgroup G)) : Set G) ≤ M' → M' = M) := by
  intro Y hWY hYT
  set W := ⨆ g : {g : G // MulAut.conj g⁻¹ • V ≤ T}, MulAut.conj (g : G)⁻¹ • V with hW
  have hconj : ∀ n ∈ normalizer (Y : Set G), ∀ w ∈ W, n * w * n⁻¹ ∈ W := by
    intro n hn w hw
    refine Subgroup.iSup_induction _ (C := fun w => n * w * n⁻¹ ∈ W) hw ?_ ?_ ?_
    · rintro ⟨g, hg⟩ x hx
      have hgW : MulAut.conj g⁻¹ • V ≤ Y := fun y hy =>
        hWY (Subgroup.mem_iSup_of_mem (⟨g, hg⟩ : {g : G // MulAut.conj g⁻¹ • V ≤ T}) hy)
      have hle : MulAut.conj (g * n⁻¹)⁻¹ • V ≤ T := by
        intro y hy
        rw [mem_conj_inv_smul_iff] at hy
        have h1 : n⁻¹ * y * n ∈ MulAut.conj g⁻¹ • V := by
          rw [mem_conj_inv_smul_iff]
          have : g * (n⁻¹ * y * n) * g⁻¹ = g * n⁻¹ * y * (g * n⁻¹)⁻¹ := by group
          rw [this]
          exact hy
        have h2 := (mem_normalizer_iff.1 hn (n⁻¹ * y * n)).1 (hgW h1)
        have : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
        rw [this] at h2
        exact hYT h2
      refine Subgroup.mem_iSup_of_mem (⟨g * n⁻¹, hle⟩ : {g : G // MulAut.conj g⁻¹ • V ≤ T}) ?_
      rw [mem_conj_inv_smul_iff] at hx ⊢
      have : g * n⁻¹ * (n * x * n⁻¹) * (g * n⁻¹)⁻¹ = g * x * g⁻¹ := by group
      change g * n⁻¹ * (n * x * n⁻¹) * (g * n⁻¹)⁻¹ ∈ V
      rw [this]
      exact hx
    · simp only [mul_one, mul_inv_cancel]
      exact W.one_mem
    · intro x y hx hy
      have : n * (x * y) * n⁻¹ = n * x * n⁻¹ * (n * y * n⁻¹) := by group
      change n * (x * y) * n⁻¹ ∈ W
      rw [this]
      exact W.mul_mem hx hy
  have hNY : normalizer (Y : Set G) ≤ normalizer (W : Set G) := by
    intro n hn
    rw [mem_normalizer_iff]
    intro h
    refine ⟨hconj n hn h, fun hh => ?_⟩
    have := hconj n⁻¹ (inv_mem hn) _ hh
    have heq : n⁻¹ * (n * h * n⁻¹) * n⁻¹⁻¹ = h := by group
    rwa [heq] at this
  refine ⟨hNY, fun hWn M hM hYM huniq => ?_⟩
  have hntop : normalizer (W : Set G) ≠ ⊤ := fun h => hWn (normalizer_eq_top_iff.1 h)
  obtain ⟨R, hR, hWR⟩ := (eq_top_or_exists_le_coatom (normalizer (W : Set G))).resolve_left hntop
  have hRM : R = M := huniq R hR (hNY.trans hWR)
  refine ⟨hRM ▸ hWR, fun M' hM' hWM' => huniq M' hM' (hNY.trans hWM')⟩

end CFSG.Quasithin.SteinbergCB
