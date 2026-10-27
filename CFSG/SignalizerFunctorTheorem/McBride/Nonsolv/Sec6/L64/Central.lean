module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Central.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Central.Components
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Central.Diagonal
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Central.Monolith
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Central.Orbit
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Central.Lift
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Central.Perfect

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

theorem false_of_perfect_central_extension {p : ℕ} (hp : p.Prime) {Γ : Type u} [Group Γ]
    [Finite Γ] {A W Z : Subgroup Γ} [Z.Normal] (T : Γ → Subgroup Γ) (hA : IsElemAbelian p A)
    (hArank : p ^ 3 ≤ Nat.card A) (hAW : A ≤ Subgroup.normalizer (W : Set Γ))
    (hWp : Nat.Coprime p (Nat.card W)) (hperf : ⁅W, W⁆ = W) (hZW : Z ≤ W)
    (hZc : ∀ z ∈ Z, ∀ w ∈ W, z * w = w * z) (hZ1 : Z ≠ ⊥)
    (hAZ : A ≤ Subgroup.normalizer (Z : Set Γ)) (hAZ' : A ⊓ Z = ⊥)
    (hZmin : ∀ Z' : Subgroup Γ, Z' ≤ Z → A ≤ Subgroup.normalizer (Z' : Set Γ) →
      Z' = ⊥ ∨ Z' = Z)
    (hT : ∀ b ∈ A, b ≠ 1 → T b ≤ W ∧ T b ⊓ Z = ⊥ ∧
      ∀ w ∈ W ⊓ Subgroup.centralizer {b}, ∃ z ∈ Z, ∃ t ∈ T b, w = z * t)
    (hTM : ∀ M : Subgroup Γ, M ≤ W → (M.subgroupOf W).Normal →
      A ≤ Subgroup.normalizer (M : Set Γ) → M ≠ W → ∀ b ∈ A, b ≠ 1 → T b ⊓ M = ⊥)
    (hB : signalizerMcBrideHypothesisB p (W.map (QuotientGroup.mk' Z))) : False := by
  have h : PerfectCentral.Setup p A W Z T :=
    ⟨hp, hA, hArank, hAW, hWp, hperf, hZW, hZc, hZ1, hAZ, hAZ', hZmin, hT, hTM⟩
  have hAs := h.isASimple
  obtain ⟨J₀, hJ₀⟩ := hAs.simpleComponents_nonempty
  obtain ⟨a, haA, haZ, hmove⟩ := h.exists_good hB hJ₀
  refine h.false_of_liftOf_inf_eq_bot fun J hJ => h.liftOf_inf_eq_bot hJ haA haZ fun hstab => ?_
  refine hmove (PerfectCentral.mem_stab_iff.mpr ⟨hstab.1, ?_⟩)
  have hiff := hAs.normalizes_component_iff h.isElemAbelian_map.1 hJ hJ₀
    (Subgroup.mem_map_of_mem (QuotientGroup.mk' Z) haA)
  have h1 := PerfectCentral.mem_stab_iff.mp hstab
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 ⊢
  exact hiff.mp h1.2

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
