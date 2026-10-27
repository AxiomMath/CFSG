module

public import CFSG.Quasithin.EmptyFaithful.E111RComp
public import CFSG.Quasithin.EmptyFaithful.E111RDiag

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB
  CFSG.Quasithin.E2.E22N CFSG.Quasithin.E2.E22N.E111R

variable {G : Type} [Group G]

@[expose] def Cov (H₁ J : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (J : Set G) ∧
    ∃ y ∈ H₁, g⁻¹ * y ∈ Subgroup.centralizer (J : Set G)}
  one_mem' := ⟨Subgroup.one_mem _, 1, H₁.one_mem, by simp⟩
  mul_mem' := by
    rintro g g' ⟨hg, y, hy, hc⟩ ⟨hg', y', hy', hc'⟩
    refine ⟨Subgroup.mul_mem _ hg hg', y * y', H₁.mul_mem hy hy', ?_⟩
    have h1 : g'⁻¹ * (g⁻¹ * y) * g' ∈ Subgroup.centralizer (J : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro x hx
      have hx' : g' * x * g'⁻¹ ∈ J := by
        have := (Subgroup.mem_normalizer_iff.mp hg' x).mp hx
        exact this
      have := hc (g' * x * g'⁻¹) hx'
      calc x * (g'⁻¹ * (g⁻¹ * y) * g') = g'⁻¹ * ((g' * x * g'⁻¹) * (g⁻¹ * y)) * g' := by group
        _ = g'⁻¹ * ((g⁻¹ * y) * (g' * x * g'⁻¹)) * g' := by rw [this]
        _ = (g'⁻¹ * (g⁻¹ * y) * g') * x := by group
    have := Subgroup.mul_mem _ h1 hc'
    simpa [mul_assoc] using this
  inv_mem' := by
    rintro g ⟨hg, y, hy, hc⟩
    refine ⟨Subgroup.inv_mem _ hg, y⁻¹, H₁.inv_mem hy, ?_⟩
    have h1 : g * (g⁻¹ * y)⁻¹ * g⁻¹ ∈ Subgroup.centralizer (J : Set G) := by
      have hinv : (g⁻¹ * y)⁻¹ ∈ Subgroup.centralizer (J : Set G) := Subgroup.inv_mem _ hc
      rw [Subgroup.mem_centralizer_iff] at hinv ⊢
      intro x hx
      have hx' : g⁻¹ * x * g ∈ J := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
        simpa using this
      have h2 := hinv _ hx'
      calc x * (g * (g⁻¹ * y)⁻¹ * g⁻¹) = g * ((g⁻¹ * x * g) * (g⁻¹ * y)⁻¹) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y)⁻¹ * (g⁻¹ * x * g)) * g⁻¹ := by rw [h2]
        _ = (g * (g⁻¹ * y)⁻¹ * g⁻¹) * x := by group
    simpa [mul_assoc] using h1

theorem mem_Cov_iff {H₁ J : Subgroup G} {g : G} :
    g ∈ Cov H₁ J ↔ g ∈ Subgroup.normalizer (J : Set G) ∧
      ∃ y ∈ H₁, g⁻¹ * y ∈ Subgroup.centralizer (J : Set G) := Iff.rfl

theorem mem_Cov_of_mem {H₁ J : Subgroup G} {g : G} (hg : g ∈ H₁)
    (hgN : g ∈ Subgroup.normalizer (J : Set G)) : g ∈ Cov H₁ J :=
  ⟨hgN, g, hg, by simp⟩

theorem inf_normalizer_le_Cov (H₁ J : Subgroup G) :
    H₁ ⊓ Subgroup.normalizer (J : Set G) ≤ Cov H₁ J := fun _ hg => mem_Cov_of_mem hg.1 hg.2

theorem le_of_le_Cov {X T J H₁ : Subgroup G} (hR : E111Reduced G X T) [Finite G] (hJ : IsComp X J)
    (hinv : ∃ x ∈ J, x ≠ 1 ∧ x ^ 2 = 1) (hTH : T ≤ H₁) (hcov : J ≤ Cov H₁ J) : J ≤ H₁ :=
  le_of_diag hJ.simple (inf_ne_bot hR hJ hinv) hTH fun x hx => (hcov hx).2

end CFSG.Quasithin.RonanE111
