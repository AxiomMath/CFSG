module

public import CFSG.Quasithin.EmptyFaithful.S153GExtra

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

@[expose] def L3ULDichotomy : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → IsLnTwoQuot L 3 → Concl15312Two Yp L →
      ⁅VZ T M, YL153 Yp L⁆ = ⊥ →
      ⁅⁅WL153 T M L, L⁆, YC153 Yp L⁆ = ⊥ ∨
        ∃ y ∈ YC153 Yp L, ∀ u ∈ ⁅WL153 T M L, L⁆, y * u * y⁻¹ = u → u = 1

namespace SBd4

section Helpers

variable {G : Type} [Group G]

theorem mem_normalizer_conjClosure {Z H : Subgroup G} {g : G}
    (hgH : g ∈ Subgroup.normalizer (H : Set G)) (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) :
    g ∈ Subgroup.normalizer (conjClosure Z H : Set G) := by
  have key : ∀ g : G, g ∈ Subgroup.normalizer (H : Set G) → g ∈ Subgroup.normalizer (Z : Set G) →
      ∀ x ∈ conjClosure Z H, g * x * g⁻¹ ∈ conjClosure Z H := by
    intro g hgH hgZ x hx
    have hle : conjClosure Z H ≤ (conjClosure Z H).comap (MulAut.conj g).toMonoidHom := by
      refine conjClosure_le fun h hh z hz => ?_
      show g * (h * z * h⁻¹) * g⁻¹ ∈ conjClosure Z H
      have e : g * (h * z * h⁻¹) * g⁻¹ =
          (g * h * g⁻¹) * (g * z * g⁻¹) * (g * h * g⁻¹)⁻¹ := by group
      rw [e]
      exact mem_conjClosure ((Subgroup.mem_normalizer_iff.mp hgH h).mp hh)
        ((Subgroup.mem_normalizer_iff.mp hgZ z).mp hz)
    exact hle hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hgH hgZ x hx, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hgH) (inv_mem hgZ) _ hx
  simpa [mul_assoc] using this

end Helpers

end SBd4

end CFSG.Quasithin
