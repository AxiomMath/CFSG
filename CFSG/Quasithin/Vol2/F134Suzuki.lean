module

public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.F134

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

theorem commutator_mem_sup_centralizer {A : Type*} [Group A] (L : Subgroup A)
    (hcomm : ∀ x y : Outer L, x * y = y * x) {a b : A}
    (ha : a ∈ Subgroup.normalizer (L : Set A)) (hb : b ∈ Subgroup.normalizer (L : Set A)) :
    ⁅a, b⁆ ∈ L ⊔ Subgroup.centralizer (L : Set A) := by
  set N := Subgroup.normalizer (L : Set A)
  let ρ : N →* MulAut L := L.normalizerMonoidHom
  let π : MulAut L →* Outer L := QuotientGroup.mk' (inner L)
  have h1 : π (ρ ⁅(⟨a, ha⟩ : N), ⟨b, hb⟩⁆) = 1 := by
    rw [map_commutatorElement, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  have h2 : ρ ⁅(⟨a, ha⟩ : N), ⟨b, hb⟩⁆ ∈ inner L := (QuotientGroup.eq_one_iff _).1 h1
  obtain ⟨l, hl⟩ := h2
  have hc : ((⁅(⟨a, ha⟩ : N), ⟨b, hb⟩⁆ : N) : A) = ⁅a, b⁆ := by
    simp [commutatorElement_def]
  have key : ∀ x : L, ⁅a, b⁆ * (x : A) * ⁅a, b⁆⁻¹ = (l : A) * x * (l : A)⁻¹ := by
    intro x
    have h3 : ((ρ ⁅(⟨a, ha⟩ : N), ⟨b, hb⟩⁆ x : L) : A) =
        ((⁅(⟨a, ha⟩ : N), ⟨b, hb⟩⁆ : N) : A) * x * ((⁅(⟨a, ha⟩ : N), ⟨b, hb⟩⁆ : N) : A)⁻¹ :=
      rfl
    rw [hc] at h3
    rw [← h3, ← hl]
    rfl
  have hcent : (l : A)⁻¹ * ⁅a, b⁆ ∈ Subgroup.centralizer (L : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := key ⟨x, hx⟩
    simp only at this
    calc x * ((l : A)⁻¹ * ⁅a, b⁆) = (l : A)⁻¹ * ((l : A) * x * (l : A)⁻¹) * ⁅a, b⁆ := by
          group
      _ = (l : A)⁻¹ * (⁅a, b⁆ * x * ⁅a, b⁆⁻¹) * ⁅a, b⁆ := by rw [this]
      _ = (l : A)⁻¹ * ⁅a, b⁆ * x := by group
  have : ⁅a, b⁆ = (l : A) * ((l : A)⁻¹ * ⁅a, b⁆) := by group
  rw [this]
  exact Subgroup.mul_mem_sup l.2 hcent

theorem commutator_mem_of_suzukiModel
    {A : Type} [Group A] {L : Subgroup A} {n : ℕ}
    (hL : CFSG.Blueprint.SuzukiModel ↥L 2 n) {a b : A}
    (ha : a ∈ Subgroup.normalizer (L : Set A)) (hb : b ∈ Subgroup.normalizer (L : Set A)) :
    ⁅a, b⁆ ∈ L ⊔ Subgroup.centralizer (L : Set A) := by
  obtain ⟨hcyc, -, -⟩ :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} ↥L 2 n hL).1
  exact commutator_mem_sup_centralizer L (fun x y => (IsCyclic.commGroup.mul_comm x y)) ha hb

end CFSG.Quasithin.F134
