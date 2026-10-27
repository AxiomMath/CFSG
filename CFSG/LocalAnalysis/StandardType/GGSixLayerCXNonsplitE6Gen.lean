module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4Basic
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace E6Nonsplit

section Layers

variable {D M : Type*} [Group D] [Group M]

theorem isQuasisimple_comap_of_layer (ψ : D →* M) (hψ : Function.Injective ψ) {P : Subgroup M}
    (hle : P ≤ ψ.range) (hq : CFSG.IsQuasisimple P) : CFSG.IsQuasisimple (P.comap ψ) := by
  have hmap : (P.comap ψ).map ψ = P := by
    rw [Subgroup.map_comap_eq, inf_of_le_right hle]
  have e : P.comap ψ ≃* P :=
    (Subgroup.equivMapOfInjective (P.comap ψ) ψ hψ).trans (MulEquiv.subgroupCongr hmap)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq

theorem isComponent_comap_of_layer (ψ : D →* M) (hψ : Function.Injective ψ) {P : Subgroup M}
    (hle : P ≤ ψ.range) (hq : CFSG.IsQuasisimple P)
    (hnorm : ∀ d : D, ∀ u ∈ P, ψ d * u * (ψ d)⁻¹ ∈ P) : CFSG.IsComponent (P.comap ψ) := by
  refine ⟨isQuasisimple_comap_of_layer ψ hψ hle hq, ?_⟩
  have hn : (P.comap ψ).Normal := ⟨fun u hu d => by
    change ψ (d * u * d⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact hnorm d _ hu⟩
  exact hn.isSubnormal

theorem exists_eq_comap_of_isComponent [Finite D] (ψ : D →* M) (hψ : Function.Injective ψ)
    {ι : Type*} (P : ι → Subgroup M) (hle : ∀ i, P i ≤ ψ.range)
    (hq : ∀ i, CFSG.IsQuasisimple (P i))
    (hnorm : ∀ i, ∀ d : D, ∀ u ∈ P i, ψ d * u * (ψ d)⁻¹ ∈ P i) {Z : Set M}
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hcent : ∀ d : D, (∀ i, ∀ u ∈ P i, ψ d * u = u * ψ d) → ψ d ∈ Z)
    {X : Subgroup D} (hX : CFSG.IsComponent X) : ∃ i, X = (P i).comap ψ := by
  by_contra hne
  push Not at hne
  have hmem : ∀ z ∈ X, ψ z ∈ Z := fun z hz => hcent z fun i u hu => by
    obtain ⟨v, hv⟩ := hle i hu
    have hvP : v ∈ (P i).comap ψ := by
      rw [Subgroup.mem_comap, hv]
      exact hu
    rcases CFSG.LocalCores.distinct_components_commute hX
        (isComponent_comap_of_layer ψ hψ (hle i) (hq i) (hnorm i)) with h | h
    · exact absurd h (hne i)
    · have h1 : v ∈ Subgroup.centralizer (X : Set D) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rwa [Subgroup.commutator_comm]))
          hvP
      have h2 := Subgroup.mem_centralizer_iff.1 h1 z hz
      rw [← hv, ← map_mul, ← map_mul, h2]
  have hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy => by
    apply hψ
    rw [map_mul, map_mul]
    exact hZ _ (hmem x hx) _ (hmem y hy)
  obtain ⟨-, -, a, b, hab⟩ := hX.1
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine hab ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hcomm _ a.2 _ b.2)

end Layers

section Order

variable {C M : Type*} [Group C] [Group M]

theorem dvd_card_of_isComponentOf_of_layers [Finite C] {A : Subgroup C} (ψ : A →* M)
    (hψ : Function.Injective ψ) {ι : Type*} (P : ι → Subgroup M) (hle : ∀ i, P i ≤ ψ.range)
    (hq : ∀ i, CFSG.IsQuasisimple (P i))
    (hnorm : ∀ i, ∀ d : A, ∀ u ∈ P i, ψ d * u * (ψ d)⁻¹ ∈ P i) {Z : Set M}
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hcent : ∀ d : A, (∀ i, ∀ u ∈ P i, ψ d * u = u * ψ d) → ψ d ∈ Z) {p : ℕ}
    (hp : ∀ i, p ∣ Nat.card (P i)) {X : Subgroup C} (hX : IsComponentOf X A) :
    p ∣ Nat.card X := by
  have hX' : CFSG.IsComponent (X.subgroupOf A) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hX.1).1 hX
  obtain ⟨i, hi⟩ := exists_eq_comap_of_isComponent ψ hψ P hle hq hnorm hZ hcent hX'
  have h1 : Nat.card X = Nat.card (P i) := by
    have hmap : ((P i).comap ψ).map ψ = P i := by
      rw [Subgroup.map_comap_eq, inf_of_le_right (hle i)]
    calc Nat.card X = Nat.card (X.subgroupOf A) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX.1).symm.toEquiv
      _ = Nat.card ((P i).comap ψ) := by rw [hi]
      _ = Nat.card (((P i).comap ψ).map ψ) :=
          (Subgroup.card_map_of_injective hψ).symm
      _ = Nat.card (P i) := by rw [hmap]
  rw [h1]
  exact hp i

end Order

end E6Nonsplit

end CFSG.StandardType
