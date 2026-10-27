module

import CFSG.GroupTheory.LocalCores.Layer
import CFSG.GH74.Constrained
public import CFSG.Assembly.Defs
public import CFSG.Foundations.Basic

public section

namespace CFSG.StandardType

theorem ggSThree_components_fitting_le_map {X : Type*} [Group X] [Finite X] {H C₁ : Subgroup X}
    {e : X} (hC₁ : CFSG.IsComponent C₁) (hC₁H : C₁ ≤ H) (he : e ∈ C₁) (he3 : orderOf e = 3)
    (hcent : Subgroup.centralizer ({e} : Set X) ≤ H) :
    (∀ K : Subgroup (X ⧸ CFSG.pPrimeCore 3 X), CFSG.IsComponent K →
        K ≤ H.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ∧
      CFSG.fittingSubgroup (X ⧸ CFSG.pPrimeCore 3 X) ≤
        H.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : X →* X ⧸ CFSG.pPrimeCore 3 X := QuotientGroup.mk' (CFSG.pPrimeCore 3 X)
  have hcop : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 X)) := CFSG.pPrimeCore_coprime_card
  have hnot3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 X) :=
    (Nat.prime_three.coprime_iff_not_dvd).1 hcop
  have hnotle : ¬ C₁ ≤ CFSG.pPrimeCore 3 X := by
    intro hle
    have hdvd : 3 ∣ Nat.card (CFSG.pPrimeCore 3 X) := by
      have h := Subgroup.orderOf_dvd_natCard (CFSG.pPrimeCore 3 X) (hle he)
      rwa [he3] at h
    exact hnot3 hdvd
  have hker : ¬ C₁ ≤ π.ker := by
    rw [show π.ker = CFSG.pPrimeCore 3 X from QuotientGroup.ker_mk' _]
    exact hnotle
  have hĈ : CFSG.IsComponent (C₁.map π) :=
    ⟨CFSG.LocalCores.isQuasisimple_map hC₁.1 π hker,
      hC₁.2.map (QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 X))⟩
  have hmemĈ : π e ∈ C₁.map π := ⟨e, he, rfl⟩
  have hcent_eq : Subgroup.centralizer ({π e} : Set (X ⧸ CFSG.pPrimeCore 3 X)) =
      (Subgroup.centralizer ({e} : Set X)).map π := by
    change Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pPrimeCore 3 X) e} : Set (X ⧸ CFSG.pPrimeCore 3 X)) =
      (Subgroup.centralizer ({e} : Set X)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))
    exact CFSG.GH74.centralizer_singleton_pPrimeCore_quotient_eq_map (N := X) 3
      ⟨1, by rw [he3, pow_one]⟩
  have key : ∀ K : Subgroup (X ⧸ CFSG.pPrimeCore 3 X), CFSG.IsComponent K →
      K ≤ H.map π := by
    intro K hK
    rcases CFSG.LocalCores.distinct_components_commute hK hĈ with h | h
    · rw [h]
      exact Subgroup.map_mono hC₁H
    · have hKle : K ≤ Subgroup.centralizer
          (C₁.map π : Set (X ⧸ CFSG.pPrimeCore 3 X)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      have hsub : ({π e} : Set (X ⧸ CFSG.pPrimeCore 3 X)) ⊆
          (C₁.map π : Set (X ⧸ CFSG.pPrimeCore 3 X)) := by
        rintro x rfl
        exact hmemĈ
      calc K ≤ Subgroup.centralizer ({π e} : Set (X ⧸ CFSG.pPrimeCore 3 X)) :=
            hKle.trans (Subgroup.centralizer_le hsub)
        _ = (Subgroup.centralizer ({e} : Set X)).map π := hcent_eq
        _ ≤ H.map π := Subgroup.map_mono hcent
  refine ⟨key, ?_⟩
  have hFY : CFSG.fittingSubgroup (X ⧸ CFSG.pPrimeCore 3 X) ≤
      Subgroup.centralizer (CFSG.layer (X ⧸ CFSG.pPrimeCore 3 X) :
        Set (X ⧸ CFSG.pPrimeCore 3 X)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.LocalCores.fitting_layer_commute (G := X ⧸ CFSG.pPrimeCore 3 X))
  have hlayer : ({π e} : Set (X ⧸ CFSG.pPrimeCore 3 X)) ⊆
      (CFSG.layer (X ⧸ CFSG.pPrimeCore 3 X) : Set (X ⧸ CFSG.pPrimeCore 3 X)) := by
    rintro x rfl
    exact CFSG.LocalCores.component_le_layer hĈ hmemĈ
  calc CFSG.fittingSubgroup (X ⧸ CFSG.pPrimeCore 3 X)
        ≤ Subgroup.centralizer (CFSG.layer (X ⧸ CFSG.pPrimeCore 3 X) :
            Set (X ⧸ CFSG.pPrimeCore 3 X)) := hFY
    _ ≤ Subgroup.centralizer ({π e} : Set (X ⧸ CFSG.pPrimeCore 3 X)) :=
          Subgroup.centralizer_le hlayer
    _ = (Subgroup.centralizer ({e} : Set X)).map π := hcent_eq
    _ ≤ H.map π := Subgroup.map_mono hcent

end CFSG.StandardType
