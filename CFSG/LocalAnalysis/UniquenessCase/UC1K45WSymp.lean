module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45WSympAux
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement

theorem sympData_of_form (hForm : SympForm) : SympData := by
  unfold SympData
  intro G _ _ X N hXn hNn hXp hcomm hsq hcyc hN
  haveI : X.Normal := hXn
  haveI : N.Normal := hNn
  obtain ⟨W, hWac, hWmod, hWfin, B, π, hBnd, hBalt, hπsurj, hπker, hB⟩ :=
    hForm ↥X hXp hcomm hsq hcyc
  letI := hWac
  letI := hWmod
  letI := hWfin
  let Φ := conjHom (π := π) hπsurj hπker
  have hNle : N ≤ Φ.ker := N_le_conjHom_ker hπsurj hπker hN
  let φ : G ⧸ N →* (W ≃ₗ[ZMod 2] W) := QuotientGroup.lift N Φ hNle
  have hφmk : ∀ g : G, φ (QuotientGroup.mk g) = conjEquiv hπsurj hπker g := by
    intro g
    exact QuotientGroup.lift_mk (N := N) (φ := Φ) hNle g
  refine ⟨W, hWac, hWmod, hWfin, B, φ, π, hBnd, hBalt, ?_, ?_, hπsurj, hπker, ?_, hB, ?_,
    ?_⟩
  · rw [QuotientGroup.injective_lift_iff]
    exact (conjHom_ker_eq hπsurj hπker hN).symm
  · intro γ x y
    revert x y
    refine QuotientGroup.induction_on γ ?_
    intro g x y
    rw [hφmk g]
    obtain ⟨a, ha⟩ := hπsurj (Multiplicative.ofAdd x)
    obtain ⟨b, hb⟩ := hπsurj (Multiplicative.ofAdd y)
    have hax : Multiplicative.toAdd (π a) = x := by rw [ha, toAdd_ofAdd]
    have hby : Multiplicative.toAdd (π b) = y := by rw [hb, toAdd_ofAdd]
    rw [← hax, ← hby, conjEquiv_apply, conjEquiv_apply]
    have h1 : B (Multiplicative.toAdd (π (MulAut.conjNormal g a)))
          (Multiplicative.toAdd (π (MulAut.conjNormal g b))) = 0 ↔
        B (Multiplicative.toAdd (π a)) (Multiplicative.toAdd (π b)) = 0 := by
      rw [hB, hB]
      have hmap := map_commutatorElement (f := (MulAut.conjNormal g).toMonoidHom)
        (g₁ := a) (g₂ := b)
      simp only [MulEquiv.coe_toMonoidHom] at hmap
      rw [← hmap]
      constructor
      · intro h
        exact (MulAut.conjNormal g).injective (by rw [h, map_one])
      · intro h; rw [h, map_one]
    exact (by
      have hzmod : ∀ p q : ZMod 2, (p = 0 ↔ q = 0) → p = q := by decide
      exact hzmod _ _ h1)
  · intro g x
    rw [hφmk g, conjEquiv_apply, ofAdd_toAdd]
  · intro g x
    have hR : ⁅X, Subgroup.zpowers g⁆ ≤ X :=
      Subgroup.commutator_le_left (H₁ := X) (H₂ := Subgroup.zpowers g)
    have hZX : (Subgroup.center ↥X).map X.subtype ≤ X :=
      Subgroup.map_subtype_le (Subgroup.center ↥X)
    rw [← Subgroup.mem_subgroupOf,
      Subgroup.subgroupOf_sup hR hZX, subgroupOf_map_center, ← hπker,
      ← comap_rangeSubgroup_eq hπsurj hπker g]
    rw [Subgroup.mem_comap, mem_rangeSubgroup, hφmk g]
  · intro g
    have hR : ⁅X, Subgroup.zpowers g⁆ ≤ X :=
      Subgroup.commutator_le_left (H₁ := X) (H₂ := Subgroup.zpowers g)
    have hZX : (Subgroup.center ↥X).map X.subtype ≤ X :=
      Subgroup.map_subtype_le (Subgroup.center ↥X)
    have hsup : ⁅X, Subgroup.zpowers g⁆ ⊔ (Subgroup.center ↥X).map X.subtype ≤ X :=
      sup_le hR hZX
    rw [show Nat.card ↥(⁅X, Subgroup.zpowers g⁆ ⊔ (Subgroup.center ↥X).map X.subtype) =
        Nat.card ↥((⁅X, Subgroup.zpowers g⁆ ⊔
          (Subgroup.center ↥X).map X.subtype).subgroupOf X) from
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsup).toEquiv).symm]
    rw [subgroupOf_sup_eq_comap hπsurj hπker g,
      card_comap_of_surjective π hπsurj (rangeSubgroup (conjEquiv hπsurj hπker g))]
    rw [show Nat.card ↥π.ker = Nat.card ↥(Subgroup.center ↥X) by rw [hπker],
      Subgroup.card_map_of_injective X.subtype_injective]
    rw [hφmk g]
    congr 1
    rw [card_rangeSubgroup]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(LinearMap.range
      ((conjEquiv hπsurj hπker g : W →ₗ[ZMod 2] W) - LinearMap.id)))]
    rw [show Nat.card (ZMod 2) = 2 by rw [Nat.card_eq_fintype_card, ZMod.card]]

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

end
