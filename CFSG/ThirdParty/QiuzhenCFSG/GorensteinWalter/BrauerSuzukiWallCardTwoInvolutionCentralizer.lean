module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoKleinFour
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Involution centralizers in the order-two branch

In the `|K| = 2` branch, `H` is Klein four and therefore abelian.  Every
involution of `H` has a centralizer containing `H`; global involution
conjugacy gives that centralizer the same order as `C_G(t) = H`.
-/

namespace CFSG.GorensteinWalter

universe u

/-- In the `|K| = 2` branch of the Brauer--Suzuki--Wall hypotheses, every
involution lying in `H` has centralizer exactly `H`. -/
public theorem
    BrauerSuzukiWallHypotheses.centralizer_eq_H_of_mem_H_isInvolution_of_card_K_eq_two
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 2) {a : G}
    (haH : a ∈ h.H) (haI : IsInvolution a) :
    Subgroup.centralizer ({a} : Set G) = h.H := by
  classical
  let : IsKleinFour h.H := h.isKleinFour_H_of_card_K_eq_two hk
  let : IsMulCommutative h.H := IsKleinFour.isMulCommutative
  have hHleC : h.H ≤ Subgroup.centralizer ({a} : Set G) := by
    intro x hxH
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      ((IsKleinFour.isMulCommutative (G := h.H)).is_comm.comm
        ⟨x, hxH⟩ ⟨a, haH⟩)
  obtain ⟨g, hga⟩ := h.involutions_conjugate a haI
  let Ca : Subgroup G := Subgroup.centralizer ({a} : Set G)
  let Ct : Subgroup G := Subgroup.centralizer ({h.t} : Set G)
  let e : Ca ≃ Ct :=
    { toFun := fun x ↦ ⟨g * (x : G) * g⁻¹, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hxcomm : (x : G) * a = a * (x : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp x.property
        rw [← hga]
        calc
          (g * (x : G) * g⁻¹) * (g * a * g⁻¹) =
              g * ((x : G) * a) * g⁻¹ := by group
          _ = g * (a * (x : G)) * g⁻¹ := by rw [hxcomm]
          _ = (g * a * g⁻¹) * (g * (x : G) * g⁻¹) := by group⟩
      invFun := fun x ↦ ⟨g⁻¹ * (x : G) * g, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hxcomm : (x : G) * h.t = h.t * (x : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp x.property
        have ha : a = g⁻¹ * h.t * g := by
          calc
            a = g⁻¹ * (g * a * g⁻¹) * g := by group
            _ = g⁻¹ * h.t * g := by rw [hga]
        rw [ha]
        calc
          (g⁻¹ * (x : G) * g) * (g⁻¹ * h.t * g) =
              g⁻¹ * ((x : G) * h.t) * g := by group
          _ = g⁻¹ * (h.t * (x : G)) * g := by rw [hxcomm]
          _ = (g⁻¹ * h.t * g) * (g⁻¹ * (x : G) * g) := by group⟩
      left_inv := by intro x; apply Subtype.ext; group
      right_inv := by intro x; apply Subtype.ext; group }
  have hCcard : Nat.card Ca = 4 := by
    calc
      Nat.card Ca = Nat.card Ct := Nat.card_congr e
      _ = Nat.card h.H := by rw [h.H_eq_centralizer]
      _ = 4 := (h.isKleinFour_H_of_card_K_eq_two hk).card_four
  exact (Subgroup.eq_of_le_of_card_ge hHleC (by
    rw [show Nat.card (Subgroup.centralizer ({a} : Set G)) = 4 by
      simpa [Ca] using hCcard,
      (h.isKleinFour_H_of_card_K_eq_two hk).card_four])).symm

end CFSG.GorensteinWalter
