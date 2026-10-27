module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardFourDihedral
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallStructure

import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallHall
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The special-order data in the order-four Brauer--Suzuki--Wall branch

Bender's treatment of the `|K| = 4` case invokes a separate large-subgroup
argument whose first conclusion is the order dichotomy `|G| = 360` or
`|G| = 168`.  This module records the bridge-free consequences of that
dichotomy together with the already proved local BSW structure.
-/

namespace CFSG.GorensteinWalter

universe u

/-- If the cited large-subgroup argument supplies the special order
dichotomy in the `|K| = 4` BSW branch, then every involution centralizer is
dihedral of order eight.  Moreover `H` has order eight, the number of
involutions is `[G:H]`, and the two possible indices are `45` and `21`.

This is the strongest conclusion available from the current local API
without an additional recognition theorem identifying the two abstract
groups as `PSL(2,9)` and `PSL(2,7)`. -/
public theorem BrauerSuzukiWallHypotheses.involution_centralizers_and_index_of_card_K_eq_four_of_card_G_eq_360_or_168
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (horder : Nat.card G = 360 ∨ Nat.card G = 168) :
    HasDihedralSylowTwo G ∧
      (∀ u : G, IsInvolution u →
        Nonempty
          (Subgroup.centralizer ({u} : Set G) ≃* DihedralGroup 4)) ∧
      Nat.card h.H = 8 ∧
      (bswInvolutions G).ncard = h.H.index ∧
      ((Nat.card G = 360 ∧ h.H.index = 45) ∨
        (Nat.card G = 168 ∧ h.H.index = 21)) := by
  classical
  have hHcard : Nat.card h.H = 8 := by
    rw [h.card_H, hk]
  have hHp : IsPGroup 2 h.H := by
    apply IsPGroup.of_card (n := 3)
    norm_num [hHcard]
  have hnotIndex : ¬ 2 ∣ h.H.index := by
    intro hdvd
    have htwoOne : 2 = 1 :=
      Nat.eq_one_of_dvd_coprimes h.hall_H
        (by omega : 2 ∣ Nat.card h.H) hdvd
    omega
  let S0 : Sylow 2 G := hHp.toSylow hnotIndex
  have hS0eqH : (S0 : Subgroup G) = h.H :=
    IsPGroup.toSylow_coe hHp hnotIndex
  have hSylow : HasDihedralSylowTwo G :=
    h.hasDihedralSylowTwo_of_card_K_eq_four hk
  obtain ⟨m, hmpos, eS0m⟩ := hSylow S0
  have hS0card : Nat.card (S0 : Subgroup G) = 8 := by
    rw [hS0eqH, hHcard]
  have hS0modelCard : Nat.card (S0 : Subgroup G) = 2 * 2 ^ m := by
    calc
      Nat.card (S0 : Subgroup G) = Nat.card (DihedralGroup (2 ^ m)) :=
        Nat.card_congr eS0m.some.toEquiv
      _ = 2 * 2 ^ m := DihedralGroup.nat_card
  have hpow : 2 ^ m = 2 ^ 2 := by
    omega
  have hm : m = 2 :=
    Nat.pow_right_injective (by omega : 2 ≤ (2 : ℕ)) hpow
  subst m
  have eS0 : Nonempty (S0 ≃* DihedralGroup 4) := eS0m
  have eS0H : S0 ≃* h.H := MulEquiv.subgroupCongr hS0eqH
  have eH : Nonempty (h.H ≃* DihedralGroup 4) :=
    ⟨eS0H.symm.trans eS0.some⟩
  have hCentralizers :
      ∀ u : G, IsInvolution u →
        Nonempty
          (Subgroup.centralizer ({u} : Set G) ≃* DihedralGroup 4) := by
    intro u hu
    obtain ⟨g, hgu⟩ := h.involutions_conjugate u hu
    let Cu : Subgroup G := Subgroup.centralizer ({u} : Set G)
    let Ct : Subgroup G := Subgroup.centralizer ({h.t} : Set G)
    let e : Cu ≃* Ct :=
      { toFun := fun x ↦ ⟨g * (x : G) * g⁻¹, by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hxcomm : (x : G) * u = u * (x : G) :=
            Subgroup.mem_centralizer_singleton_iff.mp x.property
          rw [← hgu]
          calc
            (g * (x : G) * g⁻¹) * (g * u * g⁻¹) =
                g * ((x : G) * u) * g⁻¹ := by group
            _ = g * (u * (x : G)) * g⁻¹ := by rw [hxcomm]
            _ = (g * u * g⁻¹) * (g * (x : G) * g⁻¹) := by group⟩
        invFun := fun x ↦ ⟨g⁻¹ * (x : G) * g, by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hxcomm : (x : G) * h.t = h.t * (x : G) :=
            Subgroup.mem_centralizer_singleton_iff.mp x.property
          have hu : u = g⁻¹ * h.t * g := by
            calc
              u = g⁻¹ * (g * u * g⁻¹) * g := by group
              _ = g⁻¹ * h.t * g := by rw [hgu]
          rw [hu]
          calc
            (g⁻¹ * (x : G) * g) * (g⁻¹ * h.t * g) =
                g⁻¹ * ((x : G) * h.t) * g := by group
            _ = g⁻¹ * (h.t * (x : G)) * g := by rw [hxcomm]
            _ = (g⁻¹ * h.t * g) * (g⁻¹ * (x : G) * g) := by group⟩
        left_inv := by intro x; apply Subtype.ext; group
        right_inv := by intro x; apply Subtype.ext; group
        map_mul' := by
          intro x y
          apply Subtype.ext
          change
            g * ((x : G) * (y : G)) * g⁻¹ =
              (g * (x : G) * g⁻¹) * (g * (y : G) * g⁻¹)
          group }
    have eCtH : Ct ≃* h.H :=
      MulEquiv.subgroupCongr h.H_eq_centralizer.symm
    exact ⟨(e.trans eCtH).trans eH.some⟩
  have hInvCard : (bswInvolutions G).ncard = h.H.index :=
    bswInvolutions_ncard_eq_index_H h
  have hcardIndex : Nat.card h.H * h.H.index = Nat.card G :=
    h.H.card_mul_index
  have hcardIndex' : 8 * h.H.index = Nat.card G := by
    simpa [hHcard] using hcardIndex
  have hindexCases :
      (Nat.card G = 360 ∧ h.H.index = 45) ∨
        (Nat.card G = 168 ∧ h.H.index = 21) := by
    rcases horder with h360 | h168
    · left
      refine ⟨h360, ?_⟩
      rw [h360] at hcardIndex'
      omega
    · right
      refine ⟨h168, ?_⟩
      rw [h168] at hcardIndex'
      omega
  exact ⟨hSylow, hCentralizers, hHcard, hInvCard, hindexCases⟩

end CFSG.GorensteinWalter
