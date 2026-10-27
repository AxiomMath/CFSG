module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallStructure

import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallStructure
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Selected centralizers of inverted order-three elements

This module exposes the source-facing order-three specialization of the
selected-centralizer infrastructure used in Bender's order-four cases.
-/

namespace CFSG.GorensteinWalter

open BenderSuzuki.External

universe u

/-- If `|K| = 4`, an element of order three inverted by the distinguished
involution has Bender's complete selected-centralizer package: its
centralizer is abelian of odd order, every nonidentity element has the same
centralizer and is inverted by `t`, and that centralizer is Hall and TI
relative to its normalizer. -/
public theorem
    BrauerSuzukiWallHypotheses.inverted_order_three_centralizer_data
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    {x : G}
    (hxOrder : orderOf x = 3)
    (htx : h.t * x * h.t⁻¹ = x⁻¹) :
    let F := Subgroup.centralizer ({x} : Set G)
    IsMulCommutative F ∧
      Odd (Nat.card F) ∧
      (∀ a : G, a ∈ F → a ≠ 1 →
        Subgroup.centralizer ({a} : Set G) = F ∧
          h.t * a * h.t⁻¹ = a⁻¹) ∧
      Nat.Coprime (Nat.card F) F.index ∧
      Suzuki.VI.IsTISubsetRelative
        (Subgroup.normalizer (F : Set G)) (F : Set G) := by
  have hxne : x ≠ 1 := by
    intro hx
    rw [hx, orderOf_one] at hxOrder
    omega
  have hxOutside : x ∉ bswKConjugates h := by
    rintro ⟨a, haK, _hane, g, hconj⟩
    have horderA : orderOf a = 3 := by
      calc
        orderOf a = orderOf (g * a * g⁻¹) := by
          simpa [MulAut.conj_apply] using
            (MulAut.conj g).orderOf_eq a |>.symm
        _ = orderOf x := by rw [← hconj]
        _ = 3 := hxOrder
    have hdvd : 3 ∣ 4 := by
      rw [← hk, ← horderA]
      exact Subgroup.orderOf_dvd_natCard h.K haK
    norm_num at hdvd
  obtain ⟨hFcomm, hFodd, hFCentInv⟩ :=
    selected_centralizer_structure h hxOutside hxne htx
  have hFCent : ∀ a : G,
      a ∈ Subgroup.centralizer ({x} : Set G) → a ≠ 1 →
        Subgroup.centralizer ({a} : Set G) =
          Subgroup.centralizer ({x} : Set G) := by
    intro a ha hane
    exact (hFCentInv a ha hane).1
  refine ⟨hFcomm, hFodd, hFCentInv,
    selected_centralizer_isHall hFCent, ?_⟩
  exact selected_centralizer_isTISubsetRelative hxne hFcomm hFCent

end CFSG.GorensteinWalter
