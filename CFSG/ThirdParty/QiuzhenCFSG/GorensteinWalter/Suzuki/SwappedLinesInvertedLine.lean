module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If an involution swaps two distinct order-three lines in an abelian
subgroup, it inverts a third order-three line in their join. -/
public theorem exists_order_three_line_inverted_of_swap
    {G : Type u} [Group G] [Finite G]
    (U W P : Subgroup G) (a : G)
    (hU3 : Nat.card U = 3)
    (hUle : U ≤ P) (hWle : W ≤ P)
    (hUneW : U ≠ W)
    (ha2 : a ^ 2 = 1)
    (haU : conjugateSubgroup U a = W)
    (hcomm : ∀ x y : G, x ∈ P → y ∈ P → x * y = y * x) :
    ∃ X : Subgroup G, Nat.card X = 3 ∧ X ≤ P ∧
      ∀ x : G, x ∈ X → a * x * a⁻¹ = x⁻¹ := by
  classical
  have hgt : 1 < Nat.card U := by rw [hU3]; norm_num
  have hnt : Nontrivial U := (Finite.one_lt_card_iff_nontrivial).mp hgt
  rcases exists_ne (1 : U) with ⟨u, hu⟩
  have huG : (u : G) ≠ 1 := by
    intro h
    apply hu
    exact Subtype.ext h
  let w : G := a * (u : G) * a⁻¹
  have hwW : w ∈ W := by
    rw [← haU]
    change w ∈ U.map (MulAut.conj a).toMonoidHom
    refine Subgroup.mem_map.mpr ⟨(u : G), u.2, ?_⟩
    simp [w, MulAut.conj_apply]
  have huP : (u : G) ∈ P := hUle u.2
  have hwP : w ∈ P := hWle hwW
  have hu3 : (u : G) ^ 3 = 1 := by
    have hd := Subgroup.orderOf_dvd_natCard U u.2
    rw [hU3, orderOf_dvd_iff_pow_eq_one] at hd
    exact hd
  have hw3 : w ^ 3 = 1 := by
    calc
      w ^ 3 = (MulAut.conj a) ((u : G) ^ 3) := by
        rw [map_pow]
        rfl
      _ = 1 := by rw [hu3]; simp
  let x : G := (u : G) * w⁻¹
  have hxP : x ∈ P := P.mul_mem huP (P.inv_mem hwP)
  have hx3 : x ^ 3 = 1 := by
    have hc : Commute (u : G) w⁻¹ :=
      hcomm (u : G) w⁻¹ huP (P.inv_mem hwP)
    dsimp [x]
    rw [hc.mul_pow, hu3, inv_pow, hw3]
    simp
  have hxne : x ≠ 1 := by
    intro hx1
    have huw : (u : G) = w := by
      have h := congrArg (fun z : G => z * w) hx1
      simpa [x] using h
    have huW : (u : G) ∈ W := by simpa [huw] using hwW
    have hUW : U = W := by
      have huord : orderOf (u : G) = 3 := orderOf_eq_prime hu3 huG
      have hgenU : Subgroup.zpowers (u : G) = U := by
        apply Subgroup.eq_of_le_of_card_ge
        · exact Subgroup.zpowers_le.mpr u.2
        · rw [Nat.card_zpowers, huord, hU3]
      have hW3 : Nat.card W = 3 := by
        calc
          Nat.card W = Nat.card (conjugateSubgroup U a) := by rw [haU]
          _ = Nat.card U := by
            exact Nat.card_congr
              (Subgroup.equivMapOfInjective U (MulAut.conj a).toMonoidHom
                (MulAut.conj a).injective).toEquiv.symm
          _ = 3 := hU3
      have hgenW : Subgroup.zpowers (u : G) = W := by
        apply Subgroup.eq_of_le_of_card_ge
        · exact Subgroup.zpowers_le.mpr huW
        · rw [Nat.card_zpowers, huord, hW3]
      exact hgenU.symm.trans hgenW
    exact hUneW hUW
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hxne
  let X : Subgroup G := Subgroup.zpowers x
  refine ⟨X, ?_, ?_, ?_⟩
  · simpa [X, Nat.card_zpowers] using hxord
  · exact Subgroup.zpowers_le.mpr hxP
  · intro z hz
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
    have hax : a * x * a⁻¹ = x⁻¹ := by
      have hainv : a⁻¹ = a :=
        inv_eq_iff_mul_eq_one.mpr (by simpa [pow_two] using ha2)
      have haa : a * a = 1 := by simpa [pow_two] using ha2
      have haw : a * w * a⁻¹ = (u : G) := by
        dsimp [w]
        rw [hainv]
        calc
          a * (a * (u : G) * a) * a =
              (a * a) * (u : G) * (a * a) := by group
          _ = (u : G) := by rw [haa]; simp
      dsimp [x]
      calc
        a * ((u : G) * w⁻¹) * a⁻¹ =
            (a * (u : G) * a⁻¹) * (a * w⁻¹ * a⁻¹) := by group
        _ = w * (u : G)⁻¹ := by
          rw [← show w = a * (u : G) * a⁻¹ by rfl]
          have hawi : a * w⁻¹ * a⁻¹ = (u : G)⁻¹ := by
            calc
              a * w⁻¹ * a⁻¹ = (a * w * a⁻¹)⁻¹ := by group
              _ = (u : G)⁻¹ := by rw [haw]
          rw [hawi]
        _ = ((u : G) * w⁻¹)⁻¹ := by
          rw [mul_inv_rev]
          simp
    change (MulAut.conj a) (x ^ n) = (x ^ n)⁻¹
    rw [map_zpow]
    change (a * x * a⁻¹) ^ n = (x ^ n)⁻¹
    rw [hax, inv_zpow]

end CFSG.GorensteinWalter
