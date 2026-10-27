module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourSymmetricFourEndpoint
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

open scoped Pointwise

universe u

public theorem no_kleinFour_centralizes_odd_cyclic_perm_four
    (A V : Subgroup (Equiv.Perm (Fin 4)))
    (hAcyc : IsCyclic A) (hAne : A ≠ ⊥)
    (hAodd : Odd (Nat.card A))
    (hVK : IsKleinFour V)
    (hVleC : V ≤ Subgroup.centralizer
      (A : Set (Equiv.Perm (Fin 4)))) :
    False := by
  classical
  let : IsCyclic A := hAcyc
  obtain ⟨a, ha_gen⟩ := IsCyclic.exists_zpow_surjective (G := A)
  let a₀ : Equiv.Perm (Fin 4) := (a : Equiv.Perm (Fin 4))
  have ha_ne : a₀ ≠ 1 := by
    intro h
    apply hAne
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨k, hk⟩ := ha_gen ⟨x, hx⟩
    have hkval : a₀ ^ k = x := congrArg Subtype.val hk
    have hx1 : x = 1 := by
      rw [← hkval, h]
      simp
    exact Subgroup.mem_bot.mpr hx1
  have hcardA : Nat.card A ∣ 24 := by
    have hle : A ≤ (⊤ : Subgroup (Equiv.Perm (Fin 4))) := le_top
    have hc := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_top] at hc
    have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      norm_num
    rwa [hperm] at hc
  have hordA : orderOf a ∣ Nat.card A := orderOf_dvd_natCard a
  have hord24 : orderOf a ∣ 24 := hordA.trans hcardA
  have hord_le : orderOf a ≤ 24 := Nat.le_of_dvd (by norm_num) hord24
  have hord_pos : 0 < orderOf a := orderOf_pos a
  have hord_odd : Odd (orderOf a) := Odd.of_dvd_nat hAodd hordA
  have hord_ne1 : orderOf a ≠ 1 := by
    intro h
    have ha1 : (a : A) = 1 := orderOf_eq_one_iff.mp h
    exact ha_ne (by simpa [a₀] using congrArg Subtype.val ha1)
  have hord3 : orderOf a = 3 := by
    interval_cases orderOf a <;>
      (rcases hord_odd with ⟨k, hk⟩; omega)
  have ha3 : (a : A) ^ 3 = 1 :=
    (orderOf_dvd_iff_pow_eq_one.mp (by
      rw [← hord3]))
  have ha3' : a₀ ^ 3 = 1 := by
    simpa [a₀] using congrArg Subtype.val ha3
  let : Fintype V := Fintype.ofFinite V
  have hlt : 1 < Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, hVK.card_four]
    norm_num
  obtain ⟨w, hwne⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : V)
  let v : Equiv.Perm (Fin 4) := (w : Equiv.Perm (Fin 4))
  have hvmem : v ∈ V := w.property
  have hvne : v ≠ 1 := by
    intro h
    apply hwne
    apply Subtype.ext
    simpa [v] using h
  have hvtwo : v * v = 1 := congrArg Subtype.val (IsKleinFour.mul_self w)
  have hcomm0 : a₀ * v = v * a₀ :=
    (Subgroup.mem_centralizer_iff.mp (hVleC hvmem)) a₀ a.2
  have hvcomm : v * a₀ = a₀ * v := hcomm0.symm
  have hv_one := no_involution_centralizes_order_three_perm_four
    ⟨a₀, ha3'⟩ ⟨v, hvtwo⟩ ha_ne hvcomm
  exact hvne hv_one

end CFSG.GorensteinWalter
