module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourExceptions
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

open scoped Pointwise

universe u

public theorem no_kleinFour_centralizes_odd_cyclic_alternatingGroup_four
    (A V : Subgroup (alternatingGroup (Fin 4)))
    (hAcyc : IsCyclic A) (hAne : A ≠ ⊥)
    (hAodd : Odd (Nat.card A))
    (hVK : IsKleinFour V)
    (hVleC : V ≤ Subgroup.centralizer
      (A : Set (alternatingGroup (Fin 4)))) :
    False := by
  classical
  let : IsCyclic A := hAcyc
  obtain ⟨a, ha_gen⟩ := IsCyclic.exists_zpow_surjective (G := A)
  let a₀ : alternatingGroup (Fin 4) := (a : alternatingGroup (Fin 4))
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
  have ha_sq_ne : a₀ * a₀ ≠ 1 := by
    intro hsq
    have hord2 : orderOf a ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      simpa [pow_two] using hsq
    have hordA : orderOf a ∣ Nat.card A := orderOf_dvd_natCard a
    have hord_odd : Odd (orderOf a) := Odd.of_dvd_nat hAodd hordA
    have hord1 : orderOf a = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
      · exact h
      · exfalso
        exact hord_odd.not_two_dvd_nat (by rw [h])
    have ha1 : (a : A) = 1 := orderOf_eq_one_iff.mp hord1
    exact ha_ne (congrArg Subtype.val ha1)
  let : Fintype V := Fintype.ofFinite V
  have hlt : 1 < Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, hVK.card_four]
    norm_num
  obtain ⟨w, hwne⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : V)
  let v : alternatingGroup (Fin 4) := (w : alternatingGroup (Fin 4))
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
  have hv_one := no_involution_centralizes_noninvolution_alternatingGroup_four
    a₀ v ha_ne ha_sq_ne hvtwo hvcomm
  exact hvne hv_one

public theorem no_kleinFour_centralizes_odd_cyclic_alternatingGroup_five
    (A V : Subgroup (alternatingGroup (Fin 5)))
    (hAcyc : IsCyclic A) (hAne : A ≠ ⊥)
    (hAodd : Odd (Nat.card A))
    (hVK : IsKleinFour V)
    (hVleC : V ≤ Subgroup.centralizer
      (A : Set (alternatingGroup (Fin 5)))) :
    False := by
  classical
  let : IsCyclic A := hAcyc
  obtain ⟨a, ha_gen⟩ := IsCyclic.exists_zpow_surjective (G := A)
  let a₀ : alternatingGroup (Fin 5) := (a : alternatingGroup (Fin 5))
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
  have ha_sq_ne : a₀ * a₀ ≠ 1 := by
    intro hsq
    have hord2 : orderOf a ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      simpa [pow_two] using hsq
    have hordA : orderOf a ∣ Nat.card A := orderOf_dvd_natCard a
    have hord_odd : Odd (orderOf a) := Odd.of_dvd_nat hAodd hordA
    have hord1 : orderOf a = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
      · exact h
      · exfalso
        exact hord_odd.not_two_dvd_nat (by rw [h])
    have ha1 : (a : A) = 1 := orderOf_eq_one_iff.mp hord1
    exact ha_ne (congrArg Subtype.val ha1)
  let : Fintype V := Fintype.ofFinite V
  have hlt : 1 < Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, hVK.card_four]
    norm_num
  obtain ⟨w, hwne⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : V)
  let v : alternatingGroup (Fin 5) := (w : alternatingGroup (Fin 5))
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
  have hv_one := no_involution_centralizes_noninvolution_alternatingGroup_five
    a₀ v ha_ne ha_sq_ne hvtwo hvcomm
  exact hvne hv_one

end CFSG.GorensteinWalter
