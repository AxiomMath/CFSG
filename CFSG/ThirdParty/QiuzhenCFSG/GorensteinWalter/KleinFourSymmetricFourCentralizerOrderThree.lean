module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourSymmetricFourEndpoint
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

open scoped Pointwise

public theorem sFour_centralizer_order_three_eq_zpowers
    {x : Equiv.Perm (Fin 4)} (hx : orderOf x = 3) :
    Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 4))) =
      Subgroup.zpowers x := by
  classical
  have hxne : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    norm_num at hx
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hCodd : Odd (Nat.card
      (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 4))))) := by
    apply Nat.not_even_iff_odd.mp
    intro hEven
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨s, hsord⟩ := exists_prime_orderOf_dvd_card'
      (G := Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 4)))) 2
      (even_iff_two_dvd.mp hEven)
    have hs2 : orderOf (s : Equiv.Perm (Fin 4)) = 2 := by
      simpa using (Subgroup.orderOf_coe s).trans hsord
    have hsI : IsInvolution (s : Equiv.Perm (Fin 4)) := by
      refine ⟨?_, ?_⟩
      · intro hs1
        rw [hs1, orderOf_one] at hs2
        norm_num at hs2
      · rw [← hs2]
        exact pow_orderOf_eq_one (s : Equiv.Perm (Fin 4))
    have hcomm : (s : Equiv.Perm (Fin 4)) * x =
        x * (s : Equiv.Perm (Fin 4)) :=
      (Subgroup.mem_centralizer_iff.mp s.2) x (by simp) |>.symm
    exact no_involution_centralizes_order_three_perm_four
      ⟨x, hx3⟩ ⟨s, hsI.2⟩ hxne hcomm |> hsI.1
  have hCdiv : Nat.card
      (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 4)))) ∣ 24 := by
    have h := Subgroup.card_dvd_of_le
      (show Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 4))) ≤ ⊤ from le_top)
    simpa [Subgroup.card_top, Fintype.card_perm, Nat.factorial] using h
  have hCge : 3 ≤ Nat.card
      (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 4)))) := by
    have hle : Subgroup.zpowers x ≤
        Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 4))) := by
      intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
      exact (Commute.refl x).zpow_left n
    have hcard : Nat.card (Subgroup.zpowers x) = 3 := by
      rw [Nat.card_zpowers, hx]
    have hlecard := Nat.le_of_dvd (Nat.card_pos)
      (Subgroup.card_dvd_of_le hle)
    rw [hcard] at hlecard
    exact hlecard
  have hCcard : Nat.card
      (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 4)))) = 3 := by
    have hCle : Nat.card
        (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 4)))) ≤ 24 :=
      Nat.le_of_dvd (by norm_num) hCdiv
    obtain ⟨k, hk⟩ := hCodd
    interval_cases hcard : Nat.card
        (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 4))))
    all_goals (try norm_num at hCdiv hCge hcard hk ⊢)
    all_goals omega
  have hle : Subgroup.zpowers x ≤
      Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 4))) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
    exact (Commute.refl x).zpow_left n
  symm
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Nat.card_zpowers, hx, hCcard])

end CFSG.GorensteinWalter
