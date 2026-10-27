module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenOrderThreeCentralizerCard
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Centralizer order of an order-three subgroup in `A7` -/

noncomputable section

namespace CFSG.GorensteinWalter

/-- An order-three subgroup of `A7` centralized by a Klein four has
centralizer of order `36`. -/
public theorem aSeven_order_three_subgroup_centralizer_card_eq_thirty_six
    (A V : Subgroup (alternatingGroup (Fin 7)))
    (hAcard : Nat.card A = 3) (hVK : IsKleinFour V)
    (hVcent : V ≤ Subgroup.centralizer
      (A : Set (alternatingGroup (Fin 7)))) :
    Nat.card (Subgroup.centralizer
      (A : Set (alternatingGroup (Fin 7)))) = 36 := by
  have hAne : A ≠ ⊥ := by
    intro hbot
    have : Nat.card A = 1 := by rw [hbot]; simp
    omega
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hAne
  obtain ⟨u, hu⟩ := exists_ne (1 : A)
  have huOrderA : orderOf u = 3 := by
    have hdiv : orderOf u ∣ 3 := by
      rw [← hAcard]
      exact orderOf_dvd_natCard u
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h1 | h3
    · exact False.elim (hu (orderOf_eq_one_iff.mp h1))
    · exact h3
  have huOrder : orderOf (u : alternatingGroup (Fin 7)) = 3 := by
    simpa only [Subgroup.orderOf_coe] using huOrderA
  have hVcentu : V ≤ Subgroup.centralizer
      ({(u : alternatingGroup (Fin 7))} :
        Set (alternatingGroup (Fin 7))) := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm := (Subgroup.mem_centralizer_iff.mp (hVcent hv))
      (u : alternatingGroup (Fin 7)) u.2
    exact hcomm.symm
  have hcard :=
    aSeven_order_three_centralizer_card_eq_thirty_six_of_kleinFour
      (u : alternatingGroup (Fin 7)) huOrder V hVK hVcentu
  have hzle : Subgroup.zpowers (u : alternatingGroup (Fin 7)) ≤ A :=
    Subgroup.zpowers_le.mpr u.2
  have hzEq : Subgroup.zpowers (u : alternatingGroup (Fin 7)) = A :=
    Subgroup.eq_of_le_of_card_ge hzle (by
      rw [Nat.card_zpowers, huOrder, hAcard])
  have hcentEq : Subgroup.centralizer
      (A : Set (alternatingGroup (Fin 7))) =
      Subgroup.centralizer
        ({(u : alternatingGroup (Fin 7))} :
          Set (alternatingGroup (Fin 7))) := by
    calc
      Subgroup.centralizer (A : Set (alternatingGroup (Fin 7))) =
          Subgroup.centralizer
            ((Subgroup.zpowers (u : alternatingGroup (Fin 7)) :
              Subgroup (alternatingGroup (Fin 7))) : Set _) := by rw [hzEq]
      _ = Subgroup.centralizer
          ({(u : alternatingGroup (Fin 7))} : Set _) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rwa [hcentEq]

end CFSG.GorensteinWalter
