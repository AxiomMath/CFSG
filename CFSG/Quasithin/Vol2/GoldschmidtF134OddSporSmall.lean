module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporDef
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Walter.Models
public import CFSG.Walter.J1Props.Facts
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Blueprint

theorem not_sq_dvd_of_squarefree {p n α β u : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hu : Squarefree u)
    (hn : n = 2 ^ α * 3 ^ β * u) : ¬ p ^ 2 ∣ n := by
  intro h
  have hp2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
  have hp3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).mpr (by omega)
  have hcop : Nat.Coprime (p ^ 2) (2 ^ α * 3 ^ β) :=
    Nat.Coprime.mul_right (Nat.Coprime.pow _ _ hp2) (Nat.Coprime.pow _ _ hp3)
  have h1 : p ^ 2 ∣ u := hcop.dvd_of_dvd_mul_left (hn ▸ h)
  have h2 := hu p (by rw [← sq]; exact h1)
  exact hp.one_lt.ne' (Nat.isUnit_iff.mp h2)

theorem noPowerOvergroup_of_not_sq_dvd {F : ∀ (X : Type) [Group X], Prop}
    (h : ∀ (X : Type) [Group X] [Finite X], F X → ∀ p : ℕ, p.Prime → 5 ≤ p →
      ¬ p ^ 2 ∣ Nat.card X) : NoPowerOvergroup F := by
  intro X _ _ hX p a hp h5 ha H S _ _ _ hH
  refine h X hX p hp h5 ?_
  have h1 : p ^ a ∣ Nat.card X := by
    have := Subgroup.card_subgroup_dvd_card H
    rw [hH] at this
    exact (Dvd.intro _ rfl).trans this
  rcases ha with rfl | rfl
  · exact h1
  · exact (pow_dvd_pow p (by norm_num : 2 ≤ 3)).trans h1

theorem card_carrier_j1 : Nat.card (NativeSporadic.Carrier .J1) = 175560 := by
  change Nat.card NativeSporadic.J1 = 175560
  rw [← Nat.card_congr CFSG.Walter.walterJ1EquivNative.toEquiv, CFSG.Walter.J1Props.J1_card]
  norm_num

theorem noPowerOvergroup_m11 :
    NoPowerOvergroup fun (X : Type) [Group X] =>
      Nonempty (X ≃* NativeSporadic.Carrier .M11) := by
  refine noPowerOvergroup_of_not_sq_dvd fun X _ _ ⟨e⟩ p hp h5 => ?_
  rw [Nat.card_congr e.toEquiv]
  show ¬ p ^ 2 ∣ Nat.card NativeSporadic.M11
  rw [CFSG.Sporadic.Mathieu.card_M11]
  exact not_sq_dvd_of_squarefree (α := 4) (β := 2) (u := 55) hp h5 (by decide +kernel) (by norm_num)

theorem noPowerOvergroup_m12 :
    NoPowerOvergroup fun (X : Type) [Group X] =>
      Nonempty (X ≃* NativeSporadic.Carrier .M12) := by
  refine noPowerOvergroup_of_not_sq_dvd fun X _ _ ⟨e⟩ p hp h5 => ?_
  rw [Nat.card_congr e.toEquiv]
  show ¬ p ^ 2 ∣ Nat.card NativeSporadic.M12
  rw [CFSG.Sporadic.Mathieu.card_M12]
  exact not_sq_dvd_of_squarefree (α := 6) (β := 3) (u := 55) hp h5 (by decide +kernel) (by norm_num)

theorem noPowerOvergroup_m22 :
    NoPowerOvergroup fun (X : Type) [Group X] =>
      Nonempty (X ≃* NativeSporadic.Carrier .M22) := by
  refine noPowerOvergroup_of_not_sq_dvd fun X _ _ ⟨e⟩ p hp h5 => ?_
  rw [Nat.card_congr e.toEquiv]
  show ¬ p ^ 2 ∣ Nat.card NativeSporadic.M22
  rw [CFSG.Sporadic.Mathieu.card_M22]
  exact not_sq_dvd_of_squarefree (α := 7) (β := 2) (u := 385) hp h5 (by decide +kernel)
    (by norm_num)

theorem noPowerOvergroup_m23 :
    NoPowerOvergroup fun (X : Type) [Group X] =>
      Nonempty (X ≃* NativeSporadic.Carrier .M23) := by
  refine noPowerOvergroup_of_not_sq_dvd fun X _ _ ⟨e⟩ p hp h5 => ?_
  rw [Nat.card_congr e.toEquiv]
  show ¬ p ^ 2 ∣ Nat.card NativeSporadic.M23
  rw [CFSG.Sporadic.Schreier.m23_card]
  exact not_sq_dvd_of_squarefree (α := 7) (β := 2) (u := 8855) hp h5 (by decide +kernel)
    (by norm_num)

theorem noPowerOvergroup_m24 :
    NoPowerOvergroup fun (X : Type) [Group X] =>
      Nonempty (X ≃* NativeSporadic.Carrier .M24) := by
  refine noPowerOvergroup_of_not_sq_dvd fun X _ _ ⟨e⟩ p hp h5 => ?_
  rw [Nat.card_congr e.toEquiv]
  show ¬ p ^ 2 ∣ Nat.card NativeSporadic.M24
  rw [CFSG.Sporadic.Mathieu.card_M24]
  exact not_sq_dvd_of_squarefree (α := 10) (β := 3) (u := 8855) hp h5 (by decide +kernel)
    (by norm_num)

theorem noPowerOvergroup_j1 :
    NoPowerOvergroup fun (X : Type) [Group X] =>
      Nonempty (X ≃* NativeSporadic.Carrier .J1) := by
  refine noPowerOvergroup_of_not_sq_dvd fun X _ _ ⟨e⟩ p hp h5 => ?_
  rw [Nat.card_congr e.toEquiv, card_carrier_j1]
  exact not_sq_dvd_of_squarefree (α := 3) (β := 1) (u := 7315) hp h5 (by decide +kernel)
    (by norm_num)

end CFSG.Quasithin.H13.NQCore
