module

public import CFSG.Open.SignalizerFunctorDefs
import CFSG.SignalizerFunctorTheorem.NearModels.Conjugacy
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Basic
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Arith
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Bridge
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.AutBound
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Frobenius
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Fixed

public section

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag

namespace CFSG.SignalizerFunctorTheorem.NearModels

open UnitaryAut

theorem psu3_card_pSubgroup_dvd {p : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p (Nat.card (PSU3 2 p)))
    (P : Subgroup (MulAut (PSU3 2 p))) (hP : IsPGroup p P) : Nat.card P ∣ p := by
  have h := unitaryFieldData_galoisField hp.one_le
  let e := psu3EquivHypPSU hp.one_le
  have hcop' : Nat.Coprime p (Nat.card (hypPSU h 1 1)) := by
    rwa [Nat.card_congr e.toEquiv]
  obtain ⟨hp2, -, hS⟩ := ne_two_ne_three_not_dvd_of_coprime hp h hcop'
  exact card_pSubgroup_mulAut_dvd hp hp2 h hS e P hP

theorem psu3_fixedSubgroup_mulEquiv {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card (PSU3 2 p)))
    (f : MulAut (PSU3 2 p)) (hf : orderOf f = p) :
    Nonempty (signalizerFixedSubgroup f ≃* PSU3 2 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have h := unitaryFieldData_galoisField hp.one_le
  have hcop' : Nat.Coprime p (Nat.card (hypPSU h 1 1)) := by
    rwa [Nat.card_congr (psu3EquivHypPSU hp.one_le).toEquiv]
  obtain ⟨hp2, hp3, -⟩ := ne_two_ne_three_not_dvd_of_coprime hp h hcop'
  obtain ⟨τ, hτ, hτx⟩ := exists_mulAut_frob4 hp
  obtain ⟨φ⟩ := nonempty_fixedSubgroup_mulEquiv_psu3_two_one hp hp2 hp3 τ hτx
  obtain ⟨ψ⟩ := signalizerFixedSubgroup_mulEquiv_of_orderOf_eq
    (psu3_card_pSubgroup_dvd hp hcop) hf hτ
  exact ⟨ψ.trans φ⟩

end CFSG.SignalizerFunctorTheorem.NearModels
