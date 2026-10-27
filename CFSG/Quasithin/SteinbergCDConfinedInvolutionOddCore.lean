module

public import CFSG.GroupTheory.PCore.CharacteristicPPrimeCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import Mathlib.GroupTheory.FixedPointFree

public section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup
open scoped IsMulCommutative

theorem confined_involution_quotient_fitting_kill_odd_core {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] (A : Subgroup H) (hA : IsCharacteristicP 2 A) (z : H)
    (hz : orderOf z = 2) (hCz : centralizer {z} ≤ A)
    (hF : (fittingSubgroup (H ⧸ N)).comap (QuotientGroup.mk' N) ≤ A) :
    pPrimeCore 2 H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := pPrimeCore 2 H with hD
  have hDn : D.Normal := pPrimeCore_normal
  have hDodd : ¬ 2 ∣ Nat.card D :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
  have hDA : D ⊓ A = ⊥ := by
    have hsub : D.subgroupOf A = ⊥ := by
      refine (characteristic_p_normal_prime_complement_trivial hA).1 _ inferInstance ?_
      let f : D.subgroupOf A →* D :=
        { toFun := fun x => ⟨((x : A) : H), x.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hdvd : Nat.card (D.subgroupOf A) ∣ Nat.card D :=
        Subgroup.card_dvd_of_injective f fun x y h =>
          Subtype.ext (Subtype.ext (congrArg (fun w : D => (w : H)) h))
      exact fun h => hDodd (h.trans hdvd)
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.2⟩ : A) ∈ D.subgroupOf A := hx.1
    rw [hsub, mem_bot] at hx'
    exact congrArg Subtype.val hx'
  let φ : MulAut D := MulAut.conjNormal z
  have hφfix : MonoidHom.FixedPointFree φ := by
    intro d hd
    have hd' : z * (d : H) * z⁻¹ = d := congrArg Subtype.val hd
    have hdc : (d : H) ∈ centralizer {z} := by
      rw [mem_centralizer_singleton_iff]
      rw [mul_inv_eq_iff_eq_mul] at hd'
      exact hd'.symm
    have hdDA : (d : H) ∈ D ⊓ A := ⟨d.2, hCz hdc⟩
    rw [hDA, mem_bot] at hdDA
    exact Subtype.ext hdDA
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hφinv : Function.Involutive φ := by
    intro d
    apply Subtype.ext
    change z * (z * (d : H) * z⁻¹) * z⁻¹ = d
    have e : z * (z * (d : H) * z⁻¹) * z⁻¹ = (z * z) * (d : H) * (z * z)⁻¹ := by group
    rw [e, ← pow_two, hz2, one_mul, inv_one, mul_one]
  have hcomm := hφfix.commute_all_of_involutive hφinv
  set π := QuotientGroup.mk' N with hπ
  have hDπ : D.map π ≤ fittingSubgroup (H ⧸ N) := by
    have : IsMulCommutative (D.map π) := ⟨⟨fun a b => by
      obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      apply Subtype.ext
      change π x * π y = π y * π x
      rw [← map_mul, ← map_mul]
      exact congrArg π (congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩).eq)⟩⟩
    exact CFSG.LocalCores.fitting_characteristic.2.2 _
      (hDn.map π (QuotientGroup.mk'_surjective N)) inferInstance
  have hDle : D ≤ A := fun x hx => hF (hDπ ⟨x, hx, rfl⟩)
  rw [eq_bot_iff, ← hDA]
  exact le_inf le_rfl hDle

end CFSG.Quasithin.SteinbergCD
