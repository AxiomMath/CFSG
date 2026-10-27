module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralOddRotationCentralizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Characteristic rotation subgroup in a reflected cyclic group

In a generalized dihedral join `T ⋊ ⟨w⟩`, every element outside the cyclic
rotation subgroup `T` is an involution.  If `|T| ≥ 3`, this makes `T` the
unique cyclic subgroup of its order, hence characteristic in the join.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A reflected cyclic subgroup of order at least three is characteristic in
its join with the reflecting involution. -/
public theorem reflectedCyclic_characteristic_in_join
    {G : Type u} [Group G] [Finite G]
    (T : Subgroup G) (w : G)
    (hTcyc : IsCyclic T) (hTcard : 3 ≤ Nat.card T)
    (hwT : w ∉ T) (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ T → w * x * w⁻¹ = x⁻¹) :
    let D := T ⊔ Subgroup.zpowers w
    (T.subgroupOf D).Characteristic := by
  let D : Subgroup G := T ⊔ Subgroup.zpowers w
  let R : Subgroup D := T.subgroupOf D
  have hRcyc : IsCyclic R := by
    let eR : R ≃* T :=
      Subgroup.subgroupOfEquivOfLe (show T ≤ D from le_sup_left)
    exact eR.isCyclic.mpr hTcyc
  have hRcard : Nat.card R = Nat.card T := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (show T ≤ D from le_sup_left)).toEquiv
  change R.Characteristic
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro phi
  let H : Subgroup D := R.map phi.toMonoidHom
  have hHcyc : IsCyclic H := by
    let eH : R ≃* H :=
      Subgroup.equivMapOfInjective R phi.toMonoidHom phi.injective
    exact eH.isCyclic.mp hRcyc
  have hHcard : Nat.card H = Nat.card R :=
    Subgroup.card_map_of_injective (K := R) phi.injective
  obtain ⟨z, hzgen⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).mp hHcyc
  have hzR : z ∈ R := by
    by_contra hznot
    have hznotT : (z : G) ∉ T := by
      intro hzT
      exact hznot hzT
    rcases (mem_sup_zpowers_of_involution_inverts hwT hwsq hwinv).mp z.2 with
      ⟨t, htT, hzt | hztw⟩
    · exact hznotT (hzt ▸ htT)
    · have hw_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hwsq
      have hw_tw : w * t * w = t⁻¹ := by
        simpa [hw_inv] using hwinv t htT
      have hsqG : ((z : D) : G) ^ 2 = 1 := by
        rw [show ((z : D) : G) = t * w from hztw]
        rw [pow_two]
        calc
          (t * w) * (t * w) = t * (w * t * w) := by group
          _ = t * t⁻¹ := by rw [hw_tw]
          _ = 1 := by simp
      have hsq : z ^ 2 = 1 := by
        apply Subtype.ext
        exact hsqG
      have horddvd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
      have hordcard : orderOf z = Nat.card H := by
        rw [← Nat.card_zpowers, hzgen]
      have hcardle : Nat.card H ≤ 2 := by
        rw [← hordcard]
        exact Nat.le_of_dvd (by norm_num) horddvd
      rw [hHcard, hRcard] at hcardle
      omega
  have hle : H ≤ R := by
    intro x hx
    rw [← hzgen] at hx
    rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
    exact R.zpow_mem hzR n
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hHcard])

end CFSG.GorensteinWalter
