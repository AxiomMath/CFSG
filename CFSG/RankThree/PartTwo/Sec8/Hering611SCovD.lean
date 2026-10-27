module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

theorem false_of_hom_injective_on_center {X : Type*} [Group X] [Finite X]
    (hX : Group.IsPerfect X) {T Z : Subgroup X} (hZc : Z ≤ Subgroup.center X)
    (hZ3 : Nat.card Z = 3) (hZT : Z ≤ T) (hidx : ¬ 3 ∣ T.index)
    (lam : T →* Multiplicative (ZMod 3))
    (hlam : ∀ z : Z, lam ⟨z, hZT z.2⟩ = 1 → z = 1) : False := by
  have htr : ∀ x : X, MonoidHom.transfer lam x = 1 := by
    intro x
    haveI : Group.IsPerfect (MonoidHom.transfer lam).range := Group.IsPerfect.range _
    have hsub : Subsingleton (MonoidHom.transfer lam).range :=
      Group.IsPerfect.subsingleton_of_isMulCommutative
    have h1 := Subsingleton.elim (⟨MonoidHom.transfer lam x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ :
      (MonoidHom.transfer lam).range) 1
    exact congrArg Subtype.val h1
  haveI : Nontrivial Z := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨z, hz⟩ := exists_ne (1 : Z)
  have hzc : (z : X) ∈ Subgroup.center X := hZc z.2
  have key : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * (z : X) ^ k * g₀ ∈ T →
      g₀⁻¹ * (z : X) ^ k * g₀ = (z : X) ^ k := by
    intro k g₀ _
    have hc : ∀ g : X, g * (z : X) ^ k = (z : X) ^ k * g := fun g =>
      Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hzc k) g
    rw [mul_assoc, ← hc g₀, inv_mul_cancel_left]
  have hpowmem : (z : X) ^ T.index ∈ T := MonoidHom.transfer_eq_pow_aux (z : X) key
  have h2 : (⟨(z : X), hZT z.2⟩ : T) ^ T.index = ⟨(z : X) ^ T.index, hpowmem⟩ :=
    Subtype.ext (by simp)
  have hwpow : lam ⟨(z : X), hZT z.2⟩ ^ T.index = 1 := by
    have h1 := MonoidHom.transfer_eq_pow lam (z : X) key
    rw [htr (z : X)] at h1
    rw [← map_pow, h2]
    exact h1.symm
  have hw3 : ∀ a : Multiplicative (ZMod 3), a ^ 3 = 1 := by
    intro a
    have hcard : Nat.card (Multiplicative (ZMod 3)) = 3 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    have h3 : a ^ Nat.card (Multiplicative (ZMod 3)) = 1 := pow_card_eq_one'
    rwa [hcard] at h3
  have hgcd : Nat.gcd 3 T.index = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hidx
  have hw1 : lam ⟨(z : X), hZT z.2⟩ = 1 := by
    have h4 := (pow_gcd_eq_one (a := lam ⟨(z : X), hZT z.2⟩) (m := 3) (n := T.index)).mpr
      ⟨hw3 _, hwpow⟩
    rwa [hgcd, pow_one] at h4
  exact hz (hlam z hw1)

end CFSG.RankThree.PartTwo.Sec8.Hering611
