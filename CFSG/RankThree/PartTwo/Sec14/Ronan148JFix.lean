module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

@[instance_reducible]
def conjActionOfNormalizes {X : Type} [Group X] (P K : Subgroup X)
    (hPK : P ≤ Subgroup.normalizer (K : Set X)) : MulAction (↥P) (↥K) where
  smul g k :=
    ⟨(g : X) * (k : X) * (g : X)⁻¹, (Subgroup.mem_normalizer_iff.mp (hPK g.2) (k : X)).mp k.2⟩
  one_smul k := Subtype.ext (by
    change ((1 : P) : X) * (k : X) * ((1 : P) : X)⁻¹ = (k : X)
    simp)
  mul_smul g h k := Subtype.ext (by
    change ((g * h : P) : X) * (k : X) * ((g * h : P) : X)⁻¹ =
      (g : X) * ((h : X) * (k : X) * (h : X)⁻¹) * (g : X)⁻¹
    simp [mul_assoc])

theorem exists_pow_eq_one_mem_centralizer {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {P K : Subgroup X} (hP : IsPGroup p P)
    (hPK : P ≤ Subgroup.normalizer (K : Set X)) (hp : p ∣ Nat.card K) :
    ∃ k ∈ K, k ≠ 1 ∧ k ^ p = 1 ∧ k ∈ Subgroup.centralizer (P : Set X) := by
  letI conj : MulAction (↥P) (↥K) := conjActionOfNormalizes P K hPK
  have hfix : ∀ k : ↥K,
      k ∈ MulAction.fixedPoints (↥P) (↥K) ↔ (k : X) ∈ Subgroup.centralizer (P : Set X) := by
    intro k
    rw [MulAction.mem_fixedPoints, Subgroup.mem_centralizer_iff]
    constructor
    · intro h y hy
      have h2 : y * (k : X) * y⁻¹ = (k : X) := congrArg Subtype.val (h ⟨y, hy⟩)
      exact mul_inv_eq_iff_eq_mul.mp h2
    · intro h m
      apply Subtype.ext
      change (m : X) * (k : X) * (m : X)⁻¹ = (k : X)
      rw [h m m.2, mul_inv_cancel_right]
  let e : ↥(MulAction.fixedPoints (↥P) (↥K)) ≃ ↥(K ⊓ Subgroup.centralizer (P : Set X)) :=
    { toFun := fun x => ⟨(x.1 : X), Subgroup.mem_inf.mpr ⟨x.1.2, (hfix x.1).mp x.2⟩⟩
      invFun := fun y =>
        ⟨⟨(y : X), (Subgroup.mem_inf.mp y.2).1⟩,
          (hfix ⟨(y : X), (Subgroup.mem_inf.mp y.2).1⟩).mpr (Subgroup.mem_inf.mp y.2).2⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl }
  have hmod : Nat.card ↥K ≡ Nat.card ↥(K ⊓ Subgroup.centralizer (P : Set X)) [MOD p] := by
    have h := hP.card_modEq_card_fixedPoints (↥K)
    rwa [Nat.card_congr e] at h
  have hdvd : p ∣ Nat.card ↥(K ⊓ Subgroup.centralizer (P : Set X)) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hp))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hxmem := Subgroup.mem_inf.mp x.2
  have hpow : x ^ p = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hpow' : (x : X) ^ p = 1 := by
    have h := congrArg Subtype.val hpow
    simpa using h
  refine ⟨(x : X), hxmem.1, ?_, hpow', hxmem.2⟩
  intro h1
  have hx1 : x = 1 := Subtype.ext (by simp [h1])
  have hp1 : 1 < p := Nat.Prime.one_lt (Fact.out)
  rw [hx1, orderOf_one] at hx
  omega

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
