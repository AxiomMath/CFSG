module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthCoprimeFixedPoints

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowthCoprime

universe u v

theorem actor_card_dvd_card_sub_one_of_free
    {W : Type u} [Group W] [Finite W] {A : Type v} [Group A] [Finite A]
    [MulDistribMulAction A W]
    (hfree : ∀ a : A, a ≠ 1 → ∀ x : W, a • x = x → x = 1) :
    Nat.card A ∣ Nat.card W - 1 := by
  classical
  let X := {x : W // x ≠ 1}
  let : MulAction A X :=
    { smul := fun a x => ⟨a • x.1, by
        intro h
        apply x.2
        have h' := congrArg (fun w : W => a⁻¹ • w) h
        simpa only [inv_smul_smul, smul_one] using h'⟩
      one_smul := fun x => Subtype.ext (one_smul A x.1)
      mul_smul := fun a b x => Subtype.ext (mul_smul a b x.1) }
  have hstab : ∀ x : X, MulAction.stabilizer A x = ⊥ := by
    intro x
    apply le_antisymm _ bot_le
    intro a ha
    apply Subgroup.mem_bot.mpr
    by_contra hane
    exact x.2 (hfree a hane x (congrArg Subtype.val ha))
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  rw [Nat.card_prod] at hcard
  have hXcard : Nat.card X = Nat.card W - 1 := by
    let : Fintype W := Fintype.ofFinite W
    let : Fintype X := Fintype.ofFinite X
    let : Fintype {x : W // x = 1} := Fintype.ofFinite {x : W // x = 1}
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun x : W => x = 1)
  rw [hXcard] at hcard
  exact hcard ▸ dvd_mul_left (Nat.card A) _

theorem odd_cyclic_actor_two_kernel_data
    {M : Type u} [Group M] [Finite M] {A : Type v} [Group A] [Finite A]
    (hM : IsPGroup 2 M) (hA : Odd (Nat.card A)) (a : A) (Q : Subgroup M) :
    Nat.card (Subgroup.zpowers a) = orderOf a ∧
      Odd (Nat.card (Subgroup.zpowers a)) ∧ Group.IsSolvable Q ∧
        Nat.Coprime (Nat.card (Subgroup.zpowers a)) (Nat.card Q) := by
  have hCodd : Odd (Nat.card (Subgroup.zpowers a)) :=
    Odd.of_dvd_nat hA (Subgroup.zpowers a).card_subgroup_dvd_card
  exact ⟨Nat.card_zpowers a, hCodd, two_subgroup_solvable_coprime hM hCodd Q⟩

end CFSG.ShultStronglyClosedTI.TwoCoreGrowthCoprime
