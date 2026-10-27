module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
import CFSG.RankThree.PartTwo.Sec21.FF79KOneSix
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G]

theorem card_modEq_card_inf_cen [Finite G] {p : ℕ} [Fact p.Prime] {a : G} (ha : orderOf a = p)
    {H : Subgroup G} (haH : a ∈ Nor H) :
    Nat.card H ≡ Nat.card (H ⊓ Cen a : Subgroup G) [MOD p] := by
  classical
  have hA : IsPGroup p (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  let α : Subgroup.zpowers a →* MulAut G := MulAut.conj.comp (Subgroup.zpowers a).subtype
  have hS : ∀ b : Subgroup.zpowers a, ∀ x ∈ (H : Set G), α b x ∈ (H : Set G) := fun b x hx =>
    conj_mem_of_mem_nor (Subgroup.zpowers_le.mpr haH b.2) hx
  letI := Semidihedral.Principal.CoprimeFixedPoint.subsetAction α (H : Set G) hS
  have hfix : ∀ x : (H : Set G),
      x ∈ MulAction.fixedPoints (Subgroup.zpowers a) (H : Set G) ↔ (x : G) ∈ Cen a := by
    intro x
    rw [MulAction.mem_fixedPoints, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have h1 : a * x * a⁻¹ = x := congrArg Subtype.val (hx ⟨a, Subgroup.mem_zpowers a⟩)
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    · intro hx b
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp b.2
      have hc : Commute a (x : G) := hx.symm
      refine Subtype.ext ?_
      change (b : G) * x * (b : G)⁻¹ = x
      rw [← hk, (hc.zpow_left k).eq, mul_inv_cancel_right]
  have e : MulAction.fixedPoints (Subgroup.zpowers a) (H : Set G) ≃ (H ⊓ Cen a : Subgroup G) :=
    { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.mpr ⟨x.1.2, (hfix x.1).mp x.2⟩⟩
      invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.mp y.2).1⟩,
        (hfix ⟨y.1, (Subgroup.mem_inf.mp y.2).1⟩).mpr (Subgroup.mem_inf.mp y.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := hA.card_modEq_card_fixedPoints (H : Set G)
  rw [Nat.card_congr e] at h
  exact h

end CFSG.RankThree.PartTwo.Sec21.FF79
