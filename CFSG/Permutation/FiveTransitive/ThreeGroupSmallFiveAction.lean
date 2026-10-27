module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.ThreeGroupSmallFiveAction

open MulAction

theorem card_and_fixed
    {A Q : Type*} [Group A] [Group Q] [Finite Q] [MulDistribMulAction A Q]
    (hA : IsPGroup 5 A) (hQ : IsPGroup 3 Q) (hcard : Nat.card Q ≤ 81)
    (hmove : ∃ a : A, ∃ q : Q, a • q ≠ q) :
    Nat.card Q = 81 ∧ FixedPoints.subgroup A Q = ⊥ := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let C := FixedPoints.subgroup A Q
  have hmod : Nat.card Q % 5 = Nat.card C % 5 := hA.card_modEq_card_fixedPoints Q
  have hle : Nat.card C ≤ Nat.card Q := Nat.card_le_card_of_injective
    (fun x : C => x.val) Subtype.val_injective
  have hlt : Nat.card C < Nat.card Q := lt_of_le_of_ne hle (by
    intro he
    have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C he
    obtain ⟨a,q,hq⟩ := hmove
    exact hq ((show q ∈ C from htop ▸ Subgroup.mem_top q) a))
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  obtain ⟨d,hd⟩ := IsPGroup.iff_card.mp (hQ.to_subgroup C)
  have hbound (k : ℕ) (hk : 3 ^ k ≤ 81) : k ≤ 4 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < 3) (by omega : 5 ≤ k)
    norm_num at hh
    omega
  have he4 := hbound e (he ▸ hcard)
  have hd4 := hbound d (hd ▸ hle.trans hcard)
  have hboth : Nat.card Q = 81 ∧ Nat.card C = 1 := by
    rw [he,hd] at hmod hlt ⊢
    interval_cases e <;> interval_cases d <;> norm_num at *
  exact ⟨hboth.1,Subgroup.card_eq_one.mp hboth.2⟩

theorem invariant_eq_top
    {A Q : Type*} [Group A] [Group Q] [Finite Q] [MulDistribMulAction A Q]
    (hA : IsPGroup 5 A) (hQ : IsPGroup 3 Q) (hcard : Nat.card Q ≤ 81)
    (hmove : ∃ a : A, ∃ q : Q, a • q ≠ q)
    (H : Subgroup Q) (hH : H ≠ ⊥)
    (hstable : ∀ (a : A) (q : Q), q ∈ H → a • q ∈ H) : H = ⊤ := by
  classical
  let _ : MulDistribMulAction A H :=
    { smul := fun a q => ⟨a • q.val, hstable a q.val q.property⟩
      one_smul := fun q => Subtype.ext (one_smul A q.val)
      mul_smul := fun a b q => Subtype.ext (mul_smul a b q.val)
      smul_one := fun a => Subtype.ext (smul_one a)
      smul_mul := fun a q r => Subtype.ext (smul_mul' a q.val r.val) }
  let _ : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH
  obtain ⟨q,hq⟩ := exists_ne (1 : H)
  have hboth := card_and_fixed hA hQ hcard hmove
  have hmoveH : ∃ a : A, ∃ q : H, a • q ≠ q := by
    by_contra hn
    push Not at hn
    have hfix : q.val ∈ FixedPoints.subgroup A Q :=
      fun a => congrArg Subtype.val (hn a q)
    rw [hboth.2,Subgroup.mem_bot] at hfix
    exact hq (Subtype.ext hfix)
  have hle : Nat.card H ≤ 81 := (Nat.card_le_card_of_injective
    (fun q : H => q.val) Subtype.val_injective).trans hcard
  have hH81 := (card_and_fixed hA (hQ.to_subgroup H) hle hmoveH).1
  exact Subgroup.eq_top_of_card_eq H (hH81.trans hboth.1.symm)

end FiveTransitive.ThreeGroupSmallFiveAction

end CFSG
