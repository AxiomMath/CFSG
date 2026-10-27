module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotJ2
public import CFSG.LargeExtraspecial.S9FiveB

public section

namespace CFSG.Quasithin

open scoped commutatorElement

theorem IsQ8D8.isExtraspecialPGroup {P : Type*} [Group P] [Finite P] (h : IsQ8D8 P) :
    CFSG.IsExtraspecialPGroup 2 P := by
  obtain ⟨z, hzc, hz1, -, hcen, hsq⟩ := H13.isQ8D8_central_facts h
  have hsqc : ∀ x : P, x ^ 2 ∈ Subgroup.center P := fun x => by
    rw [pow_two]
    rcases hsq x with hx | hx
    · rw [hx]; exact Subgroup.one_mem _
    · rw [hx]; exact hzc
  have hZ : Nat.card (Subgroup.center P) = 2 := by
    rw [Nat.card_eq_two_iff' (1 : Subgroup.center P)]
    refine ⟨⟨z, hzc⟩, fun h1 => hz1 (congrArg Subtype.val h1), fun y hy => ?_⟩
    rcases hcen y y.2 with h1 | h1
    · exact absurd (Subtype.ext h1) hy
    · exact Subtype.ext h1
  refine CFSG.LargeExtraspecial.S9.isExtraspecialPGroup_of_center
    (IsPGroup.of_card (n := 5) (by rw [h.1]; norm_num)) hZ le_rfl (fun x y => ?_) hsqc
    (fun x hx => Subgroup.mem_center_iff.mpr fun y => (hx y).symm) ?_
  · have : ⁅x, y⁆ = x ^ 2 * (x⁻¹ * y) ^ 2 * (y⁻¹) ^ 2 := by
      simp only [commutatorElement_def, pow_two]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hsqc x) (hsqc _)) (hsqc _)
  · by_contra hne
    push Not at hne
    have htop : Subgroup.center P = ⊤ := eq_top_iff.mpr fun x _ => hne x
    rw [htop, Subgroup.card_top, h.1] at hZ
    omega

end CFSG.Quasithin
