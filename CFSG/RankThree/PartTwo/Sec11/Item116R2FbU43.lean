module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SylowU43
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemU43

public section

open Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem zmod3_four_pow_three_eq_one
    (y : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3)) : y ^ 3 = 1 := by
  have h3 : ∀ a : ZMod 3, (3 : ℕ) • a = 0 := fun a => by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  apply Multiplicative.toAdd.injective
  exact Prod.ext (h3 _) (Prod.ext (h3 _) (Prod.ext (h3 _) (h3 _)))

theorem exists_elemAbelian81_of_mulEquiv {X X₀' : Type} [Group X] [Group X₀'] (g : X₀' ≃* X)
    (E₀ : Subgroup X₀') (hcomm : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a)
    (hcube : ∀ x ∈ E₀, x ^ 3 = 1) (hcard : 81 ≤ Nat.card E₀) :
    ∃ E : Subgroup X, IsMulCommutative E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧ 81 ≤ Nat.card E := by
  refine ⟨E₀.map (g : X₀' →* X), ⟨⟨fun a b => ?_⟩⟩, ?_, ?_⟩
  · apply Subtype.ext
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
    show (a : X) * (b : X) = (b : X) * (a : X)
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, hcomm x hx y hy]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hcube y hy, map_one]
  · rw [Subgroup.card_map_of_injective (f := (g : X₀' →* X)) g.injective]
    exact hcard

theorem exists_elemAbelian81_U43 {X : Type} [Group X]
    (e : X ≃* CFSG.Assembly.RankThreeEven.projSU 4 3 1) :
    ∃ E : Subgroup X, IsMulCommutative E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧ 81 ≤ Nat.card E := by
  refine exists_elemAbelian81_of_mulEquiv
    (CFSG.RankThree.PartTwo.Sec4.Item434RemU43.projSUEquivUX.symm.trans e.symm :
      CFSG.LieType.Multipliers.U43.X₀ ≃* X)
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.U43Six.thetaBar.range ?_ ?_ ?_
  · intro a ha b hb
    exact CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.U43Six.thetaBar_comm a b ha hb
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    rw [← map_pow, zmod3_four_pow_three_eq_one y, map_one]
  · rw [CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.U43Six.card_range_thetaBar]
    norm_num

end CFSG.RankThree.PartTwo.Sec11
