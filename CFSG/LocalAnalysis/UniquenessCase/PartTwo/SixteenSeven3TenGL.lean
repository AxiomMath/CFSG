module

public import CFSG.LieType.TwoRank.GLElementaryAbelian
public import CFSG.Quasithin.Background.A1bPGroups

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Quasithin

theorem s16c167_elem_two_in_gl {n : ℕ} (X : Subgroup (GL (Fin n) (ZMod 7)))
    (hX : ∀ x ∈ X, x * x = 1) :
    Nat.card X ≤ 2 ^ n ∧ (Nat.card X = 2 ^ n → (-1 : GL (Fin n) (ZMod 7)) ∈ X) := by
  have h2 : (2 : ZMod 7) ≠ 0 := by decide
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hx2 : ∀ x : ↥X, x * x = 1 := fun x => Subtype.ext (hX _ x.2)
  have hcomm : ∀ x y : ↥X, x * y = y * x := by
    intro x y
    have hxy : (x * y) * (x * y) = 1 := Subtype.ext (hX _ (X.mul_mem x.2 y.2))
    calc x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left hxy
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [inv_eq_of_mul_eq_one_right (hx2 x), inv_eq_of_mul_eq_one_right (hx2 y)]
  haveI : CFSG.IsElementaryAbelian 2 X :=
    { toIsMulCommutative := ⟨⟨hcomm⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => by
        rw [pow_two]
        exact hx2 x }
  have hle := CFSG.LieType.TwoRank.card_le_two_pow_of_isElementaryAbelian h2 X
  rw [Fintype.card_fin] at hle
  refine ⟨hle, fun heq => ?_⟩
  by_contra hneg
  have h := CFSG.LieType.TwoRank.two_mul_card_le_two_pow_of_neg_one_not_mem h2 X hneg
  rw [Fintype.card_fin, heq] at h
  have hpos : 0 < 2 ^ n := by positivity
  omega

theorem s16c167_elem_two_in_aut {T : Type} [Group T] (hT : IsElemAbelianOfRank 7 3 T)
    {X : Subgroup (MulAut T)} (hX : ∀ x ∈ X, x * x = 1) :
    Nat.card X ≤ 8 ∧ (Nat.card X = 8 → ∃ x ∈ X, ∀ t : T, x t = t⁻¹) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨e⟩ := hT
  let φ := CFSG.SectionRank.Ccomm.elemAutEquivGL (p := 7) e
  have hX' : ∀ y ∈ X.map φ.toMonoidHom, y * y = 1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_mul, hX x hx, map_one]
  have hcard : Nat.card (X.map φ.toMonoidHom) = Nat.card X :=
    Subgroup.card_map_of_injective (MulEquiv.injective φ)
  obtain ⟨h1, h2⟩ := s16c167_elem_two_in_gl (X.map φ.toMonoidHom) hX'
  rw [hcard] at h1 h2
  refine ⟨by simpa using h1, fun h8 => ?_⟩
  obtain ⟨x, hx, hxφ⟩ := Subgroup.mem_map.1 (h2 (by simpa using h8))
  exact ⟨x, hx, (CFSG.SectionRank.Ccomm.elemAutEquivGL_eq_neg_one_iff e x).1 hxφ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
