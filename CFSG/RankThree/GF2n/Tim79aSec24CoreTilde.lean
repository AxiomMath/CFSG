module

public import CFSG.RankThree.GF2n.Tim79aSec23Defs

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G]

theorem normalizer_Vy_eq (V H : Subgroup G) :
    Subgroup.normalizer (Vy V H : Set (Xbar V H)) =
      (Subgroup.normalizer (barOf V H V : Set (Hbar V H)) ⊓ barOf V H (xOf V H)).subgroupOf
        (barOf V H (xOf V H)) := by
  rw [Subgroup.inf_subgroupOf_right]
  ext b
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hb x
    constructor
    · intro hx
      have hxX : x ∈ barOf V H (xOf V H) := barOf_V_le V H hx
      have := (hb ⟨x, hxX⟩).mp (Subgroup.mem_subgroupOf.mpr hx)
      exact Subgroup.mem_subgroupOf.mp this
    · intro hx
      have hxX' : (b : Hbar V H) * x * (b : Hbar V H)⁻¹ ∈ barOf V H (xOf V H) :=
        barOf_V_le V H hx
      have hxX : x ∈ barOf V H (xOf V H) := by
        have h1 : (b : Hbar V H)⁻¹ * ((b : Hbar V H) * x * (b : Hbar V H)⁻¹) * (b : Hbar V H) ∈
            barOf V H (xOf V H) :=
          (barOf V H (xOf V H)).mul_mem ((barOf V H (xOf V H)).mul_mem
            ((barOf V H (xOf V H)).inv_mem b.2) hxX') b.2
        simpa [mul_assoc] using h1
      have h2 := (hb ⟨x, hxX⟩).mpr (Subgroup.mem_subgroupOf.mpr hx)
      exact Subgroup.mem_subgroupOf.mp h2
  · intro hb y
    simp only [Vy, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hb (y : Hbar V H)

end CFSG.RankThree.GF2n.Tim79a
