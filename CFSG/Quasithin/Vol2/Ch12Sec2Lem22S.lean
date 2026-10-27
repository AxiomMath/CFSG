module

public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Lem22

variable {W : Type*} [CommGroup W] {G₀ : Subgroup (MulAut W)} {Z : Subgroup W}

theorem l3_β_eq_iff (D : L3Data G₀ ⊤ Z) (a b : W) :
    D.β ⟨a, Subgroup.mem_top a⟩ = D.β ⟨b, Subgroup.mem_top b⟩ ↔ a * b⁻¹ ∈ Z := by
  have e : (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup W)) =
      ⟨a * b⁻¹, Subgroup.mem_top _⟩ * ⟨b, Subgroup.mem_top b⟩ := Subtype.ext (by simp)
  rw [e, map_mul, mul_eq_right]
  exact D.ker_β ⟨a * b⁻¹, Subgroup.mem_top _⟩

end Lem22

end CFSG.Quasithin.H13
