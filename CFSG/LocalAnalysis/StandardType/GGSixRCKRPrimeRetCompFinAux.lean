module

public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.LieType.Chevalley.LangFiniteRootCentralizer

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule

theorem rckCf_center_le_isogeny_ker
    (k : Type) [Field k] [Finite k] [CharP k 2] :
    Subgroup.center ↥(e6Data_valid.minGroup k) ≤ (e6Isogeny k).ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  have hzc : e6Isogeny k z ∈ Subgroup.center ↥(adjointGroup Tag.E6 k) := by
    refine Subgroup.mem_center_iff.2 fun y => ?_
    obtain ⟨u, rfl⟩ := e6Isogeny_surjective k y
    calc e6Isogeny k u * e6Isogeny k z = e6Isogeny k (u * z) := (map_mul _ _ _).symm
      _ = e6Isogeny k (z * u) := by rw [Subgroup.mem_center_iff.1 hz u]
      _ = e6Isogeny k z * e6Isogeny k u := map_mul _ _ _
  exact Subgroup.mem_bot.1 (by
    rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot_field Tag.E6 k] at hzc
    exact hzc)

end CFSG.StandardType.RCKRP

end
