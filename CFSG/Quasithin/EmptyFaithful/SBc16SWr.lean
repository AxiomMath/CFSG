module

public import CFSG.Quasithin.EmptyFaithful.SBc15R3W
public import CFSG.Quasithin.EmptyFaithful.SBc15Weak

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Quasithin.GoldS146P CFSG.Quasithin.SBc15

namespace SBc16

section Wreath

variable {D : Type} [Group D]

instance normal_wrPerf (D' : Subgroup D) [D'.Normal] : (wrPerf D').Normal := by
  refine ⟨fun x hx w => ?_⟩
  obtain ⟨hxr, hxl⟩ := R3.mem_wrPerf.mp hx
  refine R3.mem_wrPerf.mpr ⟨by simp [hxr], fun z => ?_⟩
  have h1 : (w * x * w⁻¹).left z = w.left z * x.left (w.right⁻¹ * z) * (w.left z)⁻¹ := by
    simp [RegularWreathProduct.mul_left, RegularWreathProduct.inv_left, hxr]
    rfl
  rw [h1]
  exact ‹D'.Normal›.conj_mem _ (hxl _) _

end Wreath

end SBc16

end CFSG.Quasithin
