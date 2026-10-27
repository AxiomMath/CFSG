module

public import CFSG.Quasithin.H13.AS91Sec7Res

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

theorem Loc49.conj_mem_E {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z) (h : ↥c.G1)
    {e : G} (he : e ∈ c.E) : (h : G) * e * (h : G)⁻¹ ∈ c.E :=
  (Subgroup.mem_normalizer_iff.1 h.2 e).1 he

structure ResM24T {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z) extends ResM24 c where
  todd : ↥c.E ≃* CFSG.Quasithin.H.Mathieu.W11
  todd_equiv : ∀ (h : ↥c.G1) (e : ↥c.E),
    todd ⟨(h : G) * e * (h : G)⁻¹, c.conj_mem_E h e.2⟩ =
      CFSG.Quasithin.H.Mathieu.rho11 CFSG.Monster.Code.AutPerm le_rfl ⟨φ h, toResM24.φ_mem h⟩
        (todd e)

end CFSG.Quasithin.H13.AS91
