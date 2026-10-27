module

public import CFSG.Quasithin.H13.L32A764g
public import CFSG.Quasithin.H13.U3L134

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem remark14_7_64_of
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h63 : Thm14_7_63) : Remark14_7_64 := by
  have h1334 : A6.Stmt13_3_4 := U3.stmt13_3_4_of h1332
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  intro G _ _ T L V h
  have S0 : Setting147 G T L V (hz T V) := ⟨h, h.isHzOne_hz h63⟩
  have hF : HypF98 T V L (fsuV1 T V) V (hz T V) := Setting147.hypF98 S0 h13322 hMod h1222
  have C : Ctx764 G T L V := ⟨h, hMod, h63, hF, h1222, h1332, h1334⟩
  refine ⟨C.comm_sup_eq, fun s hs hsQ u hu h0 => C.comm_mem_v1_of_mem_u0 hs hsQ hu h0,
    C.card_u0_le, fun h8 => ⟨fun s hs hsQ u hu hV => ?_, fun f hf => C.mem_union_of_eight h8 hf⟩,
    fun h4 => ⟨fun s hs hsQ => ⟨C.exists_comm_of_four h4 hs hsQ,
      fun u₁ hu₁ u₂ hu₂ h₁ h₂ => C.comm_mem_of_four h4 hs hsQ hu₁ hu₂ h₁ h₂⟩,
      fun f hf => C.mem_union_of_four h4 hf⟩⟩
  rw [← C.dS_inf_V_of_eight h8 hs hsQ]
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left (Subgroup.subset_closure ⟨u, hu, rfl⟩), hV⟩

end CFSG.Quasithin.H13.L32A
