module

public import Certificates.Kernel.S1277.Facts

public section

public section

namespace Certificates

theorem certificate589103 :
    (∀ Γ ∈ [CFSG.Quasithin.H13.S127.Mod.gm6, CFSG.Quasithin.H13.S127.Mod.nm6],
      Certificates.Data.S1277Facts.ModelFacts1277 Γ) ∧
    (CFSG.Quasithin.H13.S127.Mod.gm6.map (·.app 5)).toFinset.card = 45 ∧
    ∀ c < 64, (CFSG.Quasithin.H13.S127.Mod.gm6.map (·.app c)).toFinset.card = 45 →
      ∃ B ∈ CFSG.Quasithin.H13.S127.Mod.gm6, B.app 5 = c :=
  ⟨List.forall_mem_cons.2 ⟨CFSG.KP.S1277Facts.modelFacts_gm6,
      List.forall_mem_cons.2 ⟨CFSG.KP.S1277Facts.modelFacts_nm6,
        fun _ h => absurd h List.not_mem_nil⟩⟩,
    CFSG.KP.S1277Gm.orbit5_card, CFSG.KP.S1277Gm.orbit45⟩

end Certificates

end

end
