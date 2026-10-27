module

public import CFSG.RankThree.PartOne.CTP.StdCent

public section

namespace CFSG.RankThree.PartOne.CTP

variable {G : Type} [Group G] [Finite G] {c : G} {f₀ : ℕ} {I K BK : Subgroup G}
  {J : Fin 3 → Fin 3 → Subgroup G}

theorem ifacts_of_config
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (cfg : IConfig c f₀ I K BK J) : IFacts c f₀ I K BK J := by
  obtain ⟨pic⟩ := exists_stdData hGA cfg
  exact
    { I_model := cfg_I_model hGA cfg
      K_perfect := cfg_K_perfect cfg
      K_ne_bot := cfg_K_ne_bot cfg
      J_le_K := fun _ _ hab => cfg_J_le_K cfg hab
      M_model := fun _ _ hab => cfg_M_model cfg pic hab
      M_quasi := fun _ _ hab => cfg_M_quasi cfg pic hab
      J_le_M := fun _ _ hab => cfg_J_le_M cfg pic hab
      M_le := fun _ _ _ => pairLayer_le_I _
      c_norm_M := fun _ _ hab => cfg_c_norm_M cfg pic hab
      c_outer_M := fun _ _ hab => cfg_c_outer_M cfg pic hab
      M_sup := fun _ _ _ hab had hbd => cfg_M_sup cfg pic hab had hbd
      K_sup_M := fun _ _ hab => cfg_K_sup_M cfg pic hab
      generation := fun _ _ hab => cfg_generation cfg pic hab
      inv_centralizes := fun _ ht ht2 hK u hu => cfg_inv_centralizes cfg pic ht ht2 hK u hu }

theorem istd_holds :
    IStd (CFSG.Open.GriessAllModelsStatement) :=
  fun hGA _ _ _ _ _ _ _ _ _ cfg => ifacts_of_config hGA cfg

end CFSG.RankThree.PartOne.CTP
