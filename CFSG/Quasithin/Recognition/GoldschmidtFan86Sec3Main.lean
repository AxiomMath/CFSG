module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Fan40
public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalPerm3
public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalGcirc

public section

namespace CFSG.Quasithin.Fan86

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem FanTree.localFacts (F : FanTree Γ G) : LocalFacts F where
  pow_smul_eq hx hord ha hb := F.exists_pow_smul_eq hx hord ha hb
  conj_mem hx hord hg := F.conj_mem_pow_mul_nbrStab hx hord hg
  cyc hva S hS := F.exists_cyclic_gen hva S hS
  perm3 hv := F.exists_perm3 hv

theorem fan_3_2_main (F : FanTree Γ G) (h29 : Sigma3Aut) : Fan32 F := fan_3_2 F.localFacts h29

theorem fan_3_3_main (F : FanTree Γ G) (h29 : Sigma3Aut) : Fan33 F :=
  fan_3_3_of_local F.localFacts h29

theorem fan_4_0_main (F : FanTree Γ G) (h29 : Sigma3Aut) : Fan40 F :=
  fan_4_0_of_local F.localFacts h29

end CFSG.Quasithin.Fan86
