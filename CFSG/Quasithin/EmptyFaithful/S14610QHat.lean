module

public import CFSG.Quasithin.EmptyFaithful.S14610QHatA
public import CFSG.Quasithin.EmptyFaithful.S14610QHatB

public section

namespace CFSG.Quasithin

theorem input14610Hat6_proved : Input14610Hat6 :=
  input14610Hat6_of_small_action
    fun _ _ _ hperf hsimple hZ hA _ _ _ _ hpow hE φ _ hz hz1 hfpf =>
      hatA6_no_small_fpf_action hperf hsimple hZ hA hpow hE φ hz hz1 hfpf

end CFSG.Quasithin
