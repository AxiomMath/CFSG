module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4XMain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Z2B

public section

namespace CFSG.Quasithin.Fan86

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem secCfgExists_proved (F : FanTree Γ G) (L : ZLab Γ G) (h7 : Fan7 F L) (h65 : Fan65 F)
    (h81 : Fan81 F L) (h83a : Fan83a F L) (h83b : Fan83b F L) (h84a : Fan84a F L)
    (h87 : Fan87 F L) : SecCfgExists F L :=
  P4X.secCfgExists_of_shape F L h7 h65 h81 h84a fun _ D' _ hY => by
    intro g h0 h2 hord hsq
    exact D'.exists_fixed_pair F h7.1 h7.2.2.1 h83a h83b h87 hY h0 h2 hord hsq

end CFSG.Quasithin.Fan86
