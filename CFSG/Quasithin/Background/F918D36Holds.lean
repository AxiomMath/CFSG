module

public import CFSG.Quasithin.Background.SmithD39TwoSzHolds
public import CFSG.Quasithin.Background.F918YM

public section

namespace CFSG.Quasithin

theorem d36_holds :
    D36 :=
  ⟨SmithD39Two.d36c_holds, d36B48q_of_narrow SmithD39Two.d36c_holds
    (d36B48qN_proved H13.d35_proved d36A38_holds (d3L38_of_a38 d3A38_holds))⟩

end CFSG.Quasithin

end
