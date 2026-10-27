module

public import CFSG.Quasithin.H13.GoldschmidtU43Act

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13.A6

@[expose] def U43Main : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), Hyp z → LieModel G .PSU 4 3 1

theorem stmtU43Type_of_main (h : U43Main) : StmtU43Type :=
  fun G _ _ z hz hiso hcen hcent hidx hg => h G z ⟨hz, hiso, hcen, hcent, hidx, hg⟩

end CFSG.Quasithin.H13.U43
