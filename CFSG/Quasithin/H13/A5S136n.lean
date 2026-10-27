module

public import CFSG.Quasithin.H13.A5S136m
public import CFSG.Quasithin.H13.A5OutAlt67

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem factOutAlt67 : FactOutAlt67 := by
  intro G _ _ K hK _ hshape g hg hodd
  rcases hshape with h6 | h7
  · obtain ⟨φ⟩ := h6
    exact inducesInner_of_odd hK.1 (Or.inl rfl) φ hg hodd
  · obtain ⟨φ⟩ := h7
    exact inducesInner_of_odd hK.1 (Or.inr rfl) φ hg hodd

theorem elim1366CD (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) : Elim1366CD :=
  elim1366CD_of h1222 h517 h37 h38 factOutAlt67

end CFSG.Quasithin.H13.A5
