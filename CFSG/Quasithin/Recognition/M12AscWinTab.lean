module

public import CFSG.Quasithin.Recognition.M12AscP2Tab

public section

namespace CFSG.Quasithin

@[expose] def cpTab (uT : List (Fin 12)) : List (Fin 12) :=
  tmul (tmul (tmul uT xTab) aFTab) (tmul uT xTab)

theorem y_exists_tab : ∀ t1 ∈ ascHTabs, t1 ∈ FTabs → t1 ≠ tid → t1 ≠ zTab →
    ∀ t3 ∈ ascHTabs, t3 ∉ qTabs → tmul t3 t3 = tid → tmul t1 t3 = tmul t3 t1 →
    ∀ t4 ∈ ascHTabs, tmul t4 t4 = tid → tmul t1 t4 = tmul t4 t1 →
      tmul (tmul t4 t3) t4 = tmul zTab t3 →
      ∃ q ∈ qTabs, tmul q q = zTab ∧ tmul q t1 = tmul (tmul t1 zTab) q ∧
        tmul q t4 = tmul (tmul zTab (tmul t3 t1)) q ∧ tmul q t3 = tmul (tmul t1 t4) q := by
  decide +kernel

@[expose] def AbarTabs (uT : List (Fin 12)) : List (List (Fin 12)) :=
  [tid, aFTab, cpTab uT, tmul aFTab (cpTab uT)]

@[expose] def normAbar (uT t : List (Fin 12)) : Bool :=
  (AbarTabs uT).all fun w => (AbarTabs uT).any fun w' => tmul t w == tmul w' t

theorem normAbar_count_u : (ascHTabs.filter (normAbar uTab)).length = 48 := by decide +kernel

theorem normAbar_count_uz : (ascHTabs.filter (normAbar uzTab)).length = 48 := by decide +kernel

end CFSG.Quasithin
