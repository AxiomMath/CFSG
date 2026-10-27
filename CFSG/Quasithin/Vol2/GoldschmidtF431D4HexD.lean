module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexCert
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Lines

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.D4Hex


theorem mem_hexLine_iff_lineSet (p : Fin 819) (l : Fin 2457) : p ∈ hexLine l ↔ p ∈ lineSet l := by
  rw [mem_lineSet_iff]
  constructor
  · rintro ⟨k, hk, h⟩
    interval_cases k
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr h.symm)
  · rintro (h | h | h)
    · exact ⟨0, by norm_num, h.symm⟩
    · exact ⟨1, by norm_num, h.symm⟩
    · exact ⟨2, by norm_num, h.symm⟩

instance instGraphActionD : GraphAction D hexGraph := hexGraphAction_of (fun x p v => by
  rw [mem_hexLine_iff_lineSet, mem_hexLine_iff_lineSet]
  exact mem_lineSet_smul_iff x p v)

theorem actsAs_d4GenG : ∀ j < 8, ActsAs (d4GenG j) permArrs[j]! := by
  intro j hj p
  exact ⟨act (d4GenG j) p, act_gen hj p, rfl⟩

theorem hexGeometryD : HexGeometry D d4GenG :=
  hexGeometry actsAs_d4GenG

theorem hexPolygonD : IsGenPolygon hexGraph 6 :=
  hexGeometryD.polygon

theorem hexPtD : HexPt D hexGraph (Sum.inl 0) (Sum.inl hexB0F) :=
  hexGeometryD.pt

theorem hexLnD :
    HexLn D hexGraph (Sum.inr 0) (Sum.inl hexY0F) (Sum.inr hexM0F) :=
  hexGeometryD.ln

end CFSG.Quasithin.D4Hex
