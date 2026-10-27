module

public import CFSG.Quasithin.Vol2.Ch11SecEK1E
public import CFSG.Quasithin.Vol2.Ch11SecEFacts5
public import CFSG.Quasithin.Vol2.Ch11SecAKB1
public import CFSG.Quasithin.Vol2.KGNatSL3PointB
public import CFSG.Quasithin.Vol2.Ch11SecBK1A
public import CFSG.Quasithin.Vol2.Ch11SecAKA2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Quasithin

open EK1 in
theorem factTorusPointSL3_holds : FactTorusPointSL3 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U hU h hh u hu hu1 hhu hc
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have hfix := KGNat.factRadicalFixedSL3_holds K n hn hK W hW H ⊥ π hπ P hP U hU
  have hpt := KGNat.factPointSL3_holds K n hn hK W hW H ⊥ π hπ P hP U hU
  have hhU := mem_stabW_of_comm hfix hpt hc
  have htriv := (KGNat.factPointSL3B_holds K n hn hK W hW H π hπ P hP U hU).2.2 h ⟨hh, hhU⟩
    u hu hu1 hhu
  have hL := KGNat.factPointCentralizerSL3_holds K n hn hK W hW H ⊥ π hπ P hP U hU h hh
    fun w hw => by
      rw [htriv w hw, mul_inv_cancel]
      exact Subgroup.one_mem _
  obtain ⟨e⟩ := KGNat.factLeviSL3_holds K n hn hK W hW H ⊥ π hπ P hP 1 U (Or.inl rfl) hU
  exact exists_pow_eq_one_of_levi e hL hc

open EK1 in
theorem factTorusPointSp4_holds : FactTorusPointSp4 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U hU h hh u hu hu1 hhu hc
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have hfix := KGNat.factRadicalFixedSp4_holds K n hn hK W hW H ⊥ π hπ P hP U hU
  have hpt := KGNat.factPointSp4_holds K n hn hK W hW H ⊥ π hπ P hP U hU
  have hhU := mem_stabW_of_comm hfix hpt hc
  have htriv := (SecB.factPointSp4_holds K n hn hK W hW H π hπ P hP U hU).2.2 h ⟨hh, hhU⟩
    u hu hu1 hhu
  obtain ⟨e⟩ := KGNat.factLeviSp4_holds K n hn hK W hW H ⊥ π hπ P hP 1 U (Or.inl rfl) hU
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four
    (KGNat.four_le_card hn hK)
  obtain ⟨f, hf, g, -, rfl⟩ := KGNat.KA.exists_point_coords hn hK hW hπ hP hU
  have hL := SecS.C11P9A.mem_gammaW_one_of_fix hK4 hf g hh hhU fun w hw => by rw [htriv w hw]
  exact exists_pow_eq_one_of_levi e hL hc

end CFSG.Quasithin.Vol2.Ch11.SecE
