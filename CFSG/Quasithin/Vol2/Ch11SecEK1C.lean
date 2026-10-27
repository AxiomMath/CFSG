module

public import CFSG.Quasithin.Vol2.Ch11SecEFacts4
public import CFSG.Quasithin.Vol2.Ch11SecAKA1
public import CFSG.Quasithin.Vol2.Ch11G2Q8NatPoint

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat

theorem factFixPointSL3_holds : FactFixPointSL3 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U hU w hw
  have : CharP K 2 := charP_two_of_card (by omega) hK
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  rw [← hK] at hU
  have hUeq := eq_U1_of_isFlagW hW hf hg hU
  subst hUeq
  have h1 := (fixedW_iff hf hg w).mp fun s hs => by
    rw [hw s hs, mul_inv_cancel]
    exact Subgroup.one_mem _
  rw [← stdLine_eq_flagSpace]
  exact h1

theorem factFixPointSp4_holds : FactFixPointSp4 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U hU w hw
  have : CharP K 2 := charP_two_of_card (by omega) hK
  obtain ⟨f, hf, g, hg, hUeq⟩ := KA.exists_point_coords hn hK hW hπ hP hU
  subst hUeq
  exact (fixedW_iff_sp hf hg w).mp fun s hs => by
    rw [hw s hs, mul_inv_cancel]
    exact Subgroup.one_mem _

open CFSG.Quasithin.Vol2.Ch11.G2Q8 in
theorem factFixPointG2_holds : FactFixPointG2 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U hU w hw
  have : CharP K 2 := charP_two_of_card (by omega) hK
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  have hU1 := eq_U1_of_isFlagWG hW hf hc0 hc1 hg (by rw [hK]; exact hU)
  subst hU1
  change f w ∈ gmapG g (stdF K 1)
  rw [mem_gmapG]
  refine fixed_U0 fun u hu => ?_
  have h1 := congrArg f (hw _ ((hg _).mpr ⟨u, hu, rfl⟩))
  rw [IsCoord.actG hf hc0 hc1] at h1
  rw [← conj_g2Act, h1]

end CFSG.Quasithin.Vol2.Ch11.SecE
