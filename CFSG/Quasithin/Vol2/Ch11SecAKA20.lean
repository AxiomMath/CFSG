module

public import CFSG.Quasithin.Vol2.Ch11SecAKA16
public import CFSG.Quasithin.Vol2.Ch11SecAKA19

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin

theorem factLineSp4_holds : Ch11.SecA.FactLineSp4 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ hZ P hP U₂ hU₂
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf hP
  rw [← hK] at hU₂
  obtain ⟨S, hS, hc, rfl⟩ := exists_eq_pre_of_isFlagW_sp hW hf hg hU₂
  rw [(eq_std_of_stable_sp hS).2.1 hc]
  exact ⟨KA.lineFacts_sp hK4 hf hZ g, fun hcomm => KA.perfCent_sp hK4 hf hZ g hcomm⟩

end CFSG.Quasithin.Vol2.KGNat
