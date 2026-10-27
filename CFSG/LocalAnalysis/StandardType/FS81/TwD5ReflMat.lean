module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5ReflStab
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5ReflExcl
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Main
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5OE6
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5ThmA
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5FixTransfer

public section

namespace CFSG.StandardType.FrameRoute.FS81

theorem t5MatFix_of_refl (hK : T5ReflFix) : T5MatFix := by
  intro Xg h
  obtain ⟨hK1, hK12, hK3⟩ := hK
  obtain ⟨c, hX⟩ := eq_closure_of_refl
    (fun M hM => mulVec_e0_of_mem_evenAll0 (evenFix0_five_subset_evenAll0 hM)) subset_rfl
    hK1 hK12 hK3 h
  fin_cases c
  · exact (false_of_eq_closure_r35 evenFix0_five_subset_evenAll0 subset_rfl h hX).elim
  · exact ⟨1, Or.inl rfl, hX⟩
  · exact ⟨-1, Or.inr rfl, hX⟩

theorem t5MatMain_of_refl (hK : T5ReflAll) : T5MatMain := by
  intro Xg h hcard
  obtain ⟨hK1, hK12, hK3⟩ := hK
  obtain ⟨c, hX⟩ := eq_closure_of_refl (fun M hM => mulVec_e0_of_mem_evenAll0 hM)
    evenFix0_five_subset_evenAll0 hK1 hK12 hK3 h
  fin_cases c
  · exact absurd hcard (not_lt.mpr (card_le_of_eq_closure_rD6 hX))
  · exact (false_of_eq_closure_r35 subset_rfl evenFix0_five_subset_evenAll0 h hX).elim
  · exact ⟨1, Or.inl rfl, hX⟩
  · exact ⟨-1, Or.inr rfl, hX⟩

theorem t5ThmA_of_refl
    (hF : T5ReflFix) (hA : T5ReflAll) : T5ThmA :=
  t5ThmA_of_cases (t5Main_of_mat (t5MatMain_of_refl hA) oE6RecOut_holds)
    (t5Fix_of_matFix (t5MatFix_of_refl hF)) t5N0_holds

end CFSG.StandardType.FrameRoute.FS81

end
