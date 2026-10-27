module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bTransD
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bNoTwo
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bOmega
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bCount
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Quasithin CFSG.Open

theorem factF4_holds : FactF4 := by
  unfold FactF4
  intro W _ _ _ q B hdim hq hB hS
  have hcard := f4_card_orthogonal q B hdim hq hB hS
  refine ⟨hcard, f4_no_normal_two q B hdim hq hB, ?_⟩
  intro Ω hΩ hrel
  have hcount := card_singular q B hdim hq hB hS
  refine ⟨omega_sing_transitive q B hq hB hcount Ω hΩ hrel,
    fun v hv hqv => relIndex_stabS_span q B hq hB hcount Ω hΩ hrel hv hqv, ?_, ?_⟩
  · intro S hS3 hSs
    exact part_c_of_MTS q B hq hB hdim hcard S hS3 hSs Ω hΩ hrel
  · intro w hw hqw
    obtain ⟨e, he, hew⟩ := exists_frame_of_singular q B hq hB hdim hS hw hqw
    exact part_d_of_frame q B hq Ω hΩ hrel hw e he hew

end CFSG.Quasithin.H13.C1294

end
