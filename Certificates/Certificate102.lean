module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnessesCore

public section

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers

namespace CertificateChecks.Batch102

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

private theorem c8FourActionRecord128_covered : c8FourActionCovered c8FourRecordData128 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨11, ?_⟩
  decide +kernel

private theorem c8FourActionRecord128_bounded : c8FourActionBounded c8FourRecordData128 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord129_covered : c8FourActionCovered c8FourRecordData129 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨30, ?_⟩
  decide +kernel

private theorem c8FourActionRecord129_bounded : c8FourActionBounded c8FourRecordData129 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord130_covered : c8FourActionCovered c8FourRecordData130 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord130_bounded : c8FourActionBounded c8FourRecordData130 := by
  decide +kernel

private theorem c8FourActionRecord131_covered : c8FourActionCovered c8FourRecordData131 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨12, ?_⟩
  decide +kernel

private theorem c8FourActionRecord131_bounded : c8FourActionBounded c8FourRecordData131 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord132_covered : c8FourActionCovered c8FourRecordData132 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨11, ?_⟩
  decide +kernel

private theorem c8FourActionRecord132_bounded : c8FourActionBounded c8FourRecordData132 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord133_covered : c8FourActionCovered c8FourRecordData133 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord133_bounded : c8FourActionBounded c8FourRecordData133 := by
  decide +kernel

private theorem c8FourActionRecord134_covered : c8FourActionCovered c8FourRecordData134 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord134_bounded : c8FourActionBounded c8FourRecordData134 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord135_covered : c8FourActionCovered c8FourRecordData135 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord135_bounded : c8FourActionBounded c8FourRecordData135 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord136_covered : c8FourActionCovered c8FourRecordData136 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨34, ?_⟩
  decide +kernel

private theorem c8FourActionRecord136_bounded : c8FourActionBounded c8FourRecordData136 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord137_covered : c8FourActionCovered c8FourRecordData137 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord137_bounded : c8FourActionBounded c8FourRecordData137 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord138_covered : c8FourActionCovered c8FourRecordData138 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord138_bounded : c8FourActionBounded c8FourRecordData138 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord139_covered : c8FourActionCovered c8FourRecordData139 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord139_bounded : c8FourActionBounded c8FourRecordData139 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord140_covered : c8FourActionCovered c8FourRecordData140 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord140_bounded : c8FourActionBounded c8FourRecordData140 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord141_covered : c8FourActionCovered c8FourRecordData141 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨42, ?_⟩
  decide +kernel

private theorem c8FourActionRecord141_bounded : c8FourActionBounded c8FourRecordData141 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord142_covered : c8FourActionCovered c8FourRecordData142 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord142_bounded : c8FourActionBounded c8FourRecordData142 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord143_covered : c8FourActionCovered c8FourRecordData143 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord143_bounded : c8FourActionBounded c8FourRecordData143 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord144_covered : c8FourActionCovered c8FourRecordData144 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨48, ?_⟩
  decide +kernel

private theorem c8FourActionRecord144_bounded : c8FourActionBounded c8FourRecordData144 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord145_covered : c8FourActionCovered c8FourRecordData145 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord145_bounded : c8FourActionBounded c8FourRecordData145 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord146_covered : c8FourActionCovered c8FourRecordData146 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord146_bounded : c8FourActionBounded c8FourRecordData146 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord147_covered : c8FourActionCovered c8FourRecordData147 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨42, ?_⟩
  decide +kernel

private theorem c8FourActionRecord147_bounded : c8FourActionBounded c8FourRecordData147 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord148_covered : c8FourActionCovered c8FourRecordData148 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨42, ?_⟩
  decide +kernel

private theorem c8FourActionRecord148_bounded : c8FourActionBounded c8FourRecordData148 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord149_covered : c8FourActionCovered c8FourRecordData149 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨22, ?_⟩
  decide +kernel

private theorem c8FourActionRecord149_bounded : c8FourActionBounded c8FourRecordData149 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord150_covered : c8FourActionCovered c8FourRecordData150 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord150_bounded : c8FourActionBounded c8FourRecordData150 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord151_covered : c8FourActionCovered c8FourRecordData151 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨42, ?_⟩
  decide +kernel

private theorem c8FourActionRecord151_bounded : c8FourActionBounded c8FourRecordData151 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord152_covered : c8FourActionCovered c8FourRecordData152 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨42, ?_⟩
  decide +kernel

private theorem c8FourActionRecord152_bounded : c8FourActionBounded c8FourRecordData152 := by
  decide +kernel

private theorem c8FourActionRecord153_covered : c8FourActionCovered c8FourRecordData153 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord153_bounded : c8FourActionBounded c8FourRecordData153 := by
  decide +kernel

private theorem c8FourActionRecord154_covered : c8FourActionCovered c8FourRecordData154 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨24, ?_⟩
  decide +kernel

private theorem c8FourActionRecord154_bounded : c8FourActionBounded c8FourRecordData154 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord155_covered : c8FourActionCovered c8FourRecordData155 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨31, ?_⟩
  decide +kernel

private theorem c8FourActionRecord155_bounded : c8FourActionBounded c8FourRecordData155 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord156_covered : c8FourActionCovered c8FourRecordData156 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨1, ?_⟩
  decide +kernel

private theorem c8FourActionRecord156_bounded : c8FourActionBounded c8FourRecordData156 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord157_covered : c8FourActionCovered c8FourRecordData157 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨1, ?_⟩
  decide +kernel

private theorem c8FourActionRecord157_bounded : c8FourActionBounded c8FourRecordData157 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord158_covered : c8FourActionCovered c8FourRecordData158 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord158_bounded : c8FourActionBounded c8FourRecordData158 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord159_covered : c8FourActionCovered c8FourRecordData159 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord159_bounded : c8FourActionBounded c8FourRecordData159 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord160_covered : c8FourActionCovered c8FourRecordData160 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord160_bounded : c8FourActionBounded c8FourRecordData160 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord161_covered : c8FourActionCovered c8FourRecordData161 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord161_bounded : c8FourActionBounded c8FourRecordData161 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord162_covered : c8FourActionCovered c8FourRecordData162 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord162_bounded : c8FourActionBounded c8FourRecordData162 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord163_covered : c8FourActionCovered c8FourRecordData163 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord163_bounded : c8FourActionBounded c8FourRecordData163 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord164_covered : c8FourActionCovered c8FourRecordData164 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord164_bounded : c8FourActionBounded c8FourRecordData164 := by
  decide +kernel

private theorem c8FourActionRecord165_covered : c8FourActionCovered c8FourRecordData165 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord165_bounded : c8FourActionBounded c8FourRecordData165 := by
  decide +kernel

private theorem c8FourActionRecord166_covered : c8FourActionCovered c8FourRecordData166 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord166_bounded : c8FourActionBounded c8FourRecordData166 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord167_covered : c8FourActionCovered c8FourRecordData167 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord167_bounded : c8FourActionBounded c8FourRecordData167 := by
  decide +kernel

private theorem c8FourActionRecord168_covered : c8FourActionCovered c8FourRecordData168 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord168_bounded : c8FourActionBounded c8FourRecordData168 := by
  decide +kernel

private theorem c8FourActionRecord169_covered : c8FourActionCovered c8FourRecordData169 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨1, ?_⟩
  decide +kernel

private theorem c8FourActionRecord169_bounded : c8FourActionBounded c8FourRecordData169 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord170_covered : c8FourActionCovered c8FourRecordData170 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord170_bounded : c8FourActionBounded c8FourRecordData170 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord171_covered : c8FourActionCovered c8FourRecordData171 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord171_bounded : c8FourActionBounded c8FourRecordData171 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord172_covered : c8FourActionCovered c8FourRecordData172 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord172_bounded : c8FourActionBounded c8FourRecordData172 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord173_covered : c8FourActionCovered c8FourRecordData173 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨21, ?_⟩
  decide +kernel

private theorem c8FourActionRecord173_bounded : c8FourActionBounded c8FourRecordData173 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord174_covered : c8FourActionCovered c8FourRecordData174 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord174_bounded : c8FourActionBounded c8FourRecordData174 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord175_covered : c8FourActionCovered c8FourRecordData175 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord175_bounded : c8FourActionBounded c8FourRecordData175 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord176_covered : c8FourActionCovered c8FourRecordData176 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord176_bounded : c8FourActionBounded c8FourRecordData176 := by
  decide +kernel

private theorem c8FourActionRecord177_covered : c8FourActionCovered c8FourRecordData177 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨37, ?_⟩
  decide +kernel

private theorem c8FourActionRecord177_bounded : c8FourActionBounded c8FourRecordData177 := by
  decide +kernel

private theorem c8FourActionRecord178_covered : c8FourActionCovered c8FourRecordData178 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord178_bounded : c8FourActionBounded c8FourRecordData178 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord179_covered : c8FourActionCovered c8FourRecordData179 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord179_bounded : c8FourActionBounded c8FourRecordData179 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord180_covered : c8FourActionCovered c8FourRecordData180 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord180_bounded : c8FourActionBounded c8FourRecordData180 := by
  decide +kernel

private theorem c8FourActionRecord181_covered : c8FourActionCovered c8FourRecordData181 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord181_bounded : c8FourActionBounded c8FourRecordData181 := by
  decide +kernel

private theorem c8FourActionRecord182_covered : c8FourActionCovered c8FourRecordData182 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨24, ?_⟩
  decide +kernel

private theorem c8FourActionRecord182_bounded : c8FourActionBounded c8FourRecordData182 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord183_covered : c8FourActionCovered c8FourRecordData183 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord183_bounded : c8FourActionBounded c8FourRecordData183 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord184_covered : c8FourActionCovered c8FourRecordData184 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord184_bounded : c8FourActionBounded c8FourRecordData184 := by
  decide +kernel

private theorem c8FourActionRecord185_covered : c8FourActionCovered c8FourRecordData185 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord185_bounded : c8FourActionBounded c8FourRecordData185 := by
  decide +kernel

private theorem c8FourActionRecord186_covered : c8FourActionCovered c8FourRecordData186 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord186_bounded : c8FourActionBounded c8FourRecordData186 := by
  decide +kernel

private theorem c8FourActionRecord187_covered : c8FourActionCovered c8FourRecordData187 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord187_bounded : c8FourActionBounded c8FourRecordData187 := by
  decide +kernel

private theorem c8FourActionRecord188_covered : c8FourActionCovered c8FourRecordData188 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨25, ?_⟩
  decide +kernel

private theorem c8FourActionRecord188_bounded : c8FourActionBounded c8FourRecordData188 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord189_covered : c8FourActionCovered c8FourRecordData189 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨25, ?_⟩
  decide +kernel

private theorem c8FourActionRecord189_bounded : c8FourActionBounded c8FourRecordData189 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord190_covered : c8FourActionCovered c8FourRecordData190 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord190_bounded : c8FourActionBounded c8FourRecordData190 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord191_covered : c8FourActionCovered c8FourRecordData191 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord191_bounded : c8FourActionBounded c8FourRecordData191 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionChunk2_covered (j : Fin 64) :
    c8FourActionCovered (c8FourRecordChunk2[j.val]!) := by
  fin_cases j
  · exact c8FourActionRecord128_covered
  · exact c8FourActionRecord129_covered
  · exact c8FourActionRecord130_covered
  · exact c8FourActionRecord131_covered
  · exact c8FourActionRecord132_covered
  · exact c8FourActionRecord133_covered
  · exact c8FourActionRecord134_covered
  · exact c8FourActionRecord135_covered
  · exact c8FourActionRecord136_covered
  · exact c8FourActionRecord137_covered
  · exact c8FourActionRecord138_covered
  · exact c8FourActionRecord139_covered
  · exact c8FourActionRecord140_covered
  · exact c8FourActionRecord141_covered
  · exact c8FourActionRecord142_covered
  · exact c8FourActionRecord143_covered
  · exact c8FourActionRecord144_covered
  · exact c8FourActionRecord145_covered
  · exact c8FourActionRecord146_covered
  · exact c8FourActionRecord147_covered
  · exact c8FourActionRecord148_covered
  · exact c8FourActionRecord149_covered
  · exact c8FourActionRecord150_covered
  · exact c8FourActionRecord151_covered
  · exact c8FourActionRecord152_covered
  · exact c8FourActionRecord153_covered
  · exact c8FourActionRecord154_covered
  · exact c8FourActionRecord155_covered
  · exact c8FourActionRecord156_covered
  · exact c8FourActionRecord157_covered
  · exact c8FourActionRecord158_covered
  · exact c8FourActionRecord159_covered
  · exact c8FourActionRecord160_covered
  · exact c8FourActionRecord161_covered
  · exact c8FourActionRecord162_covered
  · exact c8FourActionRecord163_covered
  · exact c8FourActionRecord164_covered
  · exact c8FourActionRecord165_covered
  · exact c8FourActionRecord166_covered
  · exact c8FourActionRecord167_covered
  · exact c8FourActionRecord168_covered
  · exact c8FourActionRecord169_covered
  · exact c8FourActionRecord170_covered
  · exact c8FourActionRecord171_covered
  · exact c8FourActionRecord172_covered
  · exact c8FourActionRecord173_covered
  · exact c8FourActionRecord174_covered
  · exact c8FourActionRecord175_covered
  · exact c8FourActionRecord176_covered
  · exact c8FourActionRecord177_covered
  · exact c8FourActionRecord178_covered
  · exact c8FourActionRecord179_covered
  · exact c8FourActionRecord180_covered
  · exact c8FourActionRecord181_covered
  · exact c8FourActionRecord182_covered
  · exact c8FourActionRecord183_covered
  · exact c8FourActionRecord184_covered
  · exact c8FourActionRecord185_covered
  · exact c8FourActionRecord186_covered
  · exact c8FourActionRecord187_covered
  · exact c8FourActionRecord188_covered
  · exact c8FourActionRecord189_covered
  · exact c8FourActionRecord190_covered
  · exact c8FourActionRecord191_covered

private theorem c8FourActionChunk2_bounded (j : Fin 64) :
    c8FourActionBounded (c8FourRecordChunk2[j.val]!) := by
  fin_cases j
  · exact c8FourActionRecord128_bounded
  · exact c8FourActionRecord129_bounded
  · exact c8FourActionRecord130_bounded
  · exact c8FourActionRecord131_bounded
  · exact c8FourActionRecord132_bounded
  · exact c8FourActionRecord133_bounded
  · exact c8FourActionRecord134_bounded
  · exact c8FourActionRecord135_bounded
  · exact c8FourActionRecord136_bounded
  · exact c8FourActionRecord137_bounded
  · exact c8FourActionRecord138_bounded
  · exact c8FourActionRecord139_bounded
  · exact c8FourActionRecord140_bounded
  · exact c8FourActionRecord141_bounded
  · exact c8FourActionRecord142_bounded
  · exact c8FourActionRecord143_bounded
  · exact c8FourActionRecord144_bounded
  · exact c8FourActionRecord145_bounded
  · exact c8FourActionRecord146_bounded
  · exact c8FourActionRecord147_bounded
  · exact c8FourActionRecord148_bounded
  · exact c8FourActionRecord149_bounded
  · exact c8FourActionRecord150_bounded
  · exact c8FourActionRecord151_bounded
  · exact c8FourActionRecord152_bounded
  · exact c8FourActionRecord153_bounded
  · exact c8FourActionRecord154_bounded
  · exact c8FourActionRecord155_bounded
  · exact c8FourActionRecord156_bounded
  · exact c8FourActionRecord157_bounded
  · exact c8FourActionRecord158_bounded
  · exact c8FourActionRecord159_bounded
  · exact c8FourActionRecord160_bounded
  · exact c8FourActionRecord161_bounded
  · exact c8FourActionRecord162_bounded
  · exact c8FourActionRecord163_bounded
  · exact c8FourActionRecord164_bounded
  · exact c8FourActionRecord165_bounded
  · exact c8FourActionRecord166_bounded
  · exact c8FourActionRecord167_bounded
  · exact c8FourActionRecord168_bounded
  · exact c8FourActionRecord169_bounded
  · exact c8FourActionRecord170_bounded
  · exact c8FourActionRecord171_bounded
  · exact c8FourActionRecord172_bounded
  · exact c8FourActionRecord173_bounded
  · exact c8FourActionRecord174_bounded
  · exact c8FourActionRecord175_bounded
  · exact c8FourActionRecord176_bounded
  · exact c8FourActionRecord177_bounded
  · exact c8FourActionRecord178_bounded
  · exact c8FourActionRecord179_bounded
  · exact c8FourActionRecord180_bounded
  · exact c8FourActionRecord181_bounded
  · exact c8FourActionRecord182_bounded
  · exact c8FourActionRecord183_bounded
  · exact c8FourActionRecord184_bounded
  · exact c8FourActionRecord185_bounded
  · exact c8FourActionRecord186_bounded
  · exact c8FourActionRecord187_bounded
  · exact c8FourActionRecord188_bounded
  · exact c8FourActionRecord189_bounded
  · exact c8FourActionRecord190_bounded
  · exact c8FourActionRecord191_bounded

end CertificateChecks.Batch102

namespace Certificates

open CertificateChecks

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers in
theorem certificate102 : (c8FourActionCovered c8FourRecordData128)
    ∧ (c8FourActionBounded c8FourRecordData128)
    ∧ (c8FourActionCovered c8FourRecordData129)
    ∧ (c8FourActionBounded c8FourRecordData129)
    ∧ (c8FourActionCovered c8FourRecordData130)
    ∧ (c8FourActionBounded c8FourRecordData130)
    ∧ (c8FourActionCovered c8FourRecordData131)
    ∧ (c8FourActionBounded c8FourRecordData131)
    ∧ (c8FourActionCovered c8FourRecordData132)
    ∧ (c8FourActionBounded c8FourRecordData132)
    ∧ (c8FourActionCovered c8FourRecordData133)
    ∧ (c8FourActionBounded c8FourRecordData133)
    ∧ (c8FourActionCovered c8FourRecordData134)
    ∧ (c8FourActionBounded c8FourRecordData134)
    ∧ (c8FourActionCovered c8FourRecordData135)
    ∧ (c8FourActionBounded c8FourRecordData135)
    ∧ (c8FourActionCovered c8FourRecordData136)
    ∧ (c8FourActionBounded c8FourRecordData136)
    ∧ (c8FourActionCovered c8FourRecordData137)
    ∧ (c8FourActionBounded c8FourRecordData137)
    ∧ (c8FourActionCovered c8FourRecordData138)
    ∧ (c8FourActionBounded c8FourRecordData138)
    ∧ (c8FourActionCovered c8FourRecordData139)
    ∧ (c8FourActionBounded c8FourRecordData139)
    ∧ (c8FourActionCovered c8FourRecordData140)
    ∧ (c8FourActionBounded c8FourRecordData140)
    ∧ (c8FourActionCovered c8FourRecordData141)
    ∧ (c8FourActionBounded c8FourRecordData141)
    ∧ (c8FourActionCovered c8FourRecordData142)
    ∧ (c8FourActionBounded c8FourRecordData142)
    ∧ (c8FourActionCovered c8FourRecordData143)
    ∧ (c8FourActionBounded c8FourRecordData143)
    ∧ (c8FourActionCovered c8FourRecordData144)
    ∧ (c8FourActionBounded c8FourRecordData144)
    ∧ (c8FourActionCovered c8FourRecordData145)
    ∧ (c8FourActionBounded c8FourRecordData145)
    ∧ (c8FourActionCovered c8FourRecordData146)
    ∧ (c8FourActionBounded c8FourRecordData146)
    ∧ (c8FourActionCovered c8FourRecordData147)
    ∧ (c8FourActionBounded c8FourRecordData147)
    ∧ (c8FourActionCovered c8FourRecordData148)
    ∧ (c8FourActionBounded c8FourRecordData148)
    ∧ (c8FourActionCovered c8FourRecordData149)
    ∧ (c8FourActionBounded c8FourRecordData149)
    ∧ (c8FourActionCovered c8FourRecordData150)
    ∧ (c8FourActionBounded c8FourRecordData150)
    ∧ (c8FourActionCovered c8FourRecordData151)
    ∧ (c8FourActionBounded c8FourRecordData151)
    ∧ (c8FourActionCovered c8FourRecordData152)
    ∧ (c8FourActionBounded c8FourRecordData152)
    ∧ (c8FourActionCovered c8FourRecordData153)
    ∧ (c8FourActionBounded c8FourRecordData153)
    ∧ (c8FourActionCovered c8FourRecordData154)
    ∧ (c8FourActionBounded c8FourRecordData154)
    ∧ (c8FourActionCovered c8FourRecordData155)
    ∧ (c8FourActionBounded c8FourRecordData155)
    ∧ (c8FourActionCovered c8FourRecordData156)
    ∧ (c8FourActionBounded c8FourRecordData156)
    ∧ (c8FourActionCovered c8FourRecordData157)
    ∧ (c8FourActionBounded c8FourRecordData157)
    ∧ (c8FourActionCovered c8FourRecordData158)
    ∧ (c8FourActionBounded c8FourRecordData158)
    ∧ (c8FourActionCovered c8FourRecordData159)
    ∧ (c8FourActionBounded c8FourRecordData159)
    ∧ (c8FourActionCovered c8FourRecordData160)
    ∧ (c8FourActionBounded c8FourRecordData160)
    ∧ (c8FourActionCovered c8FourRecordData161)
    ∧ (c8FourActionBounded c8FourRecordData161)
    ∧ (c8FourActionCovered c8FourRecordData162)
    ∧ (c8FourActionBounded c8FourRecordData162)
    ∧ (c8FourActionCovered c8FourRecordData163)
    ∧ (c8FourActionBounded c8FourRecordData163)
    ∧ (c8FourActionCovered c8FourRecordData164)
    ∧ (c8FourActionBounded c8FourRecordData164)
    ∧ (c8FourActionCovered c8FourRecordData165)
    ∧ (c8FourActionBounded c8FourRecordData165)
    ∧ (c8FourActionCovered c8FourRecordData166)
    ∧ (c8FourActionBounded c8FourRecordData166)
    ∧ (c8FourActionCovered c8FourRecordData167)
    ∧ (c8FourActionBounded c8FourRecordData167)
    ∧ (c8FourActionCovered c8FourRecordData168)
    ∧ (c8FourActionBounded c8FourRecordData168)
    ∧ (c8FourActionCovered c8FourRecordData169)
    ∧ (c8FourActionBounded c8FourRecordData169)
    ∧ (c8FourActionCovered c8FourRecordData170)
    ∧ (c8FourActionBounded c8FourRecordData170)
    ∧ (c8FourActionCovered c8FourRecordData171)
    ∧ (c8FourActionBounded c8FourRecordData171)
    ∧ (c8FourActionCovered c8FourRecordData172)
    ∧ (c8FourActionBounded c8FourRecordData172)
    ∧ (c8FourActionCovered c8FourRecordData173)
    ∧ (c8FourActionBounded c8FourRecordData173)
    ∧ (c8FourActionCovered c8FourRecordData174)
    ∧ (c8FourActionBounded c8FourRecordData174)
    ∧ (c8FourActionCovered c8FourRecordData175)
    ∧ (c8FourActionBounded c8FourRecordData175)
    ∧ (c8FourActionCovered c8FourRecordData176)
    ∧ (c8FourActionBounded c8FourRecordData176)
    ∧ (c8FourActionCovered c8FourRecordData177)
    ∧ (c8FourActionBounded c8FourRecordData177)
    ∧ (c8FourActionCovered c8FourRecordData178)
    ∧ (c8FourActionBounded c8FourRecordData178)
    ∧ (c8FourActionCovered c8FourRecordData179)
    ∧ (c8FourActionBounded c8FourRecordData179)
    ∧ (c8FourActionCovered c8FourRecordData180)
    ∧ (c8FourActionBounded c8FourRecordData180)
    ∧ (c8FourActionCovered c8FourRecordData181)
    ∧ (c8FourActionBounded c8FourRecordData181)
    ∧ (c8FourActionCovered c8FourRecordData182)
    ∧ (c8FourActionBounded c8FourRecordData182)
    ∧ (c8FourActionCovered c8FourRecordData183)
    ∧ (c8FourActionBounded c8FourRecordData183)
    ∧ (c8FourActionCovered c8FourRecordData184)
    ∧ (c8FourActionBounded c8FourRecordData184)
    ∧ (c8FourActionCovered c8FourRecordData185)
    ∧ (c8FourActionBounded c8FourRecordData185)
    ∧ (c8FourActionCovered c8FourRecordData186)
    ∧ (c8FourActionBounded c8FourRecordData186)
    ∧ (c8FourActionCovered c8FourRecordData187)
    ∧ (c8FourActionBounded c8FourRecordData187)
    ∧ (c8FourActionCovered c8FourRecordData188)
    ∧ (c8FourActionBounded c8FourRecordData188)
    ∧ (c8FourActionCovered c8FourRecordData189)
    ∧ (c8FourActionBounded c8FourRecordData189)
    ∧ (c8FourActionCovered c8FourRecordData190)
    ∧ (c8FourActionBounded c8FourRecordData190)
    ∧ (c8FourActionCovered c8FourRecordData191)
    ∧ (c8FourActionBounded c8FourRecordData191) := by
  exact ⟨CertificateChecks.Batch102.c8FourActionRecord128_covered, CertificateChecks.Batch102.c8FourActionRecord128_bounded, CertificateChecks.Batch102.c8FourActionRecord129_covered, CertificateChecks.Batch102.c8FourActionRecord129_bounded, CertificateChecks.Batch102.c8FourActionRecord130_covered, CertificateChecks.Batch102.c8FourActionRecord130_bounded, CertificateChecks.Batch102.c8FourActionRecord131_covered, CertificateChecks.Batch102.c8FourActionRecord131_bounded, CertificateChecks.Batch102.c8FourActionRecord132_covered, CertificateChecks.Batch102.c8FourActionRecord132_bounded, CertificateChecks.Batch102.c8FourActionRecord133_covered, CertificateChecks.Batch102.c8FourActionRecord133_bounded, CertificateChecks.Batch102.c8FourActionRecord134_covered, CertificateChecks.Batch102.c8FourActionRecord134_bounded, CertificateChecks.Batch102.c8FourActionRecord135_covered, CertificateChecks.Batch102.c8FourActionRecord135_bounded, CertificateChecks.Batch102.c8FourActionRecord136_covered, CertificateChecks.Batch102.c8FourActionRecord136_bounded, CertificateChecks.Batch102.c8FourActionRecord137_covered, CertificateChecks.Batch102.c8FourActionRecord137_bounded, CertificateChecks.Batch102.c8FourActionRecord138_covered, CertificateChecks.Batch102.c8FourActionRecord138_bounded, CertificateChecks.Batch102.c8FourActionRecord139_covered, CertificateChecks.Batch102.c8FourActionRecord139_bounded, CertificateChecks.Batch102.c8FourActionRecord140_covered, CertificateChecks.Batch102.c8FourActionRecord140_bounded, CertificateChecks.Batch102.c8FourActionRecord141_covered, CertificateChecks.Batch102.c8FourActionRecord141_bounded, CertificateChecks.Batch102.c8FourActionRecord142_covered, CertificateChecks.Batch102.c8FourActionRecord142_bounded, CertificateChecks.Batch102.c8FourActionRecord143_covered, CertificateChecks.Batch102.c8FourActionRecord143_bounded, CertificateChecks.Batch102.c8FourActionRecord144_covered, CertificateChecks.Batch102.c8FourActionRecord144_bounded, CertificateChecks.Batch102.c8FourActionRecord145_covered, CertificateChecks.Batch102.c8FourActionRecord145_bounded, CertificateChecks.Batch102.c8FourActionRecord146_covered, CertificateChecks.Batch102.c8FourActionRecord146_bounded, CertificateChecks.Batch102.c8FourActionRecord147_covered, CertificateChecks.Batch102.c8FourActionRecord147_bounded, CertificateChecks.Batch102.c8FourActionRecord148_covered, CertificateChecks.Batch102.c8FourActionRecord148_bounded, CertificateChecks.Batch102.c8FourActionRecord149_covered, CertificateChecks.Batch102.c8FourActionRecord149_bounded, CertificateChecks.Batch102.c8FourActionRecord150_covered, CertificateChecks.Batch102.c8FourActionRecord150_bounded, CertificateChecks.Batch102.c8FourActionRecord151_covered, CertificateChecks.Batch102.c8FourActionRecord151_bounded, CertificateChecks.Batch102.c8FourActionRecord152_covered, CertificateChecks.Batch102.c8FourActionRecord152_bounded, CertificateChecks.Batch102.c8FourActionRecord153_covered, CertificateChecks.Batch102.c8FourActionRecord153_bounded, CertificateChecks.Batch102.c8FourActionRecord154_covered, CertificateChecks.Batch102.c8FourActionRecord154_bounded, CertificateChecks.Batch102.c8FourActionRecord155_covered, CertificateChecks.Batch102.c8FourActionRecord155_bounded, CertificateChecks.Batch102.c8FourActionRecord156_covered, CertificateChecks.Batch102.c8FourActionRecord156_bounded, CertificateChecks.Batch102.c8FourActionRecord157_covered, CertificateChecks.Batch102.c8FourActionRecord157_bounded, CertificateChecks.Batch102.c8FourActionRecord158_covered, CertificateChecks.Batch102.c8FourActionRecord158_bounded, CertificateChecks.Batch102.c8FourActionRecord159_covered, CertificateChecks.Batch102.c8FourActionRecord159_bounded, CertificateChecks.Batch102.c8FourActionRecord160_covered, CertificateChecks.Batch102.c8FourActionRecord160_bounded, CertificateChecks.Batch102.c8FourActionRecord161_covered, CertificateChecks.Batch102.c8FourActionRecord161_bounded, CertificateChecks.Batch102.c8FourActionRecord162_covered, CertificateChecks.Batch102.c8FourActionRecord162_bounded, CertificateChecks.Batch102.c8FourActionRecord163_covered, CertificateChecks.Batch102.c8FourActionRecord163_bounded, CertificateChecks.Batch102.c8FourActionRecord164_covered, CertificateChecks.Batch102.c8FourActionRecord164_bounded, CertificateChecks.Batch102.c8FourActionRecord165_covered, CertificateChecks.Batch102.c8FourActionRecord165_bounded, CertificateChecks.Batch102.c8FourActionRecord166_covered, CertificateChecks.Batch102.c8FourActionRecord166_bounded, CertificateChecks.Batch102.c8FourActionRecord167_covered, CertificateChecks.Batch102.c8FourActionRecord167_bounded, CertificateChecks.Batch102.c8FourActionRecord168_covered, CertificateChecks.Batch102.c8FourActionRecord168_bounded, CertificateChecks.Batch102.c8FourActionRecord169_covered, CertificateChecks.Batch102.c8FourActionRecord169_bounded, CertificateChecks.Batch102.c8FourActionRecord170_covered, CertificateChecks.Batch102.c8FourActionRecord170_bounded, CertificateChecks.Batch102.c8FourActionRecord171_covered, CertificateChecks.Batch102.c8FourActionRecord171_bounded, CertificateChecks.Batch102.c8FourActionRecord172_covered, CertificateChecks.Batch102.c8FourActionRecord172_bounded, CertificateChecks.Batch102.c8FourActionRecord173_covered, CertificateChecks.Batch102.c8FourActionRecord173_bounded, CertificateChecks.Batch102.c8FourActionRecord174_covered, CertificateChecks.Batch102.c8FourActionRecord174_bounded, CertificateChecks.Batch102.c8FourActionRecord175_covered, CertificateChecks.Batch102.c8FourActionRecord175_bounded, CertificateChecks.Batch102.c8FourActionRecord176_covered, CertificateChecks.Batch102.c8FourActionRecord176_bounded, CertificateChecks.Batch102.c8FourActionRecord177_covered, CertificateChecks.Batch102.c8FourActionRecord177_bounded, CertificateChecks.Batch102.c8FourActionRecord178_covered, CertificateChecks.Batch102.c8FourActionRecord178_bounded, CertificateChecks.Batch102.c8FourActionRecord179_covered, CertificateChecks.Batch102.c8FourActionRecord179_bounded, CertificateChecks.Batch102.c8FourActionRecord180_covered, CertificateChecks.Batch102.c8FourActionRecord180_bounded, CertificateChecks.Batch102.c8FourActionRecord181_covered, CertificateChecks.Batch102.c8FourActionRecord181_bounded, CertificateChecks.Batch102.c8FourActionRecord182_covered, CertificateChecks.Batch102.c8FourActionRecord182_bounded, CertificateChecks.Batch102.c8FourActionRecord183_covered, CertificateChecks.Batch102.c8FourActionRecord183_bounded, CertificateChecks.Batch102.c8FourActionRecord184_covered, CertificateChecks.Batch102.c8FourActionRecord184_bounded, CertificateChecks.Batch102.c8FourActionRecord185_covered, CertificateChecks.Batch102.c8FourActionRecord185_bounded, CertificateChecks.Batch102.c8FourActionRecord186_covered, CertificateChecks.Batch102.c8FourActionRecord186_bounded, CertificateChecks.Batch102.c8FourActionRecord187_covered, CertificateChecks.Batch102.c8FourActionRecord187_bounded, CertificateChecks.Batch102.c8FourActionRecord188_covered, CertificateChecks.Batch102.c8FourActionRecord188_bounded, CertificateChecks.Batch102.c8FourActionRecord189_covered, CertificateChecks.Batch102.c8FourActionRecord189_bounded, CertificateChecks.Batch102.c8FourActionRecord190_covered, CertificateChecks.Batch102.c8FourActionRecord190_bounded, CertificateChecks.Batch102.c8FourActionRecord191_covered, CertificateChecks.Batch102.c8FourActionRecord191_bounded⟩

end Certificates
