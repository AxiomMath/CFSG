module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecFB
public import CFSG.Milestones.ASVolI.E1
public import CFSG.Quasithin.Vol2.KGFactC31KG443Sec

public section

namespace CFSG.Quasithin.H13.P31Sec

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open CFSG.Assembly.LowTwoRank

section NoCert

theorem e114Used_w31_of (h : CFSG.ASVolI.E_1_14) : E114Used_w31 := by
  intro G' _ _ T' hsqtk hsimple hsyl hFT
  obtain ⟨⟨h1a, h1b⟩, -, h3, -, h5, -, -⟩ := h G' T' hsqtk hsimple hsyl hFT
  refine ⟨?_, h1b, h3, fun hM => h5 (Or.inr (Or.inr (Or.inr (Or.inl hM))))⟩
  intro n hn hfam
  refine h1a n hn ?_
  rcases hfam with h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

end NoCert

section Cert


theorem simpleSectionSQT_holds
    : SimpleSectionSQT :=
  fun hX H N _ _ hnab =>
    (CFSG.SectionRank.sqt_catalog_of_simple_section_of_sqtk hX H N hnab).1

theorem m22_facts
    :
    IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧
      ∃ a b : CFSG.Blueprint.NativeSporadic.Carrier .M22, a * b ≠ b * a :=
  ⟨CFSG.Quasithin.KGC31.KG443.isSimpleGroup_m22, CFSG.Quasithin.KGC31.KG443.not_comm_m22⟩

theorem lemmaFBound_w31_final
    (h1222 : Stmt12_2_2) : LemmaFBound_w31 :=
  lemmaFBound_w31_of h1222 (e114Used_w31_of CFSG.ASVolI.as_E_1_14) simpleSectionSQT_holds m22_facts

end Cert

end CFSG.Quasithin.H13.P31Sec
