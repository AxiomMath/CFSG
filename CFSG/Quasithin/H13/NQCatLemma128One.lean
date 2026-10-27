module

public import CFSG.Quasithin.H13.LocDblSporadic

public section

namespace CFSG.Quasithin.H13.NQCat

theorem lemma128One_holds
    : CFSG.Quasithin.Lemma128One := by
  intro G _ _ hQ hs hnab S L K hL hK hLK s hs'
  exact conjugate_eq_self_iff.mp
    (LocDbl.local_double_embedding_exclusion G S L K hs hnab hQ hL hK hLK s hs')

end CFSG.Quasithin.H13.NQCat
