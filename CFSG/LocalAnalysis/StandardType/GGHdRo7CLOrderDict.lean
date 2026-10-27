module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLOrderKnown
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLOrderLabel
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLOrderSp
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLOrderF4
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordAux

public section

namespace CFSG.StandardType.HdRo7C

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem c2_lorder_of_dict
    (hKG : GGPumpCLabelKnown) :
    C2LOrderLeaf := by
  intro _ _ _ hRig _ G _ _ p B Bs x L D J y K hH hfact hrow n V _ _ ι b hy hp3 hn hyb hAK
  obtain ⟨lab, hlab, hLlab⟩ := c2_lorder_label_exists hH
  have hrow2 := hrow
  obtain ⟨labJ, labK, hJlam, hKlam, hJlab, hKlab, hrow'⟩ := hrow2
  obtain ⟨-, hJtag, hJn, -, -, hrank⟩ := hrow'
  have h5 : 5 ≤ labK.rank := hdRo7CLCoordAux_rank_ge_five hJlam hJn hJtag hrank
  rcases ggCorank2CDict_of_known hKG hRig G p B Bs x L D J y K hH hrow labJ hJlam hJlab hJtag hJn lab hlab
      hLlab with
    ⟨htag, hn1, hlt⟩ | ⟨htag, hn1, -⟩
  · exact c2_lorder_sp hRig hH n V ι b hp3 hn lab hlab hLlab htag hn1 (by omega)
  · exact (c2_lorder_f4 hRig hH n V ι b hp3 hn lab hlab hLlab htag hn1).elim

end CFSG.StandardType.HdRo7C

end
