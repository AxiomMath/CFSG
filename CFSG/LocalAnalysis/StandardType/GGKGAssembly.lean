module

public import CFSG.LocalAnalysis.StandardType.GGKGDefs

public section

namespace CFSG.StandardType.KG

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10F

theorem kgSimple_of_families (hL : KGSimpleOn FamLin) (hU : KGSimpleOn FamUni)
    (hS : KGSimpleOn FamSymp) (hO : KGSimpleOn FamOrth) (hE : KGSimpleOn FamExc) : KGSimple := by
  intro p hp hp2 S _ _ lab α K _ hlab hcen hin hαp hα1 hK k f hk hlabK
  rcases fam_cover lab with h | h | h | h | h
  · exact hL p hp hp2 S lab α K h hlab hcen hin hαp hα1 hK k f hk hlabK
  · exact hU p hp hp2 S lab α K h hlab hcen hin hαp hα1 hK k f hk hlabK
  · exact hS p hp hp2 S lab α K h hlab hcen hin hαp hα1 hK k f hk hlabK
  · exact hO p hp hp2 S lab α K h hlab hcen hin hαp hα1 hK k f hk hlabK
  · exact hE p hp hp2 S lab α K h hlab hcen hin hαp hα1 hK k f hk hlabK

theorem kgExc_of_split (hE : KGSimpleOn FamExcE) (hT : KGSimpleOn FamExcTw)
    (hF : KGSimpleOn FamExcF4) (hS : KGSimpleOn FamExcSmall) : KGSimpleOn FamExc := by
  intro p hp hp2 S _ _ lab α K hFam hlab hcen hin hαp hα1 hK k f hk hlabK
  rcases hFam with h | h | h | h | h | h | h | h | h | h | h
  · exact hE p hp hp2 S lab α K (Or.inl h) hlab hcen hin hαp hα1 hK k f hk hlabK
  · exact hE p hp hp2 S lab α K (Or.inr (Or.inl h)) hlab hcen hin hαp hα1 hK k f hk hlabK
  · exact hE p hp hp2 S lab α K (Or.inr (Or.inr h)) hlab hcen hin hαp hα1 hK k f hk hlabK
  · exact hF p hp hp2 S lab α K h hlab hcen hin hαp hα1 hK k f hk hlabK
  · exact hT p hp hp2 S lab α K h hlab hcen hin hαp hα1 hK k f hk hlabK
  · exact hS p hp hp2 S lab α K (Or.inl h) hlab hcen hin hαp hα1 hK k f hk hlabK
  · exact hS p hp hp2 S lab α K (Or.inr (Or.inl h)) hlab hcen hin hαp hα1 hK k f hk hlabK
  · exact hS p hp hp2 S lab α K (Or.inr (Or.inr (Or.inl h))) hlab hcen hin hαp hα1 hK k f hk hlabK
  · exact hS p hp hp2 S lab α K (Or.inr (Or.inr (Or.inr (Or.inl h)))) hlab hcen hin hαp hα1 hK k f
      hk hlabK
  · exact hS p hp hp2 S lab α K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) hlab hcen hin hαp hα1
      hK k f hk hlabK
  · exact hS p hp hp2 S lab α K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))) hlab hcen hin hαp hα1
      hK k f hk hlabK

end CFSG.StandardType.KG
