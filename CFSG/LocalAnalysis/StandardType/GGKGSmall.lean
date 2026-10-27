module

public import CFSG.LocalAnalysis.StandardType.GGKGSmallA
public import CFSG.LocalAnalysis.StandardType.GGKGSmallB

public section

namespace CFSG.StandardType.KG

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10F

theorem kgExcSmall_holds :
    KGSimpleOn FamExcSmall := by
  intro p hp hp2 S _ _ lab α K hFam hlab hcen hin hαp hα1 hK k f hk hlabK
  rcases hFam with h | h | h | h | h | h
  · exact kgSmallB_holds p hp hp2 S lab α K (Or.inl h) hlab hcen hin hαp hα1 hK k f hk hlabK
  · exact kgSmallA_holds p hp hp2 S lab α K (Or.inr (Or.inl h)) hlab hcen hin hαp hα1 hK k f hk
      hlabK
  · exact kgSmallA_holds p hp hp2 S lab α K (Or.inr (Or.inr (Or.inl h))) hlab hcen hin hαp hα1 hK
      k f hk hlabK
  · exact kgSmallA_holds p hp hp2 S lab α K (Or.inl h) hlab hcen hin hαp hα1 hK k f hk hlabK
  · exact kgSmallB_holds p hp hp2 S lab α K (Or.inr h) hlab hcen hin hαp hα1 hK k f hk hlabK
  · exact kgSmallA_holds p hp hp2 S lab α K (Or.inr (Or.inr (Or.inr h))) hlab hcen hin hαp hα1 hK
      k f hk hlabK

end CFSG.StandardType.KG
