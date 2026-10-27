module

public import CFSG.Quasithin.Vol2.Ch1Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique.Vol2Native (SQTKHypCat A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat
  A312ForSQTKCat)

theorem SQTKHyp.toCat {G : Type} [Group G] (h : SQTKHyp G) : SQTKHypCat G :=
  have := h.finite
  { finite := h.finite
    sqt := CFSG.SectionRank.isStronglyQuasithin_iff.mpr h.sqt
    kgroup := h.kgroup
    o2 := h.o2 }

theorem sqtkHyp_of_cat {G : Type} [Group G] (h : SQTKHypCat G) : SQTKHyp G :=
  have := h.finite
  { finite := h.finite
    sqt := CFSG.SectionRank.isStronglyQuasithin_iff.mp h.sqt
    kgroup := h.kgroup
    o2 := h.o2 }

theorem a37ForSQTK_of_cat (h : A37ForSQTKCat) : A37ForSQTK := fun Q _ hQ => h Q hQ.toCat

theorem a38ForSQTK_of_cat (h : A38ForSQTKCat) : A38ForSQTK := fun Q _ hQ => h Q hQ.toCat

theorem a39ForSQTK_of_cat (h : A39ForSQTKCat) : A39ForSQTK := fun Q _ hQ => h Q hQ.toCat

theorem a312ForSQTK_of_cat (h : A312ForSQTKCat) : A312ForSQTK := fun Q _ hQ => h Q hQ.toCat

theorem a37ForSQTKCat_of_sqtk (h : A37ForSQTK) : A37ForSQTKCat := fun Q _ hQ =>
  h Q (sqtkHyp_of_cat hQ)

theorem a38ForSQTKCat_of_sqtk (h : A38ForSQTK) : A38ForSQTKCat := fun Q _ hQ =>
  h Q (sqtkHyp_of_cat hQ)

theorem a39ForSQTKCat_of_sqtk (h : A39ForSQTK) : A39ForSQTKCat := fun Q _ hQ =>
  h Q (sqtkHyp_of_cat hQ)

theorem a312ForSQTKCat_of_sqtk (h : A312ForSQTK) : A312ForSQTKCat := fun Q _ hQ =>
  h Q (sqtkHyp_of_cat hQ)

end CFSG.Quasithin
