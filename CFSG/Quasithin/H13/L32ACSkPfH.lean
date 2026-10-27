module

public import CFSG.Quasithin.H13.L32ACSkPfC
public import CFSG.Quasithin.H13.L32ACSkPfG2
public import CFSG.Quasithin.H13.L32ACSkPfL3
public import CFSG.Quasithin.H13.L32ACSkPfSz
public import CFSG.Quasithin.H13.L32ACSkPfF4
public import CFSG.Quasithin.H13.L32ACSkPfD4
public import CFSG.Quasithin.H13.L32ACSkPfSp4
public import CFSG.Quasithin.H13.L32ACSkPfU3
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee

public section

namespace CFSG.Quasithin.H13.L32A.C.SkPf

open CFSG.Quasithin

theorem n2Model_n4Model_of_isLieChar2
    {M : Type} [Group M]
    {n : ℕ} (hn : 1 < n) (h : A315.IsLieChar2 n M) : N2Model M ∧ N4Model M := by
  rcases h with h | h | h | h | h | h | h | h
  · exact n2Model_n4Model_of_isPSL2 hn h
  · exact n2Model_n4Model_of_isPSL3 hn h
  · exact n2Model_n4Model_of_isPSU3 hn h
  · exact n2Model_n4Model_of_isPSp4 hn h
  · exact n2Model_n4Model_of_isG2 hn h
  · exact n2Model_n4Model_of_is3D4 hn.le h
  · exact n2Model_n4Model_of_isSz h
  · exact n2Model_n4Model_of_is2F4 h

theorem lieBorelInvert3_holds :
    LieBorelInvert3 :=
  lieBorelInvert3_of fun _ _ _ _ hn _ hL => n2Model_n4Model_of_isLieChar2 hn hL

end CFSG.Quasithin.H13.L32A.C.SkPf
