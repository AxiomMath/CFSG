module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143K
public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143M22
public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143ON
public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143J3
public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143McL
public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143U43
public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143G23
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47f
import CFSG.RankThree.PartTwo.Sec15.Sylow155L143Alt
import CFSG.RankThree.PartTwo.Sec15.Sylow155L143L3Eig
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155L143

open CFSG CFSG.RankThree.PartTwo

private theorem rowsT_A6 (T : Type) [Group T]
    (hT : Nonempty (T ≃* alternatingGroup (Fin 6))) : L143Rows T :=
  hT.elim fun φ => L143Rows.of_mulEquiv φ l143Rows_alternating_six

private theorem rowsT_A7 (T : Type) [Group T]
    (hT : Nonempty (T ≃* alternatingGroup (Fin 7))) : L143Rows T :=
  hT.elim fun φ => L143Rows.of_mulEquiv φ l143Rows_alternating_seven

private theorem rowsT_U43
    (T : Type) [Group T] (hT : Nonempty (T ≃* CFSG.PGLModel.projSU 4 3 1)) : L143Rows T :=
  hT.elim fun φ => L143Rows.of_mulEquiv φ l143Rows_U43

private theorem rowsT_M22
    (T : Type) [Group T] (hT : Nonempty (T ≃* Blueprint.NativeSporadic.M22)) : L143Rows T :=
  hT.elim fun φ => L143Rows.of_mulEquiv φ l143Rows_M22

theorem l143RowsK_of
    (h47 : CFSG.GH74.GLS.IVK.IVK_4_7ef) : L143RowsK :=
  ⟨rowsT_A6, rowsT_A7, l143Rows_G23 h47, rowsT_U43, rowsT_M22, l143RowsT_J3, l143RowsT_McL,
    l143RowsT_ON⟩

theorem l143RowsK_holds :
    L143RowsK :=
  l143RowsK_of CFSG.GH74.GLS.IVK.Proofs2.ivk_4_7ef

theorem k143Excl_of_inputs
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3)
    (hin : Sec4.Census.CoverInputs46) : K143Excl :=
  k143Excl_of h2 h43 hin l143EigProp_holds l143RowsK_holds

end CFSG.RankThree.PartTwo.Sec15.Sylow155L143
