module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K108BT
public import CFSG.LocalAnalysis.UniquenessCase.UC22K108BTExc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

@[expose] def K108SplitBN (F : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], F S → IsSimpleGroup S →
    ∃ B N : Subgroup S, CFSG.ASVolI.ChIJK.IsSplitBNPair 2 B N ∧ B ≠ ⊤


theorem k108Rows_of_inputs (hBig : ∀ F : (S : Type) → [Group S] → Prop, K108SplitBN F → K108RowX F)
    (hL2 : K108SplitBN K108FamL2) (hSz : K108SplitBN K108FamSz) (hU3 : K108SplitBN K108FamU3)
    (hL3 : K108SplitBN K108FamL3) (hSp4 : K108SplitBN K108FamSp4) (hG2 : K108SplitBN K108FamG2)
    (h3D4 : K108SplitBN K108Fam3D4) (h2F4 : K108SplitBN K108Fam2F4) (hU4 : K108SplitBN K108FamU4)
    (hU5 : K108SplitBN K108FamU5) (hL4 : K108SplitBN K108FamL4) (hSp6 : K108SplitBN K108FamSp6)
    (hO8m : K108SplitBN K108FamO8m) (h3D4two : K108Row3D4two) : K108Rows :=
  { l2 := hBig _ hL2, sz := hBig _ hSz, u3 := hBig _ hU3, l3 := hBig _ hL3, sp4 := hBig _ hSp4,
    g2 := hBig _ hG2, d4 := hBig _ h3D4, f4 := hBig _ h2F4, u4 := hBig _ hU4, u5 := hBig _ hU5,
    l4 := hBig _ hL4, sp6 := hBig _ hSp6, o8m := hBig _ hO8m,
    bt_l2 := k108BTL2_holds, bt_sz := k108BTSz_holds, bt_u3 := k108BTU3_holds, bt_l3 := k108BTL3_holds,
    bt_sp4 := k108BTSp4_holds, bt_g2 := k108BTG2_holds, bt_d4 := k108BT3D4_holds, bt_f4 := k108BT2F4_holds,
    bt_u4 := k108BTU4_holds, bt_u5 := k108BTU5_holds, bt_l4 := k108BTL4_holds, bt_sp6 := k108BTSp6_holds,
    bt_o8m := k108BTO8m_holds, d4two := h3D4two }

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
