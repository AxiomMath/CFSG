module

public import CFSG.Quasithin.H13.L32A58e

public section

namespace CFSG.Quasithin.H13.L32A.T53

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Contra14_5_3Solv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V V₂ Y : Subgroup G), Ctx G T L V V₂ Y →
    pCoreOf 2 (hY T L V₂ Y) ≠ ⊥ → Group.IsSolvable ↥(hY T L V₂ Y) → False

theorem contra14_5_3_of (hS : Contra14_5_3Solv) (h4 : Lemma14_7_4_two_three)
    (h55 : Lemma14_5_5Q) (h36 : A36ForSQTK) (h1434 : Lemma1434One) (hSym : Lemma14_5_8Sym) :
    Contra14_5_3 := by
  intro G _ _ T L V V₂ Y C
  exact hS G T L V V₂ Y C (lemma14_5_5_of h55 h4 G T L V V₂ Y C)
    (C.isSolvable_hY h4 h55 h36 h1434 hSym)

theorem thm14_5_3_of_solv (hS : Contra14_5_3Solv) (h4 : Lemma14_7_4_two_three)
    (h55 : Lemma14_5_5Q) (h36 : A36ForSQTK) (h1434 : Lemma1434One) (hSym : Lemma14_5_8Sym)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) : Thm14_5_3 :=
  thm14_5_3_of (contra14_5_3_of hS h4 h55 h36 h1434 hSym) h1222 h1332 h1334

end CFSG.Quasithin.H13.L32A.T53
