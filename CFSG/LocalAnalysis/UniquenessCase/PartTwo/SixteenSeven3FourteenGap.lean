module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenCorr
public import CFSG.LocalAnalysis.WeakClosure81.Eleven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Residual1614At (D : Data G) (V L : Subgroup G)
    (hV : IsElemAbelian 2 V) (U : Subgroup G) : Prop :=
  (Case168_3 D ⊥ V hV L ∧ (Nat.card ↥(Mbar D.M ⊥ V hV)).factorization 3 = 3 ∧
      Desc1614Three D V L hV U) ∨
    (Case168_11 D ⊥ V hV L ∧
      ∃ t ∈ D.M, t ^ 2 ∈ centralizer (V : Set G) ∧ t ∉ centralizer (V : Set G) ∧
        U ≤ V ⊓ centralizer ({t} : Set G) ∧
          E3.mQuot V (V ⊓ centralizer ({t} : Set G)) = 3)

@[expose] noncomputable def S16GapFourteenBlock (D : Data G) : Prop :=
  ∀ (V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D ⊥ V L hV →
    ∀ U : Subgroup G, Min1614 D V U → U ∉ gammaEleven D.M V →
      Cartan1614 D V U ∨ (E3.mQuot V U = D.k + 2 ∧ Residual1614At D V L hV U)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
