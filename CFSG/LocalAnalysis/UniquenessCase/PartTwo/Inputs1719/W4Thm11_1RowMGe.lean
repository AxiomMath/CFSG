module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowHalf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def W4Thm11_1RowMGe (s : TauCeti.SporadicName) (c : ℕ) : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      IsQuasisimple ↥L → O2Trivial L → IsSpor (↥L ⧸ Subgroup.center ↥L) s →
        c ≤ E3.mParam Y

@[expose] def W4Thm11_1RowM4 (s : TauCeti.SporadicName) : Prop :=
  W4Thm11_1RowMGe s 4

theorem w4Thm11_1RowM_iff {s : TauCeti.SporadicName} :
    W4Thm11_1RowM s ↔ W4Thm11_1RowMGe s (tableM s) :=
  Iff.rfl

theorem W4Thm11_1RowMGe.mono {s : TauCeti.SporadicName} {c d : ℕ} (hcd : c ≤ d)
    (h : W4Thm11_1RowMGe s d) : W4Thm11_1RowMGe s c :=
  fun W _ _ hw Y L h1 h2 h3 h4 h5 hs => hcd.trans (h W hw Y L h1 h2 h3 h4 h5 hs)

theorem W4Thm11_1RowM.rowMGe {s : TauCeti.SporadicName} {c : ℕ} (h : W4Thm11_1RowM s)
    (hc : c ≤ tableM s) : W4Thm11_1RowMGe s c :=
  (w4Thm11_1RowM_iff.1 h).mono hc

theorem W4Thm11_1RowM.rowM4 {s : TauCeti.SporadicName} (h : W4Thm11_1RowM s)
    (hc : 4 ≤ tableM s) : W4Thm11_1RowM4 s :=
  h.rowMGe hc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
