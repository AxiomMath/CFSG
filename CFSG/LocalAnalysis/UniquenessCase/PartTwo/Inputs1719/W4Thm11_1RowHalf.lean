module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1Row

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def W4Thm11_1RowA (s : TauCeti.SporadicName) : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      IsQuasisimple ↥L → O2Trivial L → IsSpor (↥L ⧸ Subgroup.center ↥L) s →
        E3.aParam Y ≤ tableA s

@[expose] def W4Thm11_1RowM (s : TauCeti.SporadicName) : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      IsQuasisimple ↥L → O2Trivial L → IsSpor (↥L ⧸ Subgroup.center ↥L) s →
        tableM s ≤ E3.mParam Y

theorem W4Thm11_1Row.rowM {s : TauCeti.SporadicName} (h : W4Thm11_1Row s) :
    W4Thm11_1RowM s :=
  fun W _ _ hw Y L h1 h2 h3 h4 h5 hs => (h W hw Y L h1 h2 h3 h4 h5 hs).2

theorem W4Thm11_1Row.of_rowA_rowM {s : TauCeti.SporadicName} (ha : W4Thm11_1RowA s)
    (hm : W4Thm11_1RowM s) : W4Thm11_1Row s :=
  fun W _ _ hw Y L h1 h2 h3 h4 h5 hs =>
    ⟨ha W hw Y L h1 h2 h3 h4 h5 hs, hm W hw Y L h1 h2 h3 h4 h5 hs⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
