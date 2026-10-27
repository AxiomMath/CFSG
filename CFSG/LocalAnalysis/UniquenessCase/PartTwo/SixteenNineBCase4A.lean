module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4Fam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4Ker

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16n9b_case4_core {T : Type} [CommGroup T] [Finite T] (hT : ∀ t : T, t ^ 2 = 1)
    {X A : Subgroup (MulAut T)} {p r k : ℕ} (hp : p = 3 ∨ p = 7) (hr : 1 < r)
    (hA : IsElemAbelianOfRank p r ↥A) (hAP : A ≤ pCoreOf p X)
    (hS : SymSumOfConj X (⊤ : Subgroup T) r (dParam p))
    (hge : 3 ≤ CFSG.Open.pRank p X) (hk : k < dParam p) :
    s16n9bGood X p k (k + 2) := by
  obtain ⟨ι, hι, Y, hind, hinj, hsup, hcard, hrk, hperm, hsurj⟩ := s16n9b_case4_data hS
  obtain ⟨F, hFX, hF, hFn, hFY, hQ⟩ :=
    s16n9b_case4_kernel hT hp hr hA hAP hge hind hinj hsup hcard hrk hperm hsurj
  exact s16n9b_case4_fam hT hp hk hind hinj hsup hrk hperm hFX hF hFn hFY hQ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
