module

public import CFSG.LocalAnalysis.WeakClosure81.W16LRootBase
public import CFSG.LocalAnalysis.WeakClosure81.W16LKPair

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75
open Subgroup

variable {P : Type} [Group P] [Finite P] {n : ℕ}

section Certified


theorem IsPSUGp.isL2Pair_sylowCenter_sup (hP : IsPSUGp P 3 n) {Q Q' : Sylow 2 P}
    (hne : Q ≠ Q') :
    IsL2Pair ↥(sylowCenter Q ⊔ sylowCenter Q')
      ((sylowCenter Q).subgroupOf (sylowCenter Q ⊔ sylowCenter Q')) (2 ^ n) :=
  hP.isU3Shape.isL2Pair_sylowCenter_sup hne

theorem IsPSUGp.isL2Gp_sylowCenter_sup (hP : IsPSUGp P 3 n) {Q Q' : Sylow 2 P}
    (hne : Q ≠ Q') : IsL2Gp ↥(sylowCenter Q ⊔ sylowCenter Q') n := by
  obtain ⟨F, hF, hfin, -, e, hq, -⟩ := hP.isL2Pair_sylowCenter_sup hne
  exact ⟨F, hF, hfin, hq, ⟨e⟩⟩

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
