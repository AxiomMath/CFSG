module

import CFSG.Certificates.Kernel.Misc.RankOneSq
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G6Natural
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Certificates.Certificate3172

public section

namespace Certificates

open CFSG CFSG.Quasithin in
open scoped Matrix in
theorem certificate7024 :
    ∀ M : Matrix (Fin 4) (Fin 4) (ZMod 2),
      8 ≤ (Finset.univ.filter fun v : Fin 4 → ZMod 2 => M *ᵥ v = v).card → M * M = 1 ∨ M * M = M :=
  fun M h => CFSG.KC.Misc.RankOne.sq_eq_of_rank_le_one (ZMod.card 2) M
    (CFSG.KC.Misc.RankOne.rank_le_one_of_card_fix (ZMod.card 2) M h)

end Certificates
