module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisAutClass

public section

namespace CFSG.RankThree.PartOne

namespace KCRootAxis

open CFSG.ComponentClassification.OuterAutomorphisms

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem autNormalizerFacts_axis {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (i : Axis) :
    AutNormalizerFacts n (rootU K i) (rootA K i) (sHom K i) (dHom K i) (rootCoord K i)
      (frobAut K) :=
  AutNormalizerFacts.of_structure (by omega) hK
    (even_symplectic_four_root_axis_centralizer_structure hK hn i) (rootCoord_injective i)
    (frobAut_rootCoord i) (frobAut_sHom i)
    (fun α hα => exists_conj_mul_frobAut_pow hn hK i α hα)
    (fun _ _ _ _ hk hk' h => conj_mul_frobAut_pow_inj (by omega) hK hk hk' h)

end KCRootAxis

end CFSG.RankThree.PartOne
