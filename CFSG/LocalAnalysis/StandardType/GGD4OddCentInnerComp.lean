module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Triality

namespace D4Inner

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_centDer_of_isComponentOf {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n) (hn3 : 3 ≤ n)
    {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) {J : Subgroup (Om8 K)}
    (hJ : IsComponentOf J (ggAutFixedSubgroup (MulAut.conj s))) : J = centDer s := by
  have hJC : J ≤ Subgroup.centralizer ({s} : Set (Om8 K)) :=
    (ggAutFixedSubgroup_conj_eq_centralizer s) ▸ hJ.1
  refine le_antisymm ?_ ?_
  ·
    have hperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.1 ⟨hJ.2.2.1⟩
    calc J = ⁅J, J⁆ := hperf.symm
      _ ≤ centDer s := Subgroup.commutator_mono hJC hJC
  ·
    refine (Subgroup.map_le_map_iff_of_injective (f := (omBridge (K := K)).toMonoidHom)
      omBridge.injective).1 ?_
    rw [map_eq_componentImage_phi_of_isComponentOf hK hn hs3 hd hJ]
    exact map_centDer_le_componentImage_phi hK hn hs3 hd

end D4Inner

end CFSG.StandardType

end
