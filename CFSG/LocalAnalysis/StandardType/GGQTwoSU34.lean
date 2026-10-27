module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNativeGen
import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
import CFSG.LocalAnalysis.StandardType.GGQTwoSU34Aux6
import CFSG.LocalAnalysis.StandardType.GGQTwoSU34Aux7

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem coordBlockSU_sup_three (hK : Nat.card K = 4) {N : ℕ} {A B : Finset (Fin N)}
    (hA : A.card = 3) (hB : B.card = 3) (hAB : (A ∪ B).card = 4) :
    coordBlockSU K 2 1 A ⊔ coordBlockSU K 2 1 B = coordBlockSU K 2 1 (A ∪ B) := by
  exact qTwoS34_sup_eq hK hA hB hAB

theorem isSolvable_coordBlockSU_of_card_le_three (hK : Nat.card K = 4) {N : ℕ} {J : Finset (Fin N)}
    (hJ : J.card ≤ 3) : IsSolvable ↥(coordBlockSU K 2 1 J) := by
  have h4 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, le_refl 1, by rw [h4]; norm_num⟩
  set k := J.card with hk
  have hk3 : k ≤ 3 := by omega
  have he : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K k) ≃*
      ↥(coordBlockSU K 2 1 J) :=
    (MulEquiv.subgroupCongr
        (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (F := K) (p := 2) (f := 1) h4 k)).symm.trans
      (MonoidHom.ofInjective (blockSUOn_injective (K := K) (p := 2) (f := 1) J))
  interval_cases k
  · exact Group.isSolvable_of_surjective (f := he.toMonoidHom) he.surjective
  · haveI : Group.IsSolvable ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 1) :=
      CFSG.StandardType.WitSU.isSolvable_unitarySU_two_one hUF (by norm_num) (by norm_num)
    exact Group.isSolvable_of_surjective (f := he.toMonoidHom) he.surjective
  · haveI : Group.IsSolvable ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 2) :=
      CFSG.StandardType.WitSU.isSolvable_unitarySU_two_one hUF (by norm_num) (by norm_num)
    exact Group.isSolvable_of_surjective (f := he.toMonoidHom) he.surjective
  · haveI : Group.IsSolvable ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 3) :=
      CFSG.StandardType.WitSU.isSolvable_unitarySU_two_one hUF (by norm_num) (by norm_num)
    exact Group.isSolvable_of_surjective (f := he.toMonoidHom) he.surjective

end CFSG.StandardType.QTwo

end
