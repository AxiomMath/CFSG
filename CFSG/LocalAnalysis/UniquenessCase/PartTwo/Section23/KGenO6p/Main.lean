module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineC2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGen.Core
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGenO6p.FixedLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGenO6p.Order
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGenO6p.Witness
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.Quasithin.EmptyFaithful.R3cBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

theorem kGenO6p_holds : KGenO6p := by
  intro W _ _ H n _ _ hn S _ _ _ hΩ p hp hp2 hdvd
  obtain ⟨-, K, hF, hFin, hK, hReal⟩ := hΩ.2
  letI : Field K := hF
  letI : Finite K := hFin
  haveI : CharP K 2 := CFSG.Quasithin.R3c.charP_two_of_natCard_eq_two_pow hK
  have hReal' : (CFSG.Quasithin.FFModel.nat
      (StatedOmega (StatedQuadPlus 3 K))).Realizes H ⊤ ⊥ := hReal
  have hline := KGenO6pProof.sylowFixedLine_omegaPlusSix K
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hdvd' : p ∣ Nat.card ↥(Hinf (KTabD.pointStab H S)) := hdvd
  obtain ⟨φ, hφ⟩ := KTabD.exists_mulEquiv_pointStab_eq_map hReal' hline S
  have hcard : Nat.card ↥(Hinf (KTabD.pointStab H S)) =
      Nat.card ↥(Hinf (KTabD.lineStab (StatedOmega (StatedQuadPlus 3 K))
        (Pi.single (Sum.inl 0) 1))) := by
    rw [hφ, ← Hinf_map φ.toMonoidHom]
    exact Subgroup.card_map_of_injective φ.injective
  have hdvd'' : p ∣ Nat.card ↥(KTabD.lineStab (StatedOmega (StatedQuadPlus 3 K))
      (Pi.single (Sum.inl 0) 1)) := by
    rw [hcard] at hdvd'
    exact hdvd'.trans (Subgroup.card_dvd_of_le (uc22p21c_Hinf_le _))
  have hpq : p ∣ Nat.card K ^ 2 - 1 :=
    KGenO6pProof.prime_dvd_sq_sub_one_of_dvd_card_lineStab hK hn hp hp2 hdvd''
  have hgen : KGenProof.GenLine p (StatedOmega (StatedQuadPlus 3 K))
      (Pi.single (Sum.inl 0) 1) := KGenO6pProof.exists_genLine_witness h4 hp hpq
  exact KGenProof.GenLine.exists_A hp hReal' hline hgen S

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
