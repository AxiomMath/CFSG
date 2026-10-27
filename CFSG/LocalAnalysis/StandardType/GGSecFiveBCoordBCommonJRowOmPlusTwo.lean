module

import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmPlusTwoAux1
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmPlusTwoAux2
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmPlusTwoAux3
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmPlusTwoAux4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJNativeConj
import CFSG.LieType.BorelTits.Classical

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.GGQ2Frame

private theorem ggCommonJOmPlusTwo_hcomp {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {m : ℕ} (hm : 4 ≤ m) (hme : Even m)
    (f : Fin m → Multiplicative (ZMod 3))
    (J : Subgroup ↥(GGQ2Frame.OrthBlocks.omegaQ (K := K) m 1))
    (hJ : IsComponentOf J (Subgroup.centralizer
      ({(CommonJOmPlusTwo.ggCommonJOmPlusTwo_tau hK m f)} :
        Set ↥(GGQ2Frame.OrthBlocks.omegaQ (K := K) m 1))))
    (hcard : Nat.card ↥((CommonJOmPlusTwo.ggCommonJOmPlusTwo_tau hK m).range ⊓
      Subgroup.centralizer (J : Set ↥(GGQ2Frame.OrthBlocks.omegaQ (K := K) m 1))) = 3) :
    (GGCoordDense f ∧ ∃ lab : LargeEvenLabel, lab = ⟨.twA, m - 1, 1⟩ ∧
        LargeEvenInLambda2 lab ∧
        GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) ∧
        (lab = ⟨.twA, 3, 1⟩ → Subgroup.center ↥J = ⊥)) ∨
      (GGCoordSparse f ∧ ∃ lab : LargeEvenLabel, lab = ⟨.twD, m, 1⟩ ∧
        LargeEvenInLambda2 lab ∧
        GGHasLabel lab (↥J ⧸ Subgroup.center ↥J)) := by
  classical
  obtain ⟨c, hc, hocc, rfl⟩ := CommonJOmPlusTwo.ggCommonJOmPlusTwo_components hK f hJ
  obtain ⟨-, hpos⟩ := CommonJOmPlusTwo.ggCommonJOmPlusTwo_position hK f c hc hocc
  rcases hpos hcard with ⟨e, rfl, hsupp, hdense⟩ | ⟨S, rfl, hsupp, hsparse⟩
  · have hlab := CommonJOmPlusTwo.ggCommonJOmPlusTwo_label hK (.extension e) hc
    have hlabel : PlaneRaw.label (.orthogonal 1) (.extension e) = ⟨.twA, m - 1, 1⟩ := by
      simp [PlaneRaw.label, hsupp]
    refine Or.inl ⟨hdense, ⟨⟨.twA, m - 1, 1⟩, rfl, ?_, ?_, ?_⟩⟩
    · rw [← hlabel]; exact hlab.1
    · rw [← hlabel]; exact hlab.2.1
    · intro h3
      exact hlab.2.2 (by rw [hlabel]; exact h3)
  · have hlab := CommonJOmPlusTwo.ggCommonJOmPlusTwo_label hK (.zero S) hc
    have hodd : ¬ Even S.card := by
      rw [hsupp]
      obtain ⟨k, hk⟩ := hme
      rintro ⟨j, hj⟩
      omega
    have hm1 : 1 ≤ m := by omega
    have hlabel : PlaneRaw.label (.orthogonal 1) (.zero S) = ⟨.twD, m, 1⟩ := by
      rw [show PlaneRaw.label (.orthogonal 1) (.zero S) =
          (if Even S.card then (⟨.D, S.card + 1, 1⟩ : LargeEvenLabel)
            else ⟨.twD, S.card + 1, 1⟩) from rfl]
      rw [if_neg hodd, hsupp, Nat.sub_add_cancel hm1]
    refine Or.inr ⟨hsparse, ⟨⟨.twD, m, 1⟩, rfl, ?_, ?_⟩⟩
    · rw [← hlabel]; exact hlab.1
    · rw [← hlabel]; exact hlab.2.1

theorem ggSecFiveBNativeRow_omPlusTwo {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2)
    (hm : 4 ≤ m) (hme : Even m) :
    GGSecFiveBNativeRow (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K (m + 1)))) 3 m
      (fun lab => lab = ⟨.twA, m - 1, 1⟩) (fun lab => lab = ⟨.twD, m, 1⟩) := by
  classical
  haveI : CharP K 2 :=
    CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := 1) (by simpa using hK)
  obtain ⟨α⟩ := CommonJOmPlusTwo.ggCommonJOmPlusTwo_equiv (K := K) hK hme
  refine GGSecFiveBNativeRow.of_mulEquiv α ?_
  refine GGSecFiveBNativeRow.of_std
    (T₀ := (CommonJOmPlusTwo.ggCommonJOmPlusTwo_tau hK m).range) ?_ ?_
  · refine GGSecFiveBNativeAt.of_torus (CommonJOmPlusTwo.ggCommonJOmPlusTwo_tau hK m) ?_ ?_ ?_
    · exact CommonJOmPlusTwo.ggCommonJOmPlusTwo_tau_injective hK m
    · exact CommonJOmPlusTwo.ggCommonJOmPlusTwo_signed hK m
    · exact ggCommonJOmPlusTwo_hcomp hK hm hme
  · intro T hT hcard
    exact CommonJOmPlusTwo.ggCommonJOmPlusTwo_conj hK hm hme T hT hcard

theorem ggSecFiveBNativeSparseRow_omPlusTwo {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    GGSecFiveBNativeSparseRow (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 5))) 3 4 := by
  classical
  haveI : CharP K 2 :=
    CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := 1) (by simpa using hK)
  obtain ⟨α⟩ := CommonJOmPlusTwo.ggCommonJOmPlusTwo_equiv (K := K) hK (m := 4) (by norm_num)
  refine GGSecFiveBNativeSparseRow.of_mulEquiv α ?_
  refine GGSecFiveBNativeSparseRow.of_std
    (T₀ := (CommonJOmPlusTwo.ggCommonJOmPlusTwo_tau hK 4).range) ?_ ?_
  · refine GGSecFiveBNativeSparseAt.of_torus (CommonJOmPlusTwo.ggCommonJOmPlusTwo_tau hK 4) ?_ ?_ ?_
    · exact CommonJOmPlusTwo.ggCommonJOmPlusTwo_tau_injective hK 4
    · exact CommonJOmPlusTwo.ggCommonJOmPlusTwo_signed hK 4
    · exact CommonJOmPlusTwo.ggCommonJOmPlusTwo_sparse hK
  · intro T hT hcard
    exact CommonJOmPlusTwo.ggCommonJOmPlusTwo_conj hK (by norm_num) (by norm_num) T hT hcard

end CFSG.StandardType

end
