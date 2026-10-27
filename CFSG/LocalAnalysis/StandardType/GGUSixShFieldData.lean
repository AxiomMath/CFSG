module

public import CFSG.LocalAnalysis.StandardType.GGTorusFieldTransferSh
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGMain
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGFieldCase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniGeom
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUUnitary
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrKGFieldShInputs
public import CFSG.LocalAnalysis.StandardType.GGUSixShKGCover

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggUSixSh_labelAll_twA {lab : LargeEvenLabel} (htag : lab.tag = .twA) {d : ℕ}
    (hd : lab.rank + 1 = d) {P : LargeEvenRawCont}
    (hP : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ lab.n) ^ 2 →
      P (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ lab.n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ lab.n)))
          (LargeEvenGUSet (Fin d) K (2 ^ lab.n)))
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ lab.n))))) :
    LargeEvenLabelAll lab P := by
  obtain ⟨t, l, n⟩ := lab
  cases htag
  subst d
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hQ', hP K hK⟩

section USixSh

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD
open CFSG.LocalAnalysis.GLTheoremA.FQ (fixF)
open CFSG.LocalAnalysis.GLTheoremA.T156.Uni (Induced subfieldHom subfieldEquiv)

section Certificates

theorem ggUSixSh_fixDataSh_field
    {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n))))
    (hord : orderOf f = 3) :
    GGFixDataSh 3 3 (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenGUSet (Fin 6) K (2 ^ n))) f := by
  have hKd : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK hn
  haveI : CharP K 2 := hKd.charP
  obtain ⟨σ, hσf⟩ := CFSG.LocalAnalysis.GLTheoremA.T156.Uni.exists_induced hf
  have hσord : orderOf σ = 3 :=
    (CFSG.LocalAnalysis.GLTheoremA.T156.Uni.orderOf_eq_of_induced (by norm_num) hn hK hσf).trans
      hord
  have hσ : Odd (orderOf σ) := by rw [hσord]; decide
  obtain ⟨hjr, hm, hk⟩ := CFSG.LocalAnalysis.GLTheoremA.T156.Uni.fixF_data hn hK σ hσ
  have hdq : ((6 : ℕ), 2 ^ (n / orderOf σ)) ≠ (3, 2) := by simp
  have hkd : UnitaryFieldData 2 (n / orderOf σ) (fixF σ) :=
    TableBU.unitaryFieldData_of_card hk hm
  have h3n : 3 ∣ n := by
    rw [hσord] at hjr
    exact ⟨n / 3, by rw [mul_comm]; exact hjr⟩
  have hmul : n = 3 * (n / 3) := (Nat.mul_div_cancel' h3n).symm
  have hpq₀ : 3 ∣ 2 ^ (n / orderOf σ) + 1 := by
    rw [hσord]
    exact CFSG.RankThree.PartOne.dvd_two_pow_add_one_of_mul Nat.prime_three (hmul ▸ hpq)
  obtain ⟨hs, hna⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T156.Uni.simple_noncomm_proj (d := 6) hk (by norm_num) hdq
  refine ⟨LargeEvenProj (LargeEvenSUGroup (Fin 6) (fixF σ) (2 ^ (n / orderOf σ))), inferInstance,
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) (fixF σ)
      (2 ^ (n / orderOf σ)))) (LargeEvenGUSet (Fin 6) (fixF σ) (2 ^ (n / orderOf σ))),
    ggUSixShSet hkd, (subfieldEquiv (by norm_num : (3 : ℕ) ≤ 6) hn hK hσ hdq hσf).symm, hs, hna,
    CFSG.LocalAnalysis.GLTheoremA.T156.Uni.ggFixGeom_unitary (by norm_num) hn hK hσ hdq hσf,
    ?_, ggUSixSh_torusNoLineSh_unitSix hk hm hpq₀ 3,
    ggUSixSh_fixNotCycOn hn hK hpq hσ hdq hσf hkd⟩
  have := ggTorusLift_unitary (K := fixF σ) (d := 6) hk hm (by norm_num) hdq Nat.prime_three hpq₀
  simpa [ggUnitaryTorusRank] using this

theorem ggUSixSh_rawFieldFixSh
    {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1) :
    GGRawFieldFixSh 3 3 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))) := by
  intro _ _ f hf hord
  exact ggUSixSh_fixDataSh_field hK hn hpq hf hord

theorem ggUnitSixFieldShInput_holds :
    GGUnitSixFieldShInput := by
  intro lab hlab htag hrank hpq _
  have hn : 1 ≤ lab.n := hlab.1
  refine ggUSixSh_labelAll_twA htag (d := 6) (by omega) fun K _ _ hK => ?_
  intro hs hna
  have hKd : UnitaryFieldData 2 lab.n K := TableBU.unitaryFieldData_of_card hK hn
  have hd : 3 ≤ 6 := by norm_num
  have hq : ¬ (6 = 3 ∧ 2 ^ lab.n = 2) := fun h => absurd h.1 (by norm_num)
  exact ggRawFieldFixSh_all
    (RecipeFieldSpU.ggRawFieldConj_unitary hKd hK hd hq Nat.prime_three (by norm_num))
    (ggRawFieldNorm_of_central (RecipeFieldSU.ggRawFieldCentral_unitary hKd hK hd hq)
      (RecipeFieldSU.ggRawInnField_unitary hKd hK hd hq (p := 3) (by norm_num)) hs hna)
    (ggRawFieldCycW_of_pCyclic (RecipeFieldSU.ggRawPCyclic_unitary hKd hK hd hq))
    (ggUSixSh_rawFieldFixSh hK hn hpq) hs hna

end Certificates

end USixSh

end CFSG.StandardType
