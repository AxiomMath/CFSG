module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.CoverLift
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.RankOne
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieSylowUnitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryUnipotentCentralizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive

open CFSG.AGLEmbedding

theorem coverActsTriviallyOnSmall_unitary {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {d : TauCeti.ValidLieTypeIndex} (hd : CFSG.AGLEmbedding.IsUnitaryIndex p d) {L : Type}
    [Group L] [Finite L] (e : L ≃* CFSG.AGLEmbedding.CatGroup d) :
    CoverActsTriviallyOnSmall p L := by
  classical
  have hp2 : p ≠ 2 := by omega
  haveI : IsSimpleGroup L := by
    obtain ⟨-, -, hq, K, _, _, J, hJ, hK, hfix, ⟨eP⟩⟩ :=
      CFSG.AGLEmbedding.UnitaryModel.exists_equiv_psu
        (CFSG.AGLEmbedding.UnitaryModel.statedClassicalModel hd ⟨e⟩)
    have hsimple := CFSG.UnitaryThreeRecognition.Model.isSimpleGroup_psu J
      (p ^ d.1.fieldExponent) hK hfix hq
    haveI := hsimple
    exact eP.isSimpleGroup
  obtain ⟨U⟩ := Sylow.nonempty (p := p) (G := L)
  obtain ⟨hcard, hcomm, -, -⟩ :=
    CFSG.AGLEmbedding.kFactUnitarySylowStructure L p d hp2 hd ⟨e⟩ U
  have hnc : ∃ a ∈ (U : Subgroup L), ∃ b ∈ (U : Subgroup L), a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hle : (U : Subgroup L) ≤ Subgroup.centralizer ((U : Subgroup L) : Set L) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (h x hx y hy).symm
    have hU : (U : Subgroup L) = ⊥ := by
      rw [← inf_eq_left.mpr hle, ← hcomm,
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle]
    have hcard1 : Nat.card (U : Subgroup L) = 1 := by rw [hU, Subgroup.card_bot]
    have hf1 : 1 ≤ d.1.fieldExponent := by
      obtain ⟨q, -, -, hfe, hq1⟩ := hd.exists_eq
      omega
    have hgt : 1 < Nat.card (U : Subgroup L) := by
      rw [hcard]
      exact one_lt_pow₀ (by omega) (by omega)
    omega
  exact coverActsTriviallyOnSmall_of_nonabelian Fact.out hp5 U.isPGroup' hnc

theorem good_unitary {p : ℕ} [Fact p.Prime] {d : TauCeti.ValidLieTypeIndex}
    (hd : CFSG.AGLEmbedding.IsUnitaryIndex p d) {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.CatGroup d) : Good p N := by
  classical
  refine good_of_rankOne hO hN ?_ ?_ ?_
  · intro T
    exact CFSG.AGLEmbedding.kFactUnitaryBorelMaximal _ p d hd ⟨e⟩ T
  · intro T
    obtain ⟨hT, hSyl⟩ :=
      CFSG.AGLEmbedding.KFactProofs.OneLieSylow.card_sylow_unitary hd ⟨e⟩ T
    rw [hSyl, hT]
  · intro T α hα
    exact CFSG.AGLEmbedding.kFactUnitaryUnipotentCentralizer _ p d hd ⟨e⟩ T α hα

theorem pElements_unitary {p : ℕ} [Fact p.Prime] {d : TauCeti.ValidLieTypeIndex}
    (hd : CFSG.AGLEmbedding.IsUnitaryIndex p d) {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.CatGroup d) :
    (∀ x y : X, x ∈ N → y ∈ N → x ≠ 1 → IsPGroup p (Subgroup.zpowers x) →
      (orderOf y).Prime → orderOf y ≠ p → x * y = y * x →
      ∃ c ∈ CFSG.generalizedFitting X, c * y = y * c ∧ IsPGroup p (Subgroup.zpowers c) ∧
        c ∉ N) ∧
    ∀ z : X, z ∈ N → IsPGroup p (Subgroup.zpowers z) → z ∈ CFSG.generalizedFitting X := by
  classical
  refine pElements_of_rankOne hO hN ?_ ?_
  · intro T
    exact CFSG.AGLEmbedding.kFactUnitaryBorelMaximal _ p d hd ⟨e⟩ T
  · intro T
    obtain ⟨hT, hSyl⟩ :=
      CFSG.AGLEmbedding.KFactProofs.OneLieSylow.card_sylow_unitary hd ⟨e⟩ T
    rw [hSyl, hT]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
