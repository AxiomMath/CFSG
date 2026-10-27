module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrAAuxFld
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
import CFSG.RankThree.PartOne.LSTD.ClsB
import CFSG.ClassicalInvolution.Phan.Assembly
import CFSG.ClassicalInvolution.Phan.Universal
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.RankThree.PartOne.CTP.ExtPhan
import CFSG.RankThree.PartOne.CTP.Frame1214
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
import CFSG.RankThree.PartOne.KF.R12Final
import CFSG.RankThree.PartOne.KF.R1Final
import CFSG.RankThree.PartOne.LSTD.StdFam
import CFSG.RankThree.PartOne.LSTD.Transport
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
import CFSG.Sporadic.M23.M23Group

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Assembly.LowTwoRank

theorem torSU_isSolvable {H : Type} [Group H] {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = 4) {n : ℕ} (hn : n ≤ 3) (e : H ≃* ↥(StatedSU n (2 ^ 1) E)) :
    Group.IsSolvable H := by
  have hKd : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 E :=
    ⟨Nat.prime_two, le_rfl, by rw [hE]; norm_num⟩
  haveI : Group.IsSolvable ↥(StatedSU n (2 ^ 1) E) := by
    interval_cases n
    · haveI : Subsingleton ↥(StatedSU 0 (2 ^ 1) E) := inferInstance
      infer_instance
    · have hpos : ∀ x : ↥(StatedSU 1 (2 ^ 1) E), x = 1 := by
        intro x
        refine Subtype.ext ?_
        apply Units.ext
        ext i j
        fin_cases i
        fin_cases j
        have h := CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU x.2
        rw [Matrix.det_fin_one] at h
        simpa using h
      haveI : Subsingleton ↥(StatedSU 1 (2 ^ 1) E) := ⟨fun a b => by rw [hpos a, hpos b]⟩
      infer_instance
    · refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
      have h := CFSG.RankThree.PartOne.LSTD.card_unitarySU_two (K := E) (f := 1) hKd
      have h6 : Nat.card ↥(StatedSU 2 (2 ^ 1) E) = 6 := by
        norm_num at h
        exact_mod_cast h
      rw [h6]
      decide +kernel
    · refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
      have h := CFSG.RankThree.PartOne.LSTD.card_unitarySU_three (K := E) (f := 1) hKd
      have h216 : Nat.card ↥(StatedSU 3 (2 ^ 1) E) = 216 := by
        norm_num at h
        exact_mod_cast h
      rw [h216]
      decide +kernel
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem torSU_isQuasisimple_label {H : Type} [Group H] {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = 4) {n : ℕ} (hn : 4 ≤ n) (e : H ≃* ↥(StatedSU n (2 ^ 1) E)) :
    IsQuasisimple H ∧
      ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
        GGHasLabel lab (H ⧸ Subgroup.center H) ∧ lab.n = 1 ∧ lab.tag ≠ .A ∧
          (lab.tag = .twD → lab.rank ≠ 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE4 : Nat.card E = (2 ^ 1) ^ 2 := by rw [hE]; norm_num
  have hn3 : 3 ≤ n := by omega
  have hnq : (n, 2 ^ 1) ≠ (3, 2) := by
    rintro ⟨h1, _⟩
    omega
  have hSU := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := E) (p := 2) (f := 1) (n := n) hE4 hn3 hnq
  let e₂ : (H ⧸ Subgroup.center H) ≃*
      (↥(StatedSU n (2 ^ 1) E) ⧸ Subgroup.center ↥(StatedSU n (2 ^ 1) E)) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  let e₃ : (↥(StatedSU n (2 ^ 1) E) ⧸ Subgroup.center ↥(StatedSU n (2 ^ 1) E)) ≃*
      StatedProj (StatedSU n (2 ^ 1) E) :=
    QuotientGroup.quotientMulEquivOfEq hSU.2
  have hscm : StatedClassicalModel (H ⧸ Subgroup.center H) .PSU n 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, hn3, hnq⟩, E, inferInstance, inferInstance, hE4, ⟨e₂.trans e₃⟩⟩
  have hR : CFSG.Blueprint.LieModel (H ⧸ Subgroup.center H) .PSU n 2 1 :=
    Or.inl ⟨by decide, hscm⟩
  have hΛ : LargeEvenInLambda2 (⟨.twA, n - 1, 1⟩ : LargeEvenLabel) := by
    unfold LargeEvenInLambda2
    refine ⟨le_refl 1, ?_, ?_⟩
    · change 2 ≤ n - 1
      omega
    · intro h
      change n - 1 = 2 at h
      change 2 ≤ 1
      omega
  refine ⟨CFSG.IsQuasisimple.of_mulEquiv e hSU.1,
    ⟨⟨.twA, n - 1, 1⟩, hΛ, ?_, rfl, ?_, ?_⟩⟩
  · exact qTwoNbrA_hasLabel_of_lieModel hn hR
  · intro h
    cases h
  · intro h
    cases h

end CFSG.StandardType.QTwo

end
