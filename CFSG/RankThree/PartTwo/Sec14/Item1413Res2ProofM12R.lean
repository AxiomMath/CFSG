module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Sporadic.Mathieu.M12
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

@[expose] noncomputable def Step1421M12QR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M12) →
        c' ∉ L' → Nat.card ↥(A ⊓ L') = 9 → A = Subgroup.zpowers c' ⊔ (A ⊓ L') →
        Nonempty (↥(Sec4.autIn L' A) ≃* Equiv.Perm (Fin 3)) →
          ∃ d ∈ A ⊓ L', d ≠ 1 ∧
            (∀ x ∈ A, x ∉ Subgroup.closure ({c', d} : Set G) →
              ∃ R ∈ scriptQPiStar A (lB A) L' (piOf 2),
                A ⊓ Subgroup.centralizer (R : Set G) = Subgroup.closure {c', x}) ∧
            ∀ R₁ ∈ scriptQPiStar A (lB A) L' (piOf 2), ∀ R₂ ∈ scriptQPiStar A (lB A) L' (piOf 2),
              A ⊓ Subgroup.centralizer (R₁ : Set G) = A ⊓ Subgroup.centralizer (R₂ : Set G) →
                R₁ = R₂

theorem step1421M12R_of
    (h131 : Item131) (hQ : Step1421M12QR) : Step1421M12R := by
  intro G _ _ A c L hR hfail c' hc' L' hL' hM
  obtain ⟨φ⟩ := hM
  have hS := Proof1413.sec14Std_at hR.toSec14Std hc'.1 hL'
  have hD := hS.toSec13Data
  have hM12s : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M12 :=
    CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  have hcL : c' ∉ L' := Proof1413.not_mem_of_mulEquiv_simple hD
    (by rw [KFacts.KS14.card_nativeM12]; norm_num) φ
  have hnL3 : ¬ IsLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') :=
    not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M12
  rcases cases131 h131 sporadicModels131 slTwoCenter hD with ⟨-, -, -, hcase⟩ |
      ⟨-, h9, -, hS3⟩ | ⟨-, hP, -⟩ | ⟨hcL', -⟩
  · exfalso
    rcases hcase with ⟨hL3, -⟩ | ⟨hA7, -⟩ | ⟨hM22, -⟩
    · exact hnL3 hL3
    · obtain ⟨ψ⟩ := hA7
      exact (Proof1413.isEmpty_mulEquiv_of_card_ne (by
        rw [KFacts.KS14.card_nativeM12, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
        norm_num)).false (φ.symm.trans ψ)
    · obtain ⟨ψ⟩ := hM22
      exact (Proof1413.isEmpty_mulEquiv_of_card_ne (by
        rw [KFacts.KS14.card_nativeM12, KFacts.KS14.card_nativeM22]
        norm_num)).false (φ.symm.trans ψ)
  · have hAa := eq_sup_of_card_nine hD h9 (fun h => hcL h.2)
    exact ⟨h9, hQ G A c L hR hfail c' hc' L' hL' ⟨φ⟩ hcL h9 hAa hS3⟩
  · exact absurd (Sec13.facts_of_isZ3PGLThreePi hD hP).1 hnL3
  · exact absurd hcL' hcL

end CFSG.RankThree.PartTwo.Sec14
