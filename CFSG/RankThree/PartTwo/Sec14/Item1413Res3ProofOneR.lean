module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofOne
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofInv
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3Proof1419
import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofM12Q
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.Sporadic.Mathieu.M12
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open CFSG.GH74.M12.Hyp (G12)

namespace Proof1413Res3

variable {G : Type} [Group G] [Finite G]

theorem m12_point_facts
    (h131 : Item131) {A L : Subgroup G} {c : G}
    (hD : Sec13Data G A c L)
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) :
    c ∉ L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L) ∧
      Nonempty (↥(Sec4.autIn L A) ≃* Equiv.Perm (Fin 3)) := by
  have hcL : c ∉ L := not_mem_of_type hD (Or.inr (Or.inr (Or.inl ⟨φ⟩)))
  have hnL3 : ¬ IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
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
  · exact ⟨hcL, h9, eq_sup_of_card_nine hD h9 (fun h => hcL h.2), hS3⟩
  · exact absurd (Sec13.facts_of_isZ3PGLThreePi hD hP).1 hnL3
  · exact absurd hcL' hcL

end Proof1413Res3

open Proof1413Res3

end CFSG.RankThree.PartTwo.Sec14
