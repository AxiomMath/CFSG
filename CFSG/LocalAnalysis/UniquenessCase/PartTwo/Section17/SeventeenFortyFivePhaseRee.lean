module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseBasic
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35cRee
public import CFSG.RankThree.Chevalley.SteinbergCFSmallReeComponentCores
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeAut
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15O1219Sigma

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

open scoped Pointwise commutatorElement

section Ree


theorem phase45_false_of_reeG2 {X : Type} [Group X] [Finite X] {L A₁ A₂ B : Subgroup X}
    (hLn : L.Normal) (hCL : centralizer (L : Set X) = ⊥) {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ m, d.1 = .reeG2 m) (e : ↥L ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hA1 : Nat.card A₁ = 31) (hA2 : Nat.card A₂ = 31) (hA12 : A₁ ⊓ A₂ = ⊥)
    (hA12c : A₁ ≤ centralizer (A₂ : Set X)) (hcomm : ⁅A₁ ⊔ A₂, B⁆ = A₁ ⊔ A₂) : False := by
  obtain ⟨d1, hv⟩ := d
  obtain ⟨m, hm⟩ := hd
  subst hm
  have hiso : CFSG.RankThree.PartOne.Census3.IsoLie ↥L (.reeG2 m) :=
    ⟨hv, ⟨e⟩⟩
  have hmodel : CFSG.Blueprint.ReeTitsModel ↥L .twistedG2 3 (2 * m + 1) :=
    CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m hiso
  obtain ⟨a, K, hKfield, hKfin, hKchar, ha, hKcard, ⟨eL⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_reeGamma_G2_of_reeTitsModel hmodel
  letI : Field K := hKfield
  letI : Finite K := hKfin
  letI : CharP K CFSG.LieType.Ree.ReeTag.G2.prime := hKchar
  haveI houtcyc : IsCyclic (Outer ↥L) :=
    CFSG.AGLEmbedding.ReeModel.isCyclic_outer_of_equiv ha hKcard eL
  have hout : CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuter.IsPByAbelian 3 (Outer ↥L) := by
    haveI : IsMulCommutative (Outer ↥L) := IsCyclic.isMulCommutative
    exact CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuter.IsPByAbelian.of_commutative
      fun x y => IsMulCommutative.is_comm.comm x y
  have hAL : A₁ ⊔ A₂ ≤ L :=
    phase45_sup_le_of_isPByAbelian_outer hLn hCL hA1 hA2 hA12c hcomm hout
  have hne : A₁ ≠ A₂ := by
    intro h
    have hbot : A₁ = ⊥ := by rw [← hA12, ← h, inf_idem]
    have hcard : Nat.card A₁ = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hAc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := by
    intro a ha b hb
    exact ((Subgroup.mem_centralizer_iff.mp (hA12c ha)) b hb).symm
  have hE : IsElemAbelian 31 (A₁ ⊔ A₂) :=
    (CFSG.LocalAnalysis.RankThreeUC.S15.O1219SigmaProof.card_sup_eq_sq
      (p := 31) (by norm_num) hA1 hA2 hne hAc).1
  have hF : IsElemAbelian 31 ((A₁ ⊔ A₂).subgroupOf L) := hE.subgroupOf L
  have hLmodel : CFSG.Blueprint.LieModel ↥L .twistedG2 0 3 (2 * m + 1) :=
    Or.inr (Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.reeTitsTags], hmodel⟩))
  have hlt := CFSG.LocalAnalysis.UniquenessCase.UCK.card_lt_sq_of_lieModel_twistedG2
    (L := ↥L) hLmodel (p := 31) (by norm_num) (by norm_num) hF
  have hcard : Nat.card ((A₁ ⊔ A₂).subgroupOf L) = 31 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv]
    exact (phase45_card_sup hA1 hA2 hA12 hA12c).1
  rw [hcard] at hlt
  exact absurd hlt (lt_irrefl (31 ^ 2))

end Ree

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
