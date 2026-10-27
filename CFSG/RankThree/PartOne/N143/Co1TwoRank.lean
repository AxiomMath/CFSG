module

public import CFSG.RankThree.PartOne.KS.Co1ScalCheck
public import Certificates.Certificate14959

public noncomputable section

namespace CFSG.RankThree.PartOne.N143

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.Sporadic.GLQ
  CFSG.Blueprint
open CFSG.RankThree.PartOne.KS
open scoped Matrix

namespace Co1TwoRank

theorem co1Two_check : co1TwoCheck = true :=
  Certificates.certificate14959

theorem exists_elemAbelian :
    ∃ E : Subgroup NativeSporadic.Co1, CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ 5 := by
  have h := co1Two_check
  unfold co1TwoCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hprog, hel⟩ := h
  have hR := regsRep_runProg co1TwoProg hprog
    (regsRep_initRegs (n := 115) Co1Scal.rep_gA Co1Scal.rep_gB)
  let u : Fin 5 → NativeSporadic.Co1 := fun i =>
    runProg (initRegs Co1Scal.gA Co1Scal.gB) co1TwoProg (co1TwoOuts i)
  have hlt : ∀ i, co1TwoOuts i < 115 := by decide
  have hX : ∀ i, (spec2 24).WF (co1TwoRegs[co1TwoOuts i]!.1) ∧
      (spec2 24).toMat (co1TwoRegs[co1TwoOuts i]!.1) = valHom Co1Scal.SM (u i) := fun i =>
    ⟨(hR.2 _ (hlt i)).1, (hR.2 _ (hlt i)).2.2.1⟩
  obtain ⟨hsq, hcomm, hker⟩ := OpsSpecFacts.elem2_of_ok (spec2 24) (valHom Co1Scal.SM)
    (valHom_injective Co1Scal.SM) u _ hX hel
  obtain ⟨-, -, -, -, hE, hcard⟩ := exists_elemAbelian_two u hsq hcomm hker
  exact ⟨_, hE, hcard⟩

end Co1TwoRank

theorem co1_two_rank_at_least_five
    (K : Type*) [Group K] [Finite K] (hK : Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.Co1)) :
    (∃ E : Subgroup K, CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ 5) ∧
      5 ≤ CFSG.pRank 2 K := by
  obtain ⟨e⟩ := hK
  obtain ⟨E, hE, hcard⟩ := Co1TwoRank.exists_elemAbelian
  exact transport_elemAbelian_two E hE hcard e

end CFSG.RankThree.PartOne.N143
