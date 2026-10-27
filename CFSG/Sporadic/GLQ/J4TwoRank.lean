module

public import CFSG.Sporadic.GLQ.RegisterProgram
public meta import CFSG.Sporadic.GLQ.RegisterProgram
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public meta import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Action
import CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.GLQ.J4TwoRankInputs
public import Certificates.Certificate2082
public import Certificates.Certificate8023

public noncomputable section

namespace CFSG.Sporadic.GLQ

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.Blueprint
open scoped Matrix

namespace J4TwoRank

theorem j4_check : j4Check = true :=
  Certificates.certificate2082

theorem rep_a : Rep (spec2 112) J4Order.ν J4Order.a
    ((ops2 112).decode NativeSporadic.J4Seed1, (ops2 112).decode NativeSporadic.J4Seed1) :=
  ⟨trivial, trivial, by rw [(spec2 112).toMat_decode, J4Order.ν_a],
    by rw [(spec2 112).toMat_decode, J4Order.ν_a_inv]⟩

theorem rep_b : Rep (spec2 112) J4Order.ν J4Order.b
    ((ops2 112).decode NativeSporadic.J4Seed2,
      (ops2 112).pow ((ops2 112).decode NativeSporadic.J4Seed2) 3) :=
  ⟨trivial, trivial, by rw [(spec2 112).toMat_decode, J4Order.ν_b],
    by rw [((spec2 112).pow_spec trivial 3).2, (spec2 112).toMat_decode, J4Order.ν_b_inv]⟩

theorem exists_elemAbelian :
    ∃ E : Subgroup NativeSporadic.J4, CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ 11 := by
  have h := j4_check
  unfold j4Check at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hprog, hel⟩ := h
  have hR := regsRep_runProg j4Prog hprog (regsRep_initRegs (n := 50) rep_a rep_b)
  let u : Fin 11 → NativeSporadic.J4 := fun i =>
    runProg (initRegs J4Order.a J4Order.b) j4Prog (j4Outs i)
  have hlt : ∀ i, j4Outs i < 50 := by decide
  have hX : ∀ i, (spec2 112).WF (j4Regs[j4Outs i]!.1) ∧
      (spec2 112).toMat (j4Regs[j4Outs i]!.1) = J4Order.ν (u i) := fun i =>
    ⟨(hR.2 _ (hlt i)).1, (hR.2 _ (hlt i)).2.2.1⟩
  obtain ⟨hsq, hcomm, hker⟩ :=
    OpsSpecFacts.elem2_of_ok (spec2 112) J4Order.ν J4Order.ν_injective u _ hX hel
  obtain ⟨-, -, -, -, hE, hcard⟩ := exists_elemAbelian_two u hsq hcomm hker
  exact ⟨_, hE, hcard⟩

end J4TwoRank

theorem j4_two_rank_at_least_eleven (K : Type*) [Group K] [Finite K]
    (hK : Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.J4)) :
    (∃ E : Subgroup K, CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ 11) ∧
      11 ≤ CFSG.pRank 2 K := by
  obtain ⟨e⟩ := hK
  obtain ⟨E, hE, hcard⟩ := J4TwoRank.exists_elemAbelian
  exact transport_elemAbelian_two E hE hcard e

end CFSG.Sporadic.GLQ
