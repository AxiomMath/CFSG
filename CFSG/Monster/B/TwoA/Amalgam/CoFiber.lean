
module

public import CFSG.Monster.B.TwoA.Amalgam.CoFiberBase

public import CFSG.Monster.B.TwoA.Amalgam.CosetGraph
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Co2 (v0 wAct_mul)

theorem Eam_inf_Jhat_le :
    Eam ⊓ Jhat ≤ P1 := fun _ hx => ⟨hx.2, Eam_le_centralizer hx.1⟩

theorem piPt_eq_of
    {k k' : Jhat} (h : cvOf (jhatS k) = cvOf (jhatS k')) : piPt k = piPt k' := by
  rw [cvOf_eq_iff] at h
  have hP : (k' * k⁻¹ : Jhat).1 ∈ P1 := Eam_inf_Jhat_le ⟨h, (k' * k⁻¹).2⟩
  have hU : jhatToKv0 (k' * k⁻¹) ∈ Unitary.Usig := by
    rw [← map_P1]
    exact ⟨k' * k⁻¹, hP, rfl⟩
  apply Subtype.ext
  show wAct v0 (jhatToKv0 k) Unitary.sigmaW = wAct v0 (jhatToKv0 k') Unitary.sigmaW
  have e : k' = (k' * k⁻¹) * k := by group
  conv_rhs => rw [e, map_mul, wAct_mul, Module.End.mul_apply, Unitary.mem_Usig.1 hU]

theorem cpsi_cvOf
    (k : Jhat) : cpsi ⟨cvOf (jhatS k), jhatS_mem_cPi0 k⟩ = piPt k := by
  apply piPt_eq_of
  have h := (jhatS_mem_cPi0 k).choose_spec.2
  rw [mul_one] at h
  exact h.symm

@[expose] def cgraphPi :
    SimpleGraph cPi0 := cgraph.induce cPi0

theorem native_Co2_coset_fiber_data :
    (∀ s : Shat, cPi s = {v | ∃ k : Shat, (k : Dfull) ∈ Jhat ∧ v = cvOf (k * s)}) ∧
    Function.Surjective jhatToKv0 ∧ jhatToKv0.ker = Ehat.subgroupOf Jhat ∧
    psiW cE = Unitary.sigmaW ∧
    Unitary.OmegaW = wOrbit Unitary.sigmaW ∧ Unitary.OmegaW.ncard = 2300 ∧
    (∀ k : Jhat, (cpsi ⟨cvOf (jhatS k), jhatS_mem_cPi0 k⟩ : Wv v0) =
      wAct v0 (jhatToKv0 k) Unitary.sigmaW) ∧
    (∀ v w : cPi0, cgraphPi.Adj v w ↔ cgraph.Adj v.1 w.1) :=
  ⟨fun _ => rfl, jhatToKv0_surjective, ker_jhatToKv0, psiW_cE, rfl, Unitary.ncard_OmegaW,
    fun k => congrArg Subtype.val (cpsi_cvOf k), fun _ _ => Iff.rfl⟩

end CFSG.Monster.B.TwoA.Amalgam
