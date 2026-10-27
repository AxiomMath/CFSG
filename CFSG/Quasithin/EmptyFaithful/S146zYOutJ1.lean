module

public import CFSG.Quasithin.EmptyFaithful.S146zYOutComm
public import CFSG.Walter.J1Props.Aut
public import CFSG.Walter.Models

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem forall_inner_of_carrierJ1 {K : Type} [Group K]
    (e : K ≃* NativeSporadic.Carrier .J1) (φ : MulAut K) : ∃ g : K, φ = MulAut.conj g := by
  let ε : K ≃* CFSG.Open.walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
  obtain ⟨g, hg⟩ := CFSG.Walter.J1Props.J3_aut (ε.symm.trans (φ.trans ε))
  refine ⟨ε.symm g, ?_⟩
  apply MulEquiv.ext
  intro x
  apply ε.injective
  have h1 := congrArg (fun f : MulAut CFSG.Open.walterJ1 => f (ε x)) hg
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
  rw [h1]
  simp

theorem outer_comm_of_carrierJ1 {K : Type} [Group K]
    (e : K ≃* NativeSporadic.Carrier .J1) : ∀ x y : Outer K, x * y = y * x :=
  outer_comm_of_forall_inner (forall_inner_of_carrierJ1 e)

end CFSG.Quasithin.S146zY
