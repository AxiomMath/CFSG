module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedAut
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedL3RigidField
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedL3RigidGraph
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedL3RigidBeta
import CFSG.RankThree.PartTwo.KFacts.L34Centralizers
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private lemma wccrc_conj_reduce {G : Type*} [Group G] {β τ c γ : MulAut G}
    (hβ : β = c * τ * c⁻¹) (hγ2 : γ * γ = 1) (hγβ : γ * β = β * γ)
    (hγfix : ∀ x : G, β x = x → γ x = x)
    (hstd : ∀ γ' : MulAut G, γ' * γ' = 1 → γ' * τ = τ * γ' →
      (∀ x : G, τ x = x → γ' x = x) → γ' = 1 ∨ γ' = τ) :
    γ = 1 ∨ γ = β := by
  have hγ'2 : (c⁻¹ * γ * c) * (c⁻¹ * γ * c) = 1 := by
    have e : (c⁻¹ * γ * c) * (c⁻¹ * γ * c) = c⁻¹ * (γ * γ) * c := by group
    rw [e, hγ2]; group
  have hγ'τ : (c⁻¹ * γ * c) * τ = τ * (c⁻¹ * γ * c) := by
    have hcomm : γ * (c * τ * c⁻¹) = (c * τ * c⁻¹) * γ := by
      rw [← hβ]; exact hγβ
    have e1 : (c⁻¹ * γ * c) * τ = c⁻¹ * (γ * (c * τ * c⁻¹)) * c := by group
    have e2 : c⁻¹ * ((c * τ * c⁻¹) * γ) * c = τ * (c⁻¹ * γ * c) := by group
    rw [e1, hcomm, e2]
  have hγ'fix : ∀ x : G, τ x = x → (c⁻¹ * γ * c) x = x := by
    intro x hx
    have hcx : β (c x) = c x := by
      rw [hβ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply,
        MulEquiv.symm_apply_apply, hx]
    have h1 : γ (c x) = c x := hγfix (c x) hcx
    calc (c⁻¹ * γ * c) x = c⁻¹ (γ (c x)) := rfl
      _ = c⁻¹ (c x) := by rw [h1]
      _ = x := by simp
  rcases hstd (c⁻¹ * γ * c) hγ'2 hγ'τ hγ'fix with h | h
  · left
    have e : γ = c * (c⁻¹ * γ * c) * c⁻¹ := by group
    rw [e, h]; group
  · right
    have e : γ = c * (c⁻¹ * γ * c) * c⁻¹ := by group
    rw [e, h, hβ]

private lemma wccrc_rigid {k : Type} [Field k] (hk : Nat.card k = 4) :
    OuterFixedRigid (projectiveSL 3 k) := by
  haveI := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hk
  haveI := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.charP_two_of_card_eq_four hk
  intro β hβ2 hout γ hγ2 hγβ hγfix
  let σ : k ≃+* k := frobeniusEquiv k 2
  have hσ : ∀ a : k, σ a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  rcases CFSG.RankThree.PartTwo.KFacts.L34.involution_cases_card hk hσ hβ2 with
    hinner | ⟨⟨H, hH⟩, -⟩ | ⟨⟨H, hH⟩, -⟩ | ⟨⟨H, hH⟩, -⟩
  · exfalso
    obtain ⟨g, hg⟩ := hinner
    exact hout ⟨g, fun x => by rw [← hg, MulAut.conj_apply]⟩
  · exact wccrc_conj_reduce (c := conjAut 3 k H) (τ := fieldAut 3 k σ) hH hγ2 hγβ hγfix
      (fun γ' h1 h2 h3 => outerRigid_field_std hk hσ h1 h2 h3)
  · exact wccrc_conj_reduce (c := conjAut 3 k H) (τ := dualAut 3 k) hH hγ2 hγβ hγfix
      (fun γ' h1 h2 h3 => outerRigid_graph_std hk hσ h1 h2 h3)
  · exact wccrc_conj_reduce (c := conjAut 3 k H) (τ := fieldAut 3 k σ * dualAut 3 k) hH hγ2
      hγβ hγfix (fun γ' h1 h2 h3 => outerRigid_beta_std hk hσ h1 h2 h3)

theorem outerFixedRigid_isL3 {M : Type} [Group M] [Finite M] (h : IsL3 M 2) :
    OuterFixedRigid M := by
  obtain ⟨K, hK, hfin, hcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
      (n := 3) (p := 2) (f := 2) h
  letI : Field K := hK
  haveI : Finite K := hfin
  have hk : Nat.card K = 4 := by rw [hcard]; norm_num
  exact outerFixedRigid_of_mulEquiv e.symm (wccrc_rigid hk)

end CFSG.LocalAnalysis.WeakClosure81

end
