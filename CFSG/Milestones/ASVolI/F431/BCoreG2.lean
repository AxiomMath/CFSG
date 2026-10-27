module

public import CFSG.Milestones.ASVolI.F431.BCoreGen
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley
open scoped commutatorElement

section G2

set_option linter.unusedSectionVars false


section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem burnsideF4m_G2_out_comm {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (α β : MulAut (H13.F431.G2.C K)) :
    ⁅α, β⁆ ∈ (MulAut.conj : H13.F431.G2.C K →* MulAut (H13.F431.G2.C K)).range :=
  burnsideF4m_out_comm_of_normalForm (H13.Sec53F.G2.fieldAut K)
    (CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K)
    (H13.F431.G2.exists_conj_fieldAut hf hK) α β

theorem burnsideF4m_G2_Pr_center_le {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    centerOf (perfectCore (H13.F431.G2.Cent.Pr K)) ≤ ctr (oPPrime 2 (H13.F431.G2.Cent.Pr K)) := by
  rw [H13.F431.G2.Cent.centerOf_perfectCore_Pr_eq hf hK]
  intro x hx
  obtain ⟨s, rfl⟩ := H13.F431.G2.mem_Xc_iff.1 hx
  by_cases hs : s = 0
  · subst hs
    rw [H13.F431.G2.xc_zero]
    exact Subgroup.one_mem _
  · rw [burnsideF4gG2Inv_oPPrime_eq_centralizer hs]
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.1 hy

theorem burnsideF4m_G2_Pa_center_eq_bot {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    centerOf (perfectCore (H13.F431.G2.Cent.Pa K)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hPC : parabolicSubgroup Tag.G2 K {CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2.i0} ≤
      adjointGroup Tag.G2 K := parabolicSubgroup_le_adjointGroup _ _ _
  unfold H13.F431.G2.Cent.Pa at hx
  obtain ⟨hx1, hx2⟩ := (H13.Sec53F.G2.mem_centerOf_perfectCore_subgroupOf hPC x).1 hx
  exact Subgroup.mem_bot.2 (Subtype.ext (H13.Sec53F.G2.center_zero hK hf hx1 hx2))

end Model

theorem burnsideF4m_G2_chart {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : HypF_4_4g .G2 2 f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      ∃ Ψ : H13.F431.G2.C K ≃* ↥Gp,
        M₁.subgroupOf Gp = (H13.F431.G2.Cent.Pr K).map Ψ.toMonoidHom ∧
        M₂.subgroupOf Gp = (H13.F431.G2.Cent.Pa K).map Ψ.toMonoidHom := by
  obtain ⟨K, fK, finK, hcard, marking, h1, h2⟩ := burnsideF4g_chart_G2 h
  letI := fK
  haveI := finK
  have hf1 : 1 ≤ f := h.model.2.1
  haveI : CharP K 2 := burnsideF4f_charP_of_card hf1 hcard
  let Ψ : H13.F431.G2.C K ≃* ↥Gp := (H13.F431.G2.mk K).trans marking
  have hΨ : ∀ L : Subgroup (G2Native.Parent K),
      G2Native.fullImage K marking L = L.map Ψ.toMonoidHom := by
    intro L
    unfold G2Native.fullImage G2Native.fullLocal
    rw [Subgroup.map_map]
    exact congrArg (fun φ => Subgroup.map φ L) (MonoidHom.ext fun y => rfl)
  refine ⟨K, fK, finK, inferInstance, hcard, Ψ, ?_, ?_⟩
  · rw [h1, hΨ, burnsideF4gG2Inv_point_eq]
  · rw [h2, hΨ, burnsideF4gG2Inv_line_eq]

theorem burnsideF4m_core12_G2 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    (∀ x ∈ centerOf (perfectCore M₁), x ≠ 1 → x * x = 1 → x ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) ∧
    (∀ x ∈ centerOf (perfectCore M₂), x ≠ 1 → x * x = 1 →
      GLKind.G2 = .Sp4 ∧ x ∈ ctr (oPPrime 2 (Gp ⊓ M₂))) := by
  haveI := hyp.normal
  obtain ⟨K, fK, finK, cK, hcard, Ψ, h1, h2⟩ := burnsideF4m_G2_chart hyp.toHypF_4_4g
  have hc : ∀ a b : E, ⁅a, b⁆ ∈ Gp := burnsideF4m_commutator_mem_of_out hyp.centralizer_trivial
    (burnsideF4m_out_transport Ψ (burnsideF4m_G2_out_comm hf hcard))
  have hφ : Function.Injective (Gp.subtype.comp Ψ.toMonoidHom) :=
    Gp.subtype_injective.comp Ψ.injective
  refine ⟨burnsideF4m_core1_of_model hc _ hφ (burnsideF4m_inf_eq_map Ψ h1)
    (burnsideF4m_G2_Pr_center_le hf hcard), ?_⟩
  intro x hx hx1 _
  rw [burnsideF4m_centerOf_perfectCore_eq_bot_of_model hc _ hφ (burnsideF4m_inf_eq_map Ψ h2)
    (burnsideF4m_G2_Pa_center_eq_bot hf hcard)] at hx
  exact absurd (Subgroup.mem_bot.1 hx) hx1

end G2

end CFSG.ASVolI
