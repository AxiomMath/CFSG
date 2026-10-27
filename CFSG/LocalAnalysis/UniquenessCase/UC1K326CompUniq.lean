module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326CompDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326ZWrC
public import CFSG.GH74.GLS.Stage2.Final.Thm6.I414Comp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {n : ℕ} {P : Subgroup G}

private theorem isMulCommutative_of_mulEquiv {M N : Type*} [Mul M] [Mul N] (e : M ≃* N)
    (h : IsMulCommutative M) : IsMulCommutative N :=
  IsMulCommutative.of_comm fun a b => by
    have h' : e (e.symm a * e.symm b) = e (e.symm b * e.symm a) :=
      congrArg e (h.is_comm.comm (e.symm a) (e.symm b))
    rwa [e.map_mul, e.map_mul, e.apply_symm_apply, e.apply_symm_apply] at h'

theorem comp_unique (h : Hyp326 G n P)
    (hS : ∀ L : Subgroup G, CFSG.Open.IsComponentOf L ⊤ → IsSL3pi ↥L)
    {L₁ L₂ : Subgroup G} (h₁ : CFSG.Open.IsComponentOf L₁ ⊤)
    (h₂ : CFSG.Open.IsComponentOf L₂ ⊤) : L₁ = L₂ := by
  by_contra hne
  have hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x := by
    have hcent : L₁ ≤ Subgroup.centralizer (L₂ : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (CFSG.ComponentClassification.LocalComponents.commute_of_ne L₁ L₂ h₁ h₂ hne)
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hcent hx) y hy).symm
  have hsub₁ : L₁.IsSubnormal :=
    CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain h₁.2.1
      Subgroup.IsSubnormal.top
  have hsub₂ : L₂.IsSubnormal :=
    CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain h₂.2.1
      Subgroup.IsSubnormal.top
  have hT₁ : IsSylowOf 3 (P ⊓ L₁) L₁ :=
    CFSG.GH74.GLS.Stage2.Final.Thm6.I414.isSylowOf_inf_of_isSubnormal h.sylow hsub₁
  have hT₂ : IsSylowOf 3 (P ⊓ L₂) L₂ :=
    CFSG.GH74.GLS.Stage2.Final.Thm6.I414.isSylowOf_inf_of_isSubnormal h.sylow hsub₂
  have hna₁ : ¬ IsMulCommutative ↥(P ⊓ L₁) :=
    not_isMulCommutative_of_isSylowOf (hS L₁ h₁).isQuasisimple (hS L₁ h₁).card_center hT₁
  have hna₂ : ¬ IsMulCommutative ↥(P ⊓ L₂) :=
    not_isMulCommutative_of_isSylowOf (hS L₂ h₂).isQuasisimple (hS L₂ h₂).card_center hT₂
  have hna₁' : ¬ IsMulCommutative ((P ⊓ L₁).subgroupOf P) := fun hh =>
    hna₁ (isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : P ⊓ L₁ ≤ P)) hh)
  have hna₂' : ¬ IsMulCommutative ((P ⊓ L₂).subgroupOf P) := fun hh =>
    hna₂ (isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : P ⊓ L₂ ≤ P)) hh)
  have hcomm' : ∀ x ∈ (P ⊓ L₁).subgroupOf P, ∀ y ∈ (P ⊓ L₂).subgroupOf P,
      x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    exact hcomm (x : G) hx.2 (y : G) hy.2
  obtain ⟨e⟩ := h.wr
  rcases zwr_no_commuting_nonabelian (P := ↥P) h.one_le e hcomm' with hc | hc
  · exact hna₁' hc
  · exact hna₂' hc

theorem comp_normal
    (hu : ∀ L₁ L₂ : Subgroup G, CFSG.Open.IsComponentOf L₁ ⊤ → CFSG.Open.IsComponentOf L₂ ⊤ →
      L₁ = L₂) {L : Subgroup G} (hL : CFSG.Open.IsComponentOf L ⊤) : L.Normal := by
  refine Subgroup.normal_iff_map_conj_eq.mpr fun g => ?_
  have hconj : CFSG.Open.IsComponentOf (L.map (MulAut.conj g).toMonoidHom) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · have h := CFSG.Open.IsSubnormal.map (MulAut.conj g).toMonoidHom hL.2.1
      rwa [Subgroup.map_top_of_surjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).surjective] at h
    · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
        (L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
        hL.2.2
  exact (hu L (L.map (MulAut.conj g).toMonoidHom) hL hconj).symm

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
