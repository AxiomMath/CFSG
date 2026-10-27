module

import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F437.Gen

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def burnsideF437_F437Kind (κ : GLKind) : Prop :=
  ∀ (degree : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E)
    (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y) (M : Type) [Group M]
    (ε : Y →* M) (z : M) (hyp : HypF_4_31 κ degree Gp M₁ M₂ β ε z),
    let chart := hyp.amalgam.toHypF_4_4g.chart
    ∀ Tb : Subgroup E, ChF.IsSylowOf 2 Tb (M₁ ⊓ M₂) →
    ∀ fb : ↥(M₁ ⊓ M₂), (fb : E) ∈ Tb →
      (fb : E) ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      (fb : E) * (fb : E) = 1 → ¬ chart.IsTypeIIIInv (fb : E) →
      ChF.IsSylowOf 2
        (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({(fb : E)} : Set E))
        (cenIn Gp (fb : E)) →
      (chart.IsFieldInv (fb : E) ∨ chart.IsGraphInv (fb : E)) ∧
      ((∃ subdegree, 0 < subdegree ∧ degree = 2 * subdegree ∧
          chart.IsFieldInv (fb : E) ∧
          IsGenLie (f437Dbar Gp (fb : E)) κ 2 subdegree ∧
          F437QuotientAssembly Gp M₁ M₂ (fb : E) κ subdegree) ∨
        (chart.IsGraphInv (fb : E) ∧ (κ = .U4 ∨ κ = .U5) ∧
          IsGenLie (f437Dbar Gp (fb : E)) .Sp4 2 degree ∧
          chart.GraphFixedMarkingGoal (fb : E) ∧
          F437QuotientAssembly Gp M₁ M₂ (fb : E) .Sp4 degree)) ∧
      F437RestrictionAssembly Gp M₁ M₂ β (fb : E) ∧
      (((f437DbarOne Gp M₁ (fb : E)).subgroupOf M₁).map (f1 (c := β)) ⊓
          ((f437DbarTwo Gp M₂ (fb : E)).subgroupOf M₂).map (f2 (c := β)) =
        ((cenIn (Gp ⊓ (M₁ ⊓ M₂)) (fb : E)).subgroupOf (M₁ ⊓ M₂)).map (bmap β)) ∧
      ((∀ e ∈ f437Ebar (fb : E), ∀ d ∈ f437Dbar Gp (fb : E),
          e * d * e⁻¹ ∈ f437Dbar Gp (fb : E)) ∧
        Subgroup.centralizer ((f437Dbar Gp (fb : E) : Subgroup E) : Set E) ⊓
          f437Ebar (fb : E) = Subgroup.zpowers (fb : E) ∧
        (∀ e ∈ f437Ebar (fb : E), ∃ d ∈ f437Dbar Gp (fb : E),
          ∃ h ∈ f437Ebar (fb : E) ⊓ (M₁ ⊓ M₂), e = d * h) ∧
        (∀ e ∈ f437Ebar (fb : E),
          e ∈ Subgroup.normalizer ((cenIn (Gp ⊓ (M₁ ⊓ M₂)) (fb : E) : Subgroup E) : Set E) →
          e ∈ Subgroup.normalizer ((f437DbarOne Gp M₁ (fb : E) : Subgroup E) : Set E))) ∧
      (ChF.IsSylowOf 2 (imB β ε Tb ⊓ Subgroup.centralizer ({bM β ε fb} : Set M))
          (Subgroup.centralizer ({bM β ε fb} : Set M)) ∨
        (κ = .U4 ∧ degree = 1 ∧ Nonempty (E ≃* MulAut Gp) ∧
          Nonempty (E ≃* β.G0) ∧ IsL43 M))

theorem burnsideF437_F_4_37_iff_kinds : F_4_37 ↔ ∀ κ, burnsideF437_F437Kind κ := Iff.rfl

theorem burnsideF437_F437Kind_Tits : burnsideF437_F437Kind .Tits := by
  intro degree E _ Gp M₁ M₂ Y _ β M _ ε z hyp chart Tb hTb fb hfbT hfbS hsq hiii hsyl
  haveI := hyp.amalgam.finite
  have hfG : (fb : E) ∉ Gp := burnsideF437_not_mem_Gp hsyl (fun h => hfbS h.1) hsq
  exact absurd (by rw [hyp.amalgam.canonical (Or.inr rfl)]; exact Subgroup.mem_top _) hfG

theorem burnsideF437_F437Kind_G2d : burnsideF437_F437Kind .G2d := by
  intro degree E _ Gp M₁ M₂ Y _ β M _ ε z hyp
  exact absurd rfl hyp.not_G2d

end CFSG.ASVolI
