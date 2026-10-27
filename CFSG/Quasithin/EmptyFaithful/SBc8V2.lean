module

public import CFSG.Quasithin.EmptyFaithful.SBd2NoA5
public import CFSG.Quasithin.EmptyFaithful.SBc5Common

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace SBc8

section V2

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem V₂_facts (h113 : StageLemma14113) (c : Ctx15330 T Mc M V₁ V₂ Yp I L t) :
    V₂ ≤ UI153 T I ∧ V₂ ≤ blockU L ∧ M ⊓ I ≤ Subgroup.normalizer (V₂ : Set G) ∧
      Nat.card ↥V₂ = 4 ∧ (∀ v ∈ V₂, v ≠ 1 → ∃ y ∈ Yp, y * v * y⁻¹ ≠ v) := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hh : Hyp153 G T Mc M := hyp.hyp
  have D : Decomp153 T M V₁ V₂ t := hyp.decomp
  have hF : Facts153 T M V₁ Yp I := c25.facts.toFacts153
  have hYp : Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) :=
    c25.facts.case_two.2
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c25.conc.1
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hLperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLI
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hYL : Yp ≤ L := c.c27.Yp_le
  have hYI : Yp ≤ I := hYL.trans hLle
  have hIU : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hLU : L ≤ Subgroup.normalizer (UI153 T I : Set G) := hLle.trans hIU
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  obtain ⟨hUOC, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl c25.ctx.charTwo
    (SBc5.omegaOneCenter_le_Sgp hyp)
  have hUO : UI153 T I ≤ pCoreOf 2 I := hUOC.trans inf_le_left
  have hU2 : IsPGroup 2 ↥(UI153 T I) := (pCoreOf_isPGroup 2 I).to_le hUO
  have hUL : UI153 T I ≤ Subgroup.normalizer (L : Set G) :=
    (hUO.trans (pCoreOf_le 2 I)).trans hIL
  have hcomm : ⁅V₂, Yp⁆ = V₂ := by
    rw [hYp]
    exact hh.commutator_V₂_Yplus h113 D
  have hV₂UI : V₂ ≤ UI153 T I := by
    have := hh.V₂_le_conjClosure_Yplus h113 D
    rw [← hYp] at this
    exact this.trans (conjClosure_mono le_rfl hYI)
  have hV₂U : V₂ ≤ blockU L :=
    calc V₂ = ⁅V₂, Yp⁆ := hcomm.symm
      _ ≤ ⁅UI153 T I, L⁆ := Subgroup.commutator_mono hV₂UI hYL
      _ ≤ blockU L := SBd2.commutator_le_blockU hLperf hLU hUL hU2
  have hYpM : Yp ≤ M ⊓ Subgroup.centralizer (V₁ : Set G) := by
    rw [hYp]
    exact (oTwoUpper_le _).trans (inf_le_inf_right _ (Y153_le Mc M))
  have hV₂eq : ⁅VZ T M, Yp⁆ = V₂ := by
    apply le_antisymm
    · calc ⁅VZ T M, Yp⁆ ≤ ⁅VZ T M, M ⊓ Subgroup.centralizer (V₁ : Set G)⁆ :=
            Subgroup.commutator_mono le_rfl hYpM
        _ = V₂ := D.comm₂
    · calc V₂ = ⁅V₂, Yp⁆ := hcomm.symm
        _ ≤ ⁅VZ T M, Yp⁆ := Subgroup.commutator_mono D.le₂ le_rfl
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := hh.le_normalizer
  have hMIYp : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := by
    rw [← hF.norm_eq]
    exact inf_le_right
  have hMN : M ⊓ I ≤ Subgroup.normalizer (V₂ : Set G) := fun m hm => by
    rw [← hV₂eq]
    exact S153H.mem_normalizer_commutator (hMV hm.1) (hMIYp hm)
  refine ⟨hV₂UI, hV₂U, hMN, D.card₂, fun v hv hv1 => ?_⟩
  obtain ⟨y, hy, hne⟩ := SBd2.exists_not_commute_V₂ h113 hh D v hv hv1
  exact ⟨y, by rw [hYp]; exact hy, hne⟩

end V2

end SBc8

end CFSG.Quasithin
