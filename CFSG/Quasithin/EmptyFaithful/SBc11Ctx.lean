module

public import CFSG.Quasithin.EmptyFaithful.SBc6Ctx
public import CFSG.Quasithin.EmptyFaithful.S153D31

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc11

section Ctx

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem ctx_basic (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) :
    L ∈ cComp I ∧ L ≤ I ∧ I ≤ Subgroup.normalizer (L : Set G) ∧ I = L ⊔ Sgp153 T V₁ ∧
      IsSylowTwoOf (Sgp153 T V₁) I ∧ ⁅L, L⁆ = L := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c25.conc.1
  exact ⟨hLc, le_of_mem_cComp hLc, c.c27.normal, c.I_eq, c25.facts.sylow,
    perfect_of_mem_cComp hLc⟩

theorem ctx_UI (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) : UI153 T I ≤ centerOf (pCoreOf 2 I) := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := c25.facts.sylow
  obtain ⟨hUOC, -⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2
    c25.ctx.charTwo (SBc5.omegaOneCenter_le_Sgp c25.ctx.hyp)
  exact hUOC

theorem ctx_star (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) :
    L ≤ Subgroup.normalizer (UI153 T I : Set G) ∧
      pCoreOf 2 L ≤ Subgroup.centralizer (UI153 T I : Set G) ∧
      ¬ L ≤ Subgroup.centralizer (UI153 T I : Set G) := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  obtain ⟨-, hLI, -, -, -, -⟩ := ctx_basic c
  refine ⟨hLI.trans (le_normalizer_conjClosure _ I), fun x hx => ?_, fun hle => ?_⟩
  · have hxI : x ∈ pCoreOf 2 I := (SBc6.pCoreOf_le_of_ctx c.toCtx15330).1 hx
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.mp (ctx_UI c hu).2 x hxI).symm
  · have hLM : L ≤ M ⊓ I := fun l hl => c25.facts.cent_le ⟨hLI hl, hle hl⟩
    exact c25.conc.2.1 hLM

theorem exists_star_hom (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) :
    ∃ ψ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(Star153 T I L), Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ∧
      ∀ l : ↥L, ψ (QuotientGroup.mk l) = 1 ↔ (l : G) ∈ Subgroup.centralizer (UI153 T I : Set G) := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  obtain ⟨hLN, hker, hnt⟩ := ctx_star c
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := c25.conc.2.2.2.2.2
  refine ⟨S153D.autOnQuot hLN hker, S153D.autOnQuot_surjective hLN hker,
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq
      (S153D.exists_autOnQuot_ne_one hLN hker hnt), fun l => ?_⟩
  rw [S153D.autOnQuot_mk]
  exact S153D.autOnHom_eq_one_iff hLN l

end Ctx

end SBc11

end CFSG.Quasithin
