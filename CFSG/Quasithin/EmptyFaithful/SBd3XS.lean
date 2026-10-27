module

public import CFSG.Quasithin.EmptyFaithful.SBd3XSAbs
public import CFSG.Quasithin.EmptyFaithful.SBd2SixP

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement

namespace CFSG.Quasithin.SBd3XS

section Context

variable {G : Type} [Group G]

theorem omegaOneCenter_le_S {T Mc M V₁ V₂ Yp : Subgroup G} {t : G} [Finite G]
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) :
    quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter (Sgp153 T V₁) := by
  unfold quasithinOmegaOneCenter
  refine Subgroup.closure_mono fun z hz => ?_
  have hzV : z ∈ VZ T M := le_conjClosure _ _ (Subgroup.subset_closure hz)
  exact ⟨⟨S153D.VZ_le_Sgp153 h hzV, Subgroup.centralizer_le (fun x hx => hx.1) hz.1.2⟩, hz.2⟩

theorem commutator_subgroup_eq_map {H : Subgroup G} :
    ⁅H, H⁆ = (commutator ↥H).map H.subtype := by
  have h1 : (⊤ : Subgroup ↥H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  show ⁅H, H⁆ = (⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ : Subgroup ↥H).map H.subtype
  rw [Subgroup.map_commutator, h1]

end Context

theorem xsIrreducibleOnP32_holds : XSIrreducibleOnP32 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hpre _h1 h4 D hD1 hD2 hD3
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hF : Facts153 T M V₁ Yp I := c25.facts.toFacts153
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hSI : Sgp153 T V₁ ≤ I := hsyl.1
  obtain ⟨hLc, -, -, -, hStarQ, -⟩ := c25.conc
  have hLI : L ≤ I := (le_of_mem_cComp hLc).trans (thompsonJ_le_self I)
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hIU : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  obtain ⟨hle, -⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2
    c25.ctx.charTwo (omegaOneCenter_le_S hyp)
  have hUIc : pCoreOf 2 I ≤ Subgroup.centralizer (UI153 T I : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp (hle hu).2 x hx).symm
  have hUUI : UL153 T I L ≤ UI153 T I :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := L) (K := UI153 T I)).mp (hLI.trans hIU)
  obtain ⟨-, hb, -⟩ := hpre
  have hker : I ⊓ Subgroup.centralizer (UI153 T I : Set G) = pCoreOf 2 I := by
    refine le_antisymm ?_ (le_inf (pCoreOf_le 2 I) hUIc)
    intro x hx
    rw [hb]
    exact ⟨hx.1, Subgroup.centralizer_le hUUI hx.2⟩
  obtain ⟨K, hKL, hmax, hSK, hX⟩ := h4
  have hcomm : commutator ↥(autOn L (UI153 T I)) = ⊤ := hStarQ.1.commutator_eq_top
  have hLp : ⁅autOn L (UI153 T I), autOn L (UI153 T I)⁆ = autOn L (UI153 T I) := by
    rw [commutator_subgroup_eq_map, hcomm, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hL1 : autOn L (UI153 T I) ≠ ⊥ := by
    intro h
    obtain ⟨-, -, a, b, hab⟩ := hStarQ
    have hss : Subsingleton ↥(autOn L (UI153 T I)) := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      exact ((Subgroup.eq_bot_iff_forall _).1 h x.1 x.2).trans
        ((Subgroup.eq_bot_iff_forall _).1 h y.1 y.2).symm
    exact hab (by rw [Subsingleton.elim a b])
  rw [hX] at hD2 hD3 ⊢
  exact xs_irreducible_abstract hIU c.c31.some hLI hKL hSI hIL hsyl hker hLp hL1 hmax hSK hD1 hD2
    hD3

end CFSG.Quasithin.SBd3XS
