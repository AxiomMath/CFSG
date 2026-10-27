module

public import CFSG.Quasithin.EmptyFaithful.S1469Inputs
public import CFSG.Quasithin.EmptyFaithful.S1469CaseA0
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem tI_le_inf_mcOf (T I : Subgroup G) : T ⊓ I ≤ I ⊓ mcOf T :=
  le_inf inf_le_right (inf_le_left.trans (le_centralizer_quasithinOmegaOneCenter T))

private theorem pCoreOf_inf_mcOf_le {T I : Subgroup G} (hsyl : IsSylowTwoOf (T ⊓ I) I) :
    pCoreOf 2 (I ⊓ mcOf T) ≤ T ⊓ I :=
  B6.pCoreOf_two_le_of_isSylowTwoOf (B6.isSylowTwoOf_mono hsyl (tI_le_inf_mcOf T I) inf_le_left)

private theorem sylow_cases_of_ctx (h1 : Stage1463One) (h2 : Stage1463Two) (h4 : Stage1463Four)
    {T M H : Subgroup G} {u : G} {I K₁ K₂ : Subgroup G} {ρ : G}
    (c : Ctx1469A5 T M H u I K₁ K₂ ρ) :
    IsSylowTwoOf (T ⊓ I) I ∧ (T ⊓ I = tU T u ∨ T ⊓ I = tZero T u) :=
  isIStar_sylow_cases c.ctx.setting c.ctx.hu
    (h1 G T M c.ctx.setting H c.ctx.hH u c.ctx.hu).2.1
    (h2 G T M c.ctx.setting H c.ctx.hH u c.ctx.hu)
    (h4 G T M c.ctx.setting H c.ctx.hH u c.ctx.hu).1 c.ctx.hI.1

theorem Setting146.facts1469_c (i4 : Input1469A5J) (h1 : Stage1463One) (h2 : Stage1463Two)
    (h4 : Stage1463Four) {T M H : Subgroup G} {u : G} {I K₁ K₂ : Subgroup G} {ρ : G}
    (c : Ctx1469A5 T M H u I K₁ K₂ ρ) :
    pCoreOf 2 (mcOf T) ≤ pCoreOf 2 (I ⊓ mcOf T) := by
  have S : Setting146 G T M := c.ctx.setting
  have hsyl : IsSylowTwoOf (T ⊓ I) I := (sylow_cases_of_ctx h1 h2 h4 c).1
  have hTz : T ⊓ I ≤ I ⊓ mcOf T := tI_le_inf_mcOf T I
  have hTG : T ⊓ I ≤ mcOf T := hTz.trans inf_le_right
  have hRzT : pCoreOf 2 (I ⊓ mcOf T) ≤ T ⊓ I := pCoreOf_inf_mcOf_le hsyl
  have hOI : pCoreOf 2 I ≤ pCoreOf 2 (I ⊓ mcOf T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((B6.pCoreOf_two_le_of_isSylowTwoOf hsyl).trans hTz)
      (inf_le_left.trans (le_normalizer_pCoreOf 2 I)) (pCoreOf_isPGroup 2 I)
  have hO : pCoreOf 2 I ≠ ⊥ := c.ctx.hI.1.1.1.2
  have hRz1 : pCoreOf 2 (I ⊓ mcOf T) ≠ ⊥ := fun h => hO (le_bot_iff.mp (hOI.trans h.le))
  have hJ : thompsonJ (pCoreOf 2 (I ⊓ mcOf T)) = thompsonJ (pCoreOf 2 I) :=
    i4 G I (T ⊓ I) (I ⊓ mcOf T) K₁ K₂ (S.isSQTKTC_of_pCoreOf_ne_bot hO) c.charTwo c.ctx.minPar
      c.blocks c.a5.1 c.a5.2 c.not_le
  have hRz2 : IsPGroup 2 (pCoreOf 2 (I ⊓ mcOf T)) := pCoreOf_isPGroup 2 _
  have hIJ : I ≤ Subgroup.normalizer (thompsonJ (pCoreOf 2 (I ⊓ mcOf T)) : Set G) := by
    rw [hJ]
    exact (le_normalizer_pCoreOf 2 I).trans (GammaExtra.normalizer_le_normalizer_thompsonJ _)
  have hJne : thompsonJ (pCoreOf 2 (I ⊓ mcOf T)) ≠ ⊥ := Setup.thompsonJ_ne_bot hRz2 hRz1
  have hJle : thompsonJ (pCoreOf 2 (I ⊓ mcOf T)) ≤ T ⊓ I :=
    (B6.thompsonJ_le _).trans hRzT
  obtain ⟨-, -, hsylJ⟩ := c.obs_a _ hJle hJne hIJ
  have hNJ : mcOf T ⊓ Subgroup.normalizer (pCoreOf 2 (I ⊓ mcOf T) : Set G) ≤
      Subgroup.normalizer (thompsonJ (pCoreOf 2 (I ⊓ mcOf T)) : Set G) :=
    inf_le_right.trans (GammaExtra.normalizer_le_normalizer_thompsonJ _)
  have hTN : T ⊓ I ≤ mcOf T ⊓ Subgroup.normalizer (pCoreOf 2 (I ⊓ mcOf T) : Set G) :=
    le_inf hTG (hTz.trans (le_normalizer_pCoreOf 2 _))
  have hsylN : IsSylowTwoOf (T ⊓ I)
      (mcOf T ⊓ Subgroup.normalizer (pCoreOf 2 (I ⊓ mcOf T) : Set G)) :=
    B6.isSylowTwoOf_mono hsylJ hTN hNJ
  have hRzG : pCoreOf 2 (I ⊓ mcOf T) ≤ mcOf T := (pCoreOf_le 2 _).trans inf_le_right
  have hRzeq : pCoreOf 2 (I ⊓ mcOf T) =
      pCoreOf 2 (mcOf T ⊓ Subgroup.normalizer (pCoreOf 2 (I ⊓ mcOf T) : Set G)) := by
    refine le_antisymm ?_ ?_
    · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (le_inf hRzG Subgroup.le_normalizer) inf_le_right hRz2
    · have hP : pCoreOf 2 (mcOf T ⊓ Subgroup.normalizer (pCoreOf 2 (I ⊓ mcOf T) : Set G)) ≤ T ⊓ I :=
        B6.pCoreOf_two_le_of_isSylowTwoOf hsylN
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hP.trans hTz) ?_
        (pCoreOf_isPGroup 2 _)
      exact (le_inf inf_le_right (le_normalizer_pCoreOf 2 _)).trans (le_normalizer_pCoreOf 2 _)
  exact pCoreOf_le_of_eq_pCoreOf_normalizer hRzG hRzeq

theorem Setting146.facts1469_d (h1 : Stage1463One) (h2 : Stage1463Two) (h4 : Stage1463Four)
    {T M H : Subgroup G} {u : G} {I K₁ K₂ : Subgroup G} {ρ : G}
    (c : Ctx1469A5 T M H u I K₁ K₂ ρ)
    (hc : pCoreOf 2 (mcOf T) ≤ pCoreOf 2 (I ⊓ mcOf T)) : T ⊓ I = tZero T u := by
  obtain ⟨hsyl, hcases⟩ := sylow_cases_of_ctx h1 h2 h4 c
  rcases hcases with h | h
  · exfalso
    obtain ⟨-, hidx, -, hT0, -⟩ := h1 G T M c.ctx.setting H c.ctx.hH u c.ctx.hu
    have hle : tZero T u ≤ tU T u := by
      rw [hT0]
      refine sup_le ?_ le_rfl
      calc pCoreOf 2 (mcOf T) ≤ pCoreOf 2 (I ⊓ mcOf T) := hc
        _ ≤ T ⊓ I := pCoreOf_inf_mcOf_le hsyl
        _ = tU T u := h
    have heq : tU T u = tZero T u := le_antisymm (tU_le_tZero T u) hle
    rw [heq, Subgroup.relIndex_self] at hidx
    omega
  · exact h

theorem Setting146.facts1469_e {T M H : Subgroup G} {u : G} {I K₁ K₂ : Subgroup G} {ρ : G}
    (c : Ctx1469A5 T M H u I K₁ K₂ ρ)
    (hc : pCoreOf 2 (mcOf T) ≤ pCoreOf 2 (I ⊓ mcOf T)) :
    omegaOneCenterOf (pCoreOf 2 (I ⊓ mcOf T)) ≤ omegaOneCenterOf (pCoreOf 2 (mcOf T)) := by
  have S : Setting146 G T M := c.ctx.setting
  have hchar : CharTwo (mcOf T) := charTwo_of_inH' S.hyp.qtke S.hyp.sylow S.isHTM_mcOf.1
  refine Subgroup.closure_mono ?_
  rintro x ⟨⟨hxR, hxC⟩, hx2⟩
  have hxG : x ∈ mcOf T := (pCoreOf_le 2 _ hxR).2
  have hxCQ : x ∈ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hc) hxC
  exact ⟨⟨hchar ⟨hxG, hxCQ⟩, hxCQ⟩, hx2⟩

end CFSG.Quasithin
