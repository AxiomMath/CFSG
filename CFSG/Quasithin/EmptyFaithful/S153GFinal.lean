module

public import CFSG.Quasithin.EmptyFaithful.S153GCount

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def CountCentralizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Concl15332 T M V₁ I L →
      I ⊓ Subgroup.centralizer (UL153 T I L : Set G) ≤ Sgp153 T V₁

@[expose] def CountJS0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Concl15332 T M V₁ I L →
      ∀ t' ∈ T, t' ∉ Sgp153 T V₁ → conjBy153 t' (S0153 T V₁ L) = S0153 T V₁ L →
        (∀ A : Subgroup G, IsOffenderB T V₁ (UL153 T I L) A → ¬ A ≤ S0153 T V₁ L) →
          thompsonJ (S0153 T V₁ L) ≤ Subgroup.centralizer (UL153 T I L : Set G)

section Tools

variable {G : Type} [Group G]

private theorem cf_mem_normalizer_commutator {g : G} {A B : Subgroup G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

private theorem cf_le_normalizer_of_relIndex_two {S T X : Subgroup G} (hidx : S.relIndex T = 2)
    (hS : S ≤ Subgroup.normalizer (X : Set G)) {t : G} (htT : t ∈ T) (htS : t ∉ S)
    (ht : t ∈ Subgroup.normalizer (X : Set G)) : T ≤ Subgroup.normalizer (X : Set G) := by
  intro x hx
  by_cases hxS : x ∈ S
  · exact hS hxS
  · have h2 : (S.subgroupOf T).index = 2 := hidx
    have hmem : (⟨t⁻¹, T.inv_mem htT⟩ : T) * ⟨x, hx⟩ ∈ S.subgroupOf T := by
      rw [Subgroup.mul_mem_iff_of_index_two h2]
      simp only [Subgroup.mem_subgroupOf, inv_mem_iff]
      exact iff_of_false htS hxS
    have hs : t⁻¹ * x ∈ S := hmem
    have hx' : x = t * (t⁻¹ * x) := by group
    rw [hx']
    exact Subgroup.mul_mem _ ht (hS hs)

private theorem cf_oTwoUpper_le_opResidual (X T : Subgroup G) :
    oTwoUpper X ≤ opResidual 2 (oTwoUpper X ⊔ T) := by
  rw [oTwoUpper, Subgroup.closure_le]
  intro x hx
  exact Subgroup.subset_closure ⟨Subgroup.mem_sup_left (mem_oTwoUpper_of_odd hx.1 hx.2),
    Nat.coprime_two_right.mpr hx.2⟩

end Tools

section Tools'

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

private theorem cf_omegaOneCenter_le (h : Hyp15310 G T Mc M V₁ V₂ Yp t) :
    quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter (Sgp153 T V₁) := by
  unfold quasithinOmegaOneCenter
  refine Subgroup.closure_mono fun z hz => ?_
  have hzV : z ∈ VZ T M := le_conjClosure _ _ (Subgroup.subset_closure hz)
  exact ⟨⟨S153D.VZ_le_Sgp153 h hzV, Subgroup.centralizer_le (fun x hx => hx.1) hz.1.2⟩, hz.2⟩

end Tools'

theorem countFinal_of_narrow (h113 : StageLemma14113) (hC : CountCentralizer) (hJ : CountJS0) :
    CountFinal := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S hS0 hB
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hF : Facts153 T M V₁ Yp I := c25.facts.toFacts153
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hSI : Sgp153 T V₁ ≤ I := hsyl.1
  have hS2 : IsPGroup 2 (Sgp153 T V₁) := hsyl.2.1
  have hLI : L ≤ I := (le_of_mem_cComp c25.conc.1).trans (thompsonJ_le_self I)
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hIUI : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hIU : I ≤ Subgroup.normalizer (UL153 T I L : Set G) := fun g hg =>
    cf_mem_normalizer_commutator (hIUI hg) (hIL hg)
  have hIeq : I = L ⊔ Sgp153 T V₁ := c.I_eq
  have hOS : pCoreOf 2 I ≤ Sgp153 T V₁ := S153D.pCoreOf_le_Sgp153' hF
  have hOL : pCoreOf 2 I ≤ L ⊔ pCoreOf 2 (L ⊔ Sgp153 T V₁) := by
    rw [hIeq]
    exact le_sup_right
  have hOS₀ : pCoreOf 2 I ≤ S0153 T V₁ L := le_inf hOS hOL
  have hKS : I ⊓ Subgroup.centralizer (UL153 T I L : Set G) ≤ Sgp153 T V₁ :=
    hC G T Mc M V₁ V₂ Yp I L t c cc
  have hKI : I ⊓ Subgroup.centralizer (UL153 T I L : Set G) ≤ I := inf_le_left
  have hIK : I ≤ Subgroup.normalizer
      ((I ⊓ Subgroup.centralizer (UL153 T I L : Set G) : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, B2F.le_normalizer_centralizer hIU hg⟩
  have hK2 : IsPGroup 2 ↥(I ⊓ Subgroup.centralizer (UL153 T I L : Set G)) := hS2.to_le hKS
  have hKO : I ⊓ Subgroup.centralizer (UL153 T I L : Set G) ≤ pCoreOf 2 I :=
    le_pCoreOf_of_le_normalizer 2 hKI hIK hK2
  have hKS₀ : I ⊓ Subgroup.centralizer (UL153 T I L : Set G) ≤ S0153 T V₁ L := hKO.trans hOS₀
  have hJS₀ : thompsonJ (S0153 T V₁ L) ≤ Subgroup.centralizer (UL153 T I L : Set G) :=
    hJ G T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S hS0 hB
  have hS₀S : S0153 T V₁ L ≤ Sgp153 T V₁ := inf_le_left
  have hJK : thompsonJ (S0153 T V₁ L) ≤ I ⊓ Subgroup.centralizer (UL153 T I L : Set G) :=
    le_inf ((GammaExtra.thompsonJ_le_self _).trans (hS₀S.trans hSI)) hJS₀
  have hJeq : thompsonJ (I ⊓ Subgroup.centralizer (UL153 T I L : Set G)) =
      thompsonJ (S0153 T V₁ L) := GammaExtra.thompsonJ_eq_of_le hJK hKS₀
  have hIJ : I ≤ Subgroup.normalizer (thompsonJ (S0153 T V₁ L) : Set G) := by
    rw [← hJeq]
    exact hIK.trans (GammaExtra.normalizer_le_normalizer_thompsonJ _)
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (S0153 T V₁ L : Set G) := by
    intro g hg
    have h1 : g ∈ Subgroup.normalizer (Sgp153 T V₁ : Set G) := Subgroup.le_normalizer hg
    have h2 : g ∈ Subgroup.normalizer
        ((L ⊔ pCoreOf 2 (L ⊔ Sgp153 T V₁) : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_sup L (pCoreOf 2 (L ⊔ Sgp153 T V₁))
        ⟨hIL (hSI hg), le_normalizer_pCoreOf 2 (L ⊔ Sgp153 T V₁) (Subgroup.mem_sup_right hg)⟩
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩
  have ht'N : t' ∈ Subgroup.normalizer (S0153 T V₁ L : Set G) :=
    GammaExtra.mem_normalizer_of_map_conj_eq hS0
  have hidx : (Sgp153 T V₁).relIndex T = 2 := hh.decomp.relIndex_nS hh.hyp
  have hTN : T ≤ Subgroup.normalizer (S0153 T V₁ L : Set G) :=
    cf_le_normalizer_of_relIndex_two hidx hSN ht'T ht'S ht'N
  have hTJ : T ≤ Subgroup.normalizer (thompsonJ (S0153 T V₁ L) : Set G) :=
    hTN.trans (GammaExtra.normalizer_le_normalizer_thompsonJ _)
  have hUO : UL153 T I L ≤ pCoreOf 2 I := by
    have hUUI : UL153 T I L ≤ UI153 T I :=
      (Subgroup.le_normalizer_iff_commutator_le_left (H := L) (K := UI153 T I)).mp
        (hLI.trans hIUI)
    obtain ⟨hle, -⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2
      c25.ctx.charTwo (cf_omegaOneCenter_le hh)
    exact hUUI.trans (hle.trans inf_le_left)
  have hS₀ne : S0153 T V₁ L ≠ ⊥ := by
    intro hbot
    obtain ⟨q, -, -, -, hcard, -⟩ := cc.orthogonal
    have hU : UL153 T I L = ⊥ := le_bot_iff.mp (hbot ▸ hUO.trans hOS₀)
    rw [hU, Subgroup.card_bot] at hcard
    omega
  have hJne : thompsonJ (S0153 T V₁ L) ≠ ⊥ :=
    Setup.thompsonJ_ne_bot (hS2.to_le hS₀S) hS₀ne
  have hJ2 : IsPGroup 2 ↥(thompsonJ (S0153 T V₁ L)) :=
    hS2.to_le ((GammaExtra.thompsonJ_le_self _).trans hS₀S)
  have hCO : thompsonJ (S0153 T V₁ L) ≤
      pCoreOf 2 (Subgroup.normalizer (thompsonJ (S0153 T V₁ L) : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hJ2
  have hYpL : Yp ≤ L := c.c27.Yp_le
  have hXN : Yp ⊔ T ≤ Subgroup.normalizer (thompsonJ (S0153 T V₁ L) : Set G) :=
    sup_le ((hYpL.trans hLI).trans hIJ) hTJ
  have hYpM : Yp ≤ M := hh.Yp_le_Y153.trans (Y153_le Mc M)
  have hXM : Yp ⊔ T ≤ M := sup_le hYpM hh.hyp.T_le
  rcases hh.hyp.lemma_15_3_2_four (le_sup_right : T ≤ Yp ⊔ T) hXM with hi | ⟨-, hU⟩
  · apply hh.hyp.Yplus_not_le_centralizer h113 hh.decomp
    have hYp : Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) :=
      c25.facts.case_two.2
    have hres := cf_oTwoUpper_le_opResidual (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) T
    rw [← hYp] at hres
    rw [← hYp]
    exact hres.trans hi
  · have hH : InH (Yp ⊔ T) (Subgroup.normalizer (thompsonJ (S0153 T V₁ L) : Set G)) :=
      ⟨hXN, fun hb => hJne (le_bot_iff.mp (hb ▸ hCO))⟩
    have hNM : Subgroup.normalizer (thompsonJ (S0153 T V₁ L) : Set G) ≤ M :=
      le_of_isUniqueM hU hH
    exact c25.conc.2.1 (le_inf (hLI.trans (hIJ.trans hNM)) hLI)

end CFSG.Quasithin
