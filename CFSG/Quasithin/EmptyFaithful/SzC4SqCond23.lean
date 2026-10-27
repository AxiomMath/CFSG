module

public import CFSG.Quasithin.EmptyFaithful.S153SwapCentralizer
public import CFSG.Quasithin.MS93.ASC134Sq
public import CFSG.Quasithin.EmptyFaithful.SzC4Close

public section

namespace CFSG.Quasithin.SzC4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem c134SqCond_of_l3Closing (h113 : StageLemma14113)
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (c12 : Concl15312Two Yp L)
    (hYY : Yp = Y153 Mc M) (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L) :
    MS93.C134SqCond (Sgp153 T V₁) L := by
  intro T₁ hT₁S hchar
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  have huniq : IsUniqueM (Y153 Mc M ⊔ T) M := Hyp153.lemma_15_3_7_unique h113 hyp
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hyp hh.decomp
  have hidx : ((Sgp153 T V₁).subgroupOf T).index = 2 := hh.decomp.relIndex_nS hyp
  have hLI : L ≤ I := (le_of_mem_cComp c.conc.1).trans (thompsonJ_le_self I)
  have hLM : ¬ L ≤ M := fun hLM => c.conc.2.1 (le_inf hLM hLI)
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := hyp.qtfe.sylow.1.to_le inf_le_left
  have hAT₁ : omegaOneCenterOf T₁ ≤ T₁ := A4.omegaOneCenterOf_le T₁
  have hA2 : IsPGroup 2 ↥(omegaOneCenterOf T₁) := hS2.to_le (hAT₁.trans hT₁S)
  have hTN : T ≤ Subgroup.normalizer (T₁ : Set G) :=
    hTS.trans (normalizer_le_normalizer_of_characteristic_subgroupOf hT₁S hchar)
  have hTA : T ≤ Subgroup.normalizer (omegaOneCenterOf T₁ : Set G) :=
    hTN.trans (A4.normalizer_le_normalizer_omegaOneCenterOf T₁)
  have hYL_L : YL153 Yp L ≤ L := (oTwoUpper_le (Yp ⊓ L)).trans inf_le_right
  have hYL : Yp ≤ L ⊔ B6.conjSub t' L := by
    rw [c12.1, ← hswap]
    refine sup_le (hYL_L.trans le_sup_left) ?_
    exact ((B6.conjSub t').le_iff_le.mpr hYL_L).trans le_sup_right
  have hT_disj : ∀ g ∈ T, g ∈ Sgp153 T V₁ ∨ t'⁻¹ * g ∈ Sgp153 T V₁ := by
    intro g hg
    by_cases hgS : g ∈ Sgp153 T V₁
    · exact Or.inl hgS
    · right
      have hiff := Subgroup.mul_mem_iff_of_index_two hidx
        (a := (⟨t'⁻¹, T.inv_mem ht'T⟩ : ↥T)) (b := (⟨g, hg⟩ : ↥T))
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hiff
      have ht'inv : ¬ ((t'⁻¹ : G) ∈ Sgp153 T V₁) := fun h =>
        ht'S (by simpa using (Sgp153 T V₁).inv_mem h)
      have hpair : ((t'⁻¹ : G) ∈ Sgp153 T V₁) ↔ ((g : G) ∈ Sgp153 T V₁) :=
        ⟨fun h => absurd h ht'inv, fun h => absurd h hgS⟩
      simpa using hiff.mpr hpair
  have ht'2 : t' * t' ∈ Sgp153 T V₁ := by
    have hiff := Subgroup.mul_mem_iff_of_index_two hidx
      (a := (⟨t', ht'T⟩ : ↥T)) (b := (⟨t', ht'T⟩ : ↥T))
    have hmem : (⟨t', ht'T⟩ * ⟨t', ht'T⟩ : ↥T) ∈ (Sgp153 T V₁).subgroupOf T :=
      hiff.mpr Iff.rfl
    rwa [Subgroup.mem_subgroupOf] at hmem
  have hX : Y153 Mc M ⊔ T ≤ Yp ⊔ T := by
    simpa only [hYY] using (le_rfl : Yp ⊔ T ≤ Yp ⊔ T)
  exact card_inf_centralizer_sq_le (X := Y153 Mc M ⊔ T) (Y := Yp) (T := T)
    (S := Sgp153 T V₁) (L := L) (A := omegaOneCenterOf T₁) (t := t')
    huniq hX hYL hLM ht'T hT_disj ht'2 hSL hTS hA2 hTA

theorem l3ClosingC134_of_corrOneSq (hMS : MS93.MRes.AS_C_1_34_corrOneSq)
    (h113 : StageLemma14113) : L3ClosingC134 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hq c12 hV hYY hSL t' ht'T ht'S hswap
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c.conc.1
  have hMSp : IsMSPair (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) := SBd7.isMSPair_sup_S c hq hV hYY hSL
  have hcomp : L ∈ cComp (L ⊔ Sgp153 T V₁) := SBd5.mem_cComp_sup' hLI hSL
  have hset : ((L ⊔ Sgp153 T V₁ : Subgroup G) : Set G) =
      (L : Set G) * (Sgp153 T V₁ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L _ hSL
  obtain ⟨e⟩ := hq
  let α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hα : IsModO2Surj L α := by
    refine ⟨e.surjective.comp (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)), ?_⟩
    show (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).ker = CFSG.pCore 2 ↥L
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) e.toMonoidHom
      e.injective, QuotientGroup.ker_mk']
  have hsq : MS93.C134SqCond (Sgp153 T V₁) L :=
    c134SqCond_of_l3Closing h113 c c12 hYY hSL ht'T ht'S hswap
  exact hMS G (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L hMSp hcomp hset
    ⟨ZMod 2, inferInstance, inferInstance, α, ZMod.card 2, hα⟩ hsq

end CFSG.Quasithin.SzC4
