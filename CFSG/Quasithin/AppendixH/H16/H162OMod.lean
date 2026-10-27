module

public import CFSG.Quasithin.AppendixH.H16.H162Mod
public import CFSG.Quasithin.AppendixH.H16.OctadBetaInduce
public import CFSG.Quasithin.AppendixH.H16.OctadChief
public import CFSG.Quasithin.AppendixH.H16.OctadSide
public import CFSG.Quasithin.AppendixH.H16.OctadTransv
public import CFSG.Quasithin.AppendixH.H16.Transport

public section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc
  CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24 CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Open

private theorem congrHom_mul_inv_aux {V W : Type*} [CommGroup V] [CommGroup W]
    (e : V ≃* W) (g : MulAut V) (y : V) :
    congrHom e g (e y) * (e y)⁻¹ = e (g y * y⁻¹) := by
  simp [congrHom_apply]

theorem h162O_transport
    {V : Type*} [CommGroup V]
    (ρ : ↥M24g →* MulAut V) (e' : V ≃* W11) (τ : ↥M24g)
    (hcongr : ∀ γ : ↥M24g, congrHom e' (ρ γ) = rhoC11 AutPerm le_rfl (τ⁻¹ * γ * τ))
    {V₅ : Subgroup V} (hV₅ : V₅.map e'.toMonoidHom = octV5)
    {β' : V →* Multiplicative (Fin 6 → ZMod 2)} (hβ : β' = octBeta.comp e'.toMonoidHom) :
    (IsChiefFactorUnder (actsOnModule (rImg ρ (MY M24g ((τ : S24) • octad0)))) ⊥
        (fixV (rImg ρ (KY M24g ((τ : S24) • octad0)))) ∧
      rk ↥(fixV (rImg ρ (KY M24g ((τ : S24) • octad0)))) = 1 ∧
      IsChiefFactorUnder (actsOnModule (rImg ρ (MY M24g ((τ : S24) • octad0))))
        (fixV (rImg ρ (KY M24g ((τ : S24) • octad0)))) V₅ ∧
      rk ↥V₅ = 5 ∧
      IsChiefFactorUnder (actsOnModule (rImg ρ (MY M24g ((τ : S24) • octad0)))) V₅ ⊤) ∧
    (FullTranspCenter (rImg ρ (MY M24g ((τ : S24) • octad0))) (rImg ρ (KY M24g ((τ : S24) • octad0)))
        V₅ (fixV (rImg ρ (KY M24g ((τ : S24) • octad0)))) ∧
      IsDualOfConj ρ (MY M24g ((τ : S24) • octad0)) V₅
        (fixV (rImg ρ (KY M24g ((τ : S24) • octad0)))) (KY M24g ((τ : S24) • octad0))) ∧
    (InducesOnVia (rImg ρ (MY M24g ((τ : S24) • octad0))) ⊤ V₅ (Multiplicative (Fin 6 → ZMod 2))
        (omegaN 6 qPlus6) (β'.comp (⊤ : Subgroup V).subtype) ∧
      (∀ g : ↥M24g, (g : S24) ∈ MY M24g ((τ : S24) • octad0) →
        ((∀ x : V, ρ g x * x⁻¹ ∈ V₅) ↔ (g : S24) ∈ KY M24g ((τ : S24) • octad0))) ∧
      rk ↥(fixV (rImg ρ (KY M24g ((τ : S24) • flagSextet))) ⊔ V₅) = 6 ∧
      (∀ x ∈ fixV (rImg ρ (KY M24g ((τ : S24) • flagSextet))) ⊔ V₅,
        qPlus6 (Multiplicative.toAdd (β' x)) = 0) ∧
      (fixV (rImg ρ (KY M24g ((τ : S24) • flagSextet))) =
        fixV (rImg ρ (KY M24g ((τ : S24) • octad0) ⊓ KY M24g ((τ : S24) • flagSextet))))) := by
  subst hβ
  have hτ : (τ : S24) ∈ M24g := τ.2
  have hKO : KY M24g octad0 = fixO := by
    unfold KY
    rw [show MY M24g octad0 = octStab octad0 from rfl]
    exact pCoreOf_octStab_octad0
  have hMY : MY M24g ((τ : S24) • octad0) = conjSubg (τ : S24) (octStab octad0) := by
    rw [MY_smul_of_mem hτ octad0]
    rfl
  have hKYO : KY M24g ((τ : S24) • octad0) = conjSubg (τ : S24) fixO := by
    rw [KY_smul_of_mem hτ octad0, hKO]
  have hKYS : KY M24g ((τ : S24) • flagSextet) =
      conjSubg (τ : S24) (KY M24g flagSextet) :=
    KY_smul_of_mem hτ flagSextet
  have hKYI : KY M24g ((τ : S24) • octad0) ⊓ KY M24g ((τ : S24) • flagSextet) =
      conjSubg (τ : S24) (KY M24g octad0 ⊓ KY M24g flagSextet) := by
    rw [KY_smul_of_mem hτ octad0, KY_smul_of_mem hτ flagSextet]
    exact (Subgroup.map_inf (KY M24g octad0) (KY M24g flagSextet)
      (MulAut.conj ((τ : S24))).toMonoidHom (MulAut.conj ((τ : S24))).injective).symm
  have hGimg : (rImg ρ (MY M24g ((τ : S24) • octad0))).map (congrHom e') =
      imgCd (octStab octad0) := by
    have h := map_congrHom_rImg ρ (rhoC11 AutPerm le_rfl) e' τ hcongr
      (A := MY M24g ((τ : S24) • octad0)) inf_le_left
    rw [h, hMY, conjSubg_inv_conjSubg]
    rfl
  have hKOimg : (rImg ρ (KY M24g ((τ : S24) • octad0))).map (congrHom e') =
      imgCd fixO := by
    have h := map_congrHom_rImg ρ (rhoC11 AutPerm le_rfl) e' τ hcongr
      (A := KY M24g ((τ : S24) • octad0)) ((pCoreOf_le_subgroup 2 _).trans inf_le_left)
    rw [h, hKYO, conjSubg_inv_conjSubg]
    rfl
  have hKSimg : (rImg ρ (KY M24g ((τ : S24) • flagSextet))).map (congrHom e') =
      imgCd (KY M24g flagSextet) := by
    have h := map_congrHom_rImg ρ (rhoC11 AutPerm le_rfl) e' τ hcongr
      (A := KY M24g ((τ : S24) • flagSextet)) ((pCoreOf_le_subgroup 2 _).trans inf_le_left)
    rw [h, hKYS, conjSubg_inv_conjSubg]
    rfl
  have hKIimg : (rImg ρ (KY M24g ((τ : S24) • octad0) ⊓
      KY M24g ((τ : S24) • flagSextet))).map (congrHom e') =
      imgCd (KY M24g octad0 ⊓ KY M24g flagSextet) := by
    have h := map_congrHom_rImg ρ (rhoC11 AutPerm le_rfl) e' τ hcongr
      (A := KY M24g ((τ : S24) • octad0) ⊓ KY M24g ((τ : S24) • flagSextet))
      (inf_le_left.trans ((pCoreOf_le_subgroup 2 _).trans inf_le_left))
    rw [h, hKYI, conjSubg_inv_conjSubg]
    rfl
  have hFixO : (fixV (rImg ρ (KY M24g ((τ : S24) • octad0)))).map e'.toMonoidHom =
      fixV (imgCd fixO) := by
    rw [← fixV_map_congrHom e' (rImg ρ (KY M24g ((τ : S24) • octad0))), hKOimg]
  have hFixS : (fixV (rImg ρ (KY M24g ((τ : S24) • flagSextet)))).map e'.toMonoidHom =
      fixV (imgCd (KY M24g flagSextet)) := by
    rw [← fixV_map_congrHom e' (rImg ρ (KY M24g ((τ : S24) • flagSextet))), hKSimg]
  have hFixI : (fixV (rImg ρ (KY M24g ((τ : S24) • octad0) ⊓
      KY M24g ((τ : S24) • flagSextet)))).map e'.toMonoidHom =
      fixV (imgCd (KY M24g octad0 ⊓ KY M24g flagSextet)) := by
    rw [← fixV_map_congrHom e' (rImg ρ (KY M24g ((τ : S24) • octad0) ⊓
      KY M24g ((τ : S24) • flagSextet))), hKIimg]
  have hsup : ((fixV (rImg ρ (KY M24g ((τ : S24) • flagSextet)))) ⊔ V₅).map e'.toMonoidHom =
      fixV (imgCd (KY M24g flagSextet)) ⊔ octV5 := by
    rw [Subgroup.map_sup, hFixS, hV₅]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · refine (isChiefFactorUnder_map e' (rImg ρ (MY M24g ((τ : S24) • octad0))) ⊥
      (fixV (rImg ρ (KY M24g ((τ : S24) • octad0))))).1 ?_
    rw [hGimg, Subgroup.map_bot, hFixO, fixV_imgCd_fixO]
    exact isChiefFactorUnder_bot_octV1
  · rw [← rk_fixV_map_congrHom e' (rImg ρ (KY M24g ((τ : S24) • octad0))), hKOimg,
      fixV_imgCd_fixO, rk_octV1]
  · refine (isChiefFactorUnder_map e' (rImg ρ (MY M24g ((τ : S24) • octad0)))
      (fixV (rImg ρ (KY M24g ((τ : S24) • octad0)))) V₅).1 ?_
    rw [hGimg, hFixO, fixV_imgCd_fixO, hV₅]
    exact isChiefFactorUnder_octV1_octV5
  · rw [← rk_map_mulEquiv e' V₅, hV₅, rk_octV5]
  · refine (isChiefFactorUnder_map e' (rImg ρ (MY M24g ((τ : S24) • octad0))) V₅ ⊤).1 ?_
    rw [hGimg, hV₅, Subgroup.map_top_of_surjective _ e'.surjective]
    exact isChiefFactorUnder_octV5_top
  · refine (fullTranspCenter_map e' (rImg ρ (MY M24g ((τ : S24) • octad0)))
      (rImg ρ (KY M24g ((τ : S24) • octad0))) V₅
      (fixV (rImg ρ (KY M24g ((τ : S24) • octad0))))).1 ?_
    rw [hGimg, hKOimg, hV₅, hFixO, fixV_imgCd_fixO]
    exact fullTranspCenter_octV5
  · refine isDualOfConj_of_twist ρ (rhoC11 AutPerm le_rfl) e' τ hcongr
      (G' := octStab octad0) (K' := fixO) ?_ ?_ ?_
    · rw [hMY, conjSubg_inv_conjSubg]
    · rw [hKYO, conjSubg_inv_conjSubg]
    · rw [hV₅, hFixO, fixV_imgCd_fixO]
      exact isDualOfConj_octV5
  · refine (inducesOnVia_top_map e' (rImg ρ (MY M24g ((τ : S24) • octad0))) V₅
      (omegaN 6 qPlus6) octBeta).1 ?_
    rw [hGimg, hV₅]
    exact inducesOnVia_octBeta
  · intro g hg
    rw [hMY] at hg
    have hg' : (τ : S24)⁻¹ * (g : S24) * (τ : S24) ∈ octStab octad0 :=
      (mem_conjSubg_iff (τ : S24) (octStab octad0) (g : S24)).1 hg
    let gA : ↥AutPerm := ⟨(τ : S24)⁻¹ * (g : S24) * (τ : S24), octStab_octad0_le_AutPerm hg'⟩
    have hcg : congrHom e' (ρ g) = rhoC11 AutPerm le_rfl gA := by
      rw [hcongr g]
      rfl
    have hLHS : (∀ x : V, ρ g x * x⁻¹ ∈ V₅) ↔
        (∀ y : W11, rhoC11 AutPerm le_rfl gA y * y⁻¹ ∈ octV5) := by
      constructor
      · intro h y
        have hmem : e' (ρ g (e'.symm y) * (e'.symm y)⁻¹) ∈ octV5 := by
          rw [← hV₅]
          exact Subgroup.mem_map_of_mem _ (h (e'.symm y))
        have h1 := congrHom_mul_inv_aux e' (ρ g) (e'.symm y)
        simp only [e'.apply_symm_apply] at h1
        rw [← h1, hcg] at hmem
        exact hmem
      · intro h x
        have hy : rhoC11 AutPerm le_rfl gA (e' x) * (e' x)⁻¹ ∈ octV5 := h (e' x)
        have h1 := congrHom_mul_inv_aux e' (ρ g) x
        rw [hcg] at h1
        have hmem : e' (ρ g x * x⁻¹) ∈ octV5 := by
          rw [← h1]
          exact hy
        rw [← hV₅] at hmem
        exact (Subgroup.mem_map_iff_mem (f := e'.toMonoidHom) e'.injective).1 hmem
    rw [hLHS, mulInv_mem_octV5_iff gA hg', hKYO, mem_conjSubg_iff]
  · rw [← rk_map_mulEquiv e' ((fixV (rImg ρ (KY M24g ((τ : S24) • flagSextet)))) ⊔ V₅), hsup]
    exact rk_fixV_flagSextet_sup_octV5
  · intro x hx
    have hmem : e' x ∈ fixV (imgCd (KY M24g flagSextet)) ⊔ octV5 := by
      rw [← hsup]
      exact Subgroup.mem_map_of_mem _ hx
    change qPlus6 (Multiplicative.toAdd (octBeta (e' x))) = 0
    rw [qPlus6_octBeta]
    exact octQ_eq_zero_of_mem_fixV_flagSextet_sup_octV5 (e' x) hmem
  · apply Subgroup.map_injective (f := e'.toMonoidHom) e'.injective
    rw [hFixS, hFixI, fixV_flagSextet_eq_fixV_inf]

end CFSG.ASVolI.H16
