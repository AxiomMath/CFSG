module

public import CFSG.Quasithin.AppendixH.H16.Transport
public import CFSG.Quasithin.AppendixH.H16.SextetTransv
public import CFSG.Quasithin.AppendixH.H16.SextetInduces

public section

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.LU24
  CFSG.Quasithin.H.LU CFSG.Monster.Code CFSG.Open

theorem h161_transport
    {V : Type*} [CommGroup V]
    (e : V ≃* W11) (G K P : Subgroup (MulAut V))
    (hG : G.map (CFSG.Quasithin.H.congrHom e) = imgCd sxGen)
    (hK : K.map (CFSG.Quasithin.H.congrHom e) = imgCd sxKS)
    (hP : P.map (CFSG.Quasithin.H.congrHom e) = imgCd sxP0) :
    ∃ V₁₀ : Subgroup V,
      (IsChiefFactorUnder (actsOnModule G) ⊥ (fixV K) ∧ rk ↥(fixV K) = 4 ∧
        IsChiefFactorUnder (actsOnModule G) (fixV K) V₁₀ ∧
        IsChiefFactorUnder (actsOnModule G) V₁₀ ⊤ ∧
        V₁₀ = CFSG.Quasithin.commV P ∧ rkIdx V₁₀ = 1) ∧
      InducesOn G (fixV K) ⊥ (Multiplicative (Fin 2 ⊕ Fin 2 → ZMod 2))
        (natSubI (Fin 2 ⊕ Fin 2) (ZMod 2) (CFSG.Open.StatedSp 2 (ZMod 2))) ∧
      FullTranspAxis G K (fixV K) V₁₀ := by
  have hFix : (fixV K).map e.toMonoidHom = US := by
    have h := CFSG.Quasithin.H.fixV_map_congrHom e K
    rw [hK, fixV_imgCd_sxKS] at h
    exact h.symm
  let V₁₀ : Subgroup V := V10.map e.symm.toMonoidHom
  have hV : V₁₀.map e.toMonoidHom = V10 := by
    rw [Subgroup.map_map]
    have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id W11 := by
      ext w; simp
    rw [this, Subgroup.map_id]
  have hTop : (⊤ : Subgroup V).map e.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ e.surjective
  have hBot : (⊥ : Subgroup V).map e.toMonoidHom = ⊥ := Subgroup.map_bot _
  have hCh : ∀ X Y : Subgroup V, X.map e.toMonoidHom = US → Y.map e.toMonoidHom = V10 →
      IsChiefFactorUnder (actsOnModule G) X Y := by
    intro X Y hX hY
    refine (isChiefFactorUnder_map e G X Y).1 ?_
    have h := isChiefFactorUnder_US_V10
    erw [hG, hX, hY]
    exact h
  refine ⟨V₁₀, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · refine (isChiefFactorUnder_map e G _ _).1 ?_
    erw [hG, hBot, hFix]
    exact isChiefFactorUnder_bot_US
  · rw [← rk_fixV_map_congrHom e K, hK, fixV_imgCd_sxKS]
    exact rk_US
  · exact hCh _ _ hFix hV
  · refine (isChiefFactorUnder_map e G _ _).1 ?_
    erw [hG, hV, hTop]
    exact isChiefFactorUnder_V10_top
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    have h := commV_map_congrHom e P
    erw [hP, commV_imgCd_sxP0] at h
    rw [hV]
    exact h
  · have h := CFSG.Quasithin.H.rkIdx_map_mulEquiv e V₁₀
    erw [hV] at h
    exact h.symm.trans rkIdx_V10
  · refine (inducesOn_map e G _ _ (natSubI (Fin 2 ⊕ Fin 2) (ZMod 2) (StatedSp 2 (ZMod 2)))).1 ?_
    erw [hG, hFix, hBot]
    exact inducesOn_imgCd_sxGen
  · refine (fullTranspAxis_map e G K _ _).1 ?_
    erw [hG, hK, hFix, hV]
    exact fullTranspAxis_imgCd_sxGen

end CFSG.ASVolI.H16
