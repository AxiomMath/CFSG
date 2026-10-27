module

public import CFSG.Quasithin.EmptyFaithful.A38c13S1565B
public import CFSG.Quasithin.EmptyFaithful.S153LKsB
public import CFSG.Quasithin.EmptyFaithful.S1565M11

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace S153L

section Inputs

attribute [local instance] commGroupOfFact

theorem input15365TypesFourNatModule_holdsC
    (hA21 : AsA21SQTKSection) (h42 : AsB42) (h45 : AsB45) : Input15365TypesFourNatModuleC := by
  intro G _ _ T Mc M V₁ V₂ H K t D hK0 I hV₁I hIU W hW hirr hcase
  have hn := D.n_gt
  obtain ⟨hkerchar, hB⟩ := e22CasesW_two_data D.e22 hn hK0
  obtain ⟨n₁, hn₂, hKs⟩ := e22CasesW_two_shape D.e22 hn hK0
  obtain ⟨hn3, hnodd⟩ := D.n_odd n₁ hn₂ hKs hB
  have hFI := factElem D.hF hIU
  have hIT := isIrrPlusTildeT_of_ambient D.hF hIU W hW hirr
  have hirr' : subM (quasithinOmegaOneCenter T) (conjClosure I H) I ∈
      IrrPlusOn (autIH (quasithinOmegaOneCenter T) I H (conjClosure K T))
        (orbSup (autIH (quasithinOmegaOneCenter T) I H T)
          (subM (quasithinOmegaOneCenter T) (conjClosure I H) I))
        (autIH (quasithinOmegaOneCenter T) I H T) := hIT
  have hnt := hnt_of_irrSec D.hF hIU hirr'.1.2.2.2.1
  have hKH : K ≤ H := le_of_mem_cComp D.hF.K_cComp
  have hne : autIH (quasithinOmegaOneCenter T) I H K ≠ ⊥ := by
    rw [autIH_eq_map D.hF hKH]
    exact map_K_ne_bot D.hF hIU hnt
  have hfin : Finite ↥(autIH (quasithinOmegaOneCenter T) I H K) :=
    Finite.of_surjective _ (toAutI_surjective D.hF I)
  obtain ⟨σ, hσ, hz⟩ := exists_sigma_central D.hF hIU hne hkerchar
  have hDD := d31_of_hyp D.hF D.sqtk hIU hV₁I hirr'
  have hKI := K₀_le_normalizer_of_isInv D.hF hIU hV₁I hirr'.1.2.1
  obtain ⟨B, hA⟩ := qOff_of_hyp D.hF hIU hV₁I hKI hnt
  have hMp : autIH (quasithinOmegaOneCenter T) I H (conjClosure K T) =
      autIH (quasithinOmegaOneCenter T) I H K := by rw [hK0]
  have hD3 : D3Std (autIH (quasithinOmegaOneCenter T) I H H)
      (autIH (quasithinOmegaOneCenter T) I H (conjClosure K T))
      (autIH (quasithinOmegaOneCenter T) I H T) (autIH (quasithinOmegaOneCenter T) I H K)
      (subM (quasithinOmegaOneCenter T) (conjClosure I H) I) :=
    ⟨hDD, hA.qhat_VT hDD.exp, hirr'⟩
  have hq := hA.qOf_VT hDD.exp
  have hHI : H ≤ Subgroup.normalizer (I : Set G) := by
    rcases hcase with hinv | ⟨hfix, -⟩
    · exact hinv
    · have hTst := stab_of_orbSup_eq hfix.symm
      have hTI : T ≤ Subgroup.normalizer (I : Set G) := by
        intro x hx
        have hxH : x ∈ H := D.hF.T_le_H hx
        have hmem : actH D.hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨x, hxH⟩ ∈
            autIH (quasithinOmegaOneCenter T) I H T := by
          rw [autIH_eq_map D.hF D.hF.T_le_H]
          exact ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
        exact (actH_mem_stabSub_subM_iff D.hF.H_le_normalizer_V₁
          (D.hF.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H) hV₁I
          (le_conjClosure I H) ⟨x, hxH⟩).mp (hTst _ hmem)
      have hKN : K ≤ Subgroup.normalizer (I : Set G) :=
        (le_conjClosure K T).trans hKI
      rw [D.H_eq]
      exact sup_le hKN hTI
  have hMst : autIH (quasithinOmegaOneCenter T) I H H ≤
      stabSub (subM (quasithinOmegaOneCenter T) (conjClosure I H) I) := by
    rw [autIH_eq_map D.hF (le_refl H)]
    exact (map_actH_le_stabSub_iff D.hF.H_le_normalizer_V₁
      (D.hF.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H) hV₁I).mpr hHI
  have hVtop : subM (quasithinOmegaOneCenter T) (conjClosure I H) I = ⊤ := by
    have hgen := hDD.gen
    rw [eq_top_iff, ← hgen]
    refine iSup₂_le fun m hm => ?_
    rintro _ ⟨v, hv, rfl⟩
    exact (hMst hm v).2 hv
  have hTle : autIH (quasithinOmegaOneCenter T) I H T ≤
      autIH (quasithinOmegaOneCenter T) I H H := by
    rw [autIH_eq_map D.hF D.hF.T_le_H, autIH_eq_map D.hF (le_refl H)]
    exact Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr (D.hF.T_le_H
      (Subgroup.mem_subgroupOf.mp hx)))
  have hT : autIH (quasithinOmegaOneCenter T) I H T ≤
      stabSub (subM (quasithinOmegaOneCenter T) (conjClosure I H) I) := hTle.trans hMst
  have hfaith : autIH (quasithinOmegaOneCenter T) I H K ⊓
      centSub (subM (quasithinOmegaOneCenter T) (conjClosure I H) I) = ⊥ := by
    rw [hVtop]
    refine eq_bot_iff.2 fun g hg => ?_
    have : g = 1 := MulEquiv.ext fun u => hg.2 u trivial
    exact this ▸ Subgroup.one_mem _
  have hKsC : KsCover ↥(autIH (quasithinOmegaOneCenter T) I H K) :=
    ⟨_, inferInstance, E2.star (H ⊓ M) H K, n₁, σ, hn3, hnodd, hKs, hσ, hz⟩
  have key := typesFour_natW_of_stab hA21 h42 h45 hD3 hMp hT hq hfaith hKsC
  rw [hVtop] at key
  rcases key with h1 | h2 | h3 | h4 | h5
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr (Or.inl h2))
  · exact Or.inl (Or.inr (Or.inr h3))
  · exact Or.inr (Or.inl h4)
  · exact Or.inr (Or.inr h5)

end Inputs

end S153L

end CFSG.Quasithin
