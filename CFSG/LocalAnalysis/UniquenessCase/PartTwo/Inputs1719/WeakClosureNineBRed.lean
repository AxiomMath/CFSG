module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBRedStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBRedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.WeakClosure81

theorem nGReduction_holds :
    (∀ (G : Type) [Group G] [Finite G] (V : Subgroup G), SevenSixThreeAbelian V) →
      NGAbstract → NGFacts → ∀ (G : Type) [Group G] [Finite G], W3Lem915 G := by
  intro h763 hAbs hFacts G _ _ V T N L hyp hTN hNM hN hL hψ L₁ L₂ hL₁ hL₂ hne hperm X hX hX1 hX2
  obtain ⟨Z, _, ψ, hψs, hψk, hcomp, hL3⟩ := hψ
  rw [hL₁] at hne hperm hX1
  obtain ⟨t, htT, rfl⟩ := hL₂
  have : Finite Z := Finite.of_surjective ψ hψs
  have hLN : L ≤ N := by rw [hN]; exact le_sup_right
  have htN : t ∈ N := hTN htT
  have hL2N : conjSubgroup L t ≤ N := (E3.conjSubgroup_mono_left t hLN).trans_eq
    (conjSubgroup_eq_iff_mem_normalizer.2 (le_normalizer htN))
  have hn1 := NG915.pCoreOf_le_normalizer_of_eq_perfectCore hL
  have hsup := NG915.map_sup_eq_top hN ψ hψs
  have hconj := NG915.map_subgroupOf_conjSubgroup ψ L htN
  have ht₀ : ψ ⟨t⁻¹, N.inv_mem htN⟩ ∈ (T.subgroupOf N).map ψ :=
    mem_map_of_mem ψ (by rw [mem_subgroupOf]; exact T.inv_mem htT)
  have hpermb := NG915.map_conj_eq_or_eq_of_perm ψ hperm
  have hneb := NG915.map_ne_map_conjSubgroup hL hLN htN hne ψ hψk
  have hcomm := NG915.commutator_eq_bot_of_isComponent hcomp hconj hneb
  have hfs := NG915.fixSwap_of_sup_eq_top hsup hcomm hneb ht₀ hconj hpermb
  have hnorm := NG915.normal_sup_of_fixSwap hfs
  have hsup' : (L.subgroupOf N).map ψ ⊔ ((conjSubgroup L t).subgroupOf N).map ψ ⊔
      (T.subgroupOf N).map ψ = ⊤ := eq_top_iff.mpr (hsup ▸ sup_le_sup_right le_sup_left _)
  have hTb2 : IsPGroup 2 ((T.subgroupOf N).map ψ) :=
    (hyp.sylow.isPGroup.of_equiv (subgroupOfEquivOfLe hTN).symm).map ψ
  have hcent := NG915.centralizer_sup_eq_bot_of_isL3 hcomp hL3 hconj hcomm hTb2 hsup'
    (NF914.eq_bot_of_normal_of_isPGroup_two ψ hψs hψk)
  have hfacts := hFacts Z _ _ _ hL3 ⟨_, ht₀, hconj⟩ hneb hpermb hcomm hnorm hcent hsup'
    (NF914.isSylowIn_map_of_surjective hyp.sylow hTN hNM ψ hψs)
  have hstar := NG915.star915_of_fixSwap hNM ψ hψk hLN hL2N hn1
    (NG915.pCoreOf_le_normalizer_conjSubgroup hn1 htN) hX hX1 hX2 hfs
  exact hAbs G V T N L _ hyp hTN hNM hLN hL2N hstar (h763 G V) Z ψ hψs hψk hfacts

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
