module

public import CFSG.Quasithin.EmptyFaithful.S14610P0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.facts14610_c1 (S : Setting146 G T M) {u : G} {I : Subgroup G}
    (hI : IsIStar T M u I) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T)) :
    CGS (pCoreOf 2 (i1Of1469 T M I)) ≤ M := by
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  obtain ⟨-, hR2⟩ := S.pCoreOf_i1_eq hLT hsyl
  obtain ⟨x, hxT, hxn, hxN⟩ := exists_mem_normalizer_of_lt_isPGroup hT2 (S.tI_lt hI.1)
  have hxO : x ∈ Subgroup.normalizer (pCoreOf 2 (yOfL22 T M ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_right hxT)
  have hxR : x ∈ Subgroup.normalizer ((pCoreOf 2 (i1Of1469 T M I) : Subgroup G) : Set G) := by
    rw [hR2]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hxO, hxN⟩
  refine iSup_le fun C => iSup_le fun hCle => iSup_le fun hC1 => iSup_le fun hCchar => ?_
  have hCn : ∀ g ∈ Subgroup.normalizer ((pCoreOf 2 (i1Of1469 T M I) : Subgroup G) : Set G),
      g ∈ Subgroup.normalizer (C : Set G) := fun g hg =>
    mem_normalizer_of_characteristic_subgroupOf hCchar hCle hg
  have hXJ : i1Of1469 T M I ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    hCn g (le_normalizer_pCoreOf 2 _ hg)
  have hxJ : x ∈ Subgroup.normalizer (C : Set G) := hCn x hxR
  have hTIJ : T ⊓ I ≤ Subgroup.normalizer (C : Set G) := (le_sup_right : T ⊓ I ≤ _).trans hXJ
  by_contra hJM
  have hCJ : C ≤ pCoreOf 2 (Subgroup.normalizer (C : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      ((pCoreOf_isPGroup 2 (i1Of1469 T M I)).to_le hCle)
  have hTu : tU T u ≤ T ⊓ I := le_inf inf_le_left hI.1.1.1
  have hJ : IsI T M u (Subgroup.normalizer (C : Set G)) :=
    ⟨⟨hTu.trans hTIJ, fun hbot => hC1 (le_bot_iff.mp (hCJ.trans hbot.le))⟩,
      fun h => S.not_lI_le_mcOf hLT (((le_sup_left : lI T M I ≤ i1Of1469 T M I)).trans (hXJ.trans h)),
      hJM⟩
  have heq := (hI.of_le_inf hJ hTIJ).2
  exact hxn (heq ▸ (⟨hxT, hxJ⟩ : x ∈ T ⊓ Subgroup.normalizer (C : Set G)))

theorem Setting146.facts14610_c2 (S : Setting146 G T M) {u : G} {I I₂ : Subgroup G}
    (hI : IsIStar T M u I) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hgen : I = i1Of1469 T M I ⊔ I₂)
    (hc1 : CGS (pCoreOf 2 (i1Of1469 T M I)) ≤ M) :
    pCoreOf 2 (i1Of1469 T M I) ≠ pCoreOf 2 I₂ := by
  intro heq
  have hTM : T ≤ M := S.hyp1281.inM.2
  have hOI : pCoreOf 2 I ≤ pCoreOf 2 (i1Of1469 T M I) := by
    have hle : pCoreOf 2 I ≤ i1Of1469 T M I :=
      (B6.pCoreOf_two_le_of_isSylowTwoOf hsyl).trans le_sup_right
    exact le_pCoreOf_of_le_normalizer 2 hle ((i1Of1469_le T M I).trans (le_normalizer_pCoreOf 2 I))
      (pCoreOf_isPGroup 2 I)
  have hR1 : pCoreOf 2 (i1Of1469 T M I) ≠ ⊥ := fun h =>
    hI.1.1.2 (le_bot_iff.mp (hOI.trans h.le))
  have hN : Subgroup.normalizer ((pCoreOf 2 (i1Of1469 T M I) : Subgroup G) : Set G) ≤
      CGS (pCoreOf 2 (i1Of1469 T M I)) := by
    have := inf_normalizer_le_cgsIn (H := (⊤ : Subgroup G)) hR1
    rwa [top_inf_eq, cgsIn_top] at this
  have hI₂ : I₂ ≤ M := by
    intro g hg
    have : g ∈ Subgroup.normalizer ((pCoreOf 2 (i1Of1469 T M I) : Subgroup G) : Set G) := by
      rw [heq]; exact le_normalizer_pCoreOf 2 I₂ hg
    exact hc1 (hN this)
  have hI₁ : i1Of1469 T M I ≤ M :=
    (i1Of1469_le_yOfL22_sup T M I).trans (sup_le S.hyp1281.le hTM)
  exact hI.1.2.2 (hgen ▸ sup_le hI₁ hI₂)

end CFSG.Quasithin
