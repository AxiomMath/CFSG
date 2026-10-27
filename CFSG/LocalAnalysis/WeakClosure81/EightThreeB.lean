module

public import CFSG.LocalAnalysis.WeakClosure81.EightThreeA
public import CFSG.LocalAnalysis.WeakClosure81.SevenFiveTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Hyp83

variable {V H T : Subgroup G}

theorem pCoreOf_kGen_le (h : Hyp83 V H T) (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H) :
    pCoreOf 2 (kGen V H T) ≤ pCoreOf 2 H := by
  refine le_trans ?_ (h.pCoreOf_kSub_le hOmH)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (kGen V H T))
  · exact (CFSG.LieType.BorelTits.pCoreOf_le (r := 2) (kGen V H T)).trans
      (h.kGen_le_kSub hOmH)
  · exact (h.kSub_le_normalizer_kGen hOmH).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)

theorem pCoreOf_inf_kGen_le (h : Hyp83 V H T) (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H) :
    pCoreOf 2 H ⊓ kGen V H T ≤ pCoreOf 2 (kGen V H T) := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ ?_
  · intro x hx
    have hxH : x ∈ H := h.kGen_le_H hOmH hx
    have h1 : x ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H (Subgroup.le_normalizer hxH)
    have h2 : x ∈ Subgroup.normalizer (kGen V H T : Set G) := Subgroup.le_normalizer hx
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, h1 y, h2 y]
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left

theorem not_le_pCoreOf_kGen (h : Hyp83 V H T)
    (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H) :
    ¬ V ≤ pCoreOf 2 (kGen V H T) :=
  fun hV => h.not_le_pCoreOf (hV.trans (h.pCoreOf_kGen_le hOmH))

theorem le_centralizer_kGen_of_not_mem_omegaOrb (h : Hyp83 V H T)
    (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H) {U : Subgroup G}
    (hU : U ∈ omegaSet V H (eSub V H T)) (hUΩ : U ∉ omegaOrb V H T) :
    U ≤ Subgroup.centralizer (kGen V H T : Set G) := by
  have hne : ∀ k ∈ kSub V H (eSub V H T), U ≠ conjSubgroup V k := fun k hk heq =>
    hUΩ ⟨k, hk, heq⟩
  have hcomm := commutator_kOrbSub_eq_bot h.elemAbelian h.isTI h.isMulCommutative_eSub
    h.eSub_le_H h.eSub_subgroupOf_normal hOmH h.mem_omegaSet_self hU hne
  rw [← kGen_eq_kOrbSub] at hcomm
  have h1 : kOrbSub V H (eSub V H T) U ≤ Subgroup.centralizer (kGen V H T : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have h2 : U ≤ kOrbSub V H (eSub V H T) U := by
    change U ≤ ⨆ k : kSub V H (eSub V H T), conjSubgroup U (k : G)
    simpa [CFSG.Quasithin.conjSubgroup_one] using
      le_iSup (fun k : kSub V H (eSub V H T) => conjSubgroup U (k : G)) 1
  exact h2.trans h1

theorem kSub_eq_kGen_sup_kOrbCompl (h : Hyp83 V H T)
    (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H) :
    kSub V H (eSub V H T) = kGen V H T ⊔ kOrbCompl V H (eSub V H T) V := by
  rw [kGen_eq_kOrbSub]
  exact kSub_eq_kOrbSub_sup_kOrbCompl h.eSub_le_H h.eSub_subgroupOf_normal hOmH
    h.mem_omegaSet_self

theorem kOrbCompl_le_centralizer_kGen (h : Hyp83 V H T)
    (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H) :
    kOrbCompl V H (eSub V H T) V ≤ Subgroup.centralizer (kGen V H T : Set G) := by
  rw [kGen_eq_kOrbSub]
  exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (commutator_kOrbSub_kOrbCompl_eq_bot h.elemAbelian h.isTI h.isMulCommutative_eSub
      h.eSub_le_H h.eSub_subgroupOf_normal hOmH h.mem_omegaSet_self))

theorem kGen_transitive (h : Hyp83 V H T) (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H)
    {U : Subgroup G} (hU : U ∈ omegaOrb V H T) :
    ∃ k ∈ kGen V H T, U = conjSubgroup V k := by
  obtain ⟨x, hx, rfl⟩ := hU
  have hsplit : x ∈ kOrbCompl V H (eSub V H T) V ⊔ kGen V H T := by
    rw [sup_comm, ← h.kSub_eq_kGen_sup_kOrbCompl hOmH]
    exact hx
  have hBN : kOrbCompl V H (eSub V H T) V ≤ Subgroup.normalizer (kGen V H T : Set G) :=
    (h.kOrbCompl_le_centralizer_kGen hOmH).trans (Subgroup.centralizer_le_normalizer _)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hBN,
    Set.mem_mul] at hsplit
  obtain ⟨b, hb, a, ha, hba⟩ := hsplit
  refine ⟨a, ha, ?_⟩
  have hbV : b ∈ Subgroup.centralizer (V : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_kGen_self V H T))
      (h.kOrbCompl_le_centralizer_kGen hOmH hb)
  have hV : conjSubgroup V b = V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.centralizer_le_normalizer _ hbV)
  rw [← hba, ← CFSG.Quasithin.conjSubgroup_conjSubgroup, hV]

theorem mem_omegaOrb_of_mem_omegaSetIn (h : Hyp83 V H T)
    (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H) {U : Subgroup G}
    (hU : U ∈ omegaSetIn V (kGen V H T) (eSub V H T)) :
    U ∈ omegaOrb V H T := by
  obtain ⟨⟨g, hg, hE, hO⟩, hUK⟩ := hU
  have hΓ : U ∈ omegaSet V H (eSub V H T) :=
    mem_omegaSet.mpr ⟨g, hg, hE,
      fun hle => hO ((le_inf hle hUK).trans (h.pCoreOf_inf_kGen_le hOmH))⟩
  by_contra hΩ
  have hcent := h.le_centralizer_kGen_of_not_mem_omegaOrb hOmH hΓ hΩ
  have hnorm : kGen V H T ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.le_centralizer_iff.mp hcent).trans (Subgroup.centralizer_le_normalizer _)
  have hUp : IsPGroup 2 ↥U := (isElemAbelian_of_mem_omegaSet h.elemAbelian hΓ).isPGroup
  exact hO (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUK hnorm hUp)

theorem inf_centralizer_kGen_eq_bot (h : Hyp83 V H T)
    (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H) :
    V ⊓ Subgroup.centralizer (kGen V H T : Set G) = ⊥ := by
  by_contra hne
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hz1' : z ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hKN : kGen V H T ≤ Subgroup.normalizer (V : Set G) := by
    intro a ha
    have haz : a * z = z * a := Subgroup.mem_centralizer_iff.mp hz.2 a ha
    have hzc : z ∈ conjSubgroup V a := by
      rw [mem_conjSubgroup_iff, show a * z * a⁻¹ = z by rw [haz]; group]
      exact hz.1
    have hne' : V ⊓ conjSubgroup V a ≠ ⊥ := by
      intro hbot
      have hmem : z ∈ V ⊓ conjSubgroup V a := ⟨hz.1, hzc⟩
      rw [hbot] at hmem
      exact hz1' (Subgroup.mem_bot.mp hmem)
    exact conjSubgroup_eq_iff_mem_normalizer.mp (conjSubgroup_eq_of_isTI h.isTI hne')
  have hK' : kOrbCompl V H (eSub V H T) V ≤ Subgroup.normalizer (V : Set G) :=
    (h.kOrbCompl_le_centralizer_kGen hOmH).trans
      ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_kGen_self V H T))).trans
        (Subgroup.centralizer_le_normalizer _))
  have hkS : kSub V H (eSub V H T) ≤ Subgroup.normalizer (V : Set G) := by
    rw [h.kSub_eq_kGen_sup_kOrbCompl hOmH]
    exact sup_le hKN hK'
  have hV := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_kSub h.mem_omegaSet_self)
    hkS h.elemAbelian.isPGroup
  exact h.not_le_pCoreOf (hV.trans (h.pCoreOf_kSub_le hOmH))

end Hyp83

end CFSG.LocalAnalysis.WeakClosure81
