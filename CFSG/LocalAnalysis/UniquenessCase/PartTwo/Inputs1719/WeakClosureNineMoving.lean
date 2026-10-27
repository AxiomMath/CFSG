module

public import CFSG.Quasithin.Background.E3Weak
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineMovingAux
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.WeakClosure81.NineDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise

theorem nine_fourteen_of_not_le_centralizer {G : Type} [Group G] [Finite G]
    {V T N L : Subgroup G} (h9 : Hyp9 V T) (hTN : T ≤ N) (hNV : N ≤ normalizer (V : Set G))
    (hN : N = T ⊔ L) (hLperf : L = CFSG.Quasithin.perfectCore (L ⊔ pCoreOf 2 N))
    (hψ : ∃ (Z : Type) (_ : Group Z) (ψ : ↥N →* Z), Function.Surjective ψ ∧
      (∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N) ∧
      CFSG.IsComponent ((L.subgroupOf N).map ψ))
    (hLV : ¬ L ≤ centralizer (V : Set G)) :
    N ≤ normalizer (E3.wClos V 0 T : Set G) := by
  obtain ⟨Z, _, ψ, hψs, hψk, hLc⟩ := hψ
  have : Finite Z := Finite.of_surjective ψ hψs
  obtain ⟨⟨hVe, hV2, hTI⟩, hTs, -, -⟩ := h9
  have hV1 : V ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hV2; omega
  have hLN : L ≤ N := le_sup_right.trans hN.ge
  have hLp : ⁅L, L⁆ = L := by
    have := CFSG.Quasithin.perfectCore_perfect (L ⊔ pCoreOf 2 N)
    rwa [← hLperf] at this
  have hTsN : IsSylowIn 2 T N := ⟨hTN, hTs.isPGroup, fun h => hTs.not_dvd_relIndex (by
    rw [← Subgroup.relIndex_mul_relIndex T N _ hTN hNV]; exact h.mul_right _)⟩
  have hQT : pCoreOf 2 N ≤ T := hTsN.le_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 N)
    ((normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 N)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
  have hCn : ((centralizer (V : Set G)).subgroupOf N).Normal := ⟨fun c hc n => by
    rw [mem_subgroupOf] at hc ⊢
    simpa using (mem_normalizer_iff.mp
      ((hNV.trans (B2F.normalizer_le_normalizer_centralizer V)) n.2) c).mp hc⟩
  have hsup : (L.subgroupOf N).map ψ ⊔ (T.subgroupOf N).map ψ = ⊤ := by
    rw [← Subgroup.map_sup, ← subgroupOf_sup hLN hTN,
      subgroupOf_eq_top.mpr (hN.le.trans (sup_comm T L).le), map_top_of_surjective ψ hψs]
  have hT2 : IsPGroup 2 ((T.subgroupOf N).map ψ) :=
    (hTs.isPGroup.comap_of_injective N.subtype N.subtype_injective).map ψ
  have hbar : ∀ x : ↥N, ψ x ∈ ((centralizer (V : Set G)).subgroupOf N).map ψ → ψ x ^ 2 = 1 →
      (x : G) ∈ pCoreOf 2 N := fun x hx hx2 =>
    (hψk x).mp (MV914.eq_one_of_isComponent hLc (hCn.map ψ hψs)
      (fun h => hLV (MV914.le_centralizer_of_map_le ψ hψk hLN hNV hLp h)) hT2 hsup
      (NF914.eq_bot_of_normal_of_isPGroup_two ψ hψs hψk) hx hx2)
  have hW : E3.wClos V 0 T ≤ pCoreOf 2 N := E3.wClos_le_of_forall fun A hA => by
    obtain ⟨hAT, g, hAg, hm⟩ := E3.mem_gammaSet_iff.mp hA
    have hel := isElemAbelian_conjSubgroup' hVe g
    obtain rfl : A = conjSubgroup V g := (E3.mQuot_eq_zero_iff hel.isPGroup hAg).mp hm
    intro a ha
    have haN : a ∈ N := hTN (hAT ha)
    have hcomm := MV914.commute_of_conjSubgroup_le_normalizer hVe hV1 hTI (hAT.trans hTs.le) a ha
    have ha2 : (⟨a, haN⟩ : ↥N) ^ 2 = 1 := Subtype.ext (by simpa using hel.2 a ha)
    refine hbar ⟨a, haN⟩ (mem_map_of_mem ψ (mem_subgroupOf.mpr
      (mem_centralizer_iff.mpr fun v hv => (hcomm v hv).symm))) ?_
    rw [← map_pow, ha2, map_one]
  have heq : E3.wClos V 0 (pCoreOf 2 N) = E3.wClos V 0 T :=
    le_antisymm (E3.wClos_mono hQT)
      (E3.wClos_le_of_forall fun A hA => E3.le_wClos ⟨(E3.le_wClos hA).trans hW, hA.2⟩)
  rw [← heq]
  exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N).trans
    (E3.normalizer_le_normalizer_wClos _)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
