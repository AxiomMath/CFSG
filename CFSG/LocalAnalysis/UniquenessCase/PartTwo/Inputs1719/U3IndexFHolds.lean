module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFourBound
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupU3
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.CoverLower
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AFix
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.CardOne
public import CFSG.CGT.PushingUpLit.CGT6.EmbLayer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem setting_map_centralizer {A : Type} [Group A] [Finite A] {L K C : Subgroup A}
    [L.Normal] [C.Normal] {n : ℕ} (hC : C = centralizer (L : Set A))
    (hq : CFSG.Open.IsQuasisimple ↥L)
    (hU3 : CFSG.LocalAnalysis.UniquenessCase.UC22.IsU3 (↥L ⧸ center ↥L) n)
    (hK : IsPGroup 2 K) (hLK : L ⊔ K = ⊤) :
    CFSG.LocalAnalysis.WeakClosure81.InFGroupU3.Setting (L.map (QuotientGroup.mk' C)) n := by
  classical
  have hZ : ∀ l : ↥L, l ∈ center ↥L ↔ QuotientGroup.mk' C (l : A) = 1 := by
    intro l
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hC, Subgroup.mem_center_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h x hx
      exact congrArg Subtype.val (h ⟨x, hx⟩)
    · intro h g
      exact Subtype.ext (h g g.2)
  obtain ⟨η, -⟩ := CFSG.RankThree.exists_quotient_mulEquiv_map (QuotientGroup.mk' C) L
    (center ↥L) hZ
  have hqb : CFSG.Open.IsQuasisimple ↥(L.map (QuotientGroup.mk' C)) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv η.symm
      (CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_quotient_center hq)
  have hZb : center ↥(L.map (QuotientGroup.mk' C)) = ⊥ := by
    rw [← Subgroup.map_center_eq η,
      CFSG.HardMathSupport.Timmesfeld.SporadicRank.center_quotient_center_eq_bot hq,
      Subgroup.map_bot]
  refine ⟨Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective C), hqb, ?_, ?_, ?_, ?_⟩
  · exact CFSG.Blueprint.LieModel.of_mulEquiv
      (η.trans ((QuotientGroup.quotientMulEquivOfEq hZb).trans QuotientGroup.quotientBot).symm) hU3
  · intro x hx
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective C x
    have hperf : ⁅L, L⁆ = L :=
      CFSG.AGLEmbeddingD2.Tits.GN516.commutator_eq_self_of_isQuasisimple hq
    have hNL : Subgroup.normalizer (L : Set A) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr inferInstance
    have haC : a ∈ C := by
      rw [hC]
      refine CFSG.RankThree.PartOne.Sec12Two.mem_centralizer_of_comm_mem_centralizer hperf
        (hNL ▸ Subgroup.mem_top a) fun l hl => ?_
      rw [← hC]
      have h1 : QuotientGroup.mk' C l * QuotientGroup.mk' C a =
          QuotientGroup.mk' C a * QuotientGroup.mk' C l :=
        (Subgroup.mem_centralizer_iff.mp hx) _ (Subgroup.mem_map_of_mem _ hl)
      have h2 : QuotientGroup.mk' C (a * l * a⁻¹ * l⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
        group
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    rw [show QuotientGroup.mk' C a = 1 from (QuotientGroup.eq_one_iff a).mpr haC]
    exact one_mem _
  · rw [hZb, Subgroup.card_bot]
    exact odd_one
  · have h2 : IsPGroup 2 (A ⧸ L) :=
      CFSG.CGT.PushingUpLit.CGT6.isPGroup_quotient_of_sup_eq_top hK hLK
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective C x
    obtain ⟨k, hk⟩ := h2 (a : A ⧸ L)
    refine ⟨k, ?_⟩
    have ha : a ^ 2 ^ k ∈ L := by
      rw [← QuotientGroup.mk_pow] at hk
      exact (QuotientGroup.eq_one_iff _).mp hk
    rw [← map_pow]
    exact Subgroup.mem_map_of_mem _ ha

theorem k_U3IndexF_holds :
    S17.K_U3IndexF := by
  intro A _ _ L _ K C _ n hC hq hU3 hK hLK
  exact (setting_map_centralizer hC hq hU3 hK hLK).inFGroup

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
