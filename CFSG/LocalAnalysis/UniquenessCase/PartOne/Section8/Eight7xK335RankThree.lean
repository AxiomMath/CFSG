module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Local
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Classical
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator
  lieOrderDivisor)

theorem k335_oNan_center (hK3 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K3)
    {X : Type} [Group X] [Finite X]
    (h : CFSG.LocalAnalysis.UniquenessCase.UCK.ThreeCover
      (fun Y _ => CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor Y .ONan) X)
    {S : Subgroup X} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S ⊤) {x : X} (hx : x ∈ S)
    (hc : ∀ y ∈ S, x * y = y * x) : x ∈ Subgroup.center X := by
  have hZcard : Nat.card (Subgroup.center X) = 3 := h.2.1
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hS
  obtain ⟨_, hSpg, hSdvd⟩ := hS
  rw [Subgroup.relIndex_top_right] at hSdvd
  let T : Sylow 3 X := hSpg.toSylow hSdvd
  have hTS : (T : Subgroup X) = S := rfl
  have hZP : IsPGroup 3 (Subgroup.center X) :=
    IsPGroup.of_card (n := 1) (by rw [hZcard]; norm_num)
  have hZS : Subgroup.center X ≤ S := by
    have h := IsPGroup.le_sylow_of_normal hZP T
    rwa [hTS] at h
  have hZc : Subgroup.center X ≤ Subgroup.centralizer (S : Set X) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact Subgroup.mem_center_iff.mp hz y
  have hK3' := hK3 X h T
  have hcard : Nat.card ↥(S ⊓ Subgroup.centralizer (S : Set X)) = 3 := by
    have h := hK3'.2.2.1
    rwa [hTS] at h
  have hZe : Subgroup.center X = S ⊓ Subgroup.centralizer (S : Set X) := by
    refine Subgroup.eq_of_le_of_card_ge (le_inf hZS hZc) ?_
    rw [hcard, hZcard]
  have hxc : x ∈ Subgroup.centralizer (S : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hc y hy).symm
  have hxS : x ∈ S ⊓ Subgroup.centralizer (S : Set X) := ⟨hx, hxc⟩
  simpa [hZe] using hxS

theorem k335_rank_three_false
    (hK34 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K34odd)
    (hK3 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K3) (hO : LieOrderFormulasInput)
    (hSO : K335SporadicOrders) {G : Type} [Group G] [Finite G] {L P S : Subgroup G}
    (h : K335Quasi G L P S) (hr : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 3) : False := by
  have hdvd := k335_card_dvd h.lie
  rcases hK34 G h.quasi (k335_isCatalog h) (k335_odd_card_center h) hr with hc | ⟨h3, hc⟩
  · obtain ⟨x, hxP, hx1, hxS⟩ := k335_exists_mem_center h.sylow.isPGroup h.le h.normal
      (k335_ne_bot h.card)
    have hm : x ∈ P ⊓ Subgroup.center G :=
      Subgroup.mem_inf.2 ⟨hxP, k335_oNan_center hK3 hc h.sylow (h.le hxP) hxS⟩
    rw [h.disjoint] at hm
    exact hx1 (Subgroup.mem_bot.1 hm)
  · obtain ⟨e⟩ := k335_mulEquiv_of_center (k335_center_eq_bot_of_not_dvd h h3)
    have hE := h.strongE9
    rcases hc with hc | hc | hc | hc
    · rcases hc with hc | hc | hc <;>
        exact k335_noStrong_alt (Nonempty.map e.symm.trans hc) (by norm_num) (by norm_num) P S hE
    · rcases hc with hc | hc
      · have hG := CFSG.Open.StatedAPI.card_mul_two_of_statedClassicalModel_psl_two_odd
          Nat.prime_three (by norm_num) ((hc.of_mulEquiv e).statedClassicalModel (by decide))
        norm_num at hG
        rw [show Nat.card G = 9828 by omega] at hdvd
        norm_num at hdvd
      · have hG := k335_card_lie hO (hc.of_mulEquiv e)
        rw [show lieOrderDivisor .PSp 2 (3 ^ 1) = 2 by decide,
          show lieOrderNumerator .PSp 2 (3 ^ 1) = 51840 by decide] at hG
        rw [show Nat.card G = 25920 by omega] at hdvd
        norm_num at hdvd
    · rcases hc with ⟨p, f, hp, hc⟩ | ⟨p, f, hp, hc⟩ | ⟨p, f, hq, hc⟩ | ⟨p, f, hq, -, hc⟩ |
        ⟨p, f, hq, hc⟩ | ⟨p, f, hq, hc⟩ | ⟨p, f, hq, hc⟩ | ⟨p, f, hq, hc⟩ | ⟨p, f, hp, hc⟩
      · exact k335_noStrong_psp6 hO (hc.of_mulEquiv e) hp P S hE
      · exact k335_noStrong_omegaMinus8 hO (hc.of_mulEquiv e) hp P S hE
      · exact k335_noStrong_psl4 hO (hc.of_mulEquiv e) hq P S hE
      · exact k335_noStrong_psu4 hO (hc.of_mulEquiv e) hq P S hE
      · exact k335_noStrong_psl67 hO (hc.of_mulEquiv e) (Or.inl rfl) hq P S hE
      · exact k335_noStrong_psu67 hO (hc.of_mulEquiv e) (Or.inl rfl) hq P S hE
      · exact k335_noStrong_psl67 hO (hc.of_mulEquiv e) (Or.inr rfl) hq P S hE
      · exact k335_noStrong_psu67 hO (hc.of_mulEquiv e) (Or.inr rfl) hq P S hE
      · exact k335_noStrong_omega7 hO (hc.of_mulEquiv e) hp P S hE
    · rw [(hSO G).2.2.2.2.2 (Nonempty.map e.symm.trans hc)] at hdvd
      norm_num at hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
