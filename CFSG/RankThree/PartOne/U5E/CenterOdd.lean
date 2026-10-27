module

public import CFSG.RankThree.PartOne.U5E.Refl
public import CFSG.RankThree.PartOne.K159.PerfNormalizerFive
public import CFSG.RankThree.PartOne.S11c.Sec68
import CFSG.RankThree.PartTwo.Sec21.Item229Orders

public section

namespace CFSG.RankThree.PartOne.U5E

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.U5K
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem card_center_lieGenerated_dvd_five
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hEin : U5EInndiag) (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) :
    Nat.card ↥(Subgroup.center ↥(lieGenerated p E)) ∣ 5 := by
  obtain ⟨f, hf, hpf, ⟨e⟩, -⟩ := id hout
  have hperf : Group.IsPerfect ↥(lieGenerated p E) :=
    K159.isPerfect_lieGenerated_five hEin h15 hF hout
  have hsimple : IsSimpleGroup (↥(lieGenerated p E) ⧸ Subgroup.center ↥(lieGenerated p E)) := by
    have := u5_isSimpleGroup f hf
    exact e.isSimpleGroup
  have hnab : ∃ a b : ↥(lieGenerated p E) ⧸ Subgroup.center ↥(lieGenerated p E), a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hq := isPerfect_quotient e hf
    have h1 : commutator (↥(lieGenerated p E) ⧸ Subgroup.center ↥(lieGenerated p E)) = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact h y x
    have h2 := hq.commutator_eq_top
    rw [h1] at h2
    have := hsimple.toNontrivial
    exact bot_ne_top h2
  have hquasi : CFSG.IsQuasisimple ↥(lieGenerated p E) := ⟨hperf, hsimple, hnab⟩
  have hmod : StatedClassicalModel
      (↥(lieGenerated p E) ⧸ Subgroup.center ↥(lieGenerated p E)) .PSU 5 2 f :=
    statedClassicalModel_of_equiv e.symm
      (CFSG.RankThree.PartTwo.Sec21.statedClassicalModel_projSU (by norm_num) hf)
  have hdvd := card_center_dvd_of_model hGA hquasi hmod
  refine hdvd.trans ?_
  simp only [CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders]
  simpa using Nat.gcd_dvd_left 5 (2 ^ f + 1)

theorem u5CenterOddFive_of_griess
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hEin : U5EInndiag) : U5CenterOddFive := by
  intro G _ _ p A c L E h15 hF hout _ _ h2
  have := card_center_lieGenerated_dvd_five hGA hEin h15 hF hout
  have h25 : 2 ∣ 5 := h2.trans this
  omega

omit [Finite G] in
theorem card_center_eq_card_inf (I : Subgroup G) :
    Nat.card ↥(Subgroup.center ↥I) = Nat.card ↥(I ⊓ Subgroup.centralizer (I : Set G)) := by
  have h : (Subgroup.center ↥I).map I.subtype = I ⊓ Subgroup.centralizer (I : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hy ⟨g, hg⟩)
    · rintro ⟨hxI, hxc⟩
      refine ⟨⟨x, hxI⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc g g.2)
  rw [← h, Subgroup.card_map_of_injective I.subtype_injective]

theorem center_lieGenerated_eq_bot_five
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hEin : U5EInndiag) (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) (hp5 : p = 5) :
    Subgroup.center ↥(lieGenerated p E) = ⊥ := by
  have hdvd := card_center_lieGenerated_dvd_five hGA hEin h15 hF hout
  have hnd := K159.not_dvd_inf_centralizer_five hEin h15 hF hout
  rw [← card_center_eq_card_inf] at hnd
  have hnd' : ¬ 5 ∣ Nat.card ↥(Subgroup.center ↥(lieGenerated p E)) := by
    rw [← hp5]
    exact hnd
  rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h1 | h5
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exact absurd (by rw [h5]) hnd'

end CFSG.RankThree.PartOne.U5E
