module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherKit
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU42Tools
import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven
import CFSG.LocalAnalysis.SectionRank.EvenCover.Unitary
import CFSG.LocalAnalysis.SectionRank.EvenCover.CoverMap
import CFSG.Permutation.AlternatingAutomorphism
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec8.Statements
import Certificates.Kernel.SporSch.Th.Orb2315
import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSU)
open Item434Kit

namespace Item434SmallTwoOther

namespace U42

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem center_layer_eq_bot
    (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSU 4 2 1) :
    Subgroup.center (layer G) = ⊥ := by
  have hK : Nat.card (GaloisField 2 (2 * 1)) = (2 ^ 1) ^ 2 := by
    rw [GaloisField.card 2 (2 * 1) (by norm_num)]
    norm_num
  have hD := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSU_four_eq_bot
    (K := GaloisField 2 (2 * 1)) (2 ^ 1)
  let ε : StatedProj (StatedSU 4 (2 ^ 1) (GaloisField 2 (2 * 1))) ≃*
      StatedSU 4 (2 ^ 1) (GaloisField 2 (2 * 1)) :=
    (QuotientGroup.quotientMulEquivOfEq hD).trans QuotientGroup.quotientBot
  let θ : layer G ⧸ Subgroup.center (layer G) ≃* CFSG.LieType.Universal.Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) 4 :=
    e₀.trans ((projSUEquivStatedProj 4 2 1).trans
      (ε.trans (CFSG.LieType.Universal.Unitary.equivStatedSU hK 4).symm))
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  have hker : (QuotientGroup.mk' (Subgroup.center (layer G))).ker = Subgroup.center (layer G) :=
    QuotientGroup.ker_mk' _
  have hodd : Odd (Nat.card (QuotientGroup.mk' (Subgroup.center (layer G))).ker) := by
    rw [hker]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_center_layer
    rw [hk]
    exact Odd.pow (by decide)
  obtain ⟨α', hα', -⟩ := CFSG.SectionRank.EvenCover.even_su_existsUnique_lift hK (by norm_num)
    (by decide : Even 4) (QuotientGroup.mk'_surjective (Subgroup.center (layer G))) hker.le hodd
    θ.symm.toMonoidHom
  have hα'x : ∀ y, QuotientGroup.mk' (Subgroup.center (layer G)) (α' y) = θ.symm y := fun y =>
    DFunLike.congr_fun hα' y
  have htop : α'.range = ⊤ := by
    refine CFSG.SectionRank.EvenCover.eq_top_of_forall_mul_center fun x =>
      ⟨α' (θ x), ⟨_, rfl⟩, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h1 := hα'x (θ x)
    rw [QuotientGroup.mk'_apply, MulEquiv.symm_apply_apply] at h1
    rw [h1, inv_mul_cancel]
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨y, hy⟩ := htop ▸ Subgroup.mem_top z
  have h1 := hα'x y
  rw [hy, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).mpr hz] at h1
  have hy1 : y = 1 := by
    have := congrArg θ h1
    rw [map_one, MulEquiv.apply_symm_apply] at this
    exact this.symm
  rw [Subgroup.mem_bot, ← hy, hy1, map_one]

theorem false_of_U42
    (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSU 4 2 1) : False := by
  have hZ := center_layer_eq_bot h e₀
  obtain ⟨θ⟩ := nonempty_mulEquiv
  rcases h.card_layerStar with h9 | ⟨h27, -⟩
  · exact Item434Spor.false_of_card_nine h hZ (e₀.trans θ) isElemAbelian_E₀ card_E₀ h9
  · obtain ⟨P, hPe, hPc, hP⟩ := exists_inner_of_inner h (e₀.trans θ)
      (fun _ hφ => mem_range_conj_of_pow_three hφ) center_SU42
    rw [h27] at hPc
    obtain ⟨g, rfl⟩ := exists_eq_map_conj hPe hPc
    exact false_of_normalizer_conj h (e₀.trans θ) (fun _ hY hN => eq_bot_of_le_normalizer hY hN)
      (MulAut.conj g) (hP.trans (map_conj_map_conj g))

end U42

end Item434SmallTwoOther

section Families


theorem item434SmallTwoOtherAtU42 : Item434SmallTwoOtherAtU42 := by
  intro _ _ _ _ _ G _ _ _ _ _ A M Q hc hL
  obtain ⟨e⟩ := hL
  exact (Item434SmallTwoOther.U42.false_of_U42 hc e).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
