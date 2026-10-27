module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherKit
import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
import CFSG.LocalAnalysis.SectionRank.EvenCover.Symplectic
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
import CFSG.Models.PGLOrders
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)

namespace Item434SmallTwoOther

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem not_isPerfect_perm_six : ¬ Group.IsPerfect (Equiv.Perm (Fin 6)) := by
  intro hp
  have hle : commutator (Equiv.Perm (Fin 6)) ≤ (Equiv.Perm.sign : Equiv.Perm (Fin 6) →* ℤˣ).ker :=
    Abelianization.commutator_subset_ker _
  have hmem : Equiv.swap (0 : Fin 6) 1 ∈ commutator (Equiv.Perm (Fin 6)) := by
    rw [hp.1]
    exact Subgroup.mem_top _
  have h1 := MonoidHom.mem_ker.mp (hle hmem)
  rw [Equiv.Perm.sign_swap (by decide)] at h1
  exact absurd h1 (by decide)

theorem false_of_sp42 (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSp 2 (GaloisField 2 1)) : False := by
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  have hperf : Group.IsPerfect (layer G ⧸ Subgroup.center (layer G)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center (layer G)))
      (QuotientGroup.mk'_surjective _)
  let ψ : StatedProj (StatedSp 2 (GaloisField 2 1)) ≃* StatedSp 2 (GaloisField 2 1) :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSp_eq_bot 2)).trans
      QuotientGroup.quotientBot
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  obtain ⟨ω⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm
    (k := GaloisField 2 1)
    (by rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 one_ne_zero, pow_one])
  let θ := ((e₀.trans (projSpEquivStatedProj 2 (GaloisField 2 1))).trans ψ).trans ω
  exact not_isPerfect_perm_six (Group.IsPerfect.ofSurjective (f := θ.toMonoidHom) θ.surjective)

theorem card_projSU_three_two_two : Nat.card (projSU 3 2 2) = 62400 :=
  CFSG.PGLModel.card_projSU_three_four

theorem not_three_dvd_card_outer_projSU_three_two_two :
    ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (projSU 3 2 2)) :=
  fun h3 => by
    have := h3.trans (card_outer_projSU_dvd 3 2 2 (by norm_num) le_rfl (by norm_num))
    norm_num at this

theorem false_of_u34 (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSU 3 2 2) : False := by
  have : Finite (projSU 3 2 2) :=
    Nat.finite_of_card_ne_zero (by rw [card_projSU_three_two_two]; norm_num)
  exact false_of_not_nine_dvd h e₀ not_three_dvd_card_outer_projSU_three_two_two
    (by rw [card_projSU_three_two_two]; norm_num)

end Item434SmallTwoOther

open Item434SmallTwoOther

section Families


theorem item434SmallTwoOtherAtSp42 : Item434SmallTwoOtherAtSp42 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨e₀⟩ := hL
  exact (false_of_sp42 hc e₀).elim

theorem item434SmallTwoOtherAtG22 : Item434SmallTwoOtherAtG22 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨q, hq2, hq1, hv, -⟩ := hL
  exfalso
  have h3 : 3 ≤ q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  rw [TauCeti.PrimePower.card_def, hq2, hq1] at h3
  omega

theorem item434SmallTwoOtherAtU34 : Item434SmallTwoOtherAtU34 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨e₀⟩ := hL
  exact (false_of_u34 hc e₀).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
