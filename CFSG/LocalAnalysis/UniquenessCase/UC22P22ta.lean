module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
import CFSG.LocalAnalysis.UniquenessCase.UC22Main1
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22qv
import CFSG.Quasithin.Background.E3Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC
open CFSG.Quasithin (IsSylowIn conjSubgroup conjSubgroup_one rk card_eq_two_pow_of_isPGroup)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (CompFactorAutInF W3Thm111 W3Lem45_2 twelve_twentyOne_two)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22p22ta_card_le {M V : Subgroup G} {k : ℕ} (h : MBarGT M ⊥ V k) : 2 ^ (k + 1) ≤ Nat.card V := by
  classical
  by_cases hex : ∃ m ∈ M, ¬ CentralizesMod ⊥ V m ∧ CentralizesMod ⊥ V (m * m)
  · obtain ⟨m, hm, h1, h2⟩ := hex
    have h3 := h.1 m hm h1 h2
    have hpos : 0 < Nat.card (centMod ⊥ V m) := by
      haveI : Nonempty (centMod ⊥ V m) := ⟨⟨1, V.one_mem, by simp⟩⟩
      exact Nat.card_pos
    calc 2 ^ (k + 1) ≤ 2 ^ (k + 1) * Nat.card (centMod ⊥ V m) := Nat.le_mul_of_pos_right _ hpos
      _ ≤ Nat.card V := h3
  · push Not at hex
    have h3 := h.2 (fun m hm h2 => by_contra fun h1 => hex m hm h1 h2)
    rwa [Subgroup.card_bot, mul_one] at h3

theorem uc22p22ta_isSylowIn (D : Data G) {X : Subgroup G} (h : D.T ≤ X) : IsSylowIn 2 D.T X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨h, D.sylowM.isPGroup, fun hdvd => ?_⟩
  have h1 := (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowG).2.2
  rw [Subgroup.relIndex_top_right] at h1
  exact h1 (hdvd.trans (Subgroup.relIndex_dvd_index_of_le h))

theorem uc22p22ta_wClos_le (V : Subgroup G) (i : ℕ) (T : Subgroup G) : CFSG.Quasithin.E3.wClos V i T ≤ T :=
  iSup₂_le fun _ hA => hA.1

theorem uc22p22ta_mem_normalizer_center {W : Subgroup G} {x : G} (hx : x ∈ normalizer (W : Set G)) :
    x ∈ normalizer ((W ⊓ centralizer (W : Set G) : Subgroup G) : Set G) := by
  have hc := uc22p22q_mem_normalizer_centralizer hx
  rw [mem_normalizer_iff]
  intro h
  exact and_congr (mem_normalizer_iff.1 hx h) (mem_normalizer_iff.1 hc h)

end CFSG.LocalAnalysis.UniquenessCase.UC22
