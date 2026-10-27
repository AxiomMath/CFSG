module

public import CFSG.Sporadic.Recognition.YCoverDouble
public import CFSG.YGroups.Exact.Y332
public import Certificates.Certificate24050

public section

namespace CFSG.Sporadic.Recognition.Fi22Multiplier

open CFSG.Certificates.CosetEnumeration (evalWord)
open CFSG.YGroups (YGroup yGen ngen spiderWord yRels evalWord_yGen_332_eq_iff
  evalWord_yGen_332_eq_one_iff card_y332)
open CFSG.Sporadic.Recognition.YCover

set_option maxRecDepth 100000 in
@[expose] def flagData332 : FlagData 3 3 2 where
  u := 6
  v₀ := 0
  Fw := fw332
  t₁ := 0
  t₂ := 3
  t₃ := 8
  q₁ := 3
  q₂ := 4
  q₃ := 6
  q₄ := 8
  parent_edge := by decide
  edges_parent := by decide
  reach := by decide
  base := by decide
  Fw_odd := by decide
  Fw_lt := by decide
  Fw_nonadj := by decide
  triple := by decide
  quad := by decide
  spider_mem := by decide
  spider_lt := by decide
  even_rels := by decide

theorem y332Conj_lt : ∀ c ∈ y332Conj, c < ngen 3 3 2 := by decide

theorem y332_I1 :
    evalWord (yGen 3 3 2)
      (List.replicate 3 ((List.replicate 5 (spiderWord 3 3)).flatten ++ [0])).flatten = 1 := by
  rw [evalWord_yGen_332_eq_one_iff]
  exact Certificates.certificate24050.1

theorem y332_I2 :
    evalWord (yGen 3 3 2) (y332Conj.reverse ++ [0, 3, 8] ++ y332Conj) =
      evalWord (yGen 3 3 2) ([3, 4, 6, 8] ++ f332Word) := by
  rw [evalWord_yGen_332_eq_iff]
  exact Certificates.certificate24050.2.1

open CFSG.Sporadic.Recognition.YCover in
@[expose] noncomputable def F332 : YGroup 3 3 2 := evalWord (yGen 3 3 2) fw332 ^ 9

theorem F332_eq : F332 = evalWord (yGen 3 3 2) f332Word := by
  rw [f332Word, evalWord_replicate_flatten']
  rfl

abbrev R332 : Type := QuotY 3 3 2 F332

theorem F332_ne_one :
    F332 ≠ 1 := by
  rw [F332_eq, Ne, evalWord_yGen_332_eq_one_iff, Certificates.certificate24050.2.2]
  simp

theorem card_R332_le :
    Finite R332 ∧ Nat.card R332 ≤ 2 * 64561751654400 := by
  have hfin : Finite (YGroup 3 3 2) := Nat.finite_of_card_ne_zero (by rw [card_y332]; norm_num)
  set N := Subgroup.normalClosure ({F332} : Set (YGroup 3 3 2)) with hN
  have hne : N ≠ ⊥ := fun h => F332_ne_one (by
    have : F332 ∈ N := Subgroup.subset_normalClosure rfl
    rw [h] at this
    exact (Subgroup.mem_bot.1 this))
  have hN2 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).2 hne
  have h := N.card_eq_card_quotient_mul_card_subgroup
  rw [card_y332] at h
  refine ⟨inferInstance, ?_⟩
  change Nat.card (YGroup 3 3 2 ⧸ N) ≤ _
  have h2 : Nat.card (YGroup 3 3 2 ⧸ N) * 2 ≤ 258247006617600 := by
    rw [h]; exact Nat.mul_le_mul_left _ hN2
  omega

theorem noPerfectDoubleCover_R332 :
    CFSG.Monster.Schur.NoPerfectDoubleCover R332 := by
  obtain ⟨hY, h1⟩ := identities_of_Y flagData332 (F := F332) rfl (MonoidHom.id R332) y332Conj
    y332_I2 y332_I1
  exact noPerfectDoubleCover_quot flagData332 (F := F332) rfl y332Conj_lt hY h1

end CFSG.Sporadic.Recognition.Fi22Multiplier
