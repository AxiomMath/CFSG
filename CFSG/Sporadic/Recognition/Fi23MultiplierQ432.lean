module

public import CFSG.Sporadic.Recognition.YCoverPerfect
public import CFSG.Sporadic.Recognition.YCoverDouble
public import CFSG.Monster.GMS.R433Cover.Y432Identities
public import CFSG.YGroups.Model432F

public section

namespace CFSG.Sporadic.Recognition.Fi23Multiplier

open CFSG.Certificates.CosetEnumeration (evalWord)
open CFSG.YGroups (YGroup yGen ngen spiderWord F432Alt F432_eq_alt rho432F ker_rho432F_eq
  card_range_rho432F F432)
open CFSG.Monster.GMS.R433Cover (yConj yConj_lt y432_I1 y432_I2)
open CFSG.Sporadic.Recognition.YCover

set_option maxRecDepth 100000 in
@[expose] def flagData432 : FlagData 4 3 2 where
  u := 4
  v₀ := 0
  Fw := [0, 5, 6, 7, 1, 2, 8]
  t₁ := 0
  t₂ := 4
  t₃ := 6
  q₁ := 2
  q₂ := 5
  q₃ := 7
  q₄ := 9
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

abbrev R432 : Type := QuotY 4 3 2 F432Alt

theorem F432Alt_eq_pow : F432Alt = evalWord (yGen 4 3 2) flagData432.Fw ^ 9 := by
  simp only [F432Alt, flagData432, evalWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, mul_assoc]

theorem isPerfect_R432 : Group.IsPerfect R432 :=
  isPerfect_quotY flagData432 F432Alt_eq_pow

theorem noPerfectDoubleCover_R432 :
    CFSG.Monster.Schur.NoPerfectDoubleCover R432 := by
  obtain ⟨hY, h1⟩ := identities_of_Y flagData432 F432Alt_eq_pow (MonoidHom.id R432) yConj
    y432_I2 y432_I1
  exact noPerfectDoubleCover_quot flagData432 F432Alt_eq_pow yConj_lt hY h1

theorem normalClosure_F432Alt :
    Subgroup.normalClosure {F432Alt} = rho432F.ker := by
  refine le_antisymm (Subgroup.normalClosure_le_normal ?_) ?_
  · rw [Set.singleton_subset_iff, SetLike.mem_coe, ← F432_eq_alt, ker_rho432F_eq]
    exact Subgroup.mem_zpowers _
  · rw [ker_rho432F_eq, Subgroup.zpowers_le, F432_eq_alt]
    exact Subgroup.subset_normalClosure rfl

noncomputable def r432EquivRange :
    R432 ≃* rho432F.range :=
  (QuotientGroup.quotientMulEquivOfEq normalClosure_F432Alt).trans
    (QuotientGroup.quotientKerEquivRange rho432F)

theorem card_R432 :
    Nat.card R432 = 4089470473293004800 := by
  rw [Nat.card_congr r432EquivRange.toEquiv]
  exact card_range_rho432F

end CFSG.Sporadic.Recognition.Fi23Multiplier
