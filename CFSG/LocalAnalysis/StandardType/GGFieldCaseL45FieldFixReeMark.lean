module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherCore
import CFSG.LieType.Simplicity.ReeLargeModel
import CFSG.LieType.Simplicity.TitsModel
import CFSG.RankThree.PartTwo.KFacts.KS14SzRee
import CFSG.LieType.Ree.LargeReeCenterTrivial
import CFSG.LieType.Ree.ReeGenericPerfect
import CFSG.LieType.Ree.LargeReeFixedGroupOddCore
import CFSG.LieType.BorelTits.DerivedQuotient

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree

private theorem gff_commutator_self {G : Type*} [Group G] {H : Subgroup G}
    (h : commutator H = ⊤) : ⁅H, H⁆ = H := by
  have h1 : (⊤ : Subgroup H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← h1, ← Subgroup.map_commutator, ← commutator_def, h]

private theorem gff_exists_ne_comm_of_isPerfect {X : Type*} [Group X] [Nontrivial X]
    (hX : Group.IsPerfect X) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hab
  push Not at hab
  have hc : commutator X = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hab y x
  rw [hX.commutator_eq_top] at hc
  exact top_ne_bot hc

section Ree

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem gff_commutator_reeFixedGroup (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ⁅reeFixedGroup Tag.F4 K reeF4Perm
        (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)),
      reeFixedGroup Tag.F4 K reeF4Perm
        (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1))⁆ =
      ReeTag.F4.reeGamma K a := by
  have h2 : ReeTag.F4.reeGamma K a = reeFixedGroup Tag.F4 K reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)) :=
    ReeTag.reeGamma_eq_reeFixedGroup
  rw [← h2]
  exact gff_commutator_self (ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) ha hK)

theorem gff_nonempty_centerQuot_equiv_reeGamma (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nonempty (LargeEvenCenterQuot (LargeEvenTwF4H a K) ≃* ↥(ReeTag.F4.reeGamma K a)) := by
  obtain ⟨e₁⟩ := centerQuot_twF4H_equiv K a
  obtain ⟨e₂⟩ := nonempty_centerQuot_congr (gff_commutator_reeFixedGroup ha hK)
  exact ⟨e₁.trans (e₂.trans
    (centerQuotEquivOfBot (ReeTag.large_Ree_fixed_group_center_trivial a K hK)))⟩

theorem gff_isSimpleGroup_reeGamma {b : ℕ} (hb : 1 ≤ b) {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    IsSimpleGroup ↥(ReeTag.F4.reeGamma k b) := by
  set e := ReeTag.reeFixedEquivReeGamma k b
  have hZ : Subgroup.center (reeFixed ReeTag.F4 k b) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center (ReeTag.F4.reeGamma k b) :=
      (MulEquivClass.apply_mem_center_iff e).2 hz
    rw [ReeTag.large_Ree_fixed_group_center_trivial b k hk, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 (e.injective (hz'.trans (map_one e).symm))
  have : IsSimpleGroup (reeFixed ReeTag.F4 k b ⧸ Subgroup.center (reeFixed ReeTag.F4 k b)) :=
    CFSG.LieType.Simplicity.isSimpleGroup_quotient_center_reeFixed_F4 b hb hk
  have hs : IsSimpleGroup (reeFixed ReeTag.F4 k b) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  exact e.symm.isSimpleGroup

theorem gff_marking_reeGamma {b : ℕ} (hb : 1 ≤ b) {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    LargeEvenMarking ↥(ReeTag.F4.reeGamma k b) fun lab _ _ _ _ _ => GGL45TorsionTag lab := by
  have hs := gff_isSimpleGroup_reeGamma hb hk
  have hperf : Group.IsPerfect ↥(ReeTag.F4.reeGamma k b) :=
    ⟨ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb hk⟩
  obtain ⟨eR⟩ := gff_nonempty_centerQuot_equiv_reeGamma hb hk
  have hZ := ReeTag.large_Ree_fixed_group_center_trivial b k hk
  have hsimple : IsSimpleGroup (LargeEvenCenterQuot (LargeEvenTwF4H b k)) := eR.isSimpleGroup
  have hnab : ∃ x y : LargeEvenCenterQuot (LargeEvenTwF4H b k), x * y ≠ y * x :=
    nonabelian_of_mulEquiv eR.symm (gff_exists_ne_comm_of_isPerfect hperf)
  have hraw : LargeEvenRawDatum (⟨.twF4, 0, 2 * b + 1⟩ : LargeEvenLabel)
      fun R _ I F => IsSimpleGroup R ∧ (∃ x y : R, x * y ≠ y * x) ∧
        ∃ θ : ↥(ReeTag.F4.reeGamma k b) ⧸ Subgroup.center ↥(ReeTag.F4.reeGamma k b) ≃* R,
          GGL45TorsionTag (⟨.twF4, 0, 2 * b + 1⟩ : LargeEvenLabel) := by
    have hb' : (2 * b + 1 - 1) / 2 = b := by omega
    dsimp only [LargeEvenRawDatum]
    rw [hb']
    exact ⟨k, inferInstance, inferInstance, hk, hsimple, hnab,
      (centerQuotEquivOfBot hZ).trans eR.symm, Or.inr (Or.inr (Or.inl rfl))⟩
  have hlab : LargeEvenInLambda2 (⟨.twF4, 0, 2 * b + 1⟩ : LargeEvenLabel) := by
    refine ⟨?_, rfl, ⟨b, rfl⟩, ?_⟩ <;> (dsimp only; omega)
  exact ⟨hperf.commutator_eq_top, ⟨.twF4, 0, 2 * b + 1⟩, hlab, hraw⟩

end Ree

section Tits

variable {k : Type} [Field k] [Finite k] [CharP k ReeTag.F4.prime]

theorem gff_isSimpleGroup_tits (hk : Nat.card k = 2) :
    IsSimpleGroup ↥(commutator ↥(reeFixed ReeTag.F4 k 0)) := by
  set D := commutator ↥(reeFixed ReeTag.F4 k 0)
  have : IsSimpleGroup (D ⧸ Subgroup.center D) :=
    ((CFSG.LieType.Simplicity.titsData k hk).isQuasisimple hk).2.1
  have hZD : Subgroup.center D = ⊥ :=
    CFSG.RankThree.PartTwo.KFacts.KS14.center_commutator_reeFixed_tits_eq_bot hk
  exact ((QuotientGroup.quotientMulEquivOfEq hZD).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

theorem gff_marking_tits (hk : Nat.card k = 2) :
    LargeEvenMarking ↥(commutator ↥(reeFixed ReeTag.F4 k 0))
      fun lab _ _ _ _ _ => GGL45TorsionTag lab := by
  have hq := (CFSG.LieType.Simplicity.titsData k hk).isQuasisimple hk
  obtain ⟨e₁⟩ := centerQuot_twF4H_equiv k 0
  have e₂ := CFSG.LieType.BorelTits.derivedCentralQuotientEquiv _
    ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed ReeTag.F4 k 0)).trans
      ((reeFixed ReeTag.F4 k 0).equivMapOfInjective _ Subtype.val_injective).symm)
  have eR := e₁.trans e₂
  have hsimple : IsSimpleGroup (LargeEvenCenterQuot (LargeEvenTwF4H 0 k)) := by
    have := hq.2.1
    exact eR.isSimpleGroup
  have hnab : ∃ x y : LargeEvenCenterQuot (LargeEvenTwF4H 0 k), x * y ≠ y * x :=
    nonabelian_of_mulEquiv eR.symm hq.2.2
  have hraw : LargeEvenRawDatum (⟨.twF4der, 0, 1⟩ : LargeEvenLabel)
      fun R _ I F => IsSimpleGroup R ∧ (∃ x y : R, x * y ≠ y * x) ∧
        ∃ θ : ↥(commutator ↥(reeFixed ReeTag.F4 k 0)) ⧸
            Subgroup.center ↥(commutator ↥(reeFixed ReeTag.F4 k 0)) ≃* R,
          GGL45TorsionTag (⟨.twF4der, 0, 1⟩ : LargeEvenLabel) := by
    dsimp only [LargeEvenRawDatum]
    exact ⟨k, inferInstance, inferInstance, by simpa using hk, hsimple, hnab, eR.symm,
      Or.inr (Or.inr (Or.inr rfl))⟩
  exact ⟨hq.1.commutator_eq_top, ⟨.twF4der, 0, 1⟩, ⟨le_rfl, rfl, rfl⟩, hraw⟩

end Tits

end CFSG.StandardType
