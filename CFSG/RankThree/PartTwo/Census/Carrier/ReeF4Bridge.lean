module

public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Index
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Local
public import CFSG.RankThree.PartTwo.Census.Carrier.TitsCert
public import CFSG.RankThree.PartTwo.Census.Criteria
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public noncomputable section

namespace CFSG.RankThree.PartTwo.Census.Carrier.ReeF4

open TauCeti CFSG.TauCetiBridge.ReeF4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.Assembly.RankThreeEven

def derivedCentralQuotientEquivOfPerfect {G : Type*} [Group G] (hG : commutator G = ⊤)
    (hZ : Subgroup.center G = ⊥) : TauCeti.DerivedCentralQuotient G ≃* G := by
  let e₁ : ↥(commutator G) ≃* G := (MulEquiv.subgroupCongr hG).trans Subgroup.topEquiv
  have hZ' : Subgroup.center ↥(commutator G) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e₁ z ∈ Subgroup.center G :=
      Subgroup.mem_center_iff.2 fun g => by
        obtain ⟨y, rfl⟩ := e₁.surjective g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y]
    rw [hZ, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 (e₁.injective (hz'.trans (map_one e₁).symm))
  exact (QuotientGroup.quotientMulEquivOfEq hZ').trans (QuotientGroup.quotientBot.trans e₁)

theorem localRank_three_reeF4Index (d : ReeF4LieIndex) (hm : 1 ≤ d.toSuzukiReeIndex.halfExponent)
    [Finite (FixedPointCandidate d.steinberg)] :
    localRank 3 (FixedPointCandidate d.steinberg) ≤ 2 := by
  set m := d.toSuzukiReeIndex.halfExponent with hmdef
  set K := d.1.fixedField
  have : CharP K ReeTag.F4.prime := (inferInstance : CharP K 2)
  have hK : Nat.card K = 2 ^ (2 * m + 1) := card_fixedField_reeF4 d
  obtain ⟨e₁⟩ := nonempty_candidate_equiv_reeF4 d
  let e₂ : ↥(reeFixed ReeTag.F4 K m) ≃* ↥(ReeTag.F4.reeGamma K m) :=
    ((reeFixed ReeTag.F4 K m).equivMapOfInjective (adjointGroup ReeTag.F4.tag K).subtype
      Subtype.val_injective).trans
      (MulEquiv.subgroupCongr LargeReeInvolution.map_reeFixed_eq_reeGamma)
  have hperf := (ReeTag.ree_generic_fixed_group_perfect .F4 m hm K hK).2.1
  have hcen := ReeTag.large_Ree_fixed_group_center_trivial m K hK
  let e₃ : FixedPointCandidate (reeF K m) ≃* ↥(ReeTag.F4.reeGamma K m) :=
    (TauCeti.DerivedCentralQuotient.congr e₂).trans
      (derivedCentralQuotientEquivOfPerfect hperf hcen)
  rw [localRank_eq_of_mulEquiv (e₁.trans e₃) Nat.prime_three]
  exact localRank_three_reeGamma hm hK

theorem localRank_three_titsIndex (d : TitsLieIndex)
    [Finite (FixedPointCandidate d.steinberg)] :
    localRank 3 (FixedPointCandidate d.steinberg) ≤ 2 := by
  have : CharP d.1.fixedField ReeTag.F4.prime := (inferInstance : CharP d.1.fixedField 2)
  obtain ⟨e₁⟩ := nonempty_candidate_equiv_tits d
  rw [localRank_eq_of_mulEquiv e₁ Nat.prime_three]
  exact Tits.localRank_three_commutator_quotient_center (card_fixedField_tits d)

end CFSG.RankThree.PartTwo.Census.Carrier.ReeF4

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti

theorem excluded433_reeF4 (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid) :
    Excluded433 (.lie ⟨.reeF4 m, hv⟩) := by
  intro G _ _ hG e
  have : Finite (CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group := Finite.of_equiv G e.toEquiv
  have hm : 1 ≤ m := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hhalf : (ReeF4LieIndex.of m hv).toSuzukiReeIndex.halfExponent = m :=
    SuzukiReeIndex.halfExponent_reeF4 m hv
  exact hG.false_of_localRank_three_le_two e
    (@Carrier.ReeF4.localRank_three_reeF4Index (ReeF4LieIndex.of m hv) (by rw [hhalf]; exact hm)
      this)

theorem excluded433_tits (hv : LieTypeIndex.tits.Valid) : Excluded433 (.lie ⟨.tits, hv⟩) := by
  intro G _ _ hG e
  have : Finite (CFSGIndex.lie ⟨.tits, hv⟩).Group := Finite.of_equiv G e.toEquiv
  exact hG.false_of_localRank_three_le_two e
    (@Carrier.ReeF4.localRank_three_titsIndex TitsLieIndex.of this)

end CFSG.RankThree.PartTwo.Census
