module

public import CFSG.RankThree.PartTwo.Census.Exceptional.Minuscule
public import CFSG.Adapters.TauCetiExceptional.MinusculeE6
public import CFSG.Adapters.TauCetiExceptional.MinusculeE7
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.RankThree.PartTwo.Census.Exceptional.Basic

public section

namespace CFSG.RankThree.PartTwo.Census.Exceptional

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.TauCetiBridge.Minuscule
  TauCeti
open scoped MatrixGroups

section E6

variable (d : TypeE6LieIndex)

@[expose] noncomputable def e6Embed :
    ↥(e6Data_valid.minGroup d.1.fixedField) →* ↥(fixedSubgroup d.steinberg) :=
  (((E6Minuscule.pointsPresentation d.1.fixedField).map
      (E6Minuscule.pointsPresentation d.1.Closure) d.1.fixedField.subtype).comp
    (((toMat e6Match.lab d.1.fixedField).toMonoidHom.comp
      (e6Data_valid.minGroup d.1.fixedField).subtype).codRestrict
        (E6Minuscule.points d.1.fixedField)
        fun g => e6_toMat_mem_points d.1.fixedField g)).codRestrict
    (fixedSubgroup d.steinberg) fun g =>
      (TypeE6LieIndex.mem_fixedSubgroup_steinberg_iff d _).2 fun r c => by
        rw [MonoidHom.comp_apply, TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map_apply]
        exact Subtype.prop _

theorem e6Embed_injective : Function.Injective (e6Embed d) := by
  intro g g' h
  have h1 := congrArg (fun x : ↥(fixedSubgroup d.steinberg) => (x : d.AmbientGroup)) h
  have h2 := TauCeti.GeneralLinear.IntegralPointsPresentation.map_injective _ _
    (f := d.1.fixedField.subtype) Subtype.val_injective h1
  exact Subtype.val_injective ((toMat e6Match.lab d.1.fixedField).injective
    (congrArg Subtype.val h2))

end E6

section E7

variable (d : TypeE7LieIndex)

@[expose] noncomputable def e7Embed :
    ↥(e7Data_valid.minGroup d.1.fixedField) →* ↥(fixedSubgroup d.steinberg) :=
  (((E7Minuscule.pointsPresentation d.1.fixedField).map
      (E7Minuscule.pointsPresentation d.1.Closure) d.1.fixedField.subtype).comp
    (((toMat e7Match.lab d.1.fixedField).toMonoidHom.comp
      (e7Data_valid.minGroup d.1.fixedField).subtype).codRestrict
        (E7Minuscule.points d.1.fixedField)
        fun g => e7_toMat_mem_points d.1.fixedField g)).codRestrict
    (fixedSubgroup d.steinberg) fun g =>
      (TypeE7LieIndex.mem_fixedSubgroup_steinberg_iff d _).2 fun r c => by
        rw [MonoidHom.comp_apply, TauCeti.GeneralLinear.IntegralPointsPresentation.coe_map_apply]
        exact Subtype.prop _

theorem e7Embed_injective : Function.Injective (e7Embed d) := by
  intro g g' h
  have h1 := congrArg (fun x : ↥(fixedSubgroup d.steinberg) => (x : d.AmbientGroup)) h
  have h2 := TauCeti.GeneralLinear.IntegralPointsPresentation.map_injective _ _
    (f := d.1.fixedField.subtype) Subtype.val_injective h1
  exact Subtype.val_injective ((toMat e7Match.lab d.1.fixedField).injective
    (congrArg Subtype.val h2))

end E7

theorem neighbour_cartan_E6 (j : Fin (Tag.rank .E6)) : ∃ l, Tag.cartan .E6 j l = -1 :=
  (by decide : ∀ j : Fin (Tag.rank .E6), ∃ l : Fin (Tag.rank .E6),
    (Tag.cartan .E6).transpose l j = -1) j

theorem neighbour_cartan_E7 (j : Fin (Tag.rank .E7)) : ∃ l, Tag.cartan .E7 j l = -1 :=
  (by decide : ∀ j : Fin (Tag.rank .E7), ∃ l : Fin (Tag.rank .E7),
    (Tag.cartan .E7).transpose l j = -1) j

theorem fieldOrder_ne_two_iff (q : PrimePower) :
    q.card ≠ 2 ↔ ¬ (q.p = 2 ∧ q.exponent = 1) := by
  rw [PrimePower.card_def]
  constructor
  · rintro h ⟨h1, h2⟩
    exact h (by rw [h1, h2, pow_one])
  · rintro h hc
    have hp2 : q.p = 2 := by
      rcases Nat.prime_two.eq_one_or_self_of_dvd q.p
        (hc ▸ dvd_pow_self q.p q.exponent_pos.ne') with h1 | h1
      · exact absurd h1 q.prime_p.one_lt.ne'
      · exact h1
    refine h ⟨hp2, ?_⟩
    rw [hp2] at hc
    exact Nat.pow_right_injective (le_refl 2) (hc.trans (pow_one 2).symm)

theorem four_le_twoLocalOddRank_e6Index (d : TypeE6LieIndex) (hq : d.1.fieldOrder ≠ 2)
    [Finite (FixedPointCandidate d.steinberg)] :
    4 ≤ CFSG.twoLocalOddRank (FixedPointCandidate d.steinberg) := by
  have : Fintype d.1.fixedField := Fintype.ofFinite _
  have hC : commutator ↥(e6Data_valid.minGroup d.1.fixedField) = ⊤ :=
    (CFSG.LieType.CurtisTits.isQuasisimple_e6 d.1.fixedField).1.commutator_eq_top
  obtain ⟨ρ, hinj, hcomm, hcen⟩ := exists_commuting_minuscule_SL2 e6Data_valid d.1.fixedField
    neighbour_cartan_E6 ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1],
      ![1, 2, 2, 3, 2, 1]] (by decide +kernel)
  refine four_le_twoLocalOddRank_of_four_commuting_SL2 (K := d.1.fixedField) ?_
    (fun i => (toQuot (e6Embed d) hC).comp (ρ i))
    (fun i => toQuot_comp_injective (e6Embed_injective d) hC (ρ i) (hcen i))
    (fun i j hij A B => ?_)
  · rw [← Nat.card_eq_fintype_card, ValidLieTypeIndex.card_fixedField]
    exact hq
  · simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]

theorem four_le_twoLocalOddRank_E6_of_ne_two (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid)
    (hq : q.card ≠ 2) [hfin : Finite (CFSGIndex.lie ⟨.E6 q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.E6 q, hv⟩).Group :=
  @four_le_twoLocalOddRank_e6Index ⟨⟨.E6 q, hv⟩, (LieTypeIndex.isTypeE6_iff _).2 trivial⟩
    (by change (LieTypeIndex.E6 q).fieldOrder ≠ 2; rw [LieTypeIndex.fieldOrder_E6]; exact hq) hfin

theorem four_le_twoLocalOddRank_e7Index (d : TypeE7LieIndex)
    [Finite (FixedPointCandidate d.steinberg)] :
    4 ≤ CFSG.twoLocalOddRank (FixedPointCandidate d.steinberg) := by
  have : Fintype d.1.fixedField := Fintype.ofFinite _
  have hC : commutator ↥(e7Data_valid.minGroup d.1.fixedField) = ⊤ :=
    (CFSG.LieType.CurtisTits.isQuasisimple_e7 d.1.fixedField).1.commutator_eq_top
  have hcard : Fintype.card d.1.fixedField = d.1.fieldOrder := by
    rw [← Nat.card_eq_fintype_card, ValidLieTypeIndex.card_fixedField]
  by_cases hq : d.1.fieldOrder = 2
  · obtain ⟨ρ, hinj, hcomm, hcen⟩ := exists_commuting_minuscule_SL2 e7Data_valid d.1.fixedField
      neighbour_cartan_E7 ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1], ![2, 2, 3, 4, 3, 2, 1]]
      (by decide +kernel)
    refine four_le_twoLocalOddRank_of_five_commuting_SL2 (K := d.1.fixedField) ?_
      (fun i => (toQuot (e7Embed d) hC).comp (ρ i))
      (fun i => toQuot_comp_injective (e7Embed_injective d) hC (ρ i) (hcen i))
      (fun i j hij A B => ?_)
    · refine (FiniteField.even_card_iff_char_two (F := d.1.fixedField)).2 ?_
      rw [hcard, hq]
    · simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]
  · obtain ⟨ρ, hinj, hcomm, hcen⟩ := exists_commuting_minuscule_SL2 e7Data_valid d.1.fixedField
      neighbour_cartan_E7 ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0],
        ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1]] (by decide +kernel)
    refine four_le_twoLocalOddRank_of_four_commuting_SL2 (K := d.1.fixedField) (hcard ▸ hq)
      (fun i => (toQuot (e7Embed d) hC).comp (ρ i))
      (fun i => toQuot_comp_injective (e7Embed_injective d) hC (ρ i) (hcen i))
      (fun i j hij A B => ?_)
    simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]

theorem four_le_twoLocalOddRank_E7 (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid)
    [hfin : Finite (CFSGIndex.lie ⟨.E7 q, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.E7 q, hv⟩).Group :=
  @four_le_twoLocalOddRank_e7Index ⟨⟨.E7 q, hv⟩, (LieTypeIndex.isTypeE7_iff _).2 trivial⟩ hfin

end CFSG.RankThree.PartTwo.Census.Exceptional
