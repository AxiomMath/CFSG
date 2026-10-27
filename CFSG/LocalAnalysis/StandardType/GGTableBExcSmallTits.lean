module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTwF4
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsLocal

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Ree CFSG.Sporadic.Schreier.Tits
open scoped commutatorElement

namespace TableBExcSmallRest

section Tits


theorem card_lt_of_isElemAbelian_commutator_reeFixed {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2)
    {E : Subgroup (commutator (reeFixed ReeTag.F4 K 0))} (hE : IsElemAbelian 3 E) :
    Nat.card E < 3 ^ 3 := by
  have : Finite (reeFixed ReeTag.F4 K 0) :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.SectionRank.TitsOrder.Tits_card hK]; norm_num)
  obtain ⟨x, y, -, -, -, hxy, -, -, hcard, -⟩ := CFSG.SectionRank.Tits_sylow3_cubic_witness hK
  refine card_lt_of_nonabelian_isPGroup Nat.prime_three (fun h => ?_) (IsPGroup.of_card hcard)
    (Subgroup.subset_closure (Set.mem_insert x {y}))
    (Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)) (fun h => hxy ?_) hE
  · have h' := dvd_trans h (CFSG.SectionRank.TitsOrder.Tits_commutator_card_dvd hK)
    norm_num at h'
  · exact commutatorElement_eq_one_iff_mul_comm.mpr h


theorem ggTitsThreeRankInput_holds : GGTitsThreeRankInput := fun _ hE =>
  card_lt_of_mulEquiv (titsDerivedIso (K := ZMod 2)).symm
    (fun _ hA => card_lt_of_isElemAbelian_commutator_reeFixed (Nat.card_zmod 2) hA) hE

theorem largeEvenLabelAll_card_lt_twF4der_holds {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twF4der) (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 :=
  largeEvenLabelAll_card_lt_twF4der ggTitsThreeRankInput_holds hp hlab ht hs

end Tits

end TableBExcSmallRest

section Inputs


theorem ggBstarInputOn_twF4der : GGBstarInputOn fun _ lab => lab.tag = .twF4der :=
  ggBstarInputOn_of_labelAll_card_lt fun _ _ hp hlab ht hs =>
    TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4der_holds hp hlab ht hs

theorem ggStdSubPreInputOn_twF4der : GGStdSubPreInputOn fun _ lab => lab.tag = .twF4der :=
  ggStdSubPreInputOn_of_labelAll_card_lt fun _ _ hp hlab ht hs =>
    TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4der_holds hp hlab ht hs

end Inputs

end CFSG.StandardType
