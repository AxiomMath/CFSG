module

public import CFSG.RankThree.GF2n.Stroth80.Conclusion

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

section QuotIncl

variable {M Q S : Subgroup G} [(Q.subgroupOf M).Normal] [(Q.subgroupOf S).Normal]

@[expose] def quotIncl (hSM : S ≤ M) : (↥S ⧸ Q.subgroupOf S) →* (↥M ⧸ Q.subgroupOf M) :=
  QuotientGroup.map (Q.subgroupOf S) (Q.subgroupOf M) (Subgroup.inclusion hSM) fun _ hx => hx

theorem quotIncl_mk (hSM : S ≤ M) (x : ↥S) :
    quotIncl (Q := Q) hSM (QuotientGroup.mk x) = QuotientGroup.mk (Subgroup.inclusion hSM x) :=
  rfl

theorem quotIncl_injective (hSM : S ≤ M) : Function.Injective (quotIncl (Q := Q) hSM) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  induction a using QuotientGroup.induction_on with
  | H x =>
    rw [quotIncl_mk, QuotientGroup.eq_one_iff] at ha
    exact (QuotientGroup.eq_one_iff x).mpr ha

theorem quotIncl_range (hSM : S ≤ M) : (quotIncl (Q := Q) hSM).range = bar M Q S := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    induction a using QuotientGroup.induction_on with
    | H x =>
      exact ⟨Subgroup.inclusion hSM x, x.2, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨QuotientGroup.mk ⟨m.1, hm⟩, rfl⟩

end QuotIncl

end CFSG.RankThree.GF2n.Smith81
