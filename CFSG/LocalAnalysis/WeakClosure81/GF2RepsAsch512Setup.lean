module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Constrained
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN1
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_isSolvable_quot {H R : Subgroup G} (hRH : R ≤ H)
    (hRs : Group.IsSolvable ↥R)
    (hY : Group.IsSolvable (↥H ⧸ (R.subgroupOf H).normalCore)) : Group.IsSolvable ↥H := by
  have hle : (R.subgroupOf H).normalCore ≤ R.subgroupOf H := Subgroup.normalCore_le _
  let f : ↥(R.subgroupOf H).normalCore →* ↥R :=
    (Subgroup.subgroupOfEquivOfLe hRH).toMonoidHom.comp (Subgroup.inclusion hle)
  have hf : Function.Injective f :=
    (Subgroup.subgroupOfEquivOfLe hRH).injective.comp (Subgroup.inclusion_injective hle)
  haveI : Group.IsSolvable ↥(R.subgroupOf H).normalCore :=
    Group.isSolvable_of_isSolvable_injective hf
  exact Group.isSolvable_of_subgroup_quotient (R.subgroupOf H).normalCore

theorem isCompositionFactor_self_of_normal {Y : Type} [Group Y] (E : Subgroup Y) [E.Normal]
    (hE : IsSimpleGroup ↥E) : E1.IsCompositionFactor Y ↥E :=
  CFSG.Quasithin.H13.L829N.isCompositionFactor_of_subnormal_surjection
    (inferInstance : E.Normal).isSubnormal hE (MonoidHom.id ↥E) Function.surjective_id

theorem one_le_pRank_three_of_three_dvd {X : Type} [Group X] [Finite X]
    (h : 3 ∣ Nat.card X) : 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 h
  have hE : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers x) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨_, i, rfl⟩ := a
      obtain ⟨_, j, rfl⟩ := b
      exact Subtype.ext (zpow_mul_comm x i j)
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx,
        pow_orderOf_eq_one, one_zpow]
  have hc : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  exact CFSG.AGLEmbeddingD2.le_pRank_of_isElemAbelian_of_pow_le_card Nat.prime_three hE le_top
    (by rw [hc]; norm_num)

theorem isSylowIn_top_map {H T : Subgroup G} {Y : Type} [Group Y] (π : ↥H →* Y)
    (hπ : Function.Surjective π) (hT : IsSylowIn 2 T H) :
    IsSylowIn 2 ((T.subgroupOf H).map π) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite Y := Finite.of_surjective π hπ
  let S' : Sylow 2 Y := hT.toSylow.mapSurjective hπ
  have hS' : (S' : Subgroup Y) = (T.subgroupOf H).map π := by
    simp only [S', Sylow.coe_mapSurjective, IsSylowIn.coe_toSylow]
  rw [← hS']
  exact ⟨le_top, S'.isPGroup', by rw [Subgroup.relIndex_top_right]; exact S'.not_dvd_index⟩

theorem lt_top_of_isSylowIn_of_not_isSolvable {Y : Type} [Group Y] [Finite Y] {Tb : Subgroup Y}
    (hT : IsSylowIn 2 Tb ⊤) (hns : ¬ Group.IsSolvable Y) : Tb < ⊤ := by
  refine lt_top_iff_ne_top.2 fun h => hns ?_
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 Y := by
    have h2 := hT.isPGroup
    rw [h] at h2
    exact h2.of_equiv Subgroup.topEquiv
  haveI := hp.isNilpotent
  infer_instance

end CFSG.LocalAnalysis.WeakClosure81

end
