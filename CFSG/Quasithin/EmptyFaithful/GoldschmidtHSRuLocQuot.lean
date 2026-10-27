module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtHSRuLocSimple
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuSimple
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.HSRuLoc.Mod

open CFSG.Quasithin CFSG.Quasithin.A312Ru

variable {H : Type} [Group H]

theorem isPerfect_of_comm_eq_self {K : Subgroup H} (h : ⁅K, K⁆ = K) : Group.IsPerfect ↥K := by
  rw [Group.isPerfect_def]
  have h1 : (commutator ↥K).map K.subtype = ⁅K, K⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have h2 : (commutator ↥K).map K.subtype = (⊤ : Subgroup ↥K).map K.subtype := by
    rw [h1, h, Subgroup.map_top, Subgroup.range_subtype]
  exact Subgroup.map_injective K.subtype_injective h2

theorem nonempty_statedSL_of_isPSL {X : Type} [Group X] (h : IsPSL 3 2 1 X) :
    Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) := by
  obtain ⟨-, F, _, _, hcard, ⟨e₀⟩⟩ := h
  exact ⟨(e₀.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 3 F
    (by rw [hcard]; norm_num))).trans
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2))⟩

variable [Finite H]

theorem hsru_quot {K R : Subgroup H} (hRK : R ≤ K) (hRn : (R.subgroupOf K).Normal)
    (hK : ⁅K, K⁆ = K) (hcard : Nat.card K = 168 * Nat.card R) :
    IsSimpleGroup (↥K ⧸ R.subgroupOf K) ∧
      ∃ a : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)),
        Function.Surjective a ∧ a.ker = R.subgroupOf K := by
  have hNc : Nat.card (R.subgroupOf K) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv
  have hQ : Nat.card (↥K ⧸ R.subgroupOf K) = 168 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (R.subgroupOf K)
    rw [hNc, hcard] at h
    have hpos : 0 < Nat.card R := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hpos h).symm
  have : Group.IsPerfect ↥K := isPerfect_of_comm_eq_self hK
  have hperf : Group.IsPerfect (↥K ⧸ R.subgroupOf K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (R.subgroupOf K))
      (QuotientGroup.mk'_surjective _)
  have hns : ¬ Group.IsSolvable (↥K ⧸ R.subgroupOf K) := by
    intro hs
    have hnt : Nontrivial (↥K ⧸ R.subgroupOf K) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hQ]; norm_num)
    have := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥K ⧸ R.subgroupOf K)
    rw [Group.IsPerfect.commutator_eq_top] at this
    exact lt_irrefl _ this
  have hsimple : IsSimpleGroup (↥K ⧸ R.subgroupOf K) := isSimpleGroup_of_card_168 hQ hns
  obtain ⟨e⟩ := nonempty_statedSL_of_isPSL (isPSL_three_two_of_simple_card_168 hQ)
  refine ⟨hsimple, e.toMonoidHom.comp (QuotientGroup.mk' (R.subgroupOf K)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

end CFSG.Quasithin.HSRuLoc.Mod
