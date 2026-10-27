module

public import CFSG.Quasithin.Vol2.Ch4Sec4F4411A
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DGroupQuotientNotTwoGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction
public import CFSG.Walter.J1.Local
public import CFSG.CharacterTheory.Burnside
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

public section

namespace CFSG.Quasithin.H13.Ch4.E443.F4411

open Subgroup CFSG.GorensteinWalter

variable {G : Type*} [Group G]

theorem commutator_eq_bot_of_solvable {U Y : Subgroup G} (hY : ⁅Y, Y⁆ = Y)
    (hYU : Y ≤ normalizer (U : Set G)) (hs : Group.IsSolvable (normalizer (U : Set G))) :
    ⁅U, Y⁆ = ⊥ := by
  rw [eq_bot_of_perfect_of_le hY hYU, commutator_bot_right]

theorem isSolvable_of_mulEquiv {H X : Type*} [Group H] [Group X] [Group.IsSolvable X]
    (e : H ≃* X) : Group.IsSolvable H :=
  Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem not_isPGroup_two_of_dvd {X : Type*} [Group X] [Finite X] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hd : r ∣ Nat.card X) : ¬ IsPGroup 2 X := by
  intro h
  obtain ⟨k, hk⟩ := h.exists_card_eq
  rw [hk] at hd
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd))

theorem eq_bot_of_normalizer_simple {X : Type*} [Group X] [IsSimpleGroup X] {U : Subgroup G}
    (hU : IsPGroup 2 U) (e : normalizer (U : Set G) ≃* X) (hX : ¬ IsPGroup 2 X) : U = ⊥ := by
  have : IsSimpleGroup (normalizer (U : Set G)) := e.isSimpleGroup
  have : (U.subgroupOf (normalizer (U : Set G))).Normal := normal_in_normalizer
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (U.subgroupOf (normalizer (U : Set G))) with
    h | h
  · exact (Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le le_normalizer
  · exact absurd ((hU.to_le (Subgroup.subgroupOf_eq_top.mp h)).of_equiv e) hX

theorem eq_bot_of_mulEquiv_pgl2 {H : Type} [Group H] [Finite H] {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) (e : H ≃* PGL2 K)
    {T : Subgroup H} [T.Normal] (hT : IsPGroup 2 T) : T = ⊥ := by
  have : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  set T' := T.map e.toMonoidHom
  have : T'.Normal := Subgroup.Normal.map ‹_› _ e.surjective
  set J := commutator (PGL2 K)
  obtain ⟨eJ⟩ := commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three K hK hcard
    (MulEquiv.refl (PGL2 K))
  have : IsSimpleGroup (PSL2 K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have : IsSimpleGroup J := eJ.isSimpleGroup
  have hT'J : ⁅T', J⁆ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T'.subgroupOf J) with h | h
    · exact le_bot_iff.mp ((Subgroup.commutator_le_inf T' J).trans
        (Subgroup.subgroupOf_eq_bot.mp h).le_bot)
    · exact absurd (((hT.map e.toMonoidHom).to_le (Subgroup.subgroupOf_eq_top.mp h)).of_equiv eJ)
        (not_isPGroup_two_of_psl2_odd K hK)
  have hC := pgl2_psl2Range_centralizer_eq_bot K hK
  rw [← pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard] at hC
  have hT' : T' = ⊥ :=
    le_bot_iff.mp (hC ▸ Subgroup.commutator_eq_bot_iff_le_centralizer.mp hT'J)
  exact (Subgroup.map_eq_bot_iff_of_injective T e.injective).mp hT'

theorem eq_bot_of_normalizer_pgl2 {G : Type} [Group G] [Finite G] {K : Type} [Field K]
    [Finite K] {U : Subgroup G} (hU : IsPGroup 2 U) (e : normalizer (U : Set G) ≃* PGL2 K)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) : U = ⊥ := by
  have : (U.subgroupOf (normalizer (U : Set G))).Normal := normal_in_normalizer
  exact (Subgroup.subgroupOf_eq_bot.mp (eq_bot_of_mulEquiv_pgl2 hK hcard e hU.comap_subtype)
    ).eq_bot_of_le le_normalizer

theorem perfCentral_of_jankoHyp {G : Type} [Group G] [Finite G]
    (h : CFSG.Walter.J1.JankoHyp G) : PerfCentral G := by
  intro U Y hU hY hYU
  by_cases h4 : Nat.card U ≤ 4
  · exact commutator_eq_bot_of_card_le_four h4 hY hYU
  obtain ⟨S, hUS⟩ := hU.exists_le_sylow
  obtain ⟨h8, -, hcomm, -⟩ := h.sylow_structure S
  have hUS' : U = S := by
    refine Subgroup.eq_of_le_of_card_ge hUS ?_
    have hd := Subgroup.card_dvd_of_le hUS
    rw [h8] at hd ⊢
    have h5 : 5 ≤ Nat.card U := by omega
    have h8' : Nat.card U ≤ 8 := Nat.le_of_dvd (by norm_num) hd
    interval_cases hc : Nat.card U <;> omega
  subst hUS'
  set N := normalizer ((S : Subgroup G) : Set G)
  have : ((S : Subgroup G).subgroupOf N).Normal := normal_in_normalizer
  have : Group.IsSolvable ((S : Subgroup G).subgroupOf N) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subtype.ext (hcomm a.1.1 a.2 b.1.1 b.2))
  have : Group.IsSolvable (N ⧸ (S : Subgroup G).subgroupOf N) := by
    have : Fintype (N ⧸ (S : Subgroup G).subgroupOf N) := Fintype.ofFinite _
    refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 1)
      (b := 1) Nat.prime_three (by norm_num : Nat.Prime 7) (by norm_num) ?_
    rw [← Nat.card_eq_fintype_card, (h.normalizer_quotient S).1]
    norm_num
  exact commutator_eq_bot_of_solvable hY hYU (Group.isSolvable_of_ker_le_range
    ((S : Subgroup G).subgroupOf N).subtype (QuotientGroup.mk' ((S : Subgroup G).subgroupOf N))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))

end CFSG.Quasithin.H13.Ch4.E443.F4411
