module

public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.CGT.PushingUpLit.T2K.SixC

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem commutator_eq_of_isShort_of_isQuasisimple {L : Subgroup G} (hL : IsShort L)
    (hq : CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L)) : ⁅L, L⁆ = L := by
  have hQ : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) := hq.1
  have hmap : (_root_.commutator ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤ := by
    rw [_root_.map_commutator_eq, MonoidHom.range_eq_top_of_surjective _
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L))]
    exact Group.isPerfect_def.mp hQ
  have hsurj : ∀ x : ↥L, ∃ c ∈ _root_.commutator ↥L, ∃ p ∈ CFSG.pCore 2 ↥L, x = c * p := by
    intro x
    have hx : QuotientGroup.mk' (CFSG.pCore 2 ↥L) x ∈
        (_root_.commutator ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
      rw [hmap]
      exact Subgroup.mem_top _
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hx
    exact ⟨c, hc, c⁻¹ * x, QuotientGroup.eq.mp hcx, (mul_inv_cancel_left c x).symm⟩
  have hPgrp : IsPGroup 2 (CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
  have hϕ : Function.Surjective ((QuotientGroup.mk' (_root_.commutator ↥L)).comp
      (CFSG.pCore 2 ↥L).subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (_root_.commutator ↥L) q
    obtain ⟨c, hc, p, hp, hxcp⟩ := hsurj x
    refine ⟨⟨p, hp⟩, ?_⟩
    have hc1 : QuotientGroup.mk' (_root_.commutator ↥L) c = 1 :=
      (QuotientGroup.eq_one_iff c).mpr hc
    show QuotientGroup.mk' (_root_.commutator ↥L) p =
      QuotientGroup.mk' (_root_.commutator ↥L) x
    rw [hxcp, map_mul, hc1, one_mul]
  have hIsP : IsPGroup 2 (↥L ⧸ _root_.commutator ↥L) := hPgrp.of_surjective _ hϕ
  have hC : _root_.commutator ↥L = ⊤ := hL.eq_twoResidual (_root_.commutator ↥L) hIsP
  exact Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hC)

theorem alternatingGroup_fin_subsingleton (n : ℕ) (hn : n ≤ 2) :
    Subsingleton (alternatingGroup (Fin n)) := by
  interval_cases n
  · infer_instance
  · infer_instance
  · have h2 : Nat.card (alternatingGroup (Fin 2)) = 1 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    exact (Nat.card_eq_one_iff_unique.mp h2).1

theorem three_le_of_isAltNaturalType {L : Subgroup G} {n : ℕ}
    (hq : CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L)) (h : IsAltNaturalType L n) : 3 ≤ n := by
  by_contra hlt
  obtain ⟨α, -, hker, -⟩ := h
  haveI : Subsingleton (alternatingGroup (Fin n)) := alternatingGroup_fin_subsingleton n (by omega)
  have hQ : Subsingleton (L ⧸ CFSG.pCore 2 L) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    rw [QuotientGroup.eq, ← hker, MonoidHom.mem_ker]
    exact Subsingleton.elim _ _
  obtain ⟨-, -, a, b, hab⟩ := hq
  refine hab ?_
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective b
  rw [Subsingleton.elim x' y']

theorem generalizedFitting_centralizer_eq_pCore
    (hchar : CFSG.Assembly.IsCharTwoType G) {M : Subgroup G} {t : G}
    (ht : t ∈ CFSG.Open.pCoreOf 2 M) (h1 : t ≠ 1) :
    CFSG.generalizedFitting ↥(Subgroup.centralizer ({t} : Set G)) =
      CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Subgroup.zpowers t ≤ CFSG.Open.pCoreOf 2 M := Subgroup.zpowers_le.mpr ht
  have hD : IsPGroup 2 ↥(Subgroup.zpowers t) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le hle
  have hD1 : Subgroup.zpowers t ≠ ⊥ := fun h => h1 (Subgroup.zpowers_eq_bot.mp h)
  have hC := CFSG.CGT.PushingUpLit.T2K.isCharacteristicP_centralizer hchar hD hD1
  have hcent : Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
    ext g
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact hg t (Subgroup.mem_zpowers t)
    · intro hg h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact Commute.zpow_left (hg t (Set.mem_singleton t) : Commute t g) k
  rw [hcent] at hC
  exact (isCharacteristicP_iff_generalizedFitting_eq_pCore _ 2).mp hC

end CFSG.RankThree.PartTwo.Sec19
