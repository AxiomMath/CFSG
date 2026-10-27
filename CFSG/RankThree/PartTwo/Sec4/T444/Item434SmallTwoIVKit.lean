module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporKit
import CFSG.RankThree.PartTwo.Sec4.Steps439
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open Item434Kit Item434Alt
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem exists_e81_of_three_lt_pRank {X : Type*} [Group X] (h : 3 < CFSG.pRank 3 X) :
    ∃ D : Subgroup X, CFSG.Assembly.IsElemAbelian 3 D ∧ Nat.card D = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S := {r : ℕ | ∃ E : Subgroup X, IsElementaryAbelian 3 E ∧ Nat.card E = 3 ^ r} with hS
  have hne : S.Nonempty := by
    by_contra hS0
    rw [Set.not_nonempty_iff_eq_empty] at hS0
    have h0 : CFSG.pRank 3 X = 0 := by
      change sSup S = 0
      rw [hS0, csSup_empty]
      rfl
    omega
  obtain ⟨r, ⟨E, hE, hEc⟩, hr⟩ := exists_lt_of_lt_csSup hne h
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; positivity)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := E) (n := 4)
    (by rw [hEc]; exact pow_dvd_pow 3 hr)
  refine ⟨K.map E.subtype, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, ⟨x, -, rfl⟩⟩ ⟨_, ⟨y, -, rfl⟩⟩
    apply Subtype.ext
    change (x : X) * y = y * x
    exact congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm x y)
  · rintro _ ⟨x, -, rfl⟩
    have := hE
    exact elemPow_eq_one_of_isElementaryAbelian (A := E) _ x.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
    norm_num

theorem exists_e27_of_e81 {X : Type*} [Group X] {D : Subgroup X}
    (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD81 : Nat.card D = 81) :
    ∃ D' : Subgroup X, CFSG.Assembly.IsElemAbelian 3 D' ∧ Nat.card D' = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hD81]; norm_num)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := D) (n := 3)
    (by rw [hD81]; norm_num)
  refine ⟨K.map D.subtype, Source.isElemAbelian_of_le hD (Subgroup.map_subtype_le K), ?_⟩
  rw [Subgroup.card_map_of_injective D.subtype_injective, hK]
  norm_num

section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {X : Type*} [Group X]

theorem center_eq_bot_of_layer_quotient (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) : Subgroup.center X = ⊥ := by
  have hL := h.isQuasisimple
  have : IsSimpleGroup (layer G ⧸ Subgroup.center (layer G)) := hL.2.1
  obtain ⟨a, b, hab⟩ := hL.2.2
  have hC : Subgroup.center (layer G ⧸ Subgroup.center (layer G)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (layer G ⧸ Subgroup.center (layer G))) with hc | hc
    · exact hc
    · exfalso
      have ha : a ∈ Subgroup.center (layer G ⧸ Subgroup.center (layer G)) := hc ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  rw [eq_bot_iff]
  intro x hx
  have hx' : e.symm x ∈ Subgroup.center (layer G ⧸ Subgroup.center (layer G)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp hx (e y)
  rw [hC, Subgroup.mem_bot] at hx'
  rw [Subgroup.mem_bot, ← e.apply_symm_apply x, hx', map_one]

theorem center_layer_eq_bot_of_no_cover (h : Ctx434Core G A M Q) {S : Type} [Group S]
    (hS : ∀ (J : Type) [Group J] [Finite J], Census.IsThreeCenterCover J S → False)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* S) : Subgroup.center (layer G) = ⊥ := by
  by_contra hZ
  have h3 : 3 ∣ Nat.card (Subgroup.center (layer G)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_center_layer
    rw [hk]
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact absurd (Subgroup.card_eq_one.mp hk) hZ
    · exact dvd_pow_self 3 (Nat.succ_ne_zero k)
  exact hS (layer G) ⟨h.isQuasisimple, h3, ⟨e⟩⟩

theorem quotConj_mem_range_conj_of_not_inducesOuter (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) {a : G} (ha : ¬ InducesOuter a (layer G)) :
    quotConj e a ∈ (MulAut.conj : X →* MulAut X).range := by
  have : (layer G).Characteristic := layer_characteristic
  obtain ⟨l, hl, hc⟩ := exists_mem_centralizer_of_not_inducesOuter ha
  have h1 : quotConj e (l⁻¹ * a) = 1 := (quotConj_eq_one_iff h.isQuasisimple e).mpr hc
  have h2 : quotConj e a = quotConj e l * quotConj e (l⁻¹ * a) := by
    rw [← map_mul, mul_inv_cancel_left]
  rw [h2, h1, mul_one, quotConj_of_mem e hl]
  exact ⟨_, rfl⟩

theorem false_of_abelian_index_three (h : Ctx434Core G A M Q) [Finite X]
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hinn : ∀ a ∈ A, quotConj e a ∈ (MulAut.conj : X →* MulAut X).range)
    (hcen : Subgroup.center X = ⊥) {N E : Subgroup X} (hN : IsMulCommutative N)
    (hN3 : IsPGroup 3 N) (hEN : E ≤ N) (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE81 : 81 ≤ Nat.card E) (hidx : 3 ^ (Nat.card X).factorization 3 ≤ 3 * Nat.card N)
    (h27 : Nat.card (A.map (layerConj G)) = 27) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h27' : Nat.card h.layerStar = 27 := h27
  have hZ : Subgroup.center (layer G) = ⊥ := by
    rcases h.card_layerStar with h9 | ⟨-, hZ⟩
    · omega
    · exact hZ
  have hA27 : Nat.card (A.map (quotConj e)) = 27 := by
    rw [Item434Spor.card_map_quotConj h e, h27']
  set P := (A.map (quotConj e)).comap (MulAut.conj : X →* MulAut X) with hP
  have hPmap : P.map MulAut.conj = A.map (quotConj e) := by
    apply Subgroup.map_comap_eq_self
    rintro _ ⟨a, ha, rfl⟩
    exact hinn a ha
  have hinj := conj_injective_of_center_eq_bot hcen
  have hP27 : Nat.card P = 27 := by
    rw [← Subgroup.card_map_of_injective hinj, hPmap, hA27]
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hP27]; norm_num)
  obtain ⟨S, hNS⟩ := hN3.exists_le_sylow
  have hScard : Nat.card (S : Subgroup X) = 3 ^ (Nat.card X).factorization 3 :=
    Sylow.card_eq_multiplicity S
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hScard hPp
  set S' := (S : Subgroup X).map (MulAut.conj g).toMonoidHom with hS'
  set N' := N.map (MulAut.conj g).toMonoidHom with hN'
  set E' := E.map (MulAut.conj g).toMonoidHom with hE'
  have hN'S' : N' ≤ S' := Subgroup.map_mono hNS
  have hE'N' : E' ≤ N' := Subgroup.map_mono hEN
  have hN'card : Nat.card N' = Nat.card N :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hE'card : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hS'card : Nat.card S' = 3 ^ (Nat.card X).factorization 3 :=
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).trans hScard
  have hE'e : CFSG.Assembly.IsElemAbelian 3 E' :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ E hE
  have hN'c : ∀ x ∈ N', ∀ y ∈ N', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hN.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  have h1 := Subgroup.relIndex_mul_card N' S'
  rw [inf_eq_left.mpr hN'S', hS'card, hN'card] at h1
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hrel : N'.relIndex S' ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have h2 : 4 * Nat.card N ≤ N'.relIndex S' * Nat.card N := Nat.mul_le_mul_right _ hlt
    omega
  have hrel0 : N'.relIndex S' ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact absurd h1.symm (pow_ne_zero _ (by norm_num))
  have hrelP : N'.relIndex P ≤ 3 :=
    (Subgroup.relIndex_le_of_le_right hg hrel0).trans hrel
  have hB9 : 9 ≤ Nat.card (N' ⊓ P : Subgroup X) := by
    have h1 := Subgroup.relIndex_mul_card N' P
    rw [hP27] at h1
    by_contra hlt
    push Not at hlt
    have h2 : N'.relIndex P * Nat.card (N' ⊓ P : Subgroup X) ≤ 3 * 8 :=
      Nat.mul_le_mul hrelP (by omega)
    omega
  set F := (N' ⊓ P).map (MulAut.conj : X →* MulAut X) with hF
  have hFA : F ≤ A.map (quotConj e) := hPmap ▸ Subgroup.map_mono inf_le_right
  have hF9 : 9 ≤ Nat.card F := by
    rw [hF, Subgroup.card_map_of_injective hinj]
    exact hB9
  refine false_of_fixed h hZ e (B := A ⊓ F.comap (quotConj e)) inf_le_left
    (hF9.trans (card_le_card_inf_comap e hFA)) hE'e (hE'card ▸ hE81) ?_
  rintro b ⟨-, hb⟩ d hd
  obtain ⟨p, hp, hpb⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hb)
  rw [← hpb, MulAut.conj_apply, hN'c p hp.1 d (hE'N' hd), mul_inv_cancel_right]

theorem false_of_elemAbelian_index_three (h : Ctx434Core G A M Q) [Finite X]
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hinn : ∀ a ∈ A, quotConj e a ∈ (MulAut.conj : X →* MulAut X).range)
    (hcen : Subgroup.center X = ⊥) {E : Subgroup X} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE81 : 81 ≤ Nat.card E) (hidx : 3 ^ (Nat.card X).factorization 3 ≤ 3 * Nat.card E)
    (h27 : Nat.card (A.map (layerConj G)) = 27) : False :=
  false_of_abelian_index_three h e hinn hcen hE.1 (Sec5.isPGroup_of_isElemAbelian hE) le_rfl hE
    hE81 hidx h27

theorem false_of_elemAbelian_index_three_of_outer (h : Ctx434Core G A M Q) [Finite X]
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hout : ¬ 3 ∣ Nat.card (Outer X))
    (hcen : Subgroup.center X = ⊥) {E : Subgroup X} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE81 : 81 ≤ Nat.card E) (hidx : 3 ^ (Nat.card X).factorization 3 ≤ 3 * Nat.card E)
    (h27 : Nat.card (A.map (layerConj G)) = 27) : False :=
  false_of_elemAbelian_index_three h e
    (fun a ha => mem_range_conj_of_pow_three hout (by rw [← map_pow, h.isE27.1.2 a ha, map_one]))
    hcen hE hE81 hidx h27

theorem false_of_elemAbelian_index_three_of_inner (h : Ctx434Core G A M Q) [Finite X]
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hin : ∀ a ∈ A, ¬ InducesOuter a (layer G))
    (hcen : Subgroup.center X = ⊥) {E : Subgroup X} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE81 : 81 ≤ Nat.card E) (hidx : 3 ^ (Nat.card X).factorization 3 ≤ 3 * Nat.card E)
    (h27 : Nat.card (A.map (layerConj G)) = 27) : False :=
  false_of_elemAbelian_index_three h e
    (fun a ha => quotConj_mem_range_conj_of_not_inducesOuter h e (hin a ha)) hcen hE hE81 hidx h27

end Ctx

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV
