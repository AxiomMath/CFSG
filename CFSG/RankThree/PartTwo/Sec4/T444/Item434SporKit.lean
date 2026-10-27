module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Spor
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434Spor

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open Item434Kit Item434Alt
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem exists_e27_of_two_lt_pRank {X : Type*} [Group X] (h : 2 < CFSG.pRank 3 X) :
    ∃ D : Subgroup X, CFSG.Assembly.IsElemAbelian 3 D ∧ Nat.card D = 27 := by
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
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := E) (n := 3)
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

theorem exists_elemAbelian_sylow_of_three_lt_pRank {X : Type*} [Group X] [Finite X]
    (h : 3 < CFSG.pRank 3 X) (hX : (Nat.card X).factorization 3 = 4) :
    ∃ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ (Nat.card X).factorization 3 := by
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
  have hdvd : 3 ^ r ∣ Nat.card X := hEc ▸ Subgroup.card_subgroup_dvd_card E
  have hr4 : r ≤ 4 := by
    rw [← hX]
    exact (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
  refine ⟨E, ⟨hE.toIsMulCommutative, fun x hx => ?_⟩, by rw [hEc, hX]; congr 1; omega⟩
  have := hE
  exact elemPow_eq_one_of_isElementaryAbelian (A := E) x hx

theorem center_eq_bot_of_simple {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (hY : ¬ (Nat.card Y).Prime) : Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative Y :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b : b ∈ _) a)⟩⟩
    exact hY (Group.is_simple_iff_prime_card.mp inferInstance)

section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {X : Type*} [Group X]

theorem card_map_quotConj (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) :
    Nat.card (A.map (quotConj e)) = Nat.card h.layerStar := by
  have h1 := card_eq_card_inf_ker_mul_card_map (quotConj e) A
  rw [ker_quotConj h.isQuasisimple e, h.isE27.2] at h1
  have h2 := h.card_inf_mul_card_layerStar
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.symm.trans h2.symm)

theorem false_of_card_nine (h : Ctx434Core G A M Q) (hZ : Subgroup.center (layer G) = ⊥)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) {D : Subgroup X}
    (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD27 : Nat.card D = 27)
    (h9 : Nat.card h.layerStar = 9) : False := by
  have hC := Item434Kit.inf_centralizer_layer_eq_bot h hZ e hD hD27
  have h27 := h.card_inf_mul_card_layerStar
  rw [hC, Subgroup.card_bot, one_mul, h9] at h27
  omega

theorem false_of_elemAbelian_sylow (h : Ctx434Core G A M Q) [Finite X]
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hout : ¬ 3 ∣ Nat.card (Outer X))
    (hcen : Subgroup.center X = ⊥) {E : Subgroup X} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hEsyl : Nat.card E = 3 ^ (Nat.card X).factorization 3) (hE81 : 81 ≤ Nat.card E)
    (h27 : Nat.card h.layerStar = 27) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Subgroup.center (layer G) = ⊥ := by
    rcases h.card_layerStar with h9 | ⟨-, hZ⟩
    · omega
    · exact hZ
  have hA27 : Nat.card (A.map (quotConj e)) = 27 := by rw [card_map_quotConj h e, h27]
  set P := (A.map (quotConj e)).comap (MulAut.conj : X →* MulAut X) with hP
  have hPmap : P.map MulAut.conj = A.map (quotConj e) := map_comap_conj_eq h e hout
  have hinj := conj_injective_of_center_eq_bot hcen
  have hP27 : Nat.card P = 27 := by
    rw [← Subgroup.card_map_of_injective hinj, hPmap, hA27]
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hP27]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hEsyl hPp
  set D := E.map (MulAut.conj g).toMonoidHom with hD
  have hDe : CFSG.Assembly.IsElemAbelian 3 D :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ E hE
  have hD81 : 81 ≤ Nat.card D := by
    rw [hD, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hE81
  refine false_of_fixed h hZ e le_rfl (by rw [h.isE27.2]; norm_num) hDe hD81 ?_
  intro a ha d hd
  have hmem : quotConj e a ∈ P.map MulAut.conj := by
    rw [hPmap]
    exact ⟨a, ha, rfl⟩
  obtain ⟨p, hp, hpa⟩ := hmem
  have hcomm : p * d = d * p :=
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨p, hg hp⟩ ⟨d, hd⟩)
  rw [← hpa, MulAut.conj_apply, hcomm, mul_inv_cancel_right]

theorem center_layer_eq_bot_of_rankFour (h : Ctx434Core G A M Q) {S : Type} [Group S]
    (hS : ∀ (J : Type) [Group J] [Finite J], Census.IsThreeCenterCover J S →
      4 ≤ CFSG.twoLocalOddRank J)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* S) (he : CFSG.twoLocalOddRank (layer G) ≤ 3) :
    Subgroup.center (layer G) = ⊥ := by
  by_contra hZ
  have h3 : 3 ∣ Nat.card (Subgroup.center (layer G)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_center_layer
    rw [hk]
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact absurd (Subgroup.card_eq_one.mp hk) hZ
    · exact dvd_pow_self 3 (Nat.succ_ne_zero k)
  have h4 := hS (layer G) ⟨h.isQuasisimple, h3, ⟨e⟩⟩
  omega

end Ctx

theorem localRank_le_three_of_section {G₀ : Type} [Group G₀] [Finite G₀]
    (hG₀ : SectionFourHyp G₀) (H : Subgroup G₀) {G : Type} [Group G] [Finite G] (f : H →* G)
    (hf : Function.Surjective f) (hker : ¬ 3 ∣ Nat.card f.ker) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : localRank p G ≤ 3 := by
  have e : H ⧸ f.ker ≃* G := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hH : localRank p H ≤ localRank p G₀ := localRank_subgroup_le hp H
  rw [← Census.localRank_eq_of_mulEquiv e hp]
  rcases (show p = 3 ∨ 3 < p by have := hp.two_le; omega) with rfl | hp3
  · exact ((CFSG.RankThree.Classical2.localRank_quotient_le hp hp2 f.ker hker).trans hH).trans
      ((OddKernel.localRank_le_evenRank Nat.prime_three (by norm_num)).trans hG₀.evenRank_le)
  · exact (OddKernel.rank_three_three_complement_quotient_sharp_local_bounds f.ker).2.1 p hp hp3
      (by have := hH.trans_lt (hG₀.localRank_lt p hp hp3); omega)

theorem twoLocalOddRank_layer_le_three {G₀ : Type} [Group G₀] [Finite G₀]
    (hG₀ : SectionFourHyp G₀) (H : Subgroup G₀) {G : Type} [Group G] [Finite G] (f : H →* G)
    (hf : Function.Surjective f) (hker : ¬ 3 ∣ Nat.card f.ker) :
    CFSG.twoLocalOddRank (layer G) ≤ 3 := by
  rw [← OddKernel.evenRank_eq_twoLocalOddRank]
  exact Census.evenRank_le_of_localRank_le fun p hp hp2 =>
    (localRank_subgroup_le hp (layer G)).trans
      (localRank_le_three_of_section hG₀ H f hf hker hp hp2)

section Families


theorem item434SporAtCard_nine_of {s : TauCeti.SporadicName}
    (hD : ∃ D : Subgroup (Spor s), CFSG.Assembly.IsElemAbelian 3 D ∧ Nat.card D = 27)
    (hc : Item434SporAtNineCover s) : Item434SporAtCard s 9 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q h hL h9
  by_cases hZ : Subgroup.center (layer G) = ⊥
  · obtain ⟨e⟩ := hL
    obtain ⟨D, hDe, hD27⟩ := hD
    exact (false_of_card_nine h hZ e hDe hD27 h9).elim
  · exact hc G₀ hG₀ H G f hf hker A M Q h hL h9 hZ

theorem item434SporAtNineCover_of_rankFour {s : TauCeti.SporadicName}
    (hS : ∀ (J : Type) [Group J] [Finite J], Census.IsThreeCenterCover J (Spor s) →
      4 ≤ CFSG.twoLocalOddRank J) :
    Item434SporAtNineCover s := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q h hL _ hZ
  obtain ⟨e⟩ := hL
  exact (hZ (center_layer_eq_bot_of_rankFour h hS e
    (twoLocalOddRank_layer_le_three hG₀ H f hf hker))).elim

end Families

end CFSG.RankThree.PartTwo.Sec4.Item434Spor
