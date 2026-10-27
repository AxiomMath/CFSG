module

public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard
public import CFSG.Quasithin.Vol2.Ch10SecAFacts
public import CFSG.Quasithin.Background.InternalSecAlt
public import CFSG.Quasithin.Background.B19Setup

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] [Finite V]

theorem le_ffJ_of_two_dvd (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hB : B4Hyp G L) (h2 : 2 ∣ Nat.card ↥(ffJ G)) : L ≤ ffJ G := by
  obtain ⟨-, hLF, hq, hirr⟩ := hB
  have hLG : L ≤ G := hLF ▸ quasithinGenFitting_le G
  have hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hLF ▸ le_normalizer_quasithinGenFitting G
  have hHG : ffJ G ≤ G := B6.ffJ_le G
  have hGH : G ≤ Subgroup.normalizer ((ffJ G) : Set (MulAut V)) := B6.le_normalizer_ffJ G
  have hqo := B1Red.isQuasisimple_to_open hq
  by_contra hLH
  have hcomm := B1Red.commute_of_normal_not_le hqo
    (fun x hx l hl => (Subgroup.mem_normalizer_iff.mp (hGL (hHG hx)) l).mp hl)
    (fun l hl x hx => (Subgroup.mem_normalizer_iff.mp (hGH (hLG hl)) x).mp hx) hLH
  have hHe : ffJ G ≤ XMod.eqvAut ↥L V := by
    intro x hx a p
    exact congrArg (fun f : MulAut V => f p) (hcomm x hx a a.2)
  have hodd := InternalSec.odd_card_eqvAut_of_irr hV hirr
    (InternalSec.exists_noncomm_of_isQuasisimple hq)
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2.trans (Subgroup.card_dvd_of_le hHe)))

omit [Finite V] in
theorem two_dvd_card_ffJ {G A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) :
    2 ∣ Nat.card ↥(ffJ G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥A := hA.2.2.1.isPGroup
  rcases hp.card_eq_or_dvd with h | h
  · exact absurd ((Subgroup.card_eq_one).mp h) hA.2.1
  · exact h.trans (Subgroup.card_dvd_of_le (B19.le_ffJ hA))

theorem center_eq_bot_of_simple {X : Type} [Group X] [hs : IsSimpleGroup X]
    (hnc : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm

omit [Finite V] in
theorem exists_normal_of_equiv {Γ : Type} [Group Γ] {H L : Subgroup (MulAut V)} (e : Γ ≃* ↥H)
    (hLH : L ≤ H) (hn : H ≤ Subgroup.normalizer (L : Set (MulAut V))) :
    ∃ N : Subgroup Γ, N.Normal ∧ Nonempty (↥N ≃* ↥L) := by
  have hLHn : (L.subgroupOf H).Normal := by
    refine ⟨fun l hl h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hn h.2) l).mp hl
  set P : Subgroup Γ := (L.subgroupOf H).comap e.toMonoidHom with hP
  have hPmap : P.map e.toMonoidHom = L.subgroupOf H :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective _
  exact ⟨P, Subgroup.Normal.comap hLHn _, ⟨(e.subgroupMap P).trans
    ((MulEquiv.subgroupCongr hPmap).trans (Subgroup.subgroupOfEquivOfLe hLH))⟩⟩

variable {G L A : Subgroup (MulAut V)}

theorem b42_of_isShapeGroup
    (hF : Facts10_1) (hV : ∀ v : V, v ^ 2 = 1) (hB : B4Hyp G L)
    (hA : IsFFStarOffender G A) (hc : B42Conclusion G L A) [hs : IsSimpleGroup ↥L]
    (hsh : IsShapeGroup ↥L) :
    (∃ n, 2 ≤ n ∧ BinaryNaturalSL L ⊤ ⊥ 2 n) ∨ BinaryNaturalSL L ⊤ ⊥ 3 1 ∨
      AlternatingNatural L ⊤ ⊥ 5 := by
  have hcard := shapeCard_of_isShapeGroup hsh
  have hnc := InternalSec.exists_noncomm_of_isQuasisimple hB.2.2.1
  have hLG : L ≤ G := hB.2.1 ▸ quasithinGenFitting_le G
  have hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hB.2.1 ▸ le_normalizer_quasithinGenFitting G
  have hnt : Nontrivial ↥L := hs.toNontrivial
  have card_false : ∀ {N : ℕ}, Nat.card ↥L = N → ¬ ShapeCard N → False :=
    fun hN hnot => hnot (hN ▸ hcard)
  have one_le : ∀ {K : Type} [Field K] [Finite K] {n : ℕ}, Nat.card K = 2 ^ n → 1 ≤ n := by
    intro K _ _ n hK
    by_contra h
    have h0 : n = 0 := by omega
    have := Finite.one_lt_card (α := K)
    rw [hK, h0] at this
    norm_num at this
  rcases hc with ⟨-, ⟨n, hnat⟩, -, -⟩ | ⟨-, ⟨n, hnat⟩, -⟩ | ⟨⟨n, hsp, hJ⟩, -⟩ |
      ⟨⟨n, hg2, -, hJ⟩, -⟩ | h5 | ⟨-, ⟨π, hR⟩, -⟩ | ⟨-, -, ⟨α, π, hR⟩, -⟩ |
      ⟨-, -, -, K, _, _, Γ₀, -, -, hhat, -, π, hR, -⟩ | ⟨-, n, hn, hnat, -⟩ | ⟨⟨π, hR⟩, -⟩ |
      ⟨-, -, -, -, π, hR, -⟩
  ·
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    have h1 := one_le hFc
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      refine (card_false ?_ not_shapeCard_six).elim
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_two_pow hFc]
      norm_num
    · exact Or.inl ⟨n, h2, hnat⟩
  ·
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    have h1 := one_le hFc
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      exact Or.inr (Or.inl hnat)
    · refine (card_false ?_ (not_shapeCard_SL_three h2)).elim
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_three_pow hFc]
  ·
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hsp.exists_equiv
    have h1 := one_le hFc
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      have hLJ := le_ffJ_of_two_dvd hV hB (two_dvd_card_ffJ hA)
      obtain ⟨N, hN, ⟨eN⟩⟩ := exists_normal_of_equiv e hLJ
        ((B6.ffJ_le G).trans hGL)
      have hq : CFSG.IsQuasisimple ↥N :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eN.symm hB.2.2.1
      have h360 := hF.sp4Two F (by rw [hFc]; norm_num) N hN hq
      exact (card_false (by rw [← Nat.card_congr eN.toEquiv, h360]) not_shapeCard_360).elim
    · have hJL := hJ (by omega)
      rw [hJL] at e
      refine (card_false ?_ (not_shapeCard_Sp4 h1)).elim
      rw [← Nat.card_congr e.toEquiv, card_Sp4_pow hFc]
  ·
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain ⟨K, _, _, hKc, π, hR⟩ := hg2
      have h1 := one_le hKc
      have hn1 : n = 1 := by omega
      subst hn1
      have hLJ := le_ffJ_of_two_dvd hV hB (two_dvd_card_ffJ hA)
      have hLn : (L.subgroupOf (ffJ G)).Normal := by
        refine ⟨fun l hl h => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hl ⊢
        exact (Subgroup.mem_normalizer_iff.mp (((B6.ffJ_le G).trans hGL) h.2) l).mp hl
      have eL := Subgroup.subgroupOfEquivOfLe hLJ
      have hq : CFSG.IsQuasisimple ↥(L.subgroupOf (ffJ G)) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eL.symm hB.2.2.1
      have h6048 := hF.g2Two K (by rw [hKc]; norm_num) _ π hR.1 _ hLn hq
      exact (card_false (by rw [← Nat.card_congr eL.toEquiv, h6048]) not_shapeCard_6048).elim
    · rw [hJ (by omega)] at hg2
      obtain ⟨K, _, _, hKc, π, hR⟩ := hg2
      exact absurd hR.1 (hF.g2 K n h2 hKc _ hsh π)
  ·
    obtain ⟨m, hm, halt, ⟨e⟩⟩ := InternalSec.alternatingNatural_of_b42Case5 hV hB h5
    rcases hm with rfl | rfl
    · exact Or.inr (Or.inr halt)
    · refine (card_false ?_ not_shapeCard_2520).elim
      rw [Nat.card_congr e.toEquiv, card_alt 7 (by norm_num)]
      decide
  ·
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective (isSimpleGroup_alt (n := 6) (by norm_num)) π
      hR.1
    refine (card_false ?_ not_shapeCard_360).elim
    rw [← Nat.card_congr e.toEquiv]
    rw [card_alt 6 (by norm_num)]
    decide
  ·
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective (isSimpleGroup_alt (n := 7) (by norm_num)) π
      hR.1
    refine (card_false ?_ not_shapeCard_2520).elim
    rw [← Nat.card_congr e.toEquiv]
    rw [card_alt 7 (by norm_num)]
    decide
  ·
    have e : ↥Γ₀ ≃* ↥L := MulEquiv.ofBijective π
      ⟨hR.injective_of_faithful (FFModel.nat_faithful _), hR.1⟩
    have hc1 : Nat.card (Subgroup.center ↥L) = 1 := by
      rw [center_eq_bot_of_simple hnc, Subgroup.card_bot]
    have hc3 := hhat.2.1
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hc1] at hc3
    norm_num at hc3
  ·
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    have hF2 : Nat.card F = 2 := by rw [hFc]; norm_num
    rcases hn with rfl | rfl
    · refine (card_false ?_ not_shapeCard_20160).elim
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_four_of_two hF2]
    · refine (card_false ?_ not_shapeCard_9999360).elim
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_five_of_two hF2]
  ·
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective
      (isSimpleGroup_statedSL_two (n := 4) (by norm_num)) π hR.1
    refine (card_false ?_ not_shapeCard_20160).elim
    rw [← Nat.card_congr e.toEquiv]
    rw [card_statedSL, card_SL_four_two]
  ·
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective
      (isSimpleGroup_statedSL_two (n := 5) (by norm_num)) π hR.1
    refine (card_false ?_ not_shapeCard_9999360).elim
    rw [← Nat.card_congr e.toEquiv]
    rw [card_statedSL, card_SL_five_two]

end CFSG.Quasithin.Vol2.Ch10.SecA
