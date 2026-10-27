module

public import CFSG.Quasithin.Background.F918K1
public import CFSG.Quasithin.Vol2.Ch10SecAShapeB42

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.Ch10.SecA

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}

theorem NSGroup.le_ffJ_of_offender (hB : B4Hyp G L) (hX : NSGroup ↥L) (hA : IsFFStarOffender G A) :
    L ≤ ffJ G := by
  have := hX.isSimple
  obtain ⟨-, hLF, hq, -⟩ := hB
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
  have hHL : ∀ x ∈ ffJ G, x = 1 := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (L : Set (MulAut V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact (hcomm x hx l hl).symm
    have hxL : x ∈ L := hLF ▸ centralizer_quasithinGenFitting_le G ⟨hHG hx, hLF ▸ hxC⟩
    have hz : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (hcomm x hx l l.2).symm
    rw [center_eq_bot_of_simple hX.noncomm, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA.2.1
  exact ha1 (Subtype.ext (hHL a.1 (B19.le_ffJ hA a.2)))


theorem NSGroup.not_b42Conclusion
    (hg2 : FactG2TwoNormal) (hB : B4Hyp G L) (hX : NSGroup ↥L)
    (hns : ¬ IsShapeGroup ↥L) (hA : IsFFStarOffender G A) : ¬ B42Conclusion G L A := by
  intro hc
  have := hX.isSimple
  have hnc := hX.noncomm
  have hcard := hX.card
  have hLJ : L ≤ ffJ G := NSGroup.le_ffJ_of_offender hB hX hA
  have hLG : L ≤ G := hB.2.1 ▸ quasithinGenFitting_le G
  have hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hB.2.1 ▸ le_normalizer_quasithinGenFitting G
  have one_le : ∀ {K : Type} [Field K] [Finite K] {n : ℕ}, Nat.card K = 2 ^ n → 1 ≤ n := by
    intro K _ _ n hK
    by_contra h
    have h0 : n = 0 := by omega
    have := Finite.one_lt_card (α := K)
    rw [hK, h0] at this
    norm_num at this
  rcases hc with ⟨-, ⟨n, hnat⟩, -, -⟩ | ⟨-, ⟨n, hnat⟩, -⟩ | ⟨⟨n, hsp, hJ⟩, -⟩ |
      ⟨⟨n, hg2', hrk, hJ⟩, -⟩ | h5 | ⟨-, ⟨π, hR⟩, -⟩ | ⟨-, -, ⟨α, π, hR⟩, -⟩ |
      ⟨-, -, -, K, _, _, Γ₀, -, -, hhat, -, π, hR, -⟩ | ⟨-, n, hn, hnat, -⟩ | ⟨⟨π, hR⟩, -⟩ |
      ⟨-, -, -, -, π, hR, -⟩
  ·
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    have h1 := one_le hFc
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      have h6 : Nat.card ↥L = 6 := by
        rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_two_pow hFc]
        norm_num
      rw [h6] at hcard
      have := hcard.ge
      omega
    · exact hns (Or.inl ⟨n, h2, F, inferInstance, inferInstance, hFc,
        ⟨e.symm.trans (specialLinearGroupEquivStatedSL 2 F).symm⟩⟩)
  ·
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    have h1 := one_le hFc
    have hcL : Nat.card ↥L = 2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) := by
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_three_pow hFc]
    rw [hcL] at hcard
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      have := hcard.ge
      norm_num at this
    · exact not_nsCard_SL_three h2 hcard
  ·
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain ⟨K, _, _, hKc, π, hR⟩ := hsp
      have h1 := one_le hKc
      have hn1 : n = 1 := by omega
      subst hn1
      have hd1 : Nat.card ↥(ffJ G) ∣ Nat.card ↥(StatedSp 2 K) :=
        Subgroup.card_dvd_of_surjective hR.1
      have h720 : Nat.card ↥(StatedSp 2 K) = 720 := by
        rw [card_Sp4_pow hKc]
        norm_num
      have hd2 : Nat.card ↥L ∣ Nat.card ↥(ffJ G) := Subgroup.card_dvd_of_le hLJ
      rw [h720] at hd1
      exact not_nsCard_of_dvd_smooth (a := 4) (b := 2) (c := 1) (d := 0)
        (by norm_num; exact hd2.trans hd1) hcard
    · rw [hJ (by omega)] at hsp
      obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hsp.exists_equiv
      have h1 := one_le hFc
      have hcL : Nat.card ↥L = 2 ^ (4 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1)) := by
        rw [← Nat.card_congr e.toEquiv, card_Sp4_pow hFc]
      rw [hcL] at hcard
      exact not_nsCard_Sp4 h1 hcard
  ·
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain ⟨K, _, _, hKc, π, hR⟩ := hg2'
      have h1 := one_le hKc
      have hn1 : n = 1 := by omega
      subst hn1
      have hLn : (L.subgroupOf (ffJ G)).Normal := by
        refine ⟨fun l hl h => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hl ⊢
        exact (Subgroup.mem_normalizer_iff.mp (((B6.ffJ_le G).trans hGL) h.2) l).mp hl
      have eL := Subgroup.subgroupOfEquivOfLe hLJ
      have hq : CFSG.IsQuasisimple ↥(L.subgroupOf (ffJ G)) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eL.symm hB.2.2.1
      have h6048 := hg2 K (by rw [hKc]; norm_num) _ π hR.1 _ hLn hq
      have hcL : Nat.card ↥L = 6048 := by rw [← Nat.card_congr eL.toEquiv, h6048]
      rw [hcL] at hcard
      exact not_nsCard_of_dvd_smooth (a := 5) (b := 3) (c := 0) (d := 1) (by norm_num) hcard
    ·
      have hAL : A ≤ L := (hJ (by omega)) ▸ B19.le_ffJ hA
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hp : IsPGroup 2 ↥A := hA.2.2.1.isPGroup
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
      have hrk' : rk ↥A = k := by rw [rk, hk, padicValNat.prime_pow]
      have hk3 : k = 3 * n := hrk'.symm.trans hrk
      let E : Subgroup ↥L := A.subgroupOf L
      have hEcard : Nat.card ↥E = 2 ^ (3 * n) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hk, hk3]
      have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
        intro a ha b hb
        exact Subtype.ext (hA.2.2.1.1 a.1 ha b.1 hb)
      have hEs : ∀ a ∈ E, a ^ 2 = 1 := by
        intro a ha
        exact Subtype.ext (by simpa using hA.2.2.1.2 a.1 ha)
      have h8 := hX.rank E hEc hEs
      rw [hEcard] at h8
      have h64 : 2 ^ 6 ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  ·
    obtain ⟨⟨n, hn, π, hR, -⟩, -⟩ := h5
    have hd1 : Nat.card ↥(ffJ G) ∣ n.factorial := by
      have := Subgroup.card_dvd_of_surjective (f := π) hR.1
      rwa [Nat.card_perm, Nat.card_fin] at this
    have hd2 : Nat.card ↥L ∣ Nat.card ↥(ffJ G) := Subgroup.card_dvd_of_le hLJ
    rcases hn with rfl | rfl
    · exact not_nsCard_of_dvd_smooth (a := 3) (b := 1) (c := 1) (d := 0)
        (by norm_num [Nat.factorial] at hd1 ⊢; exact hd2.trans hd1) hcard
    · exact not_nsCard_of_dvd_smooth (a := 4) (b := 2) (c := 1) (d := 1)
        (by norm_num [Nat.factorial] at hd1 ⊢; exact hd2.trans hd1) hcard
  ·
    have hd : Nat.card ↥L ∣ Nat.card ↥(alternatingGroup (Fin 6)) :=
      Subgroup.card_dvd_of_surjective hR.1
    rw [card_alt 6 (by norm_num)] at hd
    exact not_nsCard_of_dvd_smooth (a := 3) (b := 2) (c := 1) (d := 0)
      (by norm_num [Nat.factorial] at hd ⊢; exact hd) hcard
  ·
    have hd : Nat.card ↥L ∣ Nat.card ↥(alternatingGroup (Fin 7)) :=
      Subgroup.card_dvd_of_surjective hR.1
    rw [card_alt 7 (by norm_num)] at hd
    exact not_nsCard_of_dvd_smooth (a := 3) (b := 2) (c := 1) (d := 1)
      (by norm_num [Nat.factorial] at hd ⊢; exact hd) hcard
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
    · have hcL : Nat.card ↥L = 20160 := by
        rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_four_of_two hF2]
      rw [hcL] at hcard
      exact not_nsCard_of_dvd_smooth (a := 6) (b := 2) (c := 1) (d := 1) (by norm_num) hcard
    · have hcL : Nat.card ↥L = 9999360 := by
        rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_five_of_two hF2]
      rw [hcL] at hcard
      exact not_nsCard_9999360 hcard
  ·
    have hd : Nat.card ↥L ∣ Nat.card ↥(StatedSL 4 (ZMod 2)) :=
      Subgroup.card_dvd_of_surjective hR.1
    rw [card_statedSL, card_SL_four_two] at hd
    exact not_nsCard_of_dvd_smooth (a := 6) (b := 2) (c := 1) (d := 1)
      (by norm_num at hd ⊢; exact hd) hcard
  ·
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective
      (isSimpleGroup_statedSL_two (n := 5) (by norm_num)) π hR.1
    have hcL : Nat.card ↥L = 9999360 := by
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_five_two]
    rw [hcL] at hcard
    exact not_nsCard_9999360 hcard

end CFSG.Quasithin
