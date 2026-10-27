module

public import CFSG.Quasithin.Vol2.Ch10SecKIc
public import CFSG.Quasithin.Vol2.Ch10SecAShapeB42
public import CFSG.Quasithin.Vol2.Ch10SecQ1G2Two

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}

theorem sixteen_dvd_two_pow_mul {k : ℕ} (hk : 4 ≤ k) (b : ℕ) : 16 ∣ 2 ^ k * b :=
  Dvd.dvd.mul_right ((show (16 : ℕ) = 2 ^ 4 by norm_num) ▸ pow_dvd_pow 2 hk) _

theorem one_le_of_card_field {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    1 ≤ n := by
  by_contra h
  have h0 : n = 0 := by omega
  have := Finite.one_lt_card (α := K)
  rw [hK, h0] at this
  norm_num at this

theorem false_of_b42
    (hV : ∀ v : V, v ^ 2 = 1) (hB : B4Hyp G L) (hGL : G = L) (hA : IsFFStarOffender G A)
    (hc : B42Conclusion G L A) (hT : TargetCard (Nat.card ↥L)) : False := by
  have hGL' : G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hB.2.1 ▸ le_normalizer_quasithinGenFitting G
  have h16 := not_sixteen_dvd hT
  have hJL : ffJ G ≤ L := hGL ▸ B6.ffJ_le G
  have hJdvd : Nat.card ↥(ffJ G) ∣ Nat.card ↥L := Subgroup.card_dvd_of_le hJL
  have card_false : ∀ {N : ℕ}, Nat.card ↥L = N → ¬ TargetCard N → False :=
    fun hN hn => hn (hN ▸ hT)
  rcases hc with ⟨-, ⟨n, hnat⟩, -, -⟩ | ⟨-, ⟨n, hnat⟩, -⟩ | ⟨⟨n, hsp, -⟩, -⟩ |
      ⟨⟨n, hg2, -, -⟩, -⟩ | h5 | ⟨-, ⟨π, hR⟩, -⟩ | ⟨-, -, ⟨α, π, hR⟩, -⟩ |
      ⟨-, -, -, K, _, _, Γ₀, -, -, hhat, -, π, hR, -⟩ | ⟨-, n, hn, hnat, -⟩ | ⟨⟨π, hR⟩, -⟩ |
      ⟨-, -, -, -, π, hR, -⟩
  ·
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    refine card_false ?_ (not_targetCard_sl2 n)
    rw [← Nat.card_congr e.toEquiv, SecA.card_statedSL, SecA.card_SL_two_pow hFc]
  ·
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    have h1 := one_le_of_card_field hFc
    have hcard : Nat.card ↥L = 2 ^ (3 * n) * ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) := by
      rw [← Nat.card_congr e.toEquiv, SecA.card_statedSL, SecA.card_SL_three_pow hFc]
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      exact card_false hcard (not_targetCard_of_lt (by norm_num))
    · exact h16 (hcard ▸ sixteen_dvd_two_pow_mul (by omega) _)
  ·
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hsp.exists_equiv
    have h1 := one_le_of_card_field hFc
    have hcard := (Nat.card_congr e.toEquiv).symm.trans (SecA.card_Sp4_pow hFc)
    exact h16 ((hcard ▸ sixteen_dvd_two_pow_mul (by omega) _).trans hJdvd)
  ·
    obtain ⟨K, _, _, hKc, π, hR⟩ := hg2
    have h1 := one_le_of_card_field hKc
    rcases Nat.lt_or_ge n 2 with h2 | h2
    ·
      have hn1 : n = 1 := by omega
      subst hn1
      have hLJ := SecA.le_ffJ_of_two_dvd hV hB (SecA.two_dvd_card_ffJ hA)
      have hLn : (L.subgroupOf (ffJ G)).Normal := by
        refine ⟨fun l hl h => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hl ⊢
        exact (Subgroup.mem_normalizer_iff.mp (((B6.ffJ_le G).trans hGL') h.2) l).mp hl
      have eL := Subgroup.subgroupOfEquivOfLe hLJ
      have hq : CFSG.IsQuasisimple ↥(L.subgroupOf (ffJ G)) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eL.symm hB.2.2.1
      have h6048 := SecA.factG2TwoNormal_holds K (by rw [hKc]; norm_num) _ π hR.1 _ hLn hq
      refine h16 ?_
      rw [← Nat.card_congr eL.toEquiv, h6048]
      norm_num
    ·
      have : Nontrivial ↥(ffJ G) := (Subgroup.nontrivial_iff_ne_bot _).2
        fun h => hA.2.1 (eq_bot_iff.2 (h ▸ B19.le_ffJ hA))
      exact false_of_g2_surj h2 hKc (fun h => h16 (h.trans hJdvd)) π hR.1
  ·
    obtain ⟨m, hm, -, ⟨e⟩⟩ := InternalSec.alternatingNatural_of_b42Case5 hV hB h5
    rcases hm with rfl | rfl
    · refine card_false (N := 60) ?_ (not_targetCard_of_lt (by norm_num))
      rw [Nat.card_congr e.toEquiv, SecA.card_alt 5 (by norm_num)]
      decide
    · refine card_false (N := 2520) ?_ not_targetCard_2520
      rw [Nat.card_congr e.toEquiv, SecA.card_alt 7 (by norm_num)]
      decide
  ·
    refine false_of_simple_surj (SecA.isSimpleGroup_alt (n := 6) (by norm_num)) ?_ hT π hR.1
    rw [SecA.card_alt 6 (by norm_num)]
    exact not_targetCard_of_lt (by decide)
  ·
    refine false_of_simple_surj (SecA.isSimpleGroup_alt (n := 7) (by norm_num)) ?_ hT π hR.1
    rw [SecA.card_alt 7 (by norm_num)]
    exact not_targetCard_2520
  ·
    have e : ↥Γ₀ ≃* ↥L := MulEquiv.ofBijective π
      ⟨hR.injective_of_faithful (FFModel.nat_faithful _), hR.1⟩
    obtain ⟨-, hc3, ⟨e6⟩⟩ := hhat
    refine card_false (N := 1080) ?_ not_targetCard_1080
    rw [← Nat.card_congr e.toEquiv, Lin2.OddRank.card_of_cover_alt (m := 6) (by norm_num) hc3 e6]
    decide
  ·
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    have hF2 : Nat.card F = 2 := by rw [hFc]; norm_num
    rcases hn with rfl | rfl
    · refine card_false (N := 20160) ?_ (not_targetCard_of_dvd (by norm_num))
      rw [← Nat.card_congr e.toEquiv, SecA.card_statedSL, SecA.card_SL_four_of_two hF2]
    · refine card_false (N := 9999360) ?_ (not_targetCard_of_dvd (by norm_num))
      rw [← Nat.card_congr e.toEquiv, SecA.card_statedSL, SecA.card_SL_five_of_two hF2]
  ·
    refine false_of_simple_surj (SecA.isSimpleGroup_statedSL_two (n := 4) (by norm_num)) ?_ hT π
      hR.1
    rw [SecA.card_statedSL, SecA.card_SL_four_of_two (Nat.card_zmod 2)]
    exact not_targetCard_of_dvd (by norm_num)
  ·
    refine false_of_simple_surj (SecA.isSimpleGroup_statedSL_two (n := 5) (by norm_num)) ?_ hT π
      hR.1
    rw [SecA.card_statedSL, SecA.card_SL_five_of_two (Nat.card_zmod 2)]
    exact not_targetCard_of_dvd (by norm_num)

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
