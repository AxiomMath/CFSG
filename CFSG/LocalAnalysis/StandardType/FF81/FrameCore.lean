module

public import CFSG.Open.LocalVocabulary
import CFSG.RankThree.PartTwo.Sec21.FF84LemmaFHolds
import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LieType.BorelTits.Basic
import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableSylowNormalizedComplement
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.RankThreeEvenClassification.HallTransport
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableSelfCentralizingCore
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.Quasithin.H13.GoldschmidtC137SQFrat
import CFSG.Quasithin.H13.GoldschmidtC137SQKg
import CFSG.Quasithin.H13.GoldschmidtC137SQSyl7

public section

namespace CFSG.StandardType.FF81

open CFSG.Open

private theorem inf_eq_bot_of_normal_simple {G : Type} [Group G] {b : G} {L R : Subgroup G}
    (hLb : L ≤ Subgroup.centralizer ({b} : Set G))
    (hLs : IsSimpleGroup ↥L) (hL3 : 3 ∣ Nat.card L)
    (hRb : R ≤ Subgroup.centralizer ({b} : Set G))
    (hRN : (R.subgroupOf (Subgroup.centralizer ({b} : Set G))).Normal)
    (hR3 : ¬ 3 ∣ Nat.card R) : R ⊓ L = ⊥ := by
  have hRN' : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRb).mp hRN
  have hLNR : L ≤ Subgroup.normalizer (R : Set G) := hLb.trans hRN'
  have hLNL : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  have hLNRinf : L ≤ Subgroup.normalizer (R ⊓ L : Set G) :=
    (le_inf hLNR hLNL).trans (Subgroup.inf_normalizer_le_normalizer_inf (H := R) (K := L))
  have hnormal : ((R ⊓ L).subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := L) (N := R ⊓ L) hLNRinf
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal ↥L _ hLs ((R ⊓ L).subgroupOf L) hnormal with
    hbot | htop
  · rw [Subgroup.subgroupOf_eq_bot, disjoint_iff] at hbot
    simpa [inf_eq_left.mpr inf_le_right] using hbot
  · exfalso
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hR3 (hL3.trans (Subgroup.card_dvd_of_le (htop.trans inf_le_left)))

private theorem inf_pCoreOf_centralizer_eq_sylow {G : Type} [Group G] [Finite G] {b : G}
    {L V : Subgroup G}
    (hLb : L ≤ Subgroup.centralizer ({b} : Set G))
    (hbL : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hLs : IsSimpleGroup ↥L) (hL3 : 3 ∣ Nat.card L)
    (hVD : V ≤ Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({b} : Set G))
    (hV2 : IsPGroup 2 V) (hVsyl : CFSG.ABGLocalTools.IsSylowOf 2 V
      (Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({b} : Set G))) :
    pCoreOf 2 (Subgroup.normalizer (V : Set G)) ⊓ Subgroup.centralizer ({b} : Set G) = V := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLcentV : L ≤ Subgroup.centralizer (V : Set G) := fun l hl =>
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      ((Subgroup.mem_centralizer_iff.mp (hVD hv).1) l hl).symm
  have hLH : L ≤ Subgroup.normalizer (V : Set G) :=
    hLcentV.trans (Subgroup.centralizer_le_normalizer (V : Set G))
  have hVVstar : V ≤ pCoreOf 2 (Subgroup.normalizer (V : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 V hV2
  have hVstar2 : IsPGroup 2 (pCoreOf 2 (Subgroup.normalizer (V : Set G))) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Subgroup.normalizer (V : Set G))
  have hHnormVstar : Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (Subgroup.normalizer (V : Set G)) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Subgroup.normalizer (V : Set G))
  have hLNVstar : L ≤
      Subgroup.normalizer (pCoreOf 2 (Subgroup.normalizer (V : Set G)) : Set G) :=
    hLH.trans hHnormVstar
  let W : Subgroup G :=
    pCoreOf 2 (Subgroup.normalizer (V : Set G)) ⊓ Subgroup.centralizer ({b} : Set G)
  have hLNW : L ≤ Subgroup.normalizer (W : Set G) :=
    (le_inf hLNVstar (hLb.trans Subgroup.le_normalizer)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := pCoreOf 2
        (Subgroup.normalizer (V : Set G))) (K := Subgroup.centralizer ({b} : Set G)))
  have hnormal : (W.subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := L) (N := W) hLNW
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal ↥L _ hLs (W.subgroupOf L) hnormal with
    hbot | htop
  · rw [Subgroup.subgroupOf_eq_bot, disjoint_iff] at hbot
    have hWcentL : W ≤ Subgroup.centralizer (L : Set G) :=
      CFSG.RankThreeEvenClassification.Helpers.disjoint_mutually_normalized_subgroups_centralize
        W L (inf_le_right.trans hbL) hLNW (disjoint_iff.mpr hbot)
    have hWD : W ≤ Subgroup.centralizer (L : Set G) ⊓
        Subgroup.centralizer ({b} : Set G) := le_inf hWcentL inf_le_right
    have hW2 : IsPGroup 2 W := hVstar2.to_le inf_le_left
    have hVW : V ≤ W := le_inf hVVstar (hVD.trans inf_le_right)
    exact hVsyl.eq_of_le hVW hWD hW2
  · exfalso
    rw [Subgroup.subgroupOf_eq_top] at htop
    have hL2 : IsPGroup 2 L := hVstar2.to_le (htop.trans inf_le_left)
    obtain ⟨k, hk⟩ := hL2.exists_card_eq
    rw [hk] at hL3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hL3) (by norm_num)

private theorem fixed_point_of_quotient {G : Type} [Group G] {b : G} {V Vstar : Subgroup G}
    (hb : orderOf b = 3) (hVb : V ≤ Subgroup.centralizer ({b} : Set G))
    (hVVstar : V ≤ Vstar) (hVstar2 : IsPGroup 2 Vstar)
    (hWV : Vstar ⊓ Subgroup.centralizer ({b} : Set G) = V) :
    ∀ x ∈ Vstar, (∃ n ∈ V, b * x * b⁻¹ = x * n) → x ∈ V := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx ⟨n, hn, hxn⟩
  have hb3 : b ^ 3 = 1 := by simpa [hb] using pow_orderOf_eq_one b
  have hnb : n * b = b * n :=
    ((Subgroup.mem_centralizer_iff.mp (hVb hn)) b (by simp)).symm
  have hbn : b * n * b⁻¹ = n := by rw [← hnb]; group
  let φ : MulAut G := MulAut.conj b
  have hφx : φ x = x * n := by simpa [φ, MulAut.conj_apply] using hxn
  have hφn : φ n = n := by simpa [φ, MulAut.conj_apply] using hbn
  have hφ3 : φ ^ 3 = 1 := by
    rw [show φ ^ 3 = MulAut.conj (b ^ 3) by simp [φ, map_pow], hb3]; simp
  have hφpow : ∀ k : ℕ, (φ ^ k) x = x * n ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc (φ ^ (k + 1)) x = φ ((φ ^ k) x) := by rw [pow_succ', MulAut.mul_apply]
          _ = φ (x * n ^ k) := by rw [ih]
          _ = φ x * φ (n ^ k) := map_mul φ _ _
          _ = (x * n) * n ^ k := by rw [hφx, map_pow, hφn]
          _ = x * n ^ (k + 1) := by rw [pow_succ']; group
  have hn3 : n ^ 3 = 1 := by
    have h := hφpow 3
    rw [hφ3] at h
    have h' : x * n ^ 3 = x := by simpa using h.symm
    exact mul_left_cancel (by rwa [mul_one])
  obtain ⟨k, hk⟩ := hVstar2.exists_orderOf_eq_pow ⟨n, hVVstar hn⟩
  have hnk : orderOf n = 2 ^ k := by simpa [Subgroup.orderOf_coe] using hk
  have hdvd : orderOf n ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hn3
  have hn1 : n = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      have hpow : 2 ^ k = 3 := by rw [← hnk]; exact h3
      have h2eq : 2 = 3 := ((Nat.Prime.pow_eq_iff Nat.prime_three).mp hpow).1
      norm_num at h2eq
  have hbx : b * x * b⁻¹ = x := by rw [hxn, hn1, mul_one]
  have hxc : x ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    calc b * x = b * x * b⁻¹ * b := by group
      _ = x * b := by rw [hbx]
  exact hWV ▸ (show x ∈ Vstar ⊓ Subgroup.centralizer ({b} : Set G) from ⟨hx, hxc⟩)

private theorem pCoreOf_le_sylow_of_lemmaF {G : Type} [Group G] [Finite G] {b : G}
    {A L V : Subgroup G}
    (hb : orderOf b = 3) (hAs : IsSimpleGroup ↥A) (hA168 : Nat.card A = 168) (hbA : b ∈ A)
    (hDA : ∀ x : G, x ∈ Subgroup.centralizer (L : Set G) → x * b = b * x →
      (∃ k : ℕ, orderOf x = 2 ^ k) → ∀ y ∈ A, x * y = y * x)
    (hVD : V ≤ Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({b} : Set G))
    (hV2 : IsPGroup 2 V)
    (hWV : pCoreOf 2 (Subgroup.normalizer (V : Set G)) ⊓
      Subgroup.centralizer ({b} : Set G) = V) :
    pCoreOf 2 (Subgroup.normalizer (V : Set G)) ≤ V := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAcentV : A ≤ Subgroup.centralizer (V : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvCL : v ∈ Subgroup.centralizer (L : Set G) := (hVD hv).1
    have hvb : v * b = b * v :=
      ((Subgroup.mem_centralizer_iff.mp (hVD hv).2) b (by simp)).symm
    obtain ⟨k, hk⟩ := hV2.exists_orderOf_eq_pow ⟨v, hv⟩
    exact hDA v hvCL hvb ⟨k, by simpa [Subgroup.orderOf_coe] using hk⟩ a ha
  have hAH : A ≤ Subgroup.normalizer (V : Set G) :=
    hAcentV.trans (Subgroup.centralizer_le_normalizer (V : Set G))
  have hHnormVstar : Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (Subgroup.normalizer (V : Set G)) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Subgroup.normalizer (V : Set G))
  have hAnormVstar : A ≤
      Subgroup.normalizer (pCoreOf 2 (Subgroup.normalizer (V : Set G)) : Set G) :=
    hAH.trans hHnormVstar
  have hVstar2 : IsPGroup 2 (pCoreOf 2 (Subgroup.normalizer (V : Set G))) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Subgroup.normalizer (V : Set G))
  have hVVstar : V ≤ pCoreOf 2 (Subgroup.normalizer (V : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 V hV2
  have hVnormalVstar : (V.subgroupOf (pCoreOf 2 (Subgroup.normalizer (V : Set G)))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVVstar).mpr
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (Subgroup.normalizer (V : Set G)))
  have hfixed : ∀ x ∈ pCoreOf 2 (Subgroup.normalizer (V : Set G)),
      (∃ n ∈ V, b * x * b⁻¹ = x * n) → x ∈ V :=
    fixed_point_of_quotient hb (hVD.trans inf_le_right) hVVstar hVstar2 hWV
  have hbot : ((⊥ : Subgroup G).subgroupOf A) = (⊥ : Subgroup ↥A) := Subgroup.bot_subgroupOf A
  let : ((⊥ : Subgroup G).subgroupOf A).Normal := by
    rw [Subgroup.bot_subgroupOf]; exact Subgroup.normal_bot
  have e : (↥A ⧸ (⊥ : Subgroup G).subgroupOf A) ≃* ↥A :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have hsimple : IsSimpleGroup (↥A ⧸ (⊥ : Subgroup G).subgroupOf A) :=
    (MulEquiv.isSimpleGroup_congr e).mpr hAs
  have hcard : Nat.card (↥A ⧸ (⊥ : Subgroup G).subgroupOf A) = 168 := by
    rw [Nat.card_congr e.toEquiv, hA168]
  exact CFSG.RankThree.PartTwo.Sec21.FF84.lemmaF_holds G A ⊥
    (pCoreOf 2 (Subgroup.normalizer (V : Set G))) V b bot_le IsPGroup.of_bot hsimple hcard
    hbA hb hVstar2 hVVstar hVnormalVstar hAnormVstar hAH hfixed

private theorem false_of_pCore_le {G : Type} [Group G] [Finite G] (hG : IsCharTwoType G)
    {V L : Subgroup G} (hVne : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (hVVstar : V ≤ pCoreOf 2 (Subgroup.normalizer (V : Set G)))
    (hVstar2 : IsPGroup 2 (pCoreOf 2 (Subgroup.normalizer (V : Set G))))
    (hVstar_le_V : pCoreOf 2 (Subgroup.normalizer (V : Set G)) ≤ V)
    (hLcentV : L ≤ Subgroup.centralizer (V : Set G)) (hL3 : 3 ∣ Nat.card L) : False := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htwoLocal : IsTwoLocal (Subgroup.normalizer (V : Set G)) := ⟨V, hVne, hV2, rfl⟩
  have hchar := hG (Subgroup.normalizer (V : Set G)) htwoLocal
  have hVstar_eq : pCoreOf 2 (Subgroup.normalizer (V : Set G)) = V :=
    le_antisymm hVstar_le_V hVVstar
  have hLle : L ≤ pCoreOf 2 (Subgroup.normalizer (V : Set G)) := by
    refine (le_inf ?_ ?_).trans hchar
    · exact hLcentV.trans (Subgroup.centralizer_le_normalizer (V : Set G))
    · simpa [hVstar_eq] using hLcentV
  have hL2 : IsPGroup 2 L := hVstar2.to_le hLle
  obtain ⟨k, hk⟩ := hL2.exists_card_eq
  rw [hk] at hL3
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hL3) (by norm_num)

theorem odd_card_of_normal {G : Type} [Group G] [Finite G] (hG : IsCharTwoType G) {b : G}
    (hb : orderOf b = 3) {L : Subgroup G} (hLb : L ≤ Subgroup.centralizer ({b} : Set G))
    (hbL : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hLs : IsSimpleGroup ↥L) (hL3 : 3 ∣ Nat.card L) {A : Subgroup G} (hAs : IsSimpleGroup ↥A)
    (hA168 : Nat.card A = 168) (hbA : b ∈ A)
    (hDA : ∀ x : G, x ∈ Subgroup.centralizer (L : Set G) → x * b = b * x →
      (∃ k : ℕ, orderOf x = 2 ^ k) → ∀ y ∈ A, x * y = y * x)
    (R : Subgroup G) (hRb : R ≤ Subgroup.centralizer ({b} : Set G))
    (hRN : (R.subgroupOf (Subgroup.centralizer ({b} : Set G))).Normal) (hR3 : ¬ 3 ∣ Nat.card R) :
    Odd (Nat.card R) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Cb : Subgroup G := Subgroup.centralizer ({b} : Set G)
  let D : Subgroup G := Subgroup.centralizer (L : Set G) ⊓ Cb
  by_contra hodd
  have hRL : R ⊓ L = ⊥ := inf_eq_bot_of_normal_simple hLb hLs hL3 hRb hRN hR3
  have hRleD : R ≤ D := by
    refine le_inf ?_ hRb
    exact
      CFSG.RankThreeEvenClassification.Helpers.disjoint_mutually_normalized_subgroups_centralize
        R L (hRb.trans hbL)
        (hLb.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hRb).mp hRN))
        (disjoint_iff.mpr hRL)
  have hD2 : 2 ∣ Nat.card D := by
    have h2R : 2 ∣ Nat.card R := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    exact h2R.trans (Subgroup.card_dvd_of_le hRleD)
  let Q : Sylow 2 D := default
  let V : Subgroup G := (Q : Subgroup D).map D.subtype
  have hVsyl : CFSG.ABGLocalTools.IsSylowOf 2 V D := ⟨Q, rfl⟩
  have hV2 : IsPGroup 2 V := hVsyl.isPGroup
  have hVD : V ≤ D := hVsyl.le
  have hVne : V ≠ ⊥ := by
    intro hbot
    have hQne : (Q : Subgroup D) ≠ ⊥ :=
      Sylow.ne_bot_of_dvd_card (G := D) (p := 2) Q hD2
    exact hQne ((Subgroup.map_eq_bot_iff_of_injective (Q : Subgroup D)
      D.subtype_injective).mp hbot)
  let W : Subgroup G := pCoreOf 2 (Subgroup.normalizer (V : Set G)) ⊓ Cb
  have hWV : W = V := inf_pCoreOf_centralizer_eq_sylow hLb hbL hLs hL3 hVD hV2 hVsyl
  have hLcentV : L ≤ Subgroup.centralizer (V : Set G) := fun l hl =>
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      ((Subgroup.mem_centralizer_iff.mp (hVD hv).1) l hl).symm
  have hVstar_le_V : pCoreOf 2 (Subgroup.normalizer (V : Set G)) ≤ V :=
    pCoreOf_le_sylow_of_lemmaF hb hAs hA168 hbA hDA hVD hV2 hWV
  have hVstar2 : IsPGroup 2 (pCoreOf 2 (Subgroup.normalizer (V : Set G))) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Subgroup.normalizer (V : Set G))
  have hVVstar : V ≤ pCoreOf 2 (Subgroup.normalizer (V : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 V hV2
  exact false_of_pCore_le hG hVne hV2 hVVstar hVstar2 hVstar_le_V hLcentV hL3

end CFSG.StandardType.FF81
