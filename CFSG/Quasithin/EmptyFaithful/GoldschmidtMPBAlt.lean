module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMPBEq
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMPBA5
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMPBA7
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMPBRank

public section

namespace CFSG.Quasithin.C58NS.MPB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.SectionRank

variable {G : Type} [Group G] [Finite G]

theorem eq_of_alternating {H T N R P K X L : Subgroup G} (hmin : MinParabolic H T N)
    (hXsub : IsSubnormal X H) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (S : L246C127.Setting X R P K) (hXSQ : IsSQTKCat ↥X) (hPN : ¬ P ≤ N)
    (hPK : P = R ⊔ conjClosure K R) (hRT : R ≤ T) (hL : IsBlock2 X L) (hKL : K ≤ L)
    (hUV : blockU L ≤ VZ R X) {m n : ℕ} (hm : Odd m) (hn : Odd n) (hm3 : 3 ≤ m) (hn3 : 3 ≤ n)
    (hLm : IsAltQuotient L (Subgroup.centralizer (VZ R X : Set G)) m)
    (hKn : IsAltQuotient K (Subgroup.centralizer (VZ R X : Set G)) n) : K = L := by
  obtain ⟨α, hα, hker⟩ := L246.exists_alt_pCore S.charTwo S.sylow hL hUV hLm
  have hcard := card_map_eq S.charTwo S.sylow hL hUV hKL α hker hKn
  have hfact : ∀ k : ℕ, 3 ≤ k →
      Nat.card (alternatingGroup (Fin k)) = Nat.factorial k / 2 := fun k hk => by
    have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [nat_card_alternatingGroup, Nat.card_fin]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXrank : CFSG.Open.pRank 3 X ≤ 2 := by
    have h6 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) = CFSG.Open.pRank 3 X :=
      pRank_top_subtype (p := 3) X
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 2 :=
      isStronglyQuasithin_iff.mp hXSQ.1 3 Nat.prime_three (by norm_num)
    omega
  have hm8 : m ≤ 8 := by
    by_contra h
    push Not at h
    have h3L := L246.three_le_pRank_of_alt (by omega) α hα hker
    have h4 : CFSG.Open.pRank 3 L ≤ CFSG.Open.pRank 3 X := pRank_mono (by norm_num) hL.2.1
    omega
  have hnm : n ≤ m := by
    by_contra h
    push Not at h
    have h1 : Nat.card ((K.subgroupOf L).map α) ≤ Nat.card (alternatingGroup (Fin m)) :=
      Subgroup.card_le_card_group _
    rw [hcard, hfact n hn3, hfact m hm3] at h1
    have h2 : Nat.factorial m < Nat.factorial n := (Nat.factorial_lt (by omega)).2 h
    have h3 : 2 ∣ Nat.factorial m := Nat.dvd_factorial (by norm_num) (by omega)
    have h4 : 2 ∣ Nat.factorial n := Nat.dvd_factorial (by norm_num) (by omega)
    omega
  rcases hnm.eq_or_lt with hnm | hnm
  ·
    subst hnm
    refine eq_of_image_top S hL hKL α hker ?_
    exact Subgroup.eq_top_of_card_eq _ (by rw [hcard])
  ·
    obtain ⟨a, ha⟩ := hm
    obtain ⟨b, hb⟩ := hn
    have hm' : m = 5 ∨ m = 7 := by omega
    rcases hm' with rfl | rfl
    · have hn' : n = 3 := by omega
      subst hn'
      exfalso
      refine false_of_three_five S hL α hα ?_
      rw [hcard, hfact 3 le_rfl]
      decide
    · exfalso
      have hLsub : IsSubnormal L H := A4.subnormal_trans (C1GN.isSubnormal_of_isBlock2 hL) hXsub
      have hTL : T ≤ Subgroup.normalizer (L : Set G) :=
        hTX.trans (normalizer_le_of_seven S.charTwo hXSQ hL α hα hker)
      have hLN : L ≤ N := le_of_seven hmin hLsub hTL α hα hker
      have hTN : T ≤ N := by
        have hmem : N ∈ maxOver H T := by
          have hU : maxOver H T = {N} := hmin.uniqueMax
          rw [hU]
          exact Set.mem_singleton N
        exact hmem.2
      apply hPN
      rw [hPK]
      refine sup_le (hRT.trans hTN) (conjClosure_le fun r hr k hk => ?_)
      have hrL : r ∈ Subgroup.normalizer (L : Set G) := hTL (hRT hr)
      exact hLN ((Subgroup.mem_normalizer_iff.1 hrL k).1 (hKL hk))

end CFSG.Quasithin.C58NS.MPB
