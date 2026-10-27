module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UCKPFI3
import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS
import CFSG.LocalAnalysis.UniquenessCase.UC6R869T3
import CFSG.LocalAnalysis.UniquenessCase.UC6R869Pair
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213a
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213Tc
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeK1
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3A
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3B

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

theorem uc22s217l2_false_of_not_isPowTwo (D : Data G) (Ch : Choice2011 G)
    (he : 3 < CFSG.Open.evenRank G) (hK3 : StronglyEmbeddedThree) (hH : H1930 D)
    (c : Ctx21 D Ch) (hc : ¬ IsPowTwo c.n) (hSE : IsStronglyPEmbedded 3 D.M)
    {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hn : IsPowTwo n) (hL2 : IsL2 (Bar2 L) n)
    (hfix : ∀ K ∈ conjSetOf D.M L, c.B0 ≤ normalizer (K : Set G))
    (h3 : 2 ≤ CFSG.Open.pRank 3 (conjClosure D.M L)) : False := by
  classical
  obtain ⟨s, r, hs, hsn, hr, hrs, -⟩ := uc22s217u3b_exists_sr (uc22p2213a_n_ne_zero D c) hc
  haveI : Fact r.Prime := ⟨hr⟩
  have hr5 : 5 ≤ r := UC6S898.prime_ne_two_three_of_dvd hr hs hrs
  have hr2 : r ≠ 2 := by omega
  obtain ⟨j, rfl⟩ := hn
  have hrn : ¬ r ∣ 2 ^ j := fun h =>
    hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  have hrL : ∀ {X : Type} [Group X] [Finite X], IsL2 X (2 ^ j) → ¬ r ∣ Nat.card X := by
    intro X _ _ hX h
    rw [uc22p22r_L2_card hX] at h
    rcases (Nat.Prime.dvd_mul hr).1 h with h1 | h1
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h1))
    · rw [← pow_mul] at h1
      have h2 : r ∣ Nat.gcd (2 ^ s - 1) (2 ^ (2 ^ j * 2) - 1) := Nat.dvd_gcd hrs h1
      rw [Nat.pow_sub_one_gcd_pow_sub_one] at h2
      have hg : Nat.gcd s (2 ^ j * 2) = 1 := by
        rw [← pow_succ]
        exact Nat.Coprime.pow_right _ hs.coprime_two_right
      rw [hg, pow_one] at h2
      exact hr.not_dvd_one (by simpa using h2)
  have hrB : r ∣ Nat.card c.B0 := by
    have hmod : 2 ^ c.n % r = 1 := UCK.two_pow_mod_eq_one hr hrs hsn
    have : r ∈ piSet c.B0 := by
      rw [c.hpi]
      exact ⟨hr, Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq
        (by rw [hmod, Nat.mod_eq_of_lt hr.one_lt]))⟩
    exact this.2
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' r hrB
  have hbB : (b : G) ∈ c.B0 := b.2
  have hbM : (b : G) ∈ D.M := c.hBM hbB
  have hbr : orderOf (b : G) = r := by rw [Subgroup.orderOf_coe, hb]
  have hbr1 : (b : G) ^ r = 1 := by
    rw [← hbr]
    exact pow_orderOf_eq_one _
  have hcb : ∀ K ∈ conjSetOf D.M L, CentralizesBar (b : G) K := by
    intro K hK
    have hbK := hfix K hK hbB
    have hK2 : IsL2 (Bar2 K) (2 ^ j) := by
      obtain ⟨g, -, rfl⟩ := hK
      obtain ⟨e⟩ := uc22p20d_bar2_conj g L
      exact CFSG.Blueprint.LieModel.of_mulEquiv e hL2
    exact uc22p2213a_centralizesBar_of_prime hK2 hr hrn (hrL hK2) hbK hbr1
  obtain ⟨hXM, hMX, hprod⟩ := uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hL
  have hbX : CentralizesBar (b : G) (conjClosure D.M L) := by
    refine uc22p2214_centralizesBar_conjClosure (hMX hbM) fun K hK k hk => ?_
    have hKC := uc22p2214_calC_of_mem_conjSetOf hL hK
    have h1 : (b : G) * k * (b : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 D.M :=
      uc22p22r_pCoreOf_le_of_isSubnormal hKC.1 ((hcb K hK).2 k hk)
    have hkX : k ∈ conjClosure D.M L := uc22s217u3a_le_conjClosure hK hk
    have h2 : (b : G) * k * (b : G)⁻¹ * k⁻¹ ∈ conjClosure D.M L :=
      (conjClosure D.M L).mul_mem ((mem_normalizer_iff.1 (hMX hbM) k).1 hkX)
        ((conjClosure D.M L).inv_mem hkX)
    exact uc22p2214_pCoreOf_inf_le hXM ⟨h1, h2⟩
  have hbc : Nat.card (zpowers (b : G)) = r := by rw [Nat.card_zpowers, hbr]
  have hXQ := uc22p21d_sup_pCore_eq hr hr2 hbc fun g hg =>
    uc22p21d_centralizesBar_of_mem_zpowers hbX hg
  have hS4 : Standing4 G :=
    ⟨D.standing.simple, D.standing.nonab, D.standing.kProper, D.standing.charTwo, by omega⟩
  have hAB : zpowers (b : G) ≤ c.B0 := Subgroup.zpowers_le.2 hbB
  exact s21_2 D Ch hH { c with B := c.B0, hB := c.hB0, hle := le_rfl } (zpowers (b : G)) hAB
    (UC6.R869S.normalizer_le_of_strongThree hS4 hK3 hSE hXM
      (UC6.R869S.perfect_of_isProdOfCalC hprod) h3 hr (hAB.trans c.hBM) hbc hXQ)

theorem uc22s217l2_ncard_le_two (D : Data G) (Ch : Choice2011 G)
    (he : 3 < CFSG.Open.evenRank G) (hK3 : StronglyEmbeddedThree) (h82 : F08.R82 D)
    (h5 : S21_5 D Ch) (hH : H1930 D) (c : Ctx21 D Ch) (hn3 : 3 ≤ c.n)
    {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hn : IsPowTwo n) (hL2 : IsL2 (Bar2 L) n) :
    (conjSetOf D.M L).ncard ≤ 2 := by
  by_contra h2
  obtain ⟨K₁, K₂, K₃, h₁, h₂, h₃, h12, h13, h23⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite _)).1 (not_le.1 h2)
  have hKs : ∀ K ∈ conjSetOf D.M L, K ∈ calC D.M ∧ IsL2 (Bar2 K) n := fun K hK =>
    ⟨uc22p2214_calC_of_mem_conjSetOf hL hK, by
      obtain ⟨g, -, rfl⟩ := hK
      obtain ⟨e⟩ := uc22p20d_bar2_conj g L
      exact CFSG.Blueprint.LieModel.of_mulEquiv e hL2⟩
  have h81 := P22fin3.hyp81_of_three_isL2 (hKs K₁ h₁).1 (hKs K₂ h₂).1 (hKs K₃ h₃).1 h12 h13 h23
    (hKs K₁ h₁).2 (hKs K₂ h₂).2 (hKs K₃ h₃).2
  have hSE : IsStronglyPEmbedded 3 D.M := h82 _ h81
  by_cases hc : IsPowTwo c.n
  · exact uc22p2213t_not_stronglyEmbedded_three D Ch hH c (by omega) hc hSE
  have h3 : 2 ≤ CFSG.Open.pRank 3 (conjClosure D.M L) := by
    have hle : K₁ ⊔ K₂ ⊔ K₃ ≤ conjClosure D.M L :=
      sup_le (sup_le (uc22s217u3a_le_conjClosure h₁) (uc22s217u3a_le_conjClosure h₂))
        (uc22s217u3a_le_conjClosure h₃)
    have h4 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hle
    have h81r := h81.2.2.1
    omega
  exact uc22s217l2_false_of_not_isPowTwo D Ch he hK3 hH c hc hSE hL hn hL2
    (fun K hK x hx => h5 hH { c with B := c.B0, hB := c.hB0, hle := le_rfl } K
      (uc22p2214_calC_of_mem_conjSetOf hL hK) hx) h3

theorem uc22s217l2_isPowTwo_of_pair (D : Data G) (Ch : Choice2011 G)
    (he : 3 < CFSG.Open.evenRank G) (hK3 : StronglyEmbeddedThree) (h8100E : R8100E D)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) (hL2 : IsL2 (Bar2 L) 2) : IsPowTwo c.n := by
  by_contra hc
  have h2 : IsPowTwo 2 := ⟨1, (pow_one 2).symm⟩
  have hSE := h8100E he L hL hc2 2 le_rfl h2 hL2
  have h3 : 2 ≤ CFSG.Open.pRank 3 (conjClosure D.M L) :=
    UC6.R869S.two_le_pRank_pair_of_isL2 hL hc2 hL2 Nat.prime_three (by norm_num) (by
      rw [uc22p22r_L2_card hL2]
      norm_num)
  refine uc22s217l2_false_of_not_isPowTwo D Ch he hK3 hH c hc hSE hL h2 hL2
    (fun K hK x hx => ?_) h3
  rw [← uc22p2214_conjSetOf_eq hK] at hc2
  exact uc22p2214_mem_normalizer_of_odd hc2 (c.hBM hx) (uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 hx)

end CFSG.LocalAnalysis.UniquenessCase.UC22
