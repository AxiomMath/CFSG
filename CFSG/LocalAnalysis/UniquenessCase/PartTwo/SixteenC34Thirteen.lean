module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Eleven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Twelve
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Ten
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenE

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R15_13Small (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp154 D V₀ V L), mSub V₀ ≤ 2 →
    barSub V₀ V h.hyp151.isElemAbelian L ≠ ⊥ →
      gamma15 D.M V₀ V h.hyp151.isElemAbelian L ≤ 3 ∧
        s15 D.M V₀ V h.hyp151.isElemAbelian L = 2

theorem R15_13.toSmall {D : Data G} (h : R15_13 D) : R15_13Small D :=
  fun V₀ V L h' _ hL => h V₀ V L h' hL

theorem s16c34_r1111_of_153 {D : Data G} (h : R1111_153 D) : R1111 D := by
  intro V₀ V hH hN p hp
  obtain ⟨h1, h2⟩ := h V₀ V hH p hp
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank p D.M,
    CFSG.SectionRank.pRank_coe_eq_openPRank p (⊤ : Subgroup (F11.MBar11 D.M V₀ V))]
  exact ⟨by omega, by omega⟩

theorem s16c34_thirteen_k_of_large_s (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h1217 : R1217 D) (h1110 : R1110Core D) (h127 : R127 D)
    {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hγ : gamma15 D.M V₀ V hV L = 2)
    (hs : 7 ≤ s15 D.M V₀ V hV L) : D.k = 1 := by
  classical
  have hpf := h.hyp151.hyp125.pairFacts
  haveI hNorm : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
    WeakClosure81.cTilde_subgroupOf_normal hV hpf.le_normalizer hpf.le_normalizer₀
  obtain ⟨n, hsn, Xbar, hXnorm, hXel, hXcard, hXc⟩ :=
    s15_Thirteen_exists_xbar D h1217 h.hyp151 hV hL hγ
  have hn6 : 6 ≤ n := by omega
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp151.hyp125
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (F11.O2p 3 D.M)
  have hO2p_le : F11.O2p 3 D.M ≤ D.M := by
    rw [F11.O2p]
    exact Subgroup.map_subtype_le _
  have hPle : P ≤ D.M := by
    obtain ⟨Q, hQ⟩ := hP
    rw [← hQ]
    exact (Subgroup.map_subtype_le (Q : Subgroup ↥(F11.O2p 3 D.M))).trans hO2p_le
  have hBple : F11.barPreimage11 D.M V₀ V Xbar ≤ D.M := by
    rw [F11.barPreimage11]
    exact Subgroup.map_subtype_le _
  have hRle : P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar ≤ D.M :=
    (inf_le_left.trans inf_le_left).trans hPle
  have hOmega : F11.Omega1p 3 (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar) ≤
      D.M := by
    rw [F11.Omega1p]
    exact (Subgroup.closure_le D.M).mpr fun x hx => hRle hx.1
  have hkey := ((h1110 V₀ V hH11 3 Nat.prime_three (by norm_num) P hP).2.2 n
    (by omega) Xbar hXnorm hXel hXcard hXc).2.2.2
  have hle : CFSG.Open.pRank 3 (F11.Omega1p 3 (P ⊓ ⁅D.M, D.M⁆ ⊓
      F11.barPreimage11 D.M V₀ V Xbar)) ≤ CFSG.Open.pRank 3 D.M :=
    CFSG.SectionRank.pRank_mono (by norm_num) hOmega
  have h4 : 4 ≤ CFSG.Open.pRank 3 D.M := by
    have h3 : 3 ≤ n / 2 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 (by omega)
    exact le_trans (by omega : 4 ≤ n / 2 + 1) (le_trans hkey hle)
  exact s15_Thirteen_k_eq_one_of_three_mem D hSg h1219
    (hSg.four_mem 3 Nat.prime_three (by norm_num) h4)

theorem s16c34_thirteen_gamma_two (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h1217 : R1217 D) (h1110 : R1110Core D) (h1111 : R1111 D)
    (h127 : R127 D) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hγ : gamma15 D.M V₀ V hV L = 2) :
    D.k = 1 ∨ (5 ∈ D.sig ∧ (s15 D.M V₀ V hV L = 5 ∨ s15 D.M V₀ V hV L = 6)) := by
  by_cases h7 : 7 ≤ s15 D.M V₀ V hV L
  · exact Or.inl (s16c34_thirteen_k_of_large_s D hSg h1219 h1217 h1110 h127 h hV hL hγ h7)
  · by_cases h3 : 3 ∈ D.sig
    · exact Or.inl (s15_Thirteen_k_eq_one_of_three_mem D hSg h1219 h3)
    · right
      obtain ⟨p, hp⟩ := hSg.nonempty
      have hpp := D.sig_prime p hp
      have hpf := h.hyp151.hyp125.pairFacts
      haveI : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
        WeakClosure81.cTilde_subgroupOf_normal hV hpf.le_normalizer hpf.le_normalizer₀
      have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp151.hyp125
      obtain ⟨-, h1p⟩ := h1111 V₀ V hH11 p hp
      rcases s15_Thirteen_mbar_primes D h1217 h hV hL hγ (by omega) hpp.1 h1p with
        h2 | h3' | ⟨h5, hs5⟩
      · exact absurd h2 hpp.2
      · exact absurd (h3' ▸ hp) h3
      · exact ⟨h5 ▸ hp, by omega⟩

theorem s16c34_fifteen_thirteen (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h129 : R129_1 D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h127 : R127 D) (h1217 : R1217 D)
    (h1110 : R1110Core D) (h1111 : R1111 D) (h115 : F11.R115 D)
    (h159 : R15_9Small D) (h1511 : R15_11Small D) (h1512 : R15_12Small D) :
    R15_13Small D := by
  intro V₀ V L h hV₀ hL
  have hV := h.hyp151.isElemAbelian
  by_contra hcon
  have hcon' : ¬ (gamma15 D.M V₀ V hV L ≤ 3 ∧ s15 D.M V₀ V hV L = 2) := hcon
  have hpos : Hyp125 D V₀ V := h.hyp151.hyp125
  have hkc := s15_Thirteen_k_cases D
  have hW : E3.wClos V 0 D.T ≤ centralizer (V : Set G) :=
    (E3.wClos_mono D.sylowM.le).trans (h159 V₀ V L h hV₀ hL)
  have hrk : ∀ p ∈ D.sig, 3 ≤ CFSG.pRank p D.M := fun p hp => by
    rw [UC6.groupPRank_eq_pRank]
    exact hSg.three_le p hp
  have hN := fifteen_thirteen_a D h129 h61 hSg.nonempty hrk hpos hW
  have h2' : gamma15 D.M V₀ V hV L = 2 →
      D.k = 1 ∨ (5 ∈ D.sig ∧ (s15 D.M V₀ V hV L = 5 ∨ s15 D.M V₀ V hV L = 6)) :=
    fun hγ => s16c34_thirteen_gamma_two D hSg h1219 h1217 h1110 h1111 h127 h hV hL hγ
  have h2 : gamma15 D.M V₀ V hV L = 2 → D.k = 1 ∨ s15 D.M V₀ V hV L = 5 ∨ s15 D.M V₀ V hV L = 6 :=
    fun hγ => (h2' hγ).imp_right fun h5 => h5.2
  have hγ2 := two_le_gamma15 D h.hyp151 hV hL
  have hs2 := fifteen_five D h129 h1217 h hV hL
  have hkm := s15_Thirteen_k_lt_m hγ2 (by omega) hkc hcon' h2
  have hC : centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M := by
    by_contra hnC
    obtain ⟨-, hcase⟩ := h1511 V₀ V L h hV₀ hL D.k (by omega) hnC
    rcases hcase with ⟨hγ, hs4, hk2⟩ | ⟨hs, hγ3⟩
    · rcases h2 hγ with h1 | h5 | h6 <;> omega
    · exact hcon' ⟨hγ3, hs⟩
  have hr := s15_Thirteen_lt_rParam D h hV hL hkm
  have hbeta : (D.k : ℕ∞) < betaN 0 D.M V :=
    lt_of_lt_of_le (by exact_mod_cast hkm) (s15_Thirteen_beta D h1217 h hV hL)
  obtain ⟨H, A, K, hS, hA, hK, hne⟩ := s15_Thirteen_exists_A_K D h126 hpos hN hC
  obtain ⟨X, g, hX, hg⟩ := s15_Thirteen_six_nine D hpos hS hA hK hr hbeta hne
  have hO : (calO D.k D.M V₀ V).Nonempty := ⟨X, g, hX, hg.1⟩
  have hkγ : D.k < gamma15 D.M V₀ V hV L := by
    by_contra hnk
    have hγ : gamma15 D.M V₀ V hV L = 2 := by omega
    rcases h2' hγ with h1 | ⟨h5, hs5⟩
    · omega
    · have hcard : Nat.card V₀ ≤ 4 := by
        have hpow := card_eq_two_pow_mSub
          h.hyp151.hyp125.pairFacts.elemAbelian₀.isPGroup
        rw [hpow]
        calc 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hV₀
          _ = 4 := by norm_num
      exact s15_Thirteen_gap1_small D hSg h1219 h1217 h127 h1111 h115 h hV hL hγ (by omega)
        h5 hs5 hcard
  exact hcon (h1512 V₀ V L h hV₀ hL D.k (by omega) hkγ hO)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
