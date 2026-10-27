module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSmallDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT8Proof

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c34_t8_caseThree (D : Data G) (h153 : R15_3Small D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV₀ : mSub V₀ ≤ 2)
    (hs4 : s15 D.M V₀ V h.hyp151.isElemAbelian L = 4)
    (htr : ∃ φ ∈ Mbar D.M (v1Sub D.M V₀ V h.hyp151.isElemAbelian L) V h.hyp151.isElemAbelian,
      InducesTransvection φ (wStar D.M V₀ V h.hyp151.isElemAbelian L)) :
    Case153_3 D V₀ V h.hyp151.isElemAbelian L := by
  rcases h153 V₀ V L h.hyp151 hV₀ htr with h1 | h2 | h3
  · obtain ⟨-, -, -, -, h1s, -⟩ := h1
    omega
  · exfalso
    obtain ⟨K₀, p, -, -, -, -, -, hrs, -⟩ := h2
    rw [hs4] at hrs
    have hne : (conjSet (barSub V₀ V h.hyp151.isElemAbelian K₀)
        (Mbar D.M V₀ V h.hyp151.isElemAbelian ⊓
          normalizer ((lBar V₀ V h.hyp151.isElemAbelian L : Subgroup _) : Set _))).Nonempty :=
      ⟨barSub V₀ V h.hyp151.isElemAbelian K₀, 1, Subgroup.one_mem _, by ext x; simp⟩
    have hpos := (Set.ncard_pos (Set.toFinite _)).2 hne
    omega
  · exact h3

theorem s16c34_t8_one (D : Data G) (h153 : R15_3Small D) (h1217 : R1217 D) (h127 : R127 D)
    (h1110 : R1110W D) (h1219 : D.sig = D.sig1) : RT8One D := by
  intro V₀ V L h hL hV1 hs4 hγ u hu hu2 hsupp hfix a ha hc
  have hle : V₀ ≤ ⊥ := by
    have := s15_Infra_le_v1Sub D.M V₀ V h.hyp151.isElemAbelian L
    rwa [hV1] at this
  obtain rfl : V₀ = ⊥ := le_bot_iff.1 hle
  have hMV : D.M ≤ normalizer (V : Set G) := h.hyp151.hyp125.pairFacts.le_normalizer
  have hMV₀ : D.M ≤ normalizer ((⊥ : Subgroup G) : Set G) :=
    h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hus : u ∈ stabTil ⊥ V := le_stabTil hMV hMV₀ hu
  have hav : a ∈ V := ha
  have hz : a * u * a⁻¹ * u⁻¹ ∈ V := by
    have h1 : u * a⁻¹ * u⁻¹ ∈ V := (mem_normalizer_iff.1 (hMV hu) a⁻¹).1 (V.inv_mem hav)
    have h2 : a * u * a⁻¹ * u⁻¹ = a * (u * a⁻¹ * u⁻¹) := by group
    rw [h2]
    exact V.mul_mem hav h1
  have htr := s15_T8_transvection D h hL h1217 hV1 hu hu2 hfix ha hc
  have hcase := s16c34_t8_caseThree D h153 h (by simp [mSub, rk_bot]) hs4 htr
  obtain ⟨r, B, Y, J, hB, hA⟩ :=
    s15_T8_blocks D h1217 h hL hV1 hs4 hγ hcase hu hu2 hsupp hfix hus ha hz
  have hcount := s15_T8_fix_count hB hA
  obtain ⟨N, hNle, hNn, hNab, ⟨n, hn1, hNcard⟩, hNc, hrk⟩ := s15_T8_xbar hB hcount
  haveI : ((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal := UC22.cTilde_bot_normal D.M V hMV
  obtain ⟨Xbar, hXn, hXab, hXcard, hXc, hXrk⟩ :=
    s15_T8_bridge D h.hyp151.isElemAbelian hMV hNle hNn hNab hNcard hNc hz hrk
  have hHyp11 : F11.Hyp11 D ⊥ V := Hyp125.hyp11 h127 h.hyp151.hyp125
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (F11.O2p 3 D.M)
  have hmax := ((h1110 V hHyp11 3 Nat.prime_three (by norm_num) P hP).2.2 n hn1 Xbar hXn hXab
    hXcard hXc).2 h1219 (a * u * a⁻¹ * u⁻¹) hz hc hXrk
  exact (centralizer_le_of_uniqueMax D.maxLocal hc
    ⟨1, by simpa using h.hyp151.isElemAbelian.2 _ hz⟩ hmax).1

theorem s16c34_rt8_of_small (D : Data G) (h153 : R15_3Small D) (h1217 : R1217 D)
    (h127 : R127 D) (h1110 : R1110W D) (h1219 : D.sig = D.sig1) : RT8 D :=
  rt8_of_one (s16c34_t8_one D h153 h1217 h127 h1110 h1219)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
