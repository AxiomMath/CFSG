module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.JMEqualFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HeJ2Local17
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZB
public import CFSG.GroupTheory.OddOrderClosurePerfect
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwelveCommutant
public import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeafProof (lieModel_eq_of_isChar2LieShape)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified


theorem omegaMinusData_of_df (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) {n : ℕ} (hm3 : MBarGT D.M V₀ V 3)
    (h6b : R18_6bAt D V₀ V p L h) (h7b : R18_7bAt D V₀ V p L h)
    (h8 : R18_8At D V₀ V p L h) (h9 : R18_9At D V₀ V p L h)
    (h10 : R18_10At D V₀ V p L h)
    (hL2 : IsL2 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) n) :
    Even n ∧
      IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 4 (n / 2) ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K)
          (π : ↥(StatedOmega (StatedQuadMinus 2 K b c)) →*
            ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))),
          Nat.card K = 2 ^ (n / 2) ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
            Inputs1719.SumOfNatVia
              (CFSG.Quasithin.FFModel.nat (StatedOmega (StatedQuadMinus 2 K b c)))
              (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤ ⊥ 2 π := by
  have hs : IsSimpleGroup
      ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  obtain ⟨hXL, ⟨e⟩⟩ := conjClosure_eq_and_bar2_equiv_of_hyp18 h hs
  have eX : Bar2 (conjClosure D.M L) ≃*
      ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) := by
    rw [hXL]
    exact e
  rcases h6b hm3 h7b with h2 | h3 | h4 | h5 | h6
  ·
    obtain ⟨m, hSUn | hOm6 | hOp4⟩ := h10 h2
    · exact absurd (lieModel_eq_of_isChar2LieShape hL2 (Or.inl ⟨rfl, rfl⟩)
        (isU4_of_isSUn_four hSUn)).1 (by decide)
    · exact absurd (lieModel_eq_of_isChar2LieShape hL2 (Or.inl ⟨rfl, rfl⟩)
        (isU4_of_isOmegaMinus hOm6)).1 (by decide)
    · exact absurd hs (not_isSimpleGroup_of_isOmegaPlus_four hOp4)
  ·
    obtain ⟨f, hsp | hom6 | hom4⟩ := h3
    · obtain ⟨hSp, -⟩ := hsp
      exact absurd (lieModel_eq_of_isChar2LieShape hL2 (Or.inl ⟨rfl, rfl⟩)
        (LieModel.of_mulEquiv eX hSp)).1 (by decide)
    · obtain ⟨hom6', -⟩ := hom6
      exact absurd (lieModel_eq_of_isChar2LieShape hL2 (Or.inl ⟨rfl, rfl⟩)
        (isU4_of_isOmegaMinus hom6')).1 (by decide)
    · obtain ⟨hEven, hOm4, K, hKf, hKfin, b, c, π, hKcard, hhbc, hsum⟩ := hom4
      have hk : 1 ≤ f / 2 := by
        exact CFSG.ComponentClassification.CatLeafProof.one_le_of_card_eq_pow hKcard
      have hL2f : IsL2 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))
          (2 * (f / 2)) := isL2_of_isOmegaMinus_four hk hOm4
      have hfn : n = 2 * (f / 2) := S17.isL2_field_unique hL2 hL2f
      have hEven' : Even n := ⟨f / 2, by omega⟩
      have hnf : n / 2 = f / 2 := by omega
      refine ⟨hEven', ?_, K, hKf, hKfin, b, c, π, ?_, hhbc, hsum⟩
      · rw [hnf]
        exact hOm4
      · rw [hnf]
        exact hKcard
  · exact absurd h4 h9
  · exact absurd h5 h8
  · obtain ⟨hSUn, -⟩ := h6
    exact absurd (lieModel_eq_of_isChar2LieShape hL2 (Or.inl ⟨rfl, rfl⟩)
      (isU4_of_isSUn_four hSUn)).1 (by decide)

theorem gap_18_12_K_of (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V)
    (h641 : S17.R17_64_1At D V₀ V) (h642 : S17.R17_64_2At D V₀ V)
    (h643 : S17.R17_64_3At D V₀ V) (h184 : R18_4At D V₀ V p L)
    (h6b : R18_6bAt D V₀ V p L h) (h7b : R18_7bAt D V₀ V p L h)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h8 : R18_8At D V₀ V p L h) (h9 : R18_9At D V₀ V p L h)
    (h10 : R18_10At D V₀ V p L h) :
    Gap_18_12_K D V₀ V p L h := by
  have hKC := @k_18_12_commutant_holds
  intro n hL2
  have hV := h.hyp125.isElemAbelian
  have hs : IsSimpleGroup ↥(barSub V₀ V hV (conjClosure D.M L)) :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  obtain ⟨hXL, ⟨e⟩⟩ := conjClosure_eq_and_bar2_equiv_of_hyp18 h hs
  have hL2' : IsL2 ↥(barSub V₀ V hV L) n := hXL ▸ hL2
  have hL2B : IsL2 (Bar2 L) n := LieModel.of_mulEquiv e.symm hL2'
  have hcard2 : Nat.card V₀ ≤ 2 :=
    (mSub_le_one_iff h.hyp125.pairFacts.elemAbelian₀).1 h.small
  have hm3 : MBarGT D.M V₀ V 3 := h1669 (hcard2.trans (by norm_num))
  have hthin : F08.Thin8 L := S17.thin8_of_isL2 hL2B
  have hL0 : L ∈ S17.calL0Star D p := hXL ▸ h.hX
  have h54 : S17.Hyp1754 D p :=
    S17.hyp1754_of_thin_mem_calL0Star D h1742 h.hp h.hL hL0 hthin
  obtain ⟨m, hHinf, hm, hpow, hL2m⟩ :=
    S17.exists_p1642_isL2_of_self h1742 h641 h642 h643 h.hp h.hL hL0 hthin
  have hmn : m = n := S17.isL2_field_unique hL2m hL2B
  have hm' : S17.P17_64_2 D p n := hmn ▸ hm
  have hpow' : IsPowTwo n := hmn ▸ hpow
  have hcong : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] := (h643 p h54 n hm').2
  have hpn : p ∣ 2 ^ n + 1 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.P2214R.dvd_of_cong hcong
  have hn2 : 2 ≤ n := uc22p20g_two_le_of_isL2 hL2B
  have hn2' : n ≠ 2 := by
    intro h2
    exact h184 (S17.isAlt_five_of_isL2_two (h2 ▸ hL2B))
  obtain ⟨k, hk⟩ := hpow'
  have hk2 : 2 ≤ k := by
    by_contra h
    have hk1 : k ≤ 1 := by omega
    interval_cases k
    · norm_num at hk
      omega
    · norm_num at hk
      exact hn2' hk
  have hn4 : 4 ≤ n := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  have hnEven : Even n := by
    rw [hk]
    exact Nat.even_pow.2 ⟨even_two, by omega⟩
  have hnot3 : ¬ 3 ∣ 2 ^ n + 1 := by
    intro hd
    have h0 : (2 ^ n + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
    rw [Nat.add_mod, CFSG.two_pow_mod_three_of_even hnEven] at h0
    norm_num at h0
  obtain ⟨KA, KB, hKA, hKB, hL2KA, hshapeKB, hne⟩ :=
    S17.exists_two_calC_of_p1642 hm' hHinf
  have hchoose : ∃ K : Subgroup G, K ∈ calC D.M ∧
      (IsL2 (Bar2 K) n ∨ IsU3 (Bar2 K) n) ∧ K ≠ L := by
    by_cases hKAL : KA = L
    · refine ⟨KB, hKB, hshapeKB, ?_⟩
      intro hKBL
      exact hne (by rw [hKAL, hKBL])
    · exact ⟨KA, hKA, Or.inl hL2KA, hKAL⟩
  obtain ⟨K, hKcal, hKshape, hKL⟩ := hchoose
  have hp : p.Prime := (D.sig_prime p h.hp).1
  have hpK : p ∣ Nat.card K := by
    rcases hKshape with hL2K | hU3K
    · exact (S17.dvd_card_bar2_of_isL2 hL2K hpn).trans
        (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K))
    · have hcard := S17.card_mul_gcd_of_isU3 hU3K
      have hgcd : Nat.gcd 3 (2 ^ n + 1) = 1 := by
        have hc : Nat.Coprime 3 (2 ^ n + 1) :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnot3
        simpa using hc
      rw [hgcd, mul_one] at hcard
      have h3n : p ∣ 2 ^ (3 * n) + 1 := by
        have hdvd : 2 ^ n + 1 ∣ 2 ^ (3 * n) + 1 := by
          have hcube : 2 ^ (3 * n) = (2 ^ n) ^ 3 := by
            rw [← pow_mul]
            ring_nf
          rw [hcube]
          exact Odd.nat_add_dvd_pow_add_pow (2 ^ n) 1 (by decide : Odd 3)
        exact hpn.trans hdvd
      have hpbar : p ∣ Nat.card (Bar2 K) := by
        rw [hcard]
        exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h3n (2 ^ (2 * n) - 1)) _
      exact hpbar.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K))
  have hKp : K ∈ S17.calLp D p := ⟨hKcal, hp, hpK⟩
  have hKn : (K.subgroupOf D.M).Normal := (h54.2 K hKcal).1
  have hKcc : conjClosure D.M K = K :=
    Inputs1719.conjClosure_eq_self_of_normal hKcal.1.le hKn
  have hsL : IsSimpleGroup (Bar2 L) := isSimpleGroup_bar2_of_hyp18 h hXL
  have hj : S17.jM D p = 4 :=
    S17.jM_eq_four_of_mem_calL0Star hL0 h.hL hsL h184 ⟨n, Or.inl hL2B⟩
  have hnotaltK : ¬ IsAlt (Bar2 K) 5 := by
    intro halt
    have hL2two : IsL2 (Bar2 K) 2 := S17.isL2_PSL2_two_of_isAlt_five halt
    rcases hKshape with hL2K | hU3K
    · exact hn2' (S17.isL2_field_unique hL2K hL2two)
    · exact absurd (lieModel_eq_of_isChar2LieShape hU3K
        (Or.inr (Or.inl ⟨rfl, rfl⟩)) hL2two).1 (by decide)
  have hKstar : K ∈ S17.calL0Star D p := by
    rw [S17.calL0Star, hj]
    have h4 : S17.calLjStar D p 4 = S17.calL4Star D p := rfl
    rw [h4, S17.mem_calL4Star]
    exact ⟨⟨K, hKp, hKcc.symm⟩, ⟨k, hk ▸ hKshape⟩, hnotaltK⟩
  obtain ⟨-, hOm4, Kf, hKf, hKfin, b, c, π, hKcard, hbc, hsum⟩ :=
    omegaMinusData_of_df D h hm3 h6b h7b h8 h9 h10 hL2
  have hCX := hKC (s15_Infra_vtil_sq_eq_one V₀ V hV)
    (barSub V₀ V hV (conjClosure D.M L)) (n / 2) Kf b c π hKcard hbc hsum
  have h4n : 4 * (n / 2) = 2 * n := by
    obtain ⟨r, hr⟩ := hnEven
    omega
  rw [h4n] at hCX
  have hKcomm : barSub V₀ V hV K ≤
      Subgroup.centralizer
        (barSub V₀ V hV (conjClosure D.M L) : Set (MulAut (Vtil V₀ V hV))) := by
    intro φ hφ
    obtain ⟨g, hgK, rfl⟩ := (mem_barSub V₀ V hV K φ).1 hφ
    rw [Subgroup.mem_centralizer_iff]
    intro ψ hψ
    obtain ⟨l, hlX, rfl⟩ :=
      (mem_barSub V₀ V hV (conjClosure D.M L) ψ).1 hψ
    have hlL : (l : G) ∈ L := by
      rw [hXL] at hlX
      exact hlX
    have hMstab : D.M ≤ stabTil V₀ V :=
      le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
    have hcommG : (g : G) * (l : G) * (g : G)⁻¹ * (l : G)⁻¹ ∈ pCoreOf 2 D.M :=
      uc22ine229_commutator_mem_of_ne hKcal h.hL.1 hKL hgK hlL
    have hcommStab : (g : G) * (l : G) * (g : G)⁻¹ * (l : G)⁻¹ ∈ stabTil V₀ V :=
      hMstab (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M hcommG)
    let u : stabTil V₀ V :=
      ⟨(g : G) * (l : G) * (g : G)⁻¹ * (l : G)⁻¹, hcommStab⟩
    have hu : u = g * l * g⁻¹ * l⁻¹ := Subtype.ext rfl
    have hbar : actTil V₀ V hV u = 1 := by
      have hmem : actTil V₀ V hV u ∈ barSub V₀ V hV (pCoreOf 2 D.M) :=
        actTil_mem_barSub V₀ V hV hcommG hcommStab
      rw [barSub_pCoreOf_eq_bot_of_hyp125 h.hyp125] at hmem
      simpa using hmem
    have h1 : actTil V₀ V hV g * actTil V₀ V hV l * (actTil V₀ V hV g)⁻¹ *
        (actTil V₀ V hV l)⁻¹ = 1 := by
      rw [← hbar, hu]
      simp only [map_mul, map_inv]
    have hcommute : actTil V₀ V hV g * actTil V₀ V hV l =
        actTil V₀ V hV l * actTil V₀ V hV g := by
      have h1' : ⁅actTil V₀ V hV g, actTil V₀ V hV l⁆ = 1 := by
        rwa [commutatorElement_def]
      exact commutatorElement_eq_one_iff_mul_comm.mp h1'
    exact hcommute.symm
  have hKs : IsSimpleGroup (Bar2 K) := by
    rcases hKshape with hL2K | hU3K
    · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2K
    · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU3K
  have hbar2gt : 2 ^ (2 * n) < Nat.card (Bar2 K) := by
    have hn1 : 1 ≤ n := by omega
    rcases hKshape with hL2K | hU3K
    · rw [S17.card_of_isL2 hL2K]
      have hA : 2 ^ n < 2 ^ (2 * n) - 1 := by
        have h2 : 2 ^ (n + 1) ≤ 2 ^ (2 * n) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        have h3 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
        have hq : 2 ≤ 2 ^ n := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
        omega
      have hq2 : 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [← pow_add]; ring_nf
      rw [hq2] at hA ⊢
      exact (Nat.mul_lt_mul_left (pow_pos (by norm_num : (0 : ℕ) < 2) n)).mpr hA
    · have hcard := S17.card_mul_gcd_of_isU3 hU3K
      have hgcd : Nat.gcd 3 (2 ^ n + 1) = 1 := by
        have hc : Nat.Coprime 3 (2 ^ n + 1) :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnot3
        simpa using hc
      rw [hgcd, mul_one] at hcard
      rw [hcard]
      have hA : 1 ≤ (2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1) := by
        have h1 : 1 ≤ 2 ^ (2 * n) - 1 := by
          have h4 : 4 ≤ 2 ^ (2 * n) := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
          exact Nat.sub_pos_of_lt (by omega)
        have h2 : 1 ≤ 2 ^ (3 * n) + 1 := Nat.succ_le_succ (Nat.zero_le _)
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      have hlt : 2 ^ (2 * n) < 2 ^ (3 * n) :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      calc 2 ^ (2 * n) < 2 ^ (3 * n) := hlt
        _ = 2 ^ (3 * n) * 1 := (mul_one _).symm
        _ ≤ 2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)) :=
            Nat.mul_le_mul_left _ hA
  have hKbot : barSub V₀ V hV K = ⊥ := by
    by_contra hne
    obtain ⟨eK⟩ := barSubBar2Equiv_of_isSimpleGroup h.hyp125 hKcal hne hKs
    have hKbar : Nat.card (barSub V₀ V hV K) = Nat.card (Bar2 K) :=
      (Nat.card_congr eK.toEquiv).symm
    have hbound : Nat.card (Bar2 K) ≤ 2 ^ (2 * n) := by
      rw [← hKbar]
      exact (Subgroup.card_le_of_le hKcomm).trans hCX
    omega
  have hperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKcal.2.1
  have hKV : K ≤ Subgroup.centralizer (V : Set G) := by
    have key : ∀ y : ↥K, Odd (orderOf y) →
        (y : G) ∈ Subgroup.centralizer (V : Set G) := by
      intro y hyodd
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hystab : (y : G) ∈ stabTil V₀ V :=
        le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
          (hKcal.1.le y.2)
      have hybar : actTil V₀ V hV ⟨(y : G), hystab⟩ = 1 := by
        have hmem : actTil V₀ V hV ⟨(y : G), hystab⟩ ∈ barSub V₀ V hV K :=
          actTil_mem_barSub V₀ V hV (X := K) y.2 hystab
        rw [hKbot] at hmem
        simpa using hmem
      have hfix : actTil V₀ V hV ⟨(y : G), hystab⟩ (tilOf V₀ V hV v hv) =
          tilOf V₀ V hV v hv := by
        rw [hybar]
        rfl
      have hoddG : Odd (orderOf (y : G)) := by
        rwa [Subgroup.orderOf_coe]
      have hfix' : (y : G) * v * (y : G)⁻¹ = v :=
        fixes_of_actTil_tilOf_eq_of_odd hV h.hyp125.pairFacts.le hcard2 hystab hv hfix hoddG
      exact (mul_inv_eq_iff_eq_mul.mp hfix').symm
    intro x hx
    exact CFSG.GroupTheory.map_le_of_isPerfect_of_forall_odd_order K.subtype
      (Subgroup.centralizer (V : Set G)) key ⟨x, hx⟩
  exact ⟨K, hKp, hKcc.symm ▸ hKstar, hKV, hKshape, hnotaltK⟩

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
