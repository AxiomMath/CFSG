module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKInputs
public import CFSG.Quasithin.Background.SmithB42Families
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.LargeExtraspecial.DW2AOut
public import CFSG.Quasithin.Background.F918G2
public import CFSG.RankThree.PartTwo.KFacts.L34Aut
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OuterTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.Sporadic.Bridge.M22

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

private theorem s16k_pRank_le_of_not_dvd {G : Type} [Group G] [Finite G] {H : Subgroup G}
    {p k : ℕ} (hp : p.Prime) (h : ¬ p ^ (k + 1) ∣ Nat.card H) : CFSG.Open.pRank p H ≤ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine CFSG.SectionRank.pRank_le hp.one_lt (fun E hEH hE => ?_)
  obtain ⟨m, hm⟩ := hE.isPGroup.exists_card_eq
  have hdvd : p ^ m ∣ Nat.card H := hm ▸ Subgroup.card_dvd_of_le hEH
  have hmk : m ≤ k := by
    by_contra hlt
    rw [not_le] at hlt
    exact h ((pow_dvd_pow p (by omega : k + 1 ≤ m)).trans hdvd)
  rw [hm]
  exact Nat.pow_le_pow_right hp.pos hmk

private theorem s16k_pRank_top_le_of_not_dvd {G : Type} [Group G] [Finite G] {p k : ℕ}
    (hp : p.Prime) (h : ¬ p ^ (k + 1) ∣ Nat.card G) :
    CFSG.Open.pRank p (⊤ : Subgroup G) ≤ k := by
  refine s16k_pRank_le_of_not_dvd (H := ⊤) hp ?_
  rwa [Subgroup.card_top]

private theorem s16k_not_pow_dvd (N r : ℕ) (hr : 0 < r) (S T : Finset ℕ) (hN : N ≠ 0)
    (hS : N.primeFactors = S) (hS' : ∀ q ∈ S, q ∉ T → ¬ q ^ r ∣ N) :
    ∀ p : ℕ, p.Prime → p ∉ T → ¬ p ^ r ∣ N := by
  intro p hp hpT h
  have hmem : p ∈ S := by
    rw [← hS]
    exact Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by omega)).trans h, hN⟩
  exact hS' p hmem hpT h

private theorem s16k_card_mulAut_dvd_of_outer_dvd {X : Type} [Group X] [Finite X] {k : ℕ}
    (hk : Nat.card (Outer X) ∣ k) : Nat.card (MulAut X) ∣ k * Nat.card X := by
  haveI : Finite (MulAut X) :=
    Finite.of_injective (fun φ : MulAut X => (φ : X → X)) DFunLike.coe_injective
  have hinner : Nat.card (inner X) ∣ Nat.card X := by
    have h1 : Nat.card (inner X) = Nat.card (X ⧸ (MulAut.conj : X →* MulAut X).ker) :=
      (Nat.card_congr
        (QuotientGroup.quotientKerEquivRange (MulAut.conj : X →* MulAut X)).toEquiv).symm
    rw [h1]
    exact Subgroup.card_quotient_dvd_card _
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (inner X)]
  exact mul_dvd_mul hk hinner

private theorem s16k_pRank_mulAut_le_of_isPGroup_outer {X : Type} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) (hOut : IsPGroup 2 (Outer X)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut X) :=
    Finite.of_injective (fun φ : MulAut X => (φ : X → X)) DFunLike.coe_injective
  have hIle : ∀ E : Subgroup (MulAut X), CFSG.Open.IsElemAbelian p E → E ≤ inner X := by
    intro E hE
    rw [← QuotientGroup.ker_mk' (inner X), ← Subgroup.map_eq_bot_iff]
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨k, hk⟩ := hOut (QuotientGroup.mk' (inner X) x)
    have hxp : (QuotientGroup.mk' (inner X) x) ^ p = 1 := by
      rw [← map_pow, hE.2 x hx, map_one]
    have hcop : Nat.Coprime p (2 ^ k) := by
      refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => hp2 ?_
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hxp) (orderOf_dvd_of_pow_eq_one hk))
  have hiso : X ≃* inner X := by
    have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      rw [Subgroup.mem_bot]
      have hxc : x ∈ Subgroup.center X := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 := congrArg (fun φ : MulAut X => φ g) hx
        simp only [MulAut.conj_apply, MulAut.one_apply] at h1
        calc g * x = (x * g * x⁻¹) * x := by rw [h1]
          _ = x * g := by group
      rw [hZ, Subgroup.mem_bot] at hxc
      exact hxc
    exact MonoidHom.ofInjective hinj
  calc CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ CFSG.Open.pRank p (inner X) := by
        refine CFSG.SectionRank.pRank_le hp.one_lt (H := ⊤)
          (k := CFSG.Open.pRank p (inner X)) (fun E _ hE => ?_)
        obtain ⟨m, hm⟩ := hE.isPGroup.exists_card_eq
        rw [hm]
        exact Nat.pow_le_pow_right hp.pos
          (CFSG.SectionRank.le_pRank hp.one_lt (hIle E hE) hE hm)
    _ = CFSG.Open.pRank p (⊤ : Subgroup X) :=
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (inner X)).trans
          (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt hiso).symm

private theorem s16k_card_m22 {X : Type} [Group X] (hX : IsSpor X .M22) :
    Nat.card X = 443520 := by
  obtain ⟨e⟩ := hX
  have h : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 := by
    have hbridge : Nat.card CFSG.Blueprint.NativeSporadic.M22 = 443520 := by
      obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Bridge.M22.finite_card_le
      exact le_antisymm ((Nat.card_le_card_of_surjective _
        CFSG.Sporadic.Bridge.M22.toNative_surjective).trans hle)
        CFSG.Sporadic.Bridge.M22.le_card_native
    simpa only [CFSG.Blueprint.NativeSporadic.Carrier] using hbridge
  rw [Nat.card_congr e.toEquiv]
  exact h

theorem s16k_pRank_aut_l32 {X : Type} [Group X] [Finite X] (hX : IsL3 X 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ 1 := by
  have hcard : Nat.card (MulAut X) ∣ 336 := card_mulAut_dvd_of_isL3 hX
  have hnot : ¬ p ^ 2 ∣ 336 :=
    s16k_not_pow_dvd 336 2 (by norm_num) {2, 3, 7} {2} (by norm_num)
      (by simp [Nat.primeFactors])
      (by
        intro q hq hqT
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact absurd (by decide : (2 : ℕ) ∈ ({2} : Finset ℕ)) hqT
        · norm_num
        · norm_num)
      p hp (by simpa using hp2)
  exact s16k_pRank_top_le_of_not_dvd hp fun hd => hnot (hd.trans hcard)

theorem s16k_pRank_aut_l34 {X : Type} [Group X] [Finite X] (hX : IsLn X 3 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ if p = 3 then 2 else 1 := by
  have hS : CFSG.Open.StatedClassicalModel X .PSL 3 2 2 :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  have hcardX : Nat.card X = 20160 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four hS
  have hout : Nat.card (Outer X) ∣ 12 := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound
      X 3 2 2 hS).2.2.2.2 (by norm_num)
    simpa using h
  have hcard : Nat.card (MulAut X) ∣ 12 * 20160 := by
    rw [show (12 * 20160 : ℕ) = 12 * Nat.card X by rw [hcardX]]
    exact s16k_card_mulAut_dvd_of_outer_dvd (X := X) hout
  by_cases hp3 : p = 3
  · rw [if_pos hp3, hp3]
    obtain ⟨K, hF, hFin, hK, ⟨e⟩⟩ :=
      CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hX
    letI : Field K := hF
    have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
    have h3eq : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut X)) = 2 :=
      (CFSG.SectionRank.pRank_eq_open_pRank_top 3 (MulAut X)).symm.trans
        (CFSG.RankThree.PartTwo.KFacts.L34.pRank_three_mulAut_of_mulEquiv hK4 e)
    exact le_of_eq h3eq
  · rw [if_neg hp3]
    have hnot : ¬ p ^ 2 ∣ 12 * 20160 :=
      s16k_not_pow_dvd (12 * 20160) 2 (by norm_num) {2, 3, 5, 7} {2, 3} (by norm_num)
        (by simp [Nat.primeFactors])
        (by
          intro q hq hqT
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl
          · exact absurd (by decide : (2 : ℕ) ∈ ({2, 3} : Finset ℕ)) hqT
          · exact absurd (by decide : (3 : ℕ) ∈ ({2, 3} : Finset ℕ)) hqT
          · norm_num
          · norm_num)
        p hp (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hp2, hp3⟩)
    exact s16k_pRank_top_le_of_not_dvd hp fun hd => hnot (hd.trans hcard)

theorem s16k_pRank_aut_l5 {X : Type} [Group X] [Finite X] (hX : IsLn X 5 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ if p = 3 then 2 else 1 := by
  have hS : CFSG.Open.StatedClassicalModel X .PSL 5 2 1 :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  have hcardX : Nat.card X = 9999360 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two hS
  have hout : Nat.card (Outer X) ∣ 2 := by
    obtain ⟨K, hF, hFin, hK, ⟨e⟩⟩ :=
      CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hX
    letI : Field K := hF
    have hK2 : Nat.card K = 2 := by simpa using hK
    obtain ⟨hfin, hle⟩ := CFSG.SeitzReduction.SeitzQ2.card_outer_le_two_of_mulEquiv_PSL_two
      (by norm_num) hK2 e
    haveI := hfin
    have hpos : 0 < Nat.card (Outer X) := Nat.card_pos
    exact (Nat.dvd_prime Nat.prime_two).2 (by omega)
  have hcard : Nat.card (MulAut X) ∣ 2 * 9999360 := by
    rw [show (2 * 9999360 : ℕ) = 2 * Nat.card X by rw [hcardX]]
    exact s16k_card_mulAut_dvd_of_outer_dvd (X := X) hout
  by_cases hp3 : p = 3
  · rw [if_pos hp3]
    have hnot : ¬ p ^ 3 ∣ 2 * 9999360 :=
      s16k_not_pow_dvd (2 * 9999360) 3 (by norm_num) {2, 3, 5, 7, 31} {2} (by norm_num)
        (by simp [Nat.primeFactors])
        (by
          intro q hq hqT
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl
          · exact absurd (by decide : (2 : ℕ) ∈ ({2} : Finset ℕ)) hqT
          · norm_num
          · norm_num
          · norm_num
          · norm_num)
        p hp (by simpa using hp2)
    exact s16k_pRank_top_le_of_not_dvd (k := 2) hp fun hd => hnot (hd.trans hcard)
  · rw [if_neg hp3]
    have hnot : ¬ p ^ 2 ∣ 2 * 9999360 :=
      s16k_not_pow_dvd (2 * 9999360) 2 (by norm_num) {2, 3, 5, 7, 31} {2, 3} (by norm_num)
        (by simp [Nat.primeFactors])
        (by
          intro q hq hqT
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl
          · exact absurd (by decide : (2 : ℕ) ∈ ({2, 3} : Finset ℕ)) hqT
          · exact absurd (by decide : (3 : ℕ) ∈ ({2, 3} : Finset ℕ)) hqT
          · norm_num
          · norm_num
          · norm_num)
        p hp (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hp2, hp3⟩)
    exact s16k_pRank_top_le_of_not_dvd hp fun hd => hnot (hd.trans hcard)

theorem s16k_pRank_aut_m22 (hOut : S16kOutM22) {X : Type} [Group X] [Finite X]
    (hX : IsSpor X .M22) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ if p = 3 then 2 else 1 := by
  have hcardX : Nat.card X = 443520 := s16k_card_m22 hX
  have hout : Nat.card (Outer X) ∣ 2 := hOut X hX
  have hcard : Nat.card (MulAut X) ∣ 2 * 443520 := by
    rw [show (2 * 443520 : ℕ) = 2 * Nat.card X by rw [hcardX]]
    exact s16k_card_mulAut_dvd_of_outer_dvd (X := X) hout
  by_cases hp3 : p = 3
  · rw [if_pos hp3]
    have hnot : ¬ p ^ 3 ∣ 2 * 443520 :=
      s16k_not_pow_dvd (2 * 443520) 3 (by norm_num) {2, 3, 5, 7, 11} {2} (by norm_num)
        (by simp [Nat.primeFactors])
        (by
          intro q hq hqT
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl
          · exact absurd (by decide : (2 : ℕ) ∈ ({2} : Finset ℕ)) hqT
          · norm_num
          · norm_num
          · norm_num
          · norm_num)
        p hp (by simpa using hp2)
    exact s16k_pRank_top_le_of_not_dvd (k := 2) hp fun hd => hnot (hd.trans hcard)
  · rw [if_neg hp3]
    have hnot : ¬ p ^ 2 ∣ 2 * 443520 :=
      s16k_not_pow_dvd (2 * 443520) 2 (by norm_num) {2, 3, 5, 7, 11} {2, 3} (by norm_num)
        (by simp [Nat.primeFactors])
        (by
          intro q hq hqT
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl
          · exact absurd (by decide : (2 : ℕ) ∈ ({2, 3} : Finset ℕ)) hqT
          · exact absurd (by decide : (3 : ℕ) ∈ ({2, 3} : Finset ℕ)) hqT
          · norm_num
          · norm_num
          · norm_num)
        p hp (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hp2, hp3⟩)
    exact s16k_pRank_top_le_of_not_dvd hp fun hd => hnot (hd.trans hcard)

theorem s16k_pRank_aut_u33 {X : Type} [Group X] [Finite X]
    (hX : CFSG.Quasithin.B42TypeU33 X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ if p = 3 then 2 else 1 := by
  obtain ⟨hZ, hmodel⟩ := hX
  have hPSU : CFSG.Quasithin.IsPSU 3 3 1 X := by
    have e : X ⧸ Subgroup.center X ≃* X :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot (G := X))
    exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e hmodel
  have hLM : CFSG.Blueprint.LieModel X .PSU 3 3 1 := Or.inl ⟨by decide, hPSU⟩
  have hout : IsPGroup 2 (Outer X) := CFSG.LargeExtraspecial.DW.isPGroup_outer_psu hLM
  have hcardX : Nat.card X = 6048 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hPSU
  by_cases hp3 : p = 3
  · rw [if_pos hp3]
    have h3 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 := by
      rw [hp3]
      exact le_of_eq (CFSG.Quasithin.pRank_three_psu33 hPSU)
    exact (s16k_pRank_mulAut_le_of_isPGroup_outer hZ hout hp hp2).trans h3
  · rw [if_neg hp3]
    have hnot : ¬ p ^ 2 ∣ 6048 :=
      s16k_not_pow_dvd 6048 2 (by norm_num) {2, 3, 7} {2, 3} (by norm_num)
        (by simp [Nat.primeFactors])
        (by
          intro q hq hqT
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl
          · exact absurd (by decide : (2 : ℕ) ∈ ({2, 3} : Finset ℕ)) hqT
          · exact absurd (by decide : (3 : ℕ) ∈ ({2, 3} : Finset ℕ)) hqT
          · norm_num)
        p hp (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hp2, hp3⟩)
    refine (s16k_pRank_mulAut_le_of_isPGroup_outer hZ hout hp hp2).trans ?_
    refine s16k_pRank_top_le_of_not_dvd hp fun hd => ?_
    rw [hcardX] at hd
    exact hnot hd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
