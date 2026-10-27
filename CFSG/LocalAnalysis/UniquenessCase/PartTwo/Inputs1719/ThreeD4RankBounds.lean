module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoFacts
public import CFSG.Blueprint.LieModelAPI
public import CFSG.RankThree.PartTwo.Sec21.Item223Rank2ProofD4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Polynomial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Is3D4)

theorem pRank_le_two_of_is3D4
    {Y : Type} [Group Y] [Finite Y] {n p : ℕ} (hY : Is3D4 Y n) (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2 := by
  obtain ⟨⟨-, hn, -⟩, hmod⟩ :=
    ((CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hY).2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4
      Nat.prime_two hn hmod
  let C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  have hK3 : Nat.card K = (2 ^ n) ^ 3 := by simpa [TwistTag.order] using hK
  have hσ3 : ∀ c, σ.toRingHom c = c ^ (2 ^ n) := fun c => hσ c
  rcases eq_or_ne p 3 with rfl | hp3
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
    refine CFSG.SectionRank.pRank_le (by norm_num : 1 < 3) fun E _ hE => ?_
    have h := CFSG.RankThree.PartTwo.Sec21.Item223Rank2Proof.card_le_nine_of_graphFixedRootGroup
      hn hK hσ E hE
    simpa using h
  · have hp5 : 5 ≤ p := by
      have hp4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
      have h2 := hp.two_le
      omega
    have hR : CFSG.LieType.SeitzGeneration.RankLE2 p C := by
      by_cases hdvd : p ∣ Nat.card C
      · obtain ⟨e'⟩ := CFSG.RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv
          .D4 Nat.prime_two hn K hK σ.toRingHom hσ3
        have hmodC : CFSG.Blueprint.ChevalleyExceptionalModel C .trialityD4 2 n :=
          ⟨⟨Nat.prime_two, hn, rfl⟩,
            ⟨K, inferInstance, inferInstance, hK, σ.toRingHom, hσ3, ⟨e'.symm⟩⟩⟩
        obtain ⟨m, hm, hd⟩ :=
          ((CFSG.RankThree.Chevalley.exact_E_type_and_triality_cross_prime_factor_exhaustion
            hp (by omega) (Ne.symm hp2) hmodC).1 hdvd).2.2.2.2 rfl
        have hq1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        by_cases h12 : m = 12
        · subst h12
          have h24 : (2 ^ n) ^ 2 ≤ (2 ^ n) ^ 4 :=
            Nat.pow_le_pow_right hq1 (by norm_num)
          have hpoly : (CFSG.RankThree.Chevalley.exhaustionPhi 12).eval
              (((2 ^ n) : ℕ) : ℤ) = (((2 ^ n) ^ 4 - (2 ^ n) ^ 2 + 1 : ℕ) : ℤ) := by
            rw [Nat.cast_add, Nat.cast_sub h24]
            push_cast
            simp [CFSG.RankThree.Chevalley.exhaustionPhi]
          rw [hpoly] at hd
          exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_of_pRank_le_one hp
            (CFSG.RankThree.PartOne.K128.pRank_le_one_D4_twelve Nat.prime_two hn K hK3
              σ hσ hp hp5 (Int.natCast_dvd_natCast.1 hd))
        · have hm' : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by omega
          exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_of_sylowShape hp
            (CFSG.RankThree.PartOne.K128.sylowShape_D4 (ℓ := 2) (f := n) hn K hK3
              σ hσ hm' hp hp5
              (CFSG.RankThree.PartOne.K128.dvd_phiNat_of_dvd_cycloVal hq1 hm' hd))
      · exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_of_not_dvd hp hdvd
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => hR E hE

theorem dvd_two_pow_six_mul_sub_one_of_is3D4
    {Y : Type} [Group Y] [Finite Y] {n p : ℕ} (hY : Is3D4 Y n) (hp : p.Prime) (hp2 : p ≠ 2)
    (h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y)) : p ∣ 2 ^ (6 * n) - 1 := by
  obtain ⟨⟨-, hn, -⟩, hmod⟩ :=
    ((CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hY).2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4
      Nat.prime_two hn hmod
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hCdef
  have hK3 : Nat.card K = (2 ^ n) ^ 3 := by simpa [TwistTag.order] using hK
  have hσ3 : ∀ c, σ.toRingHom c = c ^ (2 ^ n) := fun c => hσ c
  rcases eq_or_ne p 3 with rfl | hp3
  · have h3 : (3 : ℕ) ∣ 2 ^ 6 - 1 := by norm_num
    have hdvd : 2 ^ 6 - 1 ∣ 2 ^ (6 * n) - 1 := by
      have h := Nat.sub_dvd_pow_sub_pow (2 ^ 6) 1 n
      simp only [one_pow] at h
      rwa [show (2 ^ 6) ^ n = 2 ^ (6 * n) by rw [← pow_mul]] at h
    exact h3.trans hdvd
  · have hp5 : 5 ≤ p := by
      have hp4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
      have h2' := hp.two_le
      omega
    have h2C : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup C) := by
      rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
      exact h2
    have h1 : 1 ≤ CFSG.pRank p C := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
      omega
    have hdvd : p ∣ Nat.card C :=
      CFSG.RankThree.PartOne.K128.dvd_card_of_pRank_pos hp h1
    obtain ⟨e'⟩ := CFSG.RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv
      .D4 Nat.prime_two hn K hK σ.toRingHom hσ3
    have hmodC : CFSG.Blueprint.ChevalleyExceptionalModel C .trialityD4 2 n :=
      ⟨⟨Nat.prime_two, hn, rfl⟩,
        ⟨K, inferInstance, inferInstance, hK, σ.toRingHom, hσ3, ⟨e'.symm⟩⟩⟩
    obtain ⟨m, hm, hd⟩ :=
      ((CFSG.RankThree.Chevalley.exact_E_type_and_triality_cross_prime_factor_exhaustion
        hp (by omega) (Ne.symm hp2) hmodC).1 hdvd).2.2.2.2 rfl
    have hq1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    set q : ℕ := 2 ^ n with hqdef
    have hq6 : q ^ 6 = 2 ^ (6 * n) := by
      rw [hqdef, ← pow_mul, Nat.mul_comm]
    by_cases h12 : m = 12
    · subst h12
      have h24 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by norm_num))
        (by norm_num)
      have hpoly : (CFSG.RankThree.Chevalley.exhaustionPhi 12).eval ((q : ℕ) : ℤ) =
          ((q ^ 4 - q ^ 2 + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_sub h24]
        push_cast
        simp [CFSG.RankThree.Chevalley.exhaustionPhi]
      rw [hpoly] at hd
      have hle : CFSG.pRank p C ≤ 1 := by
        have h := CFSG.RankThree.PartOne.K128.pRank_le_one_D4_twelve Nat.prime_two hn K hK3
          σ hσ hp hp5 (Int.natCast_dvd_natCast.1 hd)
        rw [hCdef]
        exact h
      have h2' : 2 ≤ CFSG.pRank p C := by
        rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
        exact h2C
      omega
    · have hm' : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by omega
      have hphi : p ∣ q ^ 6 - 1 := by
        have hq1' : 1 ≤ q := by rw [hqdef]; exact hq1
        have hq6pos : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq1'
        have hq2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
        have hqfac : q ^ 6 - 1 = (q - 1) * ((q + 1) * ((q ^ 2 + q + 1) * (q ^ 2 - q + 1))) := by
          zify [hq1', hq2, hq6pos]
          ring
        have hdphi : p ∣ CFSG.RankThree.PartOne.K128.phiNat m q :=
          CFSG.RankThree.PartOne.K128.dvd_phiNat_of_dvd_cycloVal
            (by simpa [hqdef] using hq1) hm'
            (by simpa [CFSG.RankThree.PartOne.KE.cycloVal, hqdef] using hd)
        rw [hqfac]
        rcases hm' with rfl | rfl | rfl | rfl
        · exact Dvd.dvd.mul_right (by simpa [CFSG.RankThree.PartOne.K128.phiNat] using hdphi)
            ((q + 1) * ((q ^ 2 + q + 1) * (q ^ 2 - q + 1)))
        · exact Dvd.dvd.mul_left
            (Dvd.dvd.mul_right (by simpa [CFSG.RankThree.PartOne.K128.phiNat] using hdphi)
              ((q ^ 2 + q + 1) * (q ^ 2 - q + 1))) (q - 1)
        · exact Dvd.dvd.mul_left
            (Dvd.dvd.mul_left
              (Dvd.dvd.mul_right (by simpa [CFSG.RankThree.PartOne.K128.phiNat] using hdphi)
                (q ^ 2 - q + 1)) (q + 1)) (q - 1)
        · exact Dvd.dvd.mul_left
            (Dvd.dvd.mul_left
              (Dvd.dvd.mul_left
                (by simpa [CFSG.RankThree.PartOne.K128.phiNat] using hdphi) (q ^ 2 + q + 1))
              (q + 1)) (q - 1)
      rwa [hq6] at hphi

theorem isMulCommutative_sylow_of_is3D4
    {Y : Type} [Group Y] [Finite Y] {n r : ℕ} (hY : Is3D4 Y n) (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrd : r ∣ 2 ^ n - 1) (P : Sylow r Y) : IsMulCommutative (P : Subgroup Y) := by
  obtain ⟨⟨-, hn, -⟩, hmod⟩ :=
    ((CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hY).2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4
      Nat.prime_two hn hmod
  have hK3 : Nat.card K = (2 ^ n) ^ 3 := by simpa [TwistTag.order] using hK
  let C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  have hshapeC : CFSG.RankThree.PartOne.K1214.SylowShape r 2 ((2 ^ n - 1).factorization r) C :=
    CFSG.RankThree.PartOne.K128.sylowShape_D4_split (ℓ := 2) (f := n) hn K hK3
      σ hσ hr hr5 hrd
  have hshapeY : CFSG.RankThree.PartOne.K1214.SylowShape r 2 ((2 ^ n - 1).factorization r) Y :=
    CFSG.RankThree.PartOne.K1214.SylowShape.of_mulEquiv e hshapeC
  obtain ⟨eP⟩ := hshapeY (P : Subgroup Y) P.isPGroup'
    (@Sylow.not_dvd_index r Y inferInstance ⟨hr⟩ P inferInstance)
  refine ⟨⟨fun a b => eP.injective ?_⟩⟩
  rw [map_mul, map_mul]
  exact mul_comm _ _

theorem card_outer_of_is3D4
    {Y : Type} [Group Y] {n : ℕ} (hY : Is3D4 Y n) : Nat.card (Outer Y) = 3 * n := by
  obtain ⟨⟨-, hn, -⟩, hmod⟩ :=
    ((CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hY).2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4
      Nat.prime_two hn hmod
  have hK3 : Nat.card K = (2 ^ n) ^ 3 := by simpa [TwistTag.order] using hK
  obtain ⟨-, -, ⟨Θ, -, hsurj, hker, -⟩, -, hcard, -, -, -⟩ :=
    CFSG.LieType.Chevalley.even_triality_exact_automorphism_normal_form (f := n) hn K hK3 σ hσ
  let C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  have hker' : Θ.ker = CFSG.ComponentClassification.OuterAutomorphisms.inner C := hker
  let Φ := QuotientGroup.lift (CFSG.ComponentClassification.OuterAutomorphisms.inner C) Θ hker'.ge
  have hΦsurj : Function.Surjective Φ := fun y => by
    obtain ⟨α, rfl⟩ := hsurj y
    exact ⟨α, QuotientGroup.lift_mk _ hker'.ge α⟩
  have hΦker : Φ.ker = ⊥ := by
    rw [QuotientGroup.ker_lift, hker', QuotientGroup.map_mk'_self]
  have hΦinj : Function.Injective Φ := (MonoidHom.ker_eq_bot_iff Φ).mp hΦker
  let Ψ : Outer C ≃* (K ≃+* K) := MulEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  have hcardOC : Nat.card (Outer C) = 3 * n := by
    rw [Nat.card_congr Ψ.toEquiv, hcard]
  rw [Nat.card_congr (equivalence e).toEquiv]
  exact hcardOC

theorem k_3D4TwoThreeRank_holds :
    K_3D4TwoThreeRank :=
  fun X _ _ hX => pRank_le_two_of_is3D4 hX Nat.prime_three (by norm_num)

theorem k_3D4TwoSylowSeven_holds :
    K_3D4TwoSylowSeven := by
  intro X _ _ hX P
  obtain ⟨⟨-, hf, -⟩, hmod⟩ :=
    ((CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hX).2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4
      Nat.prime_two hf hmod
  have hK3 : Nat.card K = (2 ^ 1) ^ 3 := by simpa [TwistTag.order] using hK
  have hshapeC : CFSG.RankThree.PartOne.K1214.SylowShape 7 2 1
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    have h := CFSG.RankThree.PartOne.K128.sylowShape_D4 (ℓ := 2) (f := 1) (by norm_num) K
      hK3 σ hσ (m := 3) (by decide) (p := 7) (by norm_num) (by norm_num)
      (by norm_num [CFSG.RankThree.PartOne.K128.phiNat])
    have hfac : (7 : ℕ).factorization 7 = 1 := by
      simpa using Nat.Prime.factorization_self (by norm_num : Nat.Prime 7)
    simpa [CFSG.RankThree.PartOne.K128.phiNat, hfac] using h
  have hshapeY : CFSG.RankThree.PartOne.K1214.SylowShape 7 2 1 X :=
    CFSG.RankThree.PartOne.K1214.SylowShape.of_mulEquiv e hshapeC
  obtain ⟨eP⟩ := hshapeY (P : Subgroup X) P.isPGroup'
    (@Sylow.not_dvd_index 7 X inferInstance ⟨by norm_num⟩ P inferInstance)
  have h7 : ∀ y : Fin 2 → Multiplicative (ZMod (7 ^ 1)), y ^ 7 = 1 := by
    intro y
    funext i
    have hcard7 : Nat.card (Multiplicative (ZMod (7 ^ 1))) = 7 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
      norm_num
    have h := pow_card_eq_one' (x := y i)
    rwa [hcard7] at h
  refine ⟨⟨⟨⟨fun a b => eP.injective ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · rw [map_mul, map_mul]
    exact mul_comm _ _
  · have hxP : (⟨x, hx⟩ : ↥P) ^ 7 = 1 := by
      apply eP.injective
      rw [map_pow, map_one]
      exact h7 (eP ⟨x, hx⟩)
    exact congrArg Subtype.val hxP
  · rw [Nat.card_congr eP.toEquiv]
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
    have hcard7 : Nat.card (Multiplicative (ZMod (7 ^ 1))) = 7 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
      norm_num
    rw [hcard7]
    norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
