module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44RankTwoX
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44RankTwoRep
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44RankTwoLift
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndMain
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartTwo
import CFSG.GroupTheory.PRankCoprimeQuotient
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThreeComplement

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG Subgroup CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)
open scoped MatrixGroups IsMulCommutative

section Endgame

variable {X : Type*} [Group X] [Finite X] [Group.IsPerfect X] {K : Subgroup X} [K.Normal]
  [IsSimpleGroup (X ⧸ K)]

theorem endgame_of_pRank_le_two (hK : Group.IsSolvable K) (hO : oddCore X = ⊥)
    (hq : ¬ IsQuasisimple X) (hRank : CFSG.pRank 2 X ≤ 2) {z₀ : X} (hz₀ : z₀ ∈ center X)
    (hz₀1 : z₀ ≠ 1) (hz₀2 : z₀ * z₀ = 1) (H2 : ∀ t ∈ center X, t * t = 1 → t = 1 ∨ t = z₀) :
    IsExtOf X (alternatingGroup (Fin 5)) Q8D8 := by
  obtain ⟨hz, h, hcyc, hZX, ⟨E, hEZ, hEZ'⟩, w, -, hcard⟩ :=
    structure_pCore_two hK hO hq hz₀ hz₀1 hz₀2 (le_center_of_pRank_le_two hRank) H2
  have hC2 := ker_quotConj_le hK hO hq hZX
  have hinvS : ∀ t ∈ center (pCore 2 X), t * t = 1 → t = 1 ∨ t = ⟨z₀, hz⟩ := by
    intro t ht htt
    rcases H2 _ (hZX t ht) (congrArg Subtype.val htt) with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)
  obtain ⟨hw, hZ⟩ := eq_two_of_pRank_le_two (K := K) hRank hz h hcyc hinvS hEZ hEZ' hcard hC2
  subst hw
  have hcard16 : Nat.card (pCore 2 X ⧸ center (pCore 2 X)) = 16 := by rw [hcard]; norm_num
  exact extOf_q8D8 (K := K) hz₀ hz h hcard16 hC2 hZ

theorem exists_central_involution (hRank : CFSG.pRank 2 X ≤ 2) (hS : pCore 2 X ≠ ⊥) :
    ∃ z₀ ∈ center X, z₀ ≠ 1 ∧ z₀ * z₀ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 (pCore 2 X) := pCore_isPGroup
  have : Nontrivial (pCore 2 X) := (Subgroup.nontrivial_iff_ne_bot _).mpr hS
  have : Nontrivial (center (pCore 2 X)) := hS2.center_nontrivial
  have h2 : 2 ∣ Nat.card (center (pCore 2 X)) := by
    obtain ⟨k, hk⟩ := (hS2.to_subgroup (center (pCore 2 X))).exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hk
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := center (pCore 2 X)) 2 h2
  have hcen := le_center_of_pRank_le_two hRank ((center (pCore 2 X)).map (pCore 2 X).subtype)
    inferInstance ((hS2.to_subgroup _).map _) inferInstance
  have hx : orderOf ((c : pCore 2 X) : X) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  refine ⟨((c : pCore 2 X) : X), hcen ⟨c, c.2, rfl⟩, fun h1 => ?_, ?_⟩
  · rw [h1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  · have := pow_orderOf_eq_one ((c : pCore 2 X) : X)
    rwa [hx, sq] at this

end Endgame

theorem fittingSubgroup_le_oddCore {G : Type*} [Group G] [Finite G] (hO2 : pCore 2 G = ⊥) :
    fittingSubgroup G ≤ oddCore G := by
  rw [LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine iSup_le fun q => ?_
  have hq : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.2
  have : Fact (q : ℕ).Prime := ⟨hq⟩
  by_cases hq2 : (q : ℕ) = 2
  · rw [hq2, hO2]
    exact bot_le
  · refine le_oddCore pCore_normal ?_
    obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup (q : ℕ) (pCore (q : ℕ) G)).exists_card_eq
    rw [hk]
    exact Odd.pow (hq.odd_of_ne_two hq2)

theorem isQuasisimple_quot_oddCore_of {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    [N.Normal] (hN : N ≤ oddCore G) {J : Type*} [Group J] [Finite J] (e : G ⧸ N ≃* J)
    (hJ : IsQuasisimple J) (hZ : Nat.card (center J) = 2) : IsQuasisimple (G ⧸ oddCore G) := by
  set M := (oddCore G).map (QuotientGroup.mk' N) with hM
  have hMn : M.Normal :=
    (inferInstance : (oddCore G).Normal).map _ (QuotientGroup.mk'_surjective N)
  have hMe : (M.map e.toMonoidHom).Normal := hMn.map _ e.surjective
  have hodd : Odd (Nat.card (M.map e.toMonoidHom)) := by
    rw [card_map_of_injective e.injective]
    exact (CFSG.ABGDGroups.odd_card_oddCore G).of_dvd_nat
      (Subgroup.card_map_dvd (oddCore G) (QuotientGroup.mk' N))
  have hbot := eq_bot_of_odd_card_of_isQuasisimple hJ hZ hMe hodd
  rw [map_eq_bot_iff_of_injective _ e.injective, hM, Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk'] at hbot
  have hEq : N = oddCore G := le_antisymm hN hbot
  exact LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hEq.symm).trans e).symm hJ

theorem partTwoRankTwo : PartTwoRankTwo := by
  intro G _ _ hG hperf K _ hK hsimple h3K hO2 hq hm2
  have := hperf
  have := hsimple
  by_cases hD : ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ D : Subgroup G, CriticalAt p D ∧
      Odd (Nat.card (Subgroup.centralizer (D : Set G)))
  ·
    by_cases hX : IsQuasisimple (G ⧸ oddCore G)
    · exact Or.inl hX
    right
    obtain ⟨p, hp, hp3, D, hD, hodd⟩ := hD
    have : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by omega
    have hp5 : 5 ≤ p := five_le_of_prime hp hp3
    have hDp : IsPGroup p D := pCore_isPGroup.to_le hD.le
    obtain ⟨-, -, -, hVelem, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hDp
    have := hVelem
    have : Module.Finite (ZMod p) (Additive (D ⧸ frattini D)) := Module.Finite.of_finite
    set b := Module.finBasis (ZMod p) (Additive (D ⧸ frattini D)) with hb
    set ρ := frattiniMat hD b with hρdef
    have hρ : ∀ y, ρ y = 1 → y ∈ oddCore G := fun y hy =>
      mem_oddCore_of_frattiniLin_eq_one hD hp2 hodd ((frattiniMat_eq_one_iff hD b y).mp hy)
    have hfix : ∀ t : G, orderOf t = 2 → Module.finrank (ZMod p) (Module.End.eigenspace
        (Matrix.toLin' (ρ t).val) 1) ≤ 2 := fun t ht => by
      rw [hρdef, finrank_fixed_mat]
      exact finrank_fixed_le_two hD hp2 (hG.localRank_lt p hp hp3) ht
    set KX := K.map (QuotientGroup.mk' (oddCore G)) with hKX
    have : KX.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    have hOK : oddCore G ≤ K := oddCore_le_of_isSimpleGroup
    have : IsSimpleGroup ((G ⧸ oddCore G) ⧸ KX) :=
      (QuotientGroup.quotientQuotientEquivQuotient (oddCore G) K hOK).isSimpleGroup
    have hKXs : Group.IsSolvable KX :=
      Group.isSolvable_of_surjective ((QuotientGroup.mk' (oddCore G)).subgroupMap_surjective K)
    have hOX : oddCore (G ⧸ oddCore G) = ⊥ :=
      CFSG.LyonsUnitaryFour.oddCore_quotient_oddCore_eq_bot G
    have hRank : CFSG.pRank 2 (G ⧸ oddCore G) ≤ 2 := by
      rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _
        (fun h2 => (Nat.not_even_iff_odd.mpr (CFSG.ABGDGroups.odd_card_oddCore G))
          (even_iff_two_dvd.mpr h2)), CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact hm2
    have hSne : pCore 2 (G ⧸ oddCore G) ≠ ⊥ := fun h0 =>
      not_pCore_two_le_center (K := KX) hKXs hOX hX (by rw [h0]; exact bot_le)
    obtain ⟨z₀, hz₀, hz₀1, hz₀2⟩ := exists_central_involution hRank hSne
    have H2 : ∀ t ∈ center (G ⧸ oddCore G), t * t = 1 → t = 1 ∨ t = z₀ := by
      intro t ht htt
      by_contra h
      push Not at h
      exact not_pCore_two_le_center (K := KX) hKXs hOX hX
        (normal_two_le_center_of_central_four hp5 hρ hfix hz₀ ht hz₀1 h.1 (Ne.symm h.2) hz₀2
          htt _ inferInstance pCore_isPGroup)
    exact endgame_of_pRank_le_two (K := KX) hKXs hOX hX hRank hz₀ hz₀1 hz₀2 H2
  ·
    left
    push Not at hD
    obtain ⟨p₀, hp₀, hS₀⟩ := exists_centralizer_pCore_le hK hq
    have hSp : ∀ p : ℕ, p.Prime → Subgroup.centralizer (pCore p G : Set G) ≤ K →
        3 < p ∧ pCore p G ≠ ⊥ := by
      intro p hp hpS
      have : Fact p.Prime := ⟨hp⟩
      have hne : pCore p G ≠ ⊥ := by
        intro h
        have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer (pCore p G : Set G) := by
          intro g _
          rw [Subgroup.mem_centralizer_iff]
          intro x hx
          rw [h] at hx
          rw [(Subgroup.mem_bot).mp hx, one_mul, mul_one]
        exact (QuotientGroup.nontrivial_iff.mp inferInstance) (top_le_iff.mp (htop.trans hpS))
      refine ⟨?_, hne⟩
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact hne hO2
      have hp3 : p ≠ 3 := by
        rintro rfl
        apply hne
        obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup 3 (pCore 3 G)).exists_card_eq
        have hdvd : 3 ^ k ∣ Nat.card K := hk ▸ Subgroup.card_dvd_of_le (pCore_le 3)
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · rw [pow_zero] at hk
          exact Subgroup.eq_bot_of_card_eq _ hk
        · exact absurd ((dvd_pow_self 3 hk0.ne').trans hdvd) h3K
      have := hp.two_le
      omega
    have hlin : ∀ p : ℕ, p.Prime → Subgroup.centralizer (pCore p G : Set G) ≤ K →
        ∃ (N : Subgroup G) (_ : N.Normal), LinearOutcome G p N := by
      intro p hp hpS
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨hp3, hne⟩ := hSp p hp hpS
      obtain ⟨D, hD'⟩ := exists_criticalAt (by omega) hne
      have heven := hD p hp hp3 D hD'
      rw [Nat.not_odd_iff_even] at heven
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer (D : Set G)) 2
        (even_iff_two_dvd.mp heven)
      have ht' : orderOf (t : G) = 2 := by rwa [Subgroup.orderOf_coe]
      have hrank := pRank_le_localRank_of_centralizes hp (by omega) ht'
        (fun h hh => Subgroup.mem_centralizer_iff.mp t.2 h hh)
      have := hG.localRank_lt p hp hp3
      exact linearOutcome_of_criticalAt hK hp3 hpS hD' (by omega)
    have hF := fittingSubgroup_le_oddCore hO2
    rcases linear_endgame hK hO2 hp₀ hS₀ hlin with ⟨⟨e⟩⟩ | ⟨p, hp, hp3, ⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      exact isQuasisimple_quot_oddCore_of hF e (isQuasisimple_SL2 le_rfl)
        (card_center_SL2 (by norm_num))
    · have : Fact p.Prime := ⟨hp⟩
      have hp2 : p ≠ 2 := by omega
      refine isQuasisimple_quot_oddCore_of (le_oddCore pCore_normal ?_) e
        (isQuasisimple_SL2 (five_le_of_prime hp hp3)) (card_center_SL2 hp2)
      obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup p (pCore p G)).exists_card_eq
      rw [hk]
      exact Odd.pow (hp.odd_of_ne_two hp2)
    ·
      exfalso
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hO3 : pCore 3 G = ⊥ := by
        obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup 3 (pCore 3 G)).exists_card_eq
        have hdvd : 3 ^ k ∣ Nat.card K := hk ▸ Subgroup.card_dvd_of_le (pCore_le 3)
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · rw [pow_zero] at hk
          exact Subgroup.eq_bot_of_card_eq _ hk
        · exact absurd ((dvd_pow_self 3 hk0.ne').trans hdvd) h3K
      have e' : G ≃* SL(3, ZMod 3) := (QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq hO3.symm)).trans e
      exact hq (LocalCores.isQuasisimple_of_mulEquiv e'.symm isQuasisimple_SL3_three)

end CFSG.RankThree.PartTwo.Sec4.Census
