module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bNorm2
public import CFSG.Sporadic.J2
import CFSG.Models.PGLOrders
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.OutSmallBasic
import CFSG.Sporadic.Schreier.PairJ2Pairs

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

private theorem j2_center_eq_bot :
    Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥ := by
  haveI : Finite CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.fam_j2_simplicity.1
  have hsimple : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 :=
    CFSG.Sporadic.J2.isSimpleGroup_J2
  have hcard : Nat.card CFSG.Blueprint.NativeSporadic.J2 = 604800 := CFSG.Sporadic.J2.card_J2
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center CFSG.Blueprint.NativeSporadic.J2)
    with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : CFSG.Blueprint.NativeSporadic.J2, a * b = b * a := by
      intro a b
      have hb : b ∈ Subgroup.center CFSG.Blueprint.NativeSporadic.J2 := by
        rw [h]
        exact Subgroup.mem_top b
      exact Subgroup.mem_center_iff.1 hb a
    have : IsMulCommutative CFSG.Blueprint.NativeSporadic.J2 := ⟨⟨hcomm⟩⟩
    have hp := Group.is_simple_iff_prime_card.1 hsimple
    rw [hcard] at hp
    exact absurd hp (by norm_num)

private theorem j2_card_mulAut_le :
    Nat.card (MulAut CFSG.Blueprint.NativeSporadic.J2) ≤
      2 * Nat.card CFSG.Blueprint.NativeSporadic.J2 := by
  haveI : Finite CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.fam_j2_simplicity.1
  exact CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.card_mulAut_le_of_card_outer_le
    (k := 2) CFSG.Sporadic.Schreier.AT_J2_Schreier.1

private theorem j2_sylow3_card
    (S : Sylow 3 CFSG.Blueprint.NativeSporadic.J2) :
    Nat.card (S : Subgroup CFSG.Blueprint.NativeSporadic.J2) = 27 := by
  haveI : Finite CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.fam_j2_simplicity.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac3 : (604800 : ℕ).factorization 3 = 3 := by
    rw [show (604800 : ℕ) = 3 ^ 3 * 22400 by norm_num,
      Nat.factorization_mul (a := 3 ^ 3) (b := 22400) (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (n := 22400) (p := 3) (by norm_num)] <;> simp
  rw [Sylow.card_eq_multiplicity S, CFSG.Sporadic.J2.card_J2, hfac3] <;> norm_num

private theorem sylow_two_projSL_card
    (T : Sylow 2 (CFSG.PGLModel.projSL 3 (GaloisField 2 2))) :
    Nat.card (T : Subgroup (CFSG.PGLModel.projSL 3 (GaloisField 2 2))) = 64 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (CFSG.PGLModel.projSL 3 (GaloisField 2 2)) :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.PGLModel.card_projSL_three_four]; norm_num)
  have hfac2 : (20160 : ℕ).factorization 2 = 6 := by
    rw [show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num,
      Nat.factorization_mul (a := 2 ^ 6) (b := 315) (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (n := 315) (p := 2) (by norm_num)] <;> simp
  rw [Sylow.card_eq_multiplicity T, CFSG.PGLModel.card_projSL_three_four, hfac2] <;> norm_num

private theorem j2_exists_nine
    (S : Sylow 3 CFSG.Blueprint.NativeSporadic.J2) (B : Subgroup CFSG.Blueprint.NativeSporadic.J2)
    (hBS : B ≤ (S : Subgroup CFSG.Blueprint.NativeSporadic.J2)) (hB9 : Nat.card B ≤ 9) :
    ∃ K : Subgroup CFSG.Blueprint.NativeSporadic.J2,
      K ≤ (S : Subgroup CFSG.Blueprint.NativeSporadic.J2) ∧ Nat.card K = 9 ∧ B ≤ K := by
  haveI : Finite CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.fam_j2_simplicity.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSc := j2_sylow3_card S
  have h1 : Nat.card B ∣ Nat.card (S : Subgroup CFSG.Blueprint.NativeSporadic.J2) :=
    Subgroup.card_dvd_of_le hBS
  rw [hSc, show (27 : ℕ) = 3 ^ 3 by norm_num] at h1
  obtain ⟨k, -, hBk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
  have hk2 : k ≤ 2 := by
    by_contra hc
    have h27 : 27 ≤ 3 ^ k :=
      calc (27 : ℕ) = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hBk] at h27
    omega
  have hBdvd : Nat.card B ∣ 3 ^ 2 := by
    rw [hBk]
    exact pow_dvd_pow 3 hk2
  obtain ⟨K, hKc, hBK, hKS⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three hBdvd (by rw [hSc]; norm_num) hBS
  exact ⟨K, hKS, hKc.trans (by norm_num), hBK⟩

private theorem j2_sylow3_nine_normalizes
    (S : Sylow 3 CFSG.Blueprint.NativeSporadic.J2) (K : Subgroup CFSG.Blueprint.NativeSporadic.J2)
    (hKS : K ≤ (S : Subgroup CFSG.Blueprint.NativeSporadic.J2)) (hK9 : Nat.card K = 9) :
    ∃ V : Subgroup CFSG.Blueprint.NativeSporadic.J2, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      K ≤ Subgroup.normalizer (V : Set CFSG.Blueprint.NativeSporadic.J2) := by
  haveI : Finite CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.fam_j2_simplicity.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, -, h5⟩ := CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15
    CFSG.Blueprint.NativeSporadic.J2 ⟨MulEquiv.refl _⟩ S _ rfl _ rfl
  obtain ⟨S₀, hS₀, -, -, ⟨T, ⟨eT⟩⟩, -⟩ := h5 K ⟨hKS, hK9⟩
  have hS₀max : Maximal (· ∈ invariantPiSubgroups ⊤ K (piOf 2)) S₀ := hS₀
  obtain ⟨-, hPG, hKN⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).1 hS₀max.1
  have hS₀ne : S₀ ≠ ⊥ := by
    intro h0
    have hc1 : Nat.card S₀ = 1 := by rw [h0, Subgroup.card_bot]
    have hc2 := Nat.card_congr eT.toEquiv
    have hc3 := sylow_two_projSL_card T
    omega
  exact ⟨S₀, hS₀ne, hPG, hKN⟩

theorem norm2_J2 :
    Norm2 (CFSG.Blueprint.NativeSporadic.J2) := by
  haveI : Finite CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.fam_j2_simplicity.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 CFSG.Blueprint.NativeSporadic.J2) := inferInstance
  refine Norm2.of_inner j2_center_eq_bot j2_card_mulAut_le S ?_
  intro B hBS hB9
  obtain ⟨K, hKS, hK9, hBK⟩ := j2_exists_nine S B hBS hB9
  obtain ⟨V, hV0, hV2, hVK⟩ := j2_sylow3_nine_normalizes S K hKS hK9
  exact ⟨V, hV0, hV2, hBK.trans hVK⟩

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
