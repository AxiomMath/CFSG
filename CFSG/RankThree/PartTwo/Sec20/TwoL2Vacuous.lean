module

public import CFSG.RankThree.PartTwo.Sec20.OneSteps
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L2Group
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL3Group
import CFSG.RankThree.PartTwo.Sec8.Hering88NLemmaB
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
import CFSG.GroupTheory.TwoElementSquare
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.RankThree.PartTwo.Sec20.OneTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

private theorem inf_pPrimeCore_le_of_simple {K H : Subgroup G} {c : G}
    (hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) (hKH : K ≤ H) (hcK : c ∈ K)
    (hc3 : orderOf c = 3) :
    K ⊓ inSubgroup (CFSG.pPrimeCore 3) H ≤ CFSG.Open.pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K₀ := inSubgroup (CFSG.pPrimeCore 3) H
  set W : Subgroup ↥K := (K ⊓ K₀).subgroupOf K
  have hWn : W.Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun k hk => ?_
    exact mem_normalizer_inf_of_mem (Subgroup.le_normalizer hk)
      (Res6.le_normalizer_inSubgroup_pPrimeCore 3 H (hKH hk))
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hWπ : (W.map π).Normal := hWn.map π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.map π) with h | h
  · rintro x ⟨hxK, hxK₀⟩
    have hx : π ⟨x, hxK⟩ ∈ W.map π := ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.mpr ⟨hxK, hxK₀⟩, rfl⟩
    rw [h, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact (CFSG.mem_openPCoreOf_iff _).mpr hx
  · exfalso
    have hcO : (⟨c, hcK⟩ : ↥K) ∉ CFSG.pCore 2 ↥K := by
      intro hc
      exact Res6.not_mem_of_isPGroup_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) hc3
        ((CFSG.mem_openPCoreOf_iff _).mpr hc)
    have hord : orderOf (π ⟨c, hcK⟩) = 3 := by
      have h1 : π ⟨c, hcK⟩ ^ 3 = 1 := by
        rw [← map_pow, show (⟨c, hcK⟩ : ↥K) ^ 3 = 1 from Subtype.ext (by
          rw [Subgroup.coe_pow, Subgroup.coe_one, ← hc3, pow_orderOf_eq_one]), map_one]
      have h2 : π ⟨c, hcK⟩ ≠ 1 := by
        rw [hπ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
        exact hcO
      exact orderOf_eq_prime h1 h2
    have hmem : π ⟨c, hcK⟩ ∈ W.map π := by rw [h]; exact Subgroup.mem_top _
    have hdvd : 3 ∣ Nat.card (W.map π) := by
      rw [← hord]
      exact Subgroup.orderOf_dvd_natCard _ hmem
    have hWc : Nat.Coprime 3 (Nat.card W) := by
      have heq : Nat.card W = Nat.card (K ⊓ K₀ : Subgroup G) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
      rw [heq]
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
        (Res6.coprime_card_inSubgroup_pPrimeCore 3 H)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hWc
      (hdvd.trans (Subgroup.card_map_dvd W π))

theorem not_nonempty_yAlpha_equiv_projSL_two {M X T : Subgroup G} {c : G}
    (hK : kTwenty M c ∈ oTwoComponentsIn M) (hc : orderOf c = 3) (hKX : kTwenty M c ≤ X)
    {n : ℕ} (hn : Odd n)
    (hKs : Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃* projSL 3 (GaloisField 2 n)))
    (m : ℕ) : ¬ Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField 2 m)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro ⟨e⟩
  obtain ⟨eK⟩ := hKs
  set K := kTwenty M c with hKdef
  set Y := yTwenty X c
  set YR := Y ⊔ CFSG.Open.pCoreOf 2 (K ⊔ T)
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥YR) with hπ
  set Yb := yAlpha M X T c
  have hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
    have : IsSimpleGroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
        (GaloisField 2 n)) :=
      CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (by norm_num)
    exact (eK.trans (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 _)).isSimpleGroup
  have hcK : c ∈ K := self_mem_normalClosureIn M c
  have hKY : K ≤ Y :=
    (Res6.le_normalClosureIn_self (isPerfect_of_mem_oTwoComponentsIn hK) hS hcK hc).trans
      (Res6.normalClosureIn_mono hKX c)
  have hKYR : K ≤ YR := hKY.trans le_sup_left
  let ψ : ↥K →* ↥Yb := (π.comp (Subgroup.inclusion hKYR)).codRestrict Yb
    fun k => ⟨Subgroup.inclusion hKYR k, hKY k.2, rfl⟩
  have hkerO : ψ.ker ≤ CFSG.pCore 2 ↥K := by
    intro k hk
    have hk1 : π (Subgroup.inclusion hKYR k) = 1 := congrArg Subtype.val hk
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk1
    have hkK₀ : (k : G) ∈ K ⊓ inSubgroup (CFSG.pPrimeCore 3) YR := ⟨k.2, ⟨_, hk1, rfl⟩⟩
    have hkO := inf_pPrimeCore_le_of_simple hS hKYR hcK hc hkK₀
    exact (Subgroup.mem_map_iff_mem K.subtype_injective).mp hkO
  let e2 := e.trans (CFSG.RankThree.PartTwo.Sec20.slTwoEquivProjSL (GaloisField 2 m)).symm
  have hsq : ∀ y : ↥K, (∃ a : ℕ, y ^ 2 ^ a = 1) →
      y ^ 2 ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).ker := by
    rintro y ⟨a, ha⟩
    rw [QuotientGroup.ker_mk']
    have h1 : ψ y ^ 2 ^ a = 1 := by rw [← map_pow, ha, map_one]
    have h2 : ψ y ^ 2 = 1 := by
      apply e2.injective
      rw [map_pow, map_one]
      exact CFSG.RankThree.PartTwo.Sec8.Hering88N.sl2_pow_two_eq_one (e2 (ψ y))
        ⟨a, by rw [← map_pow, h1, map_one]⟩
    exact hkerO (MonoidHom.mem_ker.mpr (show ψ (y ^ 2) = 1 by rw [map_pow, h2]))
  obtain ⟨x, hx⟩ := CFSG.RankThree.PartTwo.Sec20.exists_orderOf_eq_four_projSL3 hn
  have hx4 : eK.symm x ^ 2 ^ 2 = 1 := by
    rw [← map_pow, show (2 : ℕ) ^ 2 = 4 by norm_num, ← hx, pow_orderOf_eq_one, map_one]
  have hx2 := CFSG.sq_eq_one_of_surjective_of_sq_mem_ker _ (QuotientGroup.mk'_surjective _) hsq
    ⟨2, hx4⟩
  have hdvd : orderOf (eK.symm x) ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  rw [MulEquiv.orderOf_eq, hx] at hdvd
  norm_num at hdvd

theorem not_exists_yAlpha_equiv_projSL_two {M T : Subgroup G} {c : G}
    (hK : kTwenty M c ∈ oTwoComponentsIn M) (hc : orderOf c = 3) {n : ℕ} (hn : Odd n)
    (hKs : Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃* projSL 3 (GaloisField 2 n))) :
    ¬ ∃ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M ∧
      CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 ∧
      ∃ m : ℕ, Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField 2 m)) := by
  rintro ⟨X, hX, -, -, m, hm⟩
  have hKTX : kTwenty M c ⊔ T ≤ X := fun x hx => hX.2 hx
  exact not_nonempty_yAlpha_equiv_projSL_two hK hc (le_sup_left.trans hKTX) hn hKs m hm

end CFSG.RankThree.PartTwo.Sec20
