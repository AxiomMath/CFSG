module

public import CFSG.RankThree.PartTwo.Late.Defs
import CFSG.RankThree.PartTwo.Sec3.Sims321Action

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

variable {G : Type} [Group G] [Finite G] {A M N L : Subgroup G}

theorem exists_subgroup_sectionCentralizer {U L : Subgroup G}
    (hUL : U ≤ Subgroup.normalizer (L : Set G)) :
    ∃ K : Subgroup G, K ≤ U ∧ (K : Set G) = sectionCentralizer U L (CFSG.Open.pCoreOf 2 L) := by
  have hnorm : ∀ x ∈ U, ∀ n ∈ CFSG.Open.pCoreOf 2 L, x * n * x⁻¹ ∈ CFSG.Open.pCoreOf 2 L :=
    fun x hx n hn => (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hUL hx)) n).mp hn
  refine ⟨{ carrier := sectionCentralizer U L (CFSG.Open.pCoreOf 2 L)
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun x hx => hx.1, rfl⟩
  · rintro a b ⟨ha, hac⟩ ⟨hb, hbc⟩
    refine ⟨U.mul_mem ha hb, fun l hl => ?_⟩
    have key : a * b * l * (a * b)⁻¹ * l⁻¹ =
        (a * (b * l * b⁻¹ * l⁻¹) * a⁻¹) * (a * l * a⁻¹ * l⁻¹) := by
      group
    rw [key]
    exact (CFSG.Open.pCoreOf 2 L).mul_mem (hnorm a ha _ (hbc l hl)) (hac l hl)
  · exact ⟨U.one_mem, fun l _ => by simp⟩
  · rintro a ⟨ha, hac⟩
    refine ⟨U.inv_mem ha, fun l hl => ?_⟩
    have hm : a⁻¹ * l * a ∈ L := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hUL (U.inv_mem ha)) l).mp hl
      rwa [inv_inv] at h1
    have key : a⁻¹ * l * a⁻¹⁻¹ * l⁻¹ =
        (a * (a⁻¹ * l * a) * a⁻¹ * (a⁻¹ * l * a)⁻¹)⁻¹ := by
      group
    rw [key]
    exact (CFSG.Open.pCoreOf 2 L).inv_mem (hac _ hm)

theorem Hyp1921.exists_ne_one_mem_sectionCentralizer_of (h : Hyp1921 G A M N L)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    ∃ c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L), c ≠ 1 := by
  obtain ⟨φ⟩ := h.quotient_iso
  have hE27 : IsE27 A := isE27_of_mem_partTwoE h.mem_partTwoE
  have hk4 : Nat.card (GaloisField 2 2) = 4 := KFacts.L34.card_galoisField_two_two
  haveI : Finite (MulAut (projectiveSL 3 (GaloisField 2 2))) :=
    Nat.finite_of_card_ne_zero (by rw [KFacts.L34.card_mulAut hk4]; norm_num)
  let β : A →* MulAut (projectiveSL 3 (GaloisField 2 2)) :=
    (Sec3.Sims321.rho φ).comp (Subgroup.inclusion hAL)
  have hnot : ¬ Function.Injective β := by
    intro hinj
    have hcomm : ∀ a b : A, a * b = b * a := fun a b => hE27.1.1.is_comm.comm a b
    have hpow : ∀ a : A, a ^ 3 = 1 := fun a =>
      Subtype.ext (by simpa using hE27.1.2 (a : G) a.2)
    have hk : Nat.card A = 3 ^ 3 := hE27.2.trans (by norm_num)
    have h3 := CFSG.SectionRank.le_pRank_of_injective (by norm_num) hcomm hpow hk β hinj le_top
    have h2 := KFacts.L34.pRank_three_mulAut hk4
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
    omega
  obtain ⟨a, ha1, ha⟩ : ∃ a : A, β a = 1 ∧ a ≠ 1 := by
    rw [injective_iff_map_eq_one] at hnot
    push Not at hnot
    exact hnot
  refine ⟨(a : G), ⟨a.2, fun l hl => ?_⟩, fun h1 => ha (Subtype.ext (by simpa using h1))⟩
  exact (Sec3.Sims321.rho_eq_one_iff φ ⟨(a : G), hAL a.2⟩).mp ha1 l hl

theorem Hyp1921.orderOf_eq_three_of (h : Hyp1921 G A M N L)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) {c : G}
    (hc : sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G)) :
    orderOf c = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE27 : IsE27 A := isE27_of_mem_partTwoE h.mem_partTwoE
  have hcZ : c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) := by
    rw [hc]
    exact Subgroup.mem_zpowers c
  have hc1 : c ≠ 1 := by
    intro hc1
    rw [hc1, Subgroup.zpowers_one_eq_bot] at hc
    obtain ⟨c', hc'C, hc'1⟩ := h.exists_ne_one_mem_sectionCentralizer_of hAL
    rw [hc] at hc'C
    exact hc'1 (by simpa using hc'C)
  exact orderOf_eq_prime (hE27.1.2 c hcZ.1) hc1

end CFSG.RankThree.PartTwo.Late
