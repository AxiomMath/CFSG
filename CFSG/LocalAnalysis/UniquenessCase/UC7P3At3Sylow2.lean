module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.LayerBasic
import CFSG.HardMathSupport.Solomon.Coordinator.I18_10Basic
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.RankThree.PartOne.CTP.StrongPQuotient
import CFSG.RankThree.PartTwo.Sec4.T444.Coprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem exists_isSylowOf_two_of_index_eq_three (k : Sec7Core4 G) {H : Subgroup G}
    (hH : Config k H) {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf k.p P (H ⊓ k.M))
    {Pb : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)}
    (hPb : (P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) = Pb)
    (hidx : (CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)).index = 3)
    (hPF : ¬ Pb ≤ CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H))
    (h27 : Nat.card Pb = 27)
    (h18 : Nat.card ↥(((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) ⊓
      CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) = 18) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ k.M) ∧
      S ≤ normalizer (P : Set G) ∧ IsCyclic S ∧
        (S.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) ≤
          CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H) := by
  subst hPb
  classical
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPHM, hPp, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hP
  have hPH : P ≤ H := hPHM.trans inf_le_left
  have hP1 : P ≠ ⊥ := by
    rintro rfl
    rw [bot_subgroupOf, Subgroup.map_bot, card_bot] at h27
    exact absurd h27 (by norm_num)
  obtain ⟨-, -, hFn, -⟩ := k.isSimpleGroup_generalizedFitting_quotient hH
  haveI := hFn
  set K₀ : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H with hK₀
  set F : Subgroup (↥H ⧸ K₀) := CFSG.generalizedFitting (↥H ⧸ K₀) with hF
  set N : Subgroup (↥H ⧸ K₀) := ((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' K₀) with hN
  have hBN : (P.subgroupOf H).map (QuotientGroup.mk' K₀) ≤ N := map_mono (subgroupOf_mono H hPHM)
  have hodd : ¬ 2 ∣ Nat.card K₀ := fun h =>
    Nat.not_even_iff_odd.mpr (k.odd_card_pPrimeCore_of_not_le hH.not_le hH.two_le_pRank)
      (even_iff_two_dvd.mpr h)
  have hFN : F.relIndex N = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (hidx ▸ relIndex_dvd_index_of_normal F N) with h | h
    · exact absurd (hBN.trans (relIndex_eq_one.mp h)) hPF
    · exact h
  have hNcard : Nat.card N = 54 := by
    rw [← relIndex_mul_card F N, hFN, inf_comm, h18]
  have hPN2 : ((P.subgroupOf H).map (QuotientGroup.mk' K₀)).relIndex N = 2 := by
    have h1 := relIndex_mul_card ((P.subgroupOf H).map (QuotientGroup.mk' K₀)) N
    rw [inf_of_le_left hBN, h27, hNcard] at h1
    omega
  have hNP : N ≤ normalizer (((P.subgroupOf H).map (QuotientGroup.mk' K₀) :
      Subgroup (↥H ⧸ K₀)) : Set (↥H ⧸ K₀)) :=
    (normal_subgroupOf_iff_le_normalizer hBN).mp (normal_of_index_eq_two hPN2)
  rw [← CFSG.RankThree.PartTwo.Sec4.map_normalizer_eq_of_not_dvd k.prime K₀
    ((k.prime.coprime_iff_not_dvd).mp CFSG.pPrimeCore_coprime_card)
    (B := P.subgroupOf H) hPp.comap_subtype] at hNP
  have hHK : H ≤ normalizer ((K₀.map H.subtype : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le K₀)).mp
      (by
        rw [show (K₀.map H.subtype).subgroupOf H = K₀ from
          comap_map_eq_self_of_injective H.subtype_injective K₀]
        infer_instance)
  have hHMY : H ⊓ k.M ≤ K₀.map H.subtype ⊔ (H ⊓ normalizer (P : Set G)) := by
    intro x hx
    obtain ⟨n, hn, hnx⟩ := mem_map.mp (hNP ⟨⟨x, hx.1⟩, mem_subgroupOf.mpr hx, rfl⟩)
    have hc : n⁻¹ * ⟨x, hx.1⟩ ∈ K₀ := QuotientGroup.eq.mp hnx
    rw [← subgroupOf_normalizer_eq hPH] at hn
    have hx' : x = (n : G) * ((n⁻¹ * ⟨x, hx.1⟩ : ↥H) : G) := by simp
    rw [hx', sup_comm]
    exact mul_mem_sup ⟨n.2, mem_subgroupOf.mp hn⟩ ⟨_, hc, rfl⟩
  have hYM : H ⊓ normalizer (P : Set G) ≤ H ⊓ k.M :=
    inf_le_inf_left H (k.strong.normalizer_le hP1 hPp (hPHM.trans inf_le_right))
  have hYodd : ¬ 2 ∣ (H ⊓ normalizer (P : Set G)).relIndex (H ⊓ k.M) := by
    intro h2
    have h1 := relIndex_mul_relIndex _ _ _ hYM hHMY
    rw [CFSG.ABGTheoremB.relIndex_sup_eq_relIndex_of_le_normalizer (inf_le_left.trans hHK)] at h1
    have h3 := (h2.trans (Dvd.intro _ h1)).trans (relIndex_dvd_card _ _)
    rw [card_map_of_injective H.subtype_injective] at h3
    exact hodd h3
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (H ⊓ normalizer (P : Set G))
  obtain ⟨hSY, hS2, hSi⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hS
  have hSHM : S ≤ H ⊓ k.M := hSY.trans hYM
  have hSH : S ≤ H := hSHM.trans inf_le_left
  have hSF : (S.subgroupOf H).map (QuotientGroup.mk' K₀) ≤ F :=
    CFSG.HardMathSupport.Solomon.Coordinator.i1810_le_of_not_dvd_index
      (hS2.comap_subtype.map _) (by rw [hidx]; norm_num)
  refine ⟨S, CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hSHM, hS2, fun h => ?_⟩,
    hSY.trans inf_le_right, ?_, hSF⟩
  · rw [← relIndex_mul_relIndex S _ _ hSY hYM] at h
    rcases (Nat.prime_two.dvd_mul).mp h with h | h
    · exact hSi h
    · exact hYodd h
  ·
    apply isCyclic_of_card_dvd_prime (p := 2)
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hS2
    have h1 : Nat.card S ∣ 18 := by
      rw [← h18, ← Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv,
        ← CFSG.RankThree.PartOne.StrongP.card_map_quotient_of_coprime (E := S.subgroupOf H)
          hS2.comap_subtype hodd]
      exact card_dvd_of_le (le_inf (map_mono (subgroupOf_mono H hSHM)) hSF)
    rw [hn] at h1 ⊢
    exact (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 9)).dvd_of_dvd_mul_right h1

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
