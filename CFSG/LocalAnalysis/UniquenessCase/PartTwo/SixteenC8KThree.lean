module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Image
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xj
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.Group
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem c8k_cyclic_sylow3 (D : Data G) (h61 : UC6.R6_1 D) (h3 : 3 ∈ D.sig)
    (hse : IsStronglyPEmbedded 3 D.M) {K : Subgroup G}
    (hK : CFSG.QuasithinUnique.CharTwo K) (hKM : ¬ K ≤ D.M) {d : G} (hdK : d ∈ K)
    (hdM : d ∈ D.M) (hd3 : orderOf d = 3) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P K ∧ P ≤ D.M ∧ IsCyclic P ∧ d ∈ P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU : IsPGroup 3 (Subgroup.zpowers d) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd3, pow_one])
  have hUle : Subgroup.zpowers d ≤ K ⊓ D.M := Subgroup.zpowers_le.2 ⟨hdK, hdM⟩
  obtain ⟨S, hS, hUS⟩ := CFSG.Quasithin.exists_isSylowIn_ge 3 hUle hU
  have hdS : d ∈ S := hUS (Subgroup.mem_zpowers d)
  have hS1 : S ≠ ⊥ := by
    intro hbot
    have hd1 : d = 1 := Subgroup.mem_bot.1 (hbot ▸ hdS)
    rw [hd1, orderOf_one] at hd3
    exact absurd hd3 (by norm_num)
  refine ⟨S, uc22s13xj_isSylowOf_of_inf hse (CFSG.ABGLocalTools.isSylowOf_iff.2 hS) hS1,
    hS.le.trans inf_le_right, ?_, hdS⟩
  by_contra hSc
  exact hKM (c8_le_of_noncyclic_three D h61 h3 hK hS.le hS.isPGroup hSc)

private theorem c8k_pSubgroups_cyclic {K P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P K) (hc : IsCyclic P) :
    ∀ A : Subgroup ↥K, IsPGroup 3 A → IsCyclic A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hP
  have hQc : IsCyclic ↥Q :=
    (Subgroup.equivMapOfInjective (Q : Subgroup ↥K) K.subtype K.subtype_injective).isCyclic.mpr
      (hQ ▸ hc)
  intro A hA
  obtain ⟨R, hAR⟩ := hA.exists_le_sylow
  haveI : IsCyclic ↥R := (Sylow.equiv Q R).isCyclic.mp hQc
  exact Subgroup.isCyclic_of_le hAR

theorem c8k_pRank_le_one_of_sylow {K P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P K)
    (hc : IsCyclic P) : pRank 3 K ≤ 1 :=
  CFSG.RankThree.PartOne.K128.pRank_le_one_of_cyclic_pSubgroups Nat.prime_three
    (c8k_pSubgroups_cyclic hP hc)

theorem c8k_three_part {B C₀ : Subgroup G} (hCB : C₀ ≤ B) (hP : C8P0 B C₀) {d : G}
    (hdB : d ∈ B) (hd3 : orderOf d = 3) (hdC : d ∉ C₀) {P : Subgroup G}
    (hPB : CFSG.ABGLocalTools.IsSylowOf 3 P B) (hdP : d ∈ P) (hPc : IsCyclic P) :
    ¬ 3 ∣ Nat.card C₀ := by
  obtain ⟨P₀, _, φ, -, hker, -, -⟩ := hP
  haveI : (C₀.subgroupOf B).Normal := hker ▸ φ.normal_ker
  have hcyc : ∀ A : Subgroup ↥B, IsPGroup 3 A → IsCyclic A := c8k_pSubgroups_cyclic hPB hPc
  have hxp : (⟨d, hdB⟩ : ↥B) ^ 3 = 1 := by
    have ho : orderOf (⟨d, hdB⟩ : ↥B) = 3 := by rw [Subgroup.orderOf_mk, hd3]
    rw [← ho]
    exact pow_orderOf_eq_one _
  have hx1 : (⟨d, hdB⟩ : ↥B) ≠ 1 := by
    intro h
    have hd1 : d = 1 := Subtype.ext_iff.mp h
    rw [hd1, orderOf_one] at hd3
    exact absurd hd3 (by norm_num)
  have hxN : (⟨d, hdB⟩ : ↥B) ∉ C₀.subgroupOf B := by
    intro h
    exact hdC (Subgroup.mem_subgroupOf.mp h)
  have hnot := CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.normal_pPrime_of_cycSylow
    (D := ↥B) Nat.prime_three hcyc (x := ⟨d, hdB⟩) hxp hx1 hxN
  have hcard : Nat.card ↥(C₀.subgroupOf B) = Nat.card C₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCB).toEquiv
  rwa [hcard] at hnot

theorem c8k_c0_three (D : Data G) (h61 : UC6.R6_1 D) (hse : IsStronglyPEmbedded 3 D.M)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {v₀ : IntMod V hV} {T₀ K T' : Subgroup G}
    (hs : C8KSetting D V₀ V L hV v₀ T₀ K T')
    (hP : C8P0 (K ⊓ D.M) (K ⊓ F11.CTilde D.M V₀ V)) {d : G} (hdL : d ∈ L) (hdK : d ∈ K)
    (hd3 : orderOf d = 3) :
    ¬ 3 ∣ Nat.card ↥(K ⊓ F11.CTilde D.M V₀ V) ∧ pRank 3 K ≤ 1 := by
  have hLM : L ≤ D.M := hs.sect.setting.hyp151.le
  have h3 : 3 ∈ D.sig := by rw [hs.case8.2.2.1]; exact Set.mem_singleton 3
  obtain ⟨P, hPK, hPM, hPc, hdP⟩ := c8k_cyclic_sylow3 D h61 h3 hse hs.setUp.mem.2.2.2
    hs.setUp.mem.2.2.1 hdK (hLM hdL) hd3
  have hdC : d ∉ K ⊓ F11.CTilde D.M V₀ V := by
    intro h
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hs.good.2) ⟨d, hdL, h.2⟩
    have hk' : 3 = 2 ^ k := by
      rw [← hd3, ← hk]
      exact (Subgroup.orderOf_mk d _).symm
    have hk2 : k < 2 := by
      by_contra hc
      have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k <;> omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPB : CFSG.ABGLocalTools.IsSylowOf 3 P (K ⊓ D.M) :=
    hPK.of_le (le_inf hPK.le hPM) inf_le_left
  exact ⟨c8k_three_part (inf_le_inf_left K (c8_cTilde_le D.M V₀ V)) hP ⟨hdK, hLM hdL⟩ hd3 hdC
    hPB hdP hPc, c8k_pRank_le_one_of_sylow hPK hPc⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
