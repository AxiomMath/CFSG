module

public import CFSG.Adapters.LieModelL3U3Torus
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPFF2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

abbrev CM (c : Ctx82E3 D) (a : G) : Subgroup G :=
  D.M ⊓ Subgroup.centralizer ({a} : Set G)

theorem not_isCyclic_of_card_nine_exp_three {E : Type} [Group E] [Finite E]
    (hE : ∀ x : E, x ^ 3 = 1) (hcard : Nat.card E = 9) : ¬ IsCyclic E := by
  classical
  intro hcyc
  haveI := hcyc
  haveI : Fintype E := Fintype.ofFinite E
  have hset : (Finset.univ.filter (fun a : E => a ^ 3 = 1)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro x _
    exact hE x
  have hle := IsCyclic.card_pow_eq_one_le (α := E) (n := 3) (by norm_num)
  change (Finset.univ.filter (fun a : E => a ^ 3 = 1)).card ≤ 3 at hle
  rw [hset, Finset.card_univ, ← Nat.card_eq_fintype_card] at hle
  omega

theorem psl3_section_data {S : Type} [Group S] [Finite S] {p f : ℕ}
    (hmodel : StatedClassicalModel S .PSL 3 p f) (hp3 : p ≠ 3)
    (hmod : p ^ f % 3 = 1) (hq : 3 ≤ p ^ f) :
    (∃ Q : Sylow 3 S, ¬ IsCyclic (Q : Subgroup S)) ∧ ¬ IsAlt S 5 ∧ ¬ IsAlt S 6 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmem : (StatedLieTag.PSL : StatedLieTag) ∈ CFSG.Blueprint.classicalTags := by decide
  have hLie : LieModel S .PSL 3 p f := Or.inl ⟨hmem, hmodel⟩
  have hdvd : 3 ∣ p ^ f - 1 := by
    have h := Nat.mod_add_div (p ^ f) 3
    rw [hmod] at h
    exact ⟨p ^ f / 3, by omega⟩
  have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) :=
    CFSG.Blueprint.LieModel.two_le_pRank_psl3_of_dvd hLie Nat.prime_three hdvd
  obtain ⟨E, -, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (H := ⊤)
      (k := 2) hrank
  have hEp : IsPGroup 3 E := hE.isPGroup
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  have hQnc : ¬ IsCyclic (Q : Subgroup S) := by
    intro hQcyc
    have hEcyc : IsCyclic E := Subgroup.isCyclic_of_le hEQ
    have hexp : ∀ x : E, x ^ 3 = 1 := by
      intro x
      apply Subtype.ext
      simpa using hE.2 (x : S) x.2
    have hcardE : Nat.card E = 9 := by rw [hEcard]; norm_num
    exact not_isCyclic_of_card_nine_exp_three hexp hcardE hEcyc
  have hgt : 3600 < Nat.card S := hLie.three_thousand_six_hundred_lt_card_psl3 hq
  refine ⟨⟨Q, hQnc⟩, ?_, ?_⟩
  · rintro ⟨e⟩
    have hc : Nat.card S = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num
    omega
  · rintro ⟨e⟩
    have hc : Nat.card S = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num
    omega

theorem psu3_section_data {S : Type} [Group S] [Finite S] {p f : ℕ}
    (hmodel : StatedClassicalModel S .PSU 3 p f) (hp3 : p ≠ 3)
    (hmod : p ^ f % 3 = 2) (hq : 3 ≤ p ^ f) :
    (∃ Q : Sylow 3 S, ¬ IsCyclic (Q : Subgroup S)) ∧ ¬ IsAlt S 5 ∧ ¬ IsAlt S 6 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmem : (StatedLieTag.PSU : StatedLieTag) ∈ CFSG.Blueprint.classicalTags := by decide
  have hLie : LieModel S .PSU 3 p f := Or.inl ⟨hmem, hmodel⟩
  have hdvd : 3 ∣ p ^ f + 1 := by
    have h := Nat.mod_add_div (p ^ f) 3
    rw [hmod] at h
    exact ⟨p ^ f / 3 + 1, by omega⟩
  have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) :=
    CFSG.Blueprint.LieModel.two_le_pRank_psu3_of_dvd hLie Nat.prime_three hdvd
  obtain ⟨E, -, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (H := ⊤)
      (k := 2) hrank
  have hEp : IsPGroup 3 E := hE.isPGroup
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  have hQnc : ¬ IsCyclic (Q : Subgroup S) := by
    intro hQcyc
    have hEcyc : IsCyclic E := Subgroup.isCyclic_of_le hEQ
    have hexp : ∀ x : E, x ^ 3 = 1 := by
      intro x
      apply Subtype.ext
      simpa using hE.2 (x : S) x.2
    have hcardE : Nat.card E = 9 := by rw [hEcard]; norm_num
    exact not_isCyclic_of_card_nine_exp_three hexp hcardE hEcyc
  have hgt : 3600 < Nat.card S := hLie.three_thousand_six_hundred_lt_card_psu3 hq
  refine ⟨⟨Q, hQnc⟩, ?_, ?_⟩
  · rintro ⟨e⟩
    have hc : Nat.card S = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num
    omega
  · rintro ⟨e⟩
    have hc : Nat.card S = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num
    omega

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
