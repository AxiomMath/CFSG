module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.OddCore
public import CFSG.RankThree.PartOne.CTP.StrongPQuotient
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.SectionRank.PRankIndex
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.HallHigman CFSG.RankThree.PartOne
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

section PSolvable

variable {p : ℕ} [hp : Fact p.Prime]

theorem isPSolvable_of_not_dvd_card {Q : Type} [Group Q] [Finite Q] (h : ¬ p ∣ Nat.card Q) :
    IsPSolvable p Q := by
  intro H _ T _ _
  right
  refine (Nat.Prime.coprime_iff_not_dvd hp.out).2 fun hd => h (hd.trans ?_)
  exact (Subgroup.index_dvd_card T).trans (Subgroup.card_subgroup_dvd_card H)

theorem isPSolvable_of_isPGroup {Q : Type} [Group Q] [Finite Q] (h : IsPGroup p Q) :
    IsPSolvable p Q := by
  intro H _ T _ hs
  left
  exact CFSG.GroupTheory.FT63ChII.card_eq_of_isSimpleGroup_of_isPGroup
    ((h.to_subgroup H).to_quotient T)

theorem isPSolvable_of_normal_sylow {G : Type} [Group G] [Finite G] {M P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P M) (hM : M = normalizer (P : Set G)) :
    IsPSolvable p ↥M := by
  obtain ⟨hPM, hPp, hidx⟩ := (CFSG.ABGLocalTools.isSylowOf_iff).1 hP
  haveI : (P.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).2 hM.le
  refine PSolvableClosure.isPSolvable_of_normal (P.subgroupOf M)
    (isPSolvable_of_isPGroup (hPp.comap_subtype (K := M))) (isPSolvable_of_not_dvd_card ?_)
  rw [← Subgroup.index]
  exact hidx

theorem isPSolvable_of_map {A B : Type} [Group A] [Finite A] [Group B] (f : A →* B) (H : Subgroup A)
    (hker : IsPSolvable p ↥(H ⊓ f.ker)) (him : IsPSolvable p ↥(H.map f)) : IsPSolvable p ↥H := by
  let f' : ↥H →* B := f.comp H.subtype
  have hker' : IsPSolvable p ↥f'.ker := by
    have h1 : f'.ker = (H ⊓ f.ker).subgroupOf H := by
      rw [Subgroup.inf_subgroupOf_left]
      rfl
    rw [h1]
    exact QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe inf_le_left).symm hker
  have hrange : f'.range = H.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e : (↥H ⧸ f'.ker) ≃* ↥(H.map f) :=
    (QuotientGroup.quotientKerEquivRange f').trans (MulEquiv.subgroupCongr hrange)
  exact PSolvableClosure.isPSolvable_of_normal f'.ker hker'
    (QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv e.symm him)

end PSolvable

section StrongEmbedding

variable {p : ℕ} [hp : Fact p.Prime] {X : Type} [Group X] [Finite X]

theorem pPrimeCore_le_of_stronglyPEmbedded {N : Subgroup X} (hN : IsStronglyPEmbedded p N)
    (h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) : CFSG.pPrimeCore p X ≤ N := by
  obtain ⟨P, hP, hPN⟩ := hN.exists_isSylowOf_le
  have hidx : ¬ p ∣ N.index := fun hd => by
    have h1 : ¬ p ∣ P.index := by simpa [Subgroup.relIndex_top_right] using hP.2.2
    exact h1 (hd.trans (Subgroup.index_dvd_of_le hPN))
  have hrank : 2 ≤ CFSG.Open.pRank p ((⊤ : Subgroup X) ⊓ N) := by
    rw [top_inf_eq]
    exact h2.trans (CFSG.SectionRank.pRank_top_le_of_not_dvd_index hp.out N hidx)
  have hle := CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.pPrimeCore_le hN hp.out hrank
  have heq : (CFSG.pPrimeCore p ↥(⊤ : Subgroup X)).map (⊤ : Subgroup X).subtype =
      CFSG.pPrimeCore p X := CFSG.pPrimeCore_map_iso p (Subgroup.topEquiv (G := X))
  rwa [heq] at hle

theorem quotient_of_stronglyPEmbedded {N : Subgroup X} (hN : IsStronglyPEmbedded p N)
    (h2 : 2 < CFSG.Open.pRank p (⊤ : Subgroup X)) :
    IsStronglyPEmbedded p (N.map (QuotientGroup.mk' (CFSG.pPrimeCore p X))) ∧
      2 < CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ CFSG.pPrimeCore p X)) ∧
      CFSG.pPrimeCore p (X ⧸ CFSG.pPrimeCore p X) = ⊥ := by
  haveI : (CFSG.pPrimeCore p X).Normal := CFSG.pPrimeCore_normal
  have hY := pPrimeCore_le_of_stronglyPEmbedded hN h2.le
  have hcop : ¬ p ∣ Nat.card (CFSG.pPrimeCore p X) :=
    (Nat.Prime.coprime_iff_not_dvd hp.out).1 CFSG.pPrimeCore_coprime_card
  refine ⟨hN.map_quotient hY hcop, ?_, CFSG.pPrimeCore_quotient_eq_bot hp.out⟩
  rw [CFSG.SectionRank.pRank_quotient_eq _ hcop]
  exact h2

theorem isPSolvable_of_quotient_pPrimeCore {N : Subgroup X} (hYN : CFSG.pPrimeCore p X ≤ N)
    (h : IsPSolvable p ↥(N.map (QuotientGroup.mk' (CFSG.pPrimeCore p X)))) : IsPSolvable p ↥N := by
  haveI : (CFSG.pPrimeCore p X).Normal := CFSG.pPrimeCore_normal
  refine isPSolvable_of_map (QuotientGroup.mk' (CFSG.pPrimeCore p X)) N ?_ h
  refine isPSolvable_of_not_dvd_card ?_
  rw [QuotientGroup.ker_mk', inf_of_le_right hYN]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 CFSG.pPrimeCore_coprime_card

end StrongEmbedding

end CFSG.LocalAnalysis.UniquenessCase.UCK
