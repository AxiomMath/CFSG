module

import CFSG.RankThree.PartOne.S10.EmbeddingTransport
public import CFSG.RankThree.PartOne.K159.CenterRank
public import CFSG.RankThree.PartOne.KP.BExclusion
public import CFSG.RankThree.PartOne.KP.Fi22Section
public import CFSG.RankThree.PartOne.KP.MSectionMonster
public import CFSG.RankThree.PartOne.KS.FischerSections
public import CFSG.RankThree.PartOne.MultRes.Trim

public section

namespace CFSG.RankThree.PartOne.K159F

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.K159 CFSG.RankThree.PartOne.Mult CFSG.RankThree.PartOne.MultRes Subgroup
open scoped MatrixGroups
open CFSG.Blueprint.NativeSporadic (Carrier)

@[expose] def ElemAbFive (p : ℕ) (K : Type) [Group K] : Prop :=
  (∃ B : Subgroup K, (∀ b ∈ B, b ^ p = 1) ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
      p ^ 5 ≤ Nat.card B) ∨
    (p = 5 ∧ ∃ B : Subgroup K, (∀ b ∈ B, b ^ p = 1) ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
      p ^ 4 ≤ Nat.card B)

theorem elemAbFive_of_pow {p n : ℕ} {K : Type} [Group K] (hp : p.Prime) (hn5 : 5 ≤ n)
    (hpn : p ∣ n) {B : Subgroup K} (hBp : ∀ b ∈ B, b ^ p = 1)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBcard : p ^ (n - 1) ≤ Nat.card B) :
    ElemAbFive p K := by
  by_cases hn : 6 ≤ n
  · left
    exact ⟨B, hBp, hBc, le_trans (Nat.pow_le_pow_right hp.pos (by omega)) hBcard⟩
  · right
    have hn5' : n = 5 := by omega
    subst hn5'
    have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hpn
    exact ⟨hp5, B, hBp, hBc, hBcard⟩

section Classical

variable {K : Type} [Group K] [Finite K]

theorem exists_elemAbelian_five_psl {p ℓ n f : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpZ : p ∣ Nat.card (Subgroup.center K)) (hodd : Odd (Nat.card (Subgroup.center K)))
    (hmod : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL n ℓ f) (hpn : p ∣ n)
    (hpq : p ∣ ℓ ^ f - 1) : ElemAbFive p K := by
  classical
  have hp2 : p ≠ 2 := by omega
  obtain ⟨⟨hℓ, hf, hn2, -⟩, k, _, hkfin, hk, ⟨e⟩⟩ := hmod
  have hp5 := five_le_of_prime' hp hp3
  have hn5 : 5 ≤ n := le_trans hp5 (Nat.le_of_dvd (by omega) hpn)
  have := Fintype.ofFinite k
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hpk : p ∣ Fintype.card k - 1 := by rwa [← Nat.card_eq_fintype_card, hk]
  have : Fact p.Prime := ⟨hp⟩
  let ψ : K ⧸ Subgroup.center K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) k :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj n k).symm
  let φ : K →* Matrix.ProjectiveSpecialLinearGroup (Fin n) k :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hφs : Function.Surjective φ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center K := ker_comp_mk'_eq_center ψ
  have hodd' : Odd (Nat.card φ.ker) := by rw [hker]; exact hodd
  have hcard : p ∣ Nat.card kˣ := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
    exact hpk
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hcard
  have hζ : ζ ^ p = 1 := by rw [← hζo, pow_orderOf_eq_one]
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) p hpZ
  have hz1 : (z : K) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hzp : (z : K) ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have hzk : (z : K) ∈ φ.ker := by rw [hker]; exact z.2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨B, hBp, hBc, hBcard⟩ := exists_elemAbelian_psl hp hp2 hζo hζ (by omega : 2 ≤ m) hφs
    hker.le hodd' hzk hz1 hzp
  refine elemAbFive_of_pow hp hn5 hpn hBp hBc ?_
  simp only [hpn, ↓reduceIte] at hBcard
  have hmm : m - 1 + 1 = m + 1 - 1 := by omega
  rw [hmm] at hBcard
  exact hBcard

theorem exists_elemAbelian_five_psu {p ℓ n f : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpZ : p ∣ Nat.card (Subgroup.center K)) (hodd : Odd (Nat.card (Subgroup.center K)))
    (hmod : StatedClassicalModel (K ⧸ Subgroup.center K) .PSU n ℓ f) (hpn : p ∣ n)
    (hpq : p ∣ ℓ ^ f + 1) : ElemAbFive p K := by
  classical
  have hp2 : p ≠ 2 := by omega
  obtain ⟨⟨hℓ, hf, hn3, -⟩, k, _, hkfin, hk, ⟨e⟩⟩ := hmod
  have hp5 := five_le_of_prime' hp hp3
  have hn5 : 5 ≤ n := le_trans hp5 (Nat.le_of_dvd (by omega) hpn)
  have : Fact p.Prime := ⟨hp⟩
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f k :=
    ⟨hℓ, hf, by rw [hk, ← pow_mul, mul_comm]⟩
  let ψ : K ⧸ Subgroup.center K ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU n :=
    e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by omega)).symm
  let φ : K →* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU n :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hφs : Function.Surjective φ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center K := ker_comp_mk'_eq_center ψ
  have hodd' : Odd (Nat.card φ.ker) := by rw [hker]; exact hodd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) p hpZ
  have hz1 : (z : K) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hzp : (z : K) ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have hzk : (z : K) ∈ φ.ker := by rw [hker]; exact z.2
  obtain ⟨B, hBp, hBc, hBcard⟩ := CFSG.RankThree.PartOne.K159.exists_elemAbelian_unitary hU hp hp3
    hpq (by omega : 3 ≤ n) φ hφs hker.le hodd' hzk hz1 hzp
  refine elemAbFive_of_pow hp hn5 hpn hBp hBc ?_
  simp only [hpn, ↓reduceIte] at hBcard
  have hmm : n - 1 - 1 + 1 = n - 1 := by omega
  rw [hmm] at hBcard
  exact hBcard

end Classical

section Table

theorem exists_elemAbelian_five_of_model
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) {t : StatedLieTag} {n ℓ f : ℕ}
    (hmod : StatedClassicalModel (K ⧸ Subgroup.center K) t n ℓ f) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpZ : p ∣ Nat.card (Subgroup.center K))
    (hodd : Odd (Nat.card (Subgroup.center K))) : ElemAbFive p K := by
  have hdvd := card_center_dvd_of_model hGA hK hmod
  rcases prime_dvd_table hp hp3 (hpZ.trans hdvd) with ⟨rfl, hpn, hpq⟩ | ⟨rfl, hpn, hpq⟩
  · exact exists_elemAbelian_five_psl hp hp3 hpZ hodd hmod hpn hpq
  · exact exists_elemAbelian_five_psu hp hp3 hpZ hodd hmod hpn hpq

end Table

theorem ElemAbFive.map {p : ℕ} {K L : Type} [Group K] [Group L] (f : K →* L)
    (hf : Function.Injective f) (h : ElemAbFive p K) : ElemAbFive p L := by
  have key : ∀ (B : Subgroup K), (∀ b ∈ B, b ^ p = 1) → (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) →
      ∀ n : ℕ, p ^ n ≤ Nat.card B →
      ∃ B' : Subgroup L, (∀ b ∈ B', b ^ p = 1) ∧ (∀ a ∈ B', ∀ b ∈ B', a * b = b * a) ∧
        p ^ n ≤ Nat.card B' := by
    intro B hBp hBc n hn
    refine ⟨B.map f, ?_, ?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      rw [← map_pow, hBp b hb, map_one]
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hBc a ha b hb]
    · rw [Subgroup.card_map_of_injective hf]
      exact hn
  rcases h with ⟨B, hBp, hBc, hBcard⟩ | ⟨hp5, B, hBp, hBc, hBcard⟩
  · left
    exact key B hBp hBc 5 hBcard
  · right
    exact ⟨hp5, key B hBp hBc 4 hBcard⟩

@[expose] def CenterRankFive : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.twoLocalOddRank X ≤ 3 → CFSG.IsKGroup X →
    ∀ (O : Subgroup X) [O.Normal], CFSG.IsQuasisimple (X ⧸ O) → ∀ p : ℕ, p.Prime → 3 < p →
      p ∣ Nat.card (Subgroup.center (X ⧸ O)) → Odd (Nat.card (Subgroup.center (X ⧸ O))) →
        ElemAbFive p (X ⧸ O)

theorem centerRankFive_of_residual_trim
    (hbridge : TauCetiCatalogBridge)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hres : SporadicResidualKernelsTrim)
    (hFi22 : SectionsForceEvenRankFour (Carrier .Fi22))
    (hFi23 : SectionsForceEvenRankFour (Carrier .Fi23))
    (hFi24 : SectionsForceEvenRankFour (Carrier .Fi24Prime))
    (hB : SectionsForceEvenRankFour (Carrier .B))
    (hM : SimplePresentationMSectionsForceEvenRankFour) : CenterRankFive := by
  intro X _ _ he hKX O _ hQq p hp hp3 hpZ hodd
  set Q := X ⧸ O with hQ
  have hQK : CFSG.IsKGroup Q := EmbeddingTransport.isKGroup_quotient hKX _
  have hqt : CFSG.IsQuasisimple (⊤ : Subgroup Q) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q).symm hQq
  have hsimple' : IsSimpleGroup ((⊤ : Subgroup Q) ⧸ Subgroup.center (⊤ : Subgroup Q)) := hqt.2.1
  have hcat : CFSG.Blueprint.Catalog ((⊤ : Subgroup Q) ⧸ Subgroup.center (⊤ : Subgroup Q)) :=
    hbridge _ hqt.2.2 (hQK ⊤ (Subgroup.center (⊤ : Subgroup Q)) hsimple')
  have hcardZ : Nat.card (Subgroup.center (⊤ : Subgroup Q)) = Nat.card (Subgroup.center Q) :=
    Nat.card_congr (Subgroup.centerCongr (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q)).toEquiv
  have hpZ' : p ∣ Nat.card (Subgroup.center (⊤ : Subgroup Q)) := by rw [hcardZ]; exact hpZ
  have hodd' : Odd (Nat.card (Subgroup.center (⊤ : Subgroup Q))) := by rw [hcardZ]; exact hodd
  have : Group.IsPerfect ↥(⊤ : Subgroup Q) := hqt.1
  apply ElemAbFive.map (⊤ : Subgroup Q).subtype (⊤ : Subgroup Q).subtype_injective
  rcases hcat with ⟨q, hq, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | hcl | hex | hsp
  · exfalso
    obtain ⟨a, b, hab⟩ := hqt.2.2
    exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
  · exact absurd hpZ' (alternating_center_small_primes hm e hp hp3)
  · obtain ⟨t, n, ℓ, f, hmod⟩ := hcl
    exact exists_elemAbelian_five_of_model hGA hqt hmod hp hp3 hpZ' hodd'
  · exact absurd hpZ' (exceptionalCenterSmallPrimes_of_griess hGA _ hqt hex p hp hp3)
  · exfalso
    obtain ⟨s, ⟨e⟩⟩ := hsp
    by_cases hexc : SectionExcluded s
    · obtain ⟨H, K, hK, ⟨φ⟩⟩ := exists_section_of_quotient_subgroup O (⊤ : Subgroup Q)
      have hrank : 4 ≤ evenRank X := by
        rcases hexc with rfl | rfl | rfl | rfl | rfl
        · exact hFi22 X H K ⟨φ.trans e⟩
        · exact hFi23 X H K ⟨φ.trans e⟩
        · exact hFi24 X H K ⟨φ.trans e⟩
        · exact hB X H K ⟨φ.trans e⟩
        · have : IsSimpleGroup (↥(⊤ : Subgroup Q) ⧸ center ↥(⊤ : Subgroup Q)) := hqt.2.1
          exact hM X H K (↥(⊤ : Subgroup Q) ⧸ center ↥(⊤ : Subgroup Q)) hqt.2.2 ⟨φ⟩ ⟨e⟩
      have := CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank X
      omega
    · obtain ⟨hpair, hnot⟩ := sporadic_residual_of_center e hp hp3 hpZ'
      exact hnot (hres.trivial_of_pair hexc hpair)

theorem centerRankFive_of_griess_of_M_section
    (hbridge : TauCetiCatalogBridge)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hMB : SimplePresentationMHasBSection) : CenterRankFive :=
  have h2224 := sectionsForceEvenRankFour_fi23_fi24prime sectionsForceEvenRankFour_Fi22
    hasSection_fi23_fi22 hasSection_fi24prime_fi23
  centerRankFive_of_residual_trim hbridge hGA sporadicResidualKernelsTrim_holds
    sectionsForceEvenRankFour_Fi22 h2224.1 h2224.2 sectionsForceEvenRankFour_B
    (simplePresentationM_sections_of_B_section sectionsForceEvenRankFour_B hMB)

theorem centerRankFive_of_griess
    (hbridge : TauCetiCatalogBridge)
    (hGA : CFSG.Open.GriessAllModelsStatement) : CenterRankFive :=
  centerRankFive_of_griess_of_M_section hbridge hGA simplePresentationMHasBSection_holds

end CFSG.RankThree.PartOne.K159F
