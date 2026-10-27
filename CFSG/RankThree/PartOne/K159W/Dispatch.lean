module

public import CFSG.RankThree.PartOne.K159F.CenterRankFive
public import CFSG.RankThree.PartOne.K159W.WeylPSU
import CFSG.RankThree.PartOne.S10.EmbeddingTransport

public section

namespace CFSG.RankThree.PartOne.K159W

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.K159 CFSG.RankThree.PartOne.Mult CFSG.RankThree.PartOne.MultRes Subgroup
  CFSG.RankThree.PartOne.K159F
open scoped MatrixGroups
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem normalizer_map_mulEquiv {K L : Type} [Group K] [Group L] (e : K ≃* L) {R : Subgroup K}
    {n : K} (hn : n ∈ Subgroup.normalizer (R : Set K)) :
    e n ∈ Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup L) : Set L) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  have hmem : ∀ x' : K, e x' ∈ R.map e.toMonoidHom ↔ x' ∈ R := fun x' =>
    ⟨fun ⟨r, hr, h⟩ => e.injective h ▸ hr, fun hx => ⟨x', hx, rfl⟩⟩
  rw [hmem, ← map_mul, ← map_inv, ← map_mul, hmem]
  exact Subgroup.mem_normalizer_iff.1 hn x

theorem ElemAbWeyl.of_mulEquiv {p : ℕ} {K L : Type} [Group K] [Group L] (e : K ≃* L)
    (h : ElemAbWeyl p K) : ElemAbWeyl p L := by
  rcases h with ⟨B, hBp, hBc, hBcard⟩ | ⟨hp5, R, hRp, hRc, hRcard, ⟨n₃, hn₃N, hn₃c, b₃, hb₃R, hb₃⟩,
    ⟨n₅, hn₅N, hn₅c, b₅, hb₅R, hb₅⟩⟩
  · left
    refine ⟨B.map e.toMonoidHom, ?_, ?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      show e b ^ p = 1
      rw [← map_pow, hBp b hb, map_one]
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      show e a * e b = e b * e a
      rw [← map_mul, ← map_mul, hBc a ha b hb]
    · rw [Subgroup.card_map_of_injective e.injective]
      exact hBcard
  · right
    have hcen : ∀ (N : ℕ) (n : K), n ^ N ∈ Subgroup.center K → (e n) ^ N ∈ Subgroup.center L := by
      intro N n hn
      rw [← map_pow]
      rw [Subgroup.mem_center_iff] at hn ⊢
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hn g']
    have hmv : ∀ (n b : K), n * b * n⁻¹ ≠ b → e n * e b * (e n)⁻¹ ≠ e b := by
      intro n b h h'
      apply h
      apply e.injective
      rw [map_mul, map_mul, map_inv]
      exact h'
    refine ⟨hp5, R.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      show e b ^ 5 = 1
      rw [← map_pow, hRp b hb, map_one]
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      show e a * e b = e b * e a
      rw [← map_mul, ← map_mul, hRc a ha b hb]
    · rw [Subgroup.card_map_of_injective e.injective]
      exact hRcard
    · exact ⟨e n₃, normalizer_map_mulEquiv e hn₃N, hcen 3 n₃ hn₃c, e b₃, ⟨b₃, hb₃R, rfl⟩,
        hmv n₃ b₃ hb₃⟩
    · exact ⟨e n₅, normalizer_map_mulEquiv e hn₅N, hcen 5 n₅ hn₅c, e b₅, ⟨b₅, hb₅R, rfl⟩,
        hmv n₅ b₅ hb₅⟩

section Classical

variable {K : Type} [Group K] [Finite K]

theorem elemAbWeyl_psl {p ℓ n f : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpZ : p ∣ Nat.card (Subgroup.center K)) (hodd : Odd (Nat.card (Subgroup.center K)))
    (hmod : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL n ℓ f) (hpn : p ∣ n)
    (hpq : p ∣ ℓ ^ f - 1) : ElemAbWeyl p K := by
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
  by_cases hn : 6 ≤ n
  · left
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨B, hBp, hBc, hBcard⟩ := exists_elemAbelian_psl hp hp2 hζo hζ (by omega : 2 ≤ m) hφs
      hker.le hodd' hzk hz1 hzp
    refine ⟨B, hBp, hBc, ?_⟩
    simp only [hpn, ↓reduceIte] at hBcard
    have hmm : m - 1 + 1 = m + 1 - 1 := by omega
    rw [hmm] at hBcard
    exact le_trans (Nat.pow_le_pow_right hp.pos (by omega)) hBcard
  · right
    have hn5' : n = 5 := by omega
    subst hn5'
    have hp5' : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hpn
    subst hp5'
    exact ⟨rfl, weylFive_psl hζo hζ hφs hker.le hodd' hzk hz1 hzp⟩

theorem elemAbWeyl_psu {p ℓ n f : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpZ : p ∣ Nat.card (Subgroup.center K)) (hodd : Odd (Nat.card (Subgroup.center K)))
    (hmod : StatedClassicalModel (K ⧸ Subgroup.center K) .PSU n ℓ f) (hpn : p ∣ n)
    (hpq : p ∣ ℓ ^ f + 1) : ElemAbWeyl p K := by
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
  by_cases hn : 6 ≤ n
  · left
    obtain ⟨B, hBp, hBc, hBcard⟩ := CFSG.RankThree.PartOne.K159.exists_elemAbelian_unitary hU hp
      hp3 hpq (by omega : 3 ≤ n) φ hφs hker.le hodd' hzk hz1 hzp
    refine ⟨B, hBp, hBc, ?_⟩
    simp only [hpn, ↓reduceIte] at hBcard
    have hmm : n - 1 - 1 + 1 = n - 1 := by omega
    rw [hmm] at hBcard
    exact le_trans (Nat.pow_le_pow_right hp.pos (by omega)) hBcard
  · right
    have hn5' : n = 5 := by omega
    subst hn5'
    have hp5' : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hpn
    subst hp5'
    obtain ⟨ζ, hζo, hζN⟩ := CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one hU hp hpq
    have hζ : ζ ^ 5 = 1 := by rw [← hζo, pow_orderOf_eq_one]
    exact ⟨rfl, weylFive_psu hU hζo hζ hζN hφs hker.le hodd' hzk hz1 hzp⟩

end Classical

section Table

theorem elemAbWeyl_of_model
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) {t : StatedLieTag} {n ℓ f : ℕ}
    (hmod : StatedClassicalModel (K ⧸ Subgroup.center K) t n ℓ f) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpZ : p ∣ Nat.card (Subgroup.center K))
    (hodd : Odd (Nat.card (Subgroup.center K))) : ElemAbWeyl p K := by
  have hdvd := card_center_dvd_of_model hGA hK hmod
  rcases prime_dvd_table hp hp3 (hpZ.trans hdvd) with ⟨rfl, hpn, hpq⟩ | ⟨rfl, hpn, hpq⟩
  · exact elemAbWeyl_psl hp hp3 hpZ hodd hmod hpn hpq
  · exact elemAbWeyl_psu hp hp3 hpZ hodd hmod hpn hpq

end Table

theorem centerWeylFive_of_residual_trim
    (hbridge : TauCetiCatalogBridge)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hres : SporadicResidualKernelsTrim)
    (hFi22 : SectionsForceEvenRankFour (Carrier .Fi22))
    (hFi23 : SectionsForceEvenRankFour (Carrier .Fi23))
    (hFi24 : SectionsForceEvenRankFour (Carrier .Fi24Prime))
    (hB : SectionsForceEvenRankFour (Carrier .B))
    (hM : SimplePresentationMSectionsForceEvenRankFour) : CenterWeylFive := by

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
  apply ElemAbWeyl.of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q)
  rcases hcat with ⟨q, hq, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | hcl | hex | hsp
  · exfalso
    obtain ⟨a, b, hab⟩ := hqt.2.2
    exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
  · exact absurd hpZ' (alternating_center_small_primes hm e hp hp3)
  · obtain ⟨t, n, ℓ, f, hmod⟩ := hcl
    exact elemAbWeyl_of_model hGA hqt hmod hp hp3 hpZ' hodd'
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

theorem centerWeylFive_of_griess
    (hbridge : TauCetiCatalogBridge)
    (hGA : CFSG.Open.GriessAllModelsStatement) : CenterWeylFive :=
  have h2224 := sectionsForceEvenRankFour_fi23_fi24prime sectionsForceEvenRankFour_Fi22
    hasSection_fi23_fi22 hasSection_fi24prime_fi23
  centerWeylFive_of_residual_trim hbridge hGA sporadicResidualKernelsTrim_holds
    sectionsForceEvenRankFour_Fi22 h2224.1 h2224.2 sectionsForceEvenRankFour_B
    (simplePresentationM_sections_of_B_section sectionsForceEvenRankFour_B
      simplePresentationMHasBSection_holds)

end CFSG.RankThree.PartOne.K159W
