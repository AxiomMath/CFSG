module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupConj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1Max

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem oddIdxProp_j1
    {K : Type} [Group K] [Finite K]
    (hK : IsSpor K .J1) : OddIdxProp K := by
  intro N Y D hNne hodd hD hDY hYN hnorm hcover hKGN
  exfalso
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hK
  let ψ : K ≃* CFSG.Sporadic.J1.J := e.trans CFSG.Sporadic.J1.nativeEquiv
  set W : Subgroup CFSG.Sporadic.J1.J := N.map ψ.toMonoidHom with hW
  set A : Subgroup CFSG.Sporadic.J1.J := D.map ψ.toMonoidHom with hA
  have hcardK : Nat.card K = 175560 :=
    (Nat.card_congr ψ.toEquiv).trans CFSG.Sporadic.J1.card_J
  have hA3 : Nat.card A = 3 := by
    rw [hA, Subgroup.card_map_of_injective ψ.injective, hD]
  have hWne : W ≠ ⊤ := by
    intro h
    have htop : (⊤ : Subgroup K).map ψ.toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective ψ.toMonoidHom ψ.surjective
    rw [hW, ← htop] at h
    exact hNne (Subgroup.map_injective ψ.injective h)
  have hNA : Subgroup.normalizer (A : Set CFSG.Sporadic.J1.J) =
      (Subgroup.normalizer (D : Set K)).map ψ.toMonoidHom := by
    rw [hA]
    exact (Subgroup.map_equiv_normalizer_eq D ψ).symm
  have hNAW : Subgroup.normalizer (A : Set CFSG.Sporadic.J1.J) ≤ W := by
    rw [hNA, hW]
    exact Subgroup.map_mono hnorm
  have hH3 : Nat.card (CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1.H) = 3 := by
    rw [CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1.H, Nat.card_zpowers,
      CFSG.Sporadic.J1.orderOf_b]
  have hcyc : ∀ X : Subgroup CFSG.Sporadic.J1.J, IsPGroup 3 X → IsCyclic X := by
    intro X hX
    obtain ⟨n, hn⟩ := hX.exists_card_eq
    have hdvd : 3 ^ n ∣ 175560 := by
      rw [← hn, ← CFSG.Sporadic.J1.card_J]
      exact Subgroup.card_subgroup_dvd_card X
    have hn1 : n ≤ 1 := by
      by_contra hlt
      have h2 : 3 ^ 2 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
      have h9 : 9 ∣ 175560 := by simpa using h2.trans hdvd
      norm_num at h9
    interval_cases n
    · rw [pow_zero] at hn
      have : Subsingleton X := (Nat.card_eq_one_iff_unique.mp hn).1
      exact isCyclic_of_subsingleton
    · rw [pow_one] at hn
      exact isCyclic_of_prime_card hn
  obtain ⟨g, hg⟩ :=
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupConj.exists_conj_eq_of_card_three
      (K := CFSG.Sporadic.J1.J) hcyc (A := CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1.H)
      (B := A) hH3 hA3
  have hgN : CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1.N ≤
      W.map (MulAut.conj g).toMonoidHom := by
    have h1 : (Subgroup.normalizer (A : Set CFSG.Sporadic.J1.J)).map
        (MulAut.conj g).toMonoidHom =
        CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1.N := by
      rw [Subgroup.map_equiv_normalizer_eq, hg]
      rfl
    rw [← h1]
    exact Subgroup.map_mono hNAW
  rcases CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1.eq_or_eq_top hgN with h | h
  ·
    have hcardW : Nat.card W = 60 := by
      have h2 : Nat.card (W.map (MulAut.conj g).toMonoidHom) = 60 := by
        rw [h, CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1.card_N.1]
      rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at h2
    have hcardN : Nat.card N = 60 := by
      have h3 : Nat.card W = Nat.card N := by
        rw [hW]
        exact Subgroup.card_map_of_injective ψ.injective
      rw [← h3]
      exact hcardW
    have hidx : N.index = 2926 := by
      have h4 := N.index_mul_card
      rw [hcardN, hcardK] at h4
      omega
    rw [hidx] at hodd
    exact (by norm_num : ¬ Odd 2926) hodd
  ·
    apply hWne
    have htop : (⊤ : Subgroup CFSG.Sporadic.J1.J).map (MulAut.conj g).toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective
    rw [← htop] at h
    exact Subgroup.map_injective (MulAut.conj g).injective h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
