module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTits
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TitsFiveLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SzFiveTrans
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.AltTenGood
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltAut
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltLocal
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229SEFZ

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

theorem sylow_of_isAltTwoP {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {X : Type} [Group X] [Finite X]
    {K : Subgroup X} [K.Normal] (hKC : Subgroup.centralizer (K : Set X) = ⊥)
    (hK : CFSG.AGLEmbedding.IsAltTwoP p ↥K) (R : Sylow p X) :
    Nat.card (R : Subgroup X) = p ^ 2 ∧ Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ R := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨e⟩ := hK
  have hq : Nat.card (X ⧸ K) ∣ 2 :=
    SEFive.card_quotient_dvd_two_of_equiv_alternating hKC (by omega) e
  have hRK : (R : Subgroup X) ≤ K := by
    intro r hr
    obtain ⟨k, hk⟩ := R.isPGroup' ⟨r, hr⟩
    have hrk : r ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf (QuotientGroup.mk' K r) ∣ 2 := (orderOf_dvd_natCard _).trans hq
    have h2 : orderOf (QuotientGroup.mk' K r) ∣ p ^ k :=
      (orderOf_map_dvd _ r).trans (orderOf_dvd_of_pow_eq_one hrk)
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      exact h
    · rw [h] at h2
      exact (hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
        (Nat.prime_two.dvd_of_dvd_pow h2)).symm).elim
  let T : Sylow p ↥K := R.subtype hRK
  have hTc : (T : Subgroup ↥K) = (R : Subgroup X).subgroupOf K := rfl
  have hcard : Nat.card (R : Subgroup X) = p ^ 2 := by
    have h := (CFSG.AGLEmbedding.KFactProofs.SmallIdent.isElemAbelian_map_sylow hp hp2 e T).2
    rw [Subgroup.card_map_of_injective
      (CFSG.AGLEmbedding.KFactProofs.SmallIdent.altPermEmbed_injective e), hTc] at h
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv] at h
  refine ⟨hcard, fun g hg => ?_⟩
  have hfix : ∀ u ∈ (T : Subgroup ↥K), (MulAut.conjNormal g : MulAut ↥K) u = u := by
    intro u hu
    rw [hTc, Subgroup.mem_subgroupOf] at hu
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, ← (Subgroup.mem_centralizer_iff.1 hg) u hu]
    group
  obtain ⟨k, hk⟩ := CFSG.AGLEmbedding.KFactProofs.SmallIdent.autFixInner_of_isAltTwoP_of_five_le
    hp hp5 ⟨e⟩ T _ hfix
  have hgk : g = (k : X) := by
    have hc : (k : X)⁻¹ * g ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h : (k : X) * y * (k : X)⁻¹ = g * y * g⁻¹ := by
        simpa using congrArg (fun f : MulAut ↥K => ((f ⟨y, hy⟩ : ↥K) : X)) hk
      calc y * ((k : X)⁻¹ * g) = (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * g := by group
        _ = (k : X)⁻¹ * (g * y * g⁻¹) * g := by rw [h]
        _ = (k : X)⁻¹ * g * y := by group
    rw [hKC, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.1 hc).symm
  have hkT : k ∈ (T : Subgroup ↥K) :=
    CFSG.AGLEmbedding.KFactProofs.SmallIdent.centralizer_le_of_isAltTwoP hp hp2 ⟨e⟩ T
      fun t ht => by
        have h := congrArg (fun f : MulAut ↥K => f t) hk
        simp only [MulAut.conj_apply] at h
        rw [hfix t ht] at h
        calc k * t = k * t * k⁻¹ * k := by group
          _ = t * k := by rw [h]
  rw [hTc, Subgroup.mem_subgroupOf] at hkT
  rw [hgk]
  exact hkT

section Tits


theorem sylow_of_isTitsGroup {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    (hKC : Subgroup.centralizer (K : Set X) = ⊥) (hK : CFSG.AGLEmbedding.IsTitsGroup ↥K)
    (R : Sylow 5 X) :
    Nat.card (R : Subgroup X) = 5 ^ 2 ∧ Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ R := by
  obtain ⟨eD⟩ := CFSG.AGLEmbedding.KFactProofs.SmallIdent.nonempty_equiv_tits hK
  obtain ⟨hRcard, -, hRC, -⟩ := CFSG.AGLEmbeddingD2.torusLocal_tits_sylow hKC eD R
  exact ⟨hRcard, hRC⟩

end Tits

theorem goodZ_of_sz32 {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hK : CFSG.AGLEmbeddingD2.Sz32Normal K) (N : Subgroup X) :
    InvolutionCentralizerHasPElementOutside 5 N ∧ AbelianPSubgroupLeFStar 5 N := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI := hK.normal
  have hq : Nat.card (X ⧸ K) ∣ 5 := by
    rw [← Subgroup.index_eq_card]
    exact hK.index_dvd_five
  refine ⟨fun A _ hA hAc t _ ht2 htA => ?_, fun B _ hB hBab hBc => ?_⟩
  · exfalso
    have htK : t ∈ K := by
      have h1 : orderOf (QuotientGroup.mk' K t) ∣ 5 := (orderOf_dvd_natCard _).trans hq
      have h2 : orderOf (QuotientGroup.mk' K t) ∣ 2 := by
        rw [← ht2]
        exact orderOf_map_dvd _ t
      have h3 : orderOf (QuotientGroup.mk' K t) ∣ 1 := by
        have h := Nat.dvd_gcd h1 h2
        rwa [show Nat.gcd 5 2 = 1 by norm_num] at h
      rw [Nat.dvd_one, orderOf_eq_one_iff, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at h3
      exact h3
    obtain ⟨z, hzA, hzK, hz1⟩ : ∃ z ∈ A, z ∈ K ∧ z ≠ 1 := by
      by_contra h
      push Not at h
      have hf : Function.Injective ((QuotientGroup.mk' K).comp A.subtype) := by
        rw [injective_iff_map_eq_one]
        intro a ha
        rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
        exact Subtype.ext (h a a.2 ha)
      have h1 := Nat.card_le_card_of_injective _ hf
      have h2 := Nat.le_of_dvd (by norm_num) hq
      rw [hAc] at h1
      norm_num at h1
      omega
    obtain ⟨R, hAR⟩ := hA.isPGroup.exists_le_sylow
    have hTc := hK.card_sylow_inf R
    have htT : t ∈ (R : Subgroup X) ⊓ K :=
      hK.mem_of_commute inf_le_right hTc ⟨hAR hzA, hzK⟩ hz1 htK (htA z hzA).symm
    have h := Subgroup.orderOf_dvd_natCard _ htT
    rw [ht2, hTc] at h
    norm_num at h
  · exfalso
    obtain ⟨R, hBR⟩ := hB.exists_le_sylow
    have hX : Nat.card X ∣ 32537600 * 5 := by
      rw [← Subgroup.card_mul_index K, hK.card]
      exact Nat.mul_dvd_mul_left _ hK.index_dvd_five
    obtain ⟨k, hk⟩ := R.isPGroup'.exists_card_eq
    have hk3 : k ≤ 3 := by
      by_contra h
      have h5 : Nat.card (R : Subgroup X) ∣ 32537600 * 5 :=
        (Subgroup.card_subgroup_dvd_card _).trans hX
      rw [hk] at h5
      have h4 : 5 ^ 4 ∣ 32537600 * 5 := (pow_dvd_pow 5 (by omega)).trans h5
      norm_num at h4
    have hRle : Nat.card (R : Subgroup X) ≤ 125 := by
      rw [hk]
      calc 5 ^ k ≤ 5 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
        _ = 125 := by norm_num
    have hBc' : 125 ≤ Nat.card B := by
      norm_num at hBc
      exact hBc
    have hBR' : B = R := Subgroup.eq_of_le_of_card_ge hBR (hRle.trans hBc')
    have hRT : (R : Subgroup X) ≤ (R : Subgroup X) ⊓ K := fun r hr =>
      hK.mem_of_forall_commute inf_le_right (hK.card_sylow_inf R) fun u hu =>
        hBab r (by rw [hBR']; exact hr) u (by rw [hBR']; exact hu.1)
    have h := Subgroup.card_le_of_le hRT
    rw [hK.card_sylow_inf R] at h
    have := Subgroup.card_le_of_le hBR
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
