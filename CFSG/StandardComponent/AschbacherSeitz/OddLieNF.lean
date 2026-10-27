module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieFinal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypNF
import CFSG.LinearAlgebra.LinearGroups.SmallFieldModels
import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Blueprint

open scoped MatrixGroups

theorem rankTwoOddLieStandardNF_of (hI : OddLieInputs) (hHRD : ModelHighestRootData)
    (h3 : Section3Config) (h32 : Lemma32) : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
      CFSG.Open.standardComponentOddCore G = ⊥ →
        ¬ RankTwoStandard.RankTwoOddLieType (rankTwoQuot A) := by
  intro G _ _ A hRT hO hT
  obtain ⟨hL, hA5, hA6, -⟩ := hT
  have hstd := hRT.standard
  have hAq : Open.IsQuasisimple A := hstd.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set G) with hK
  have h31 : Hyp31 A := ⟨hstd, hypII_of_oddLieType hI hHRD A hAq hL, hO,
    by have := hRT.rank; omega, hRT.not_normal⟩
  obtain ⟨g, hg, R, T, hR, hTs, hTN, hRN, -, hTt, hRt⟩ := h3 G A h31
  have hRe : IsElemAbelian 2 R := h32 G A h31 R hR
  have hKg : Odd (Nat.card (K ⊓ rightConjugate K g : Subgroup G)) :=
    (CFSG.ComponentClassification.AS76b.tightlyEmbedded_centralizer hstd).2 g fun h => hg (hstd.2.2.2.1 ▸ h)
  have hR4 : 4 ≤ Nat.card R := by
    obtain ⟨E, hEK, -, hEc⟩ := CFSG.SectionRank.exists_pRank (p := 2) one_lt_two K
    have h1 : Nat.card E ∣ Nat.card K := card_dvd_of_le hEK
    rw [hEc] at h1
    have hdvd : 2 ^ 2 ∣ Nat.card K := (Nat.pow_dvd_pow 2 hRT.rank).trans h1
    have hle : 2 ≤ (Nat.card K).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
    rw [hR.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (Nat.card K).factorization 2 := Nat.pow_le_pow_right (by norm_num) hle
  have hT4 : 4 ≤ Nat.card T := by
    rw [hTs.card_eq, rightConjugate_card, ← hR.card_eq]
    exact hR4
  have hTe : IsElemAbelian 2 T := by
    have h1 : IsSylowOf 2 (rightConjugate T g⁻¹) K := by
      have := isSylowOf_rightConjugate hTs g⁻¹
      rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at this
    have h2 := isElemAbelian_rightConjugate' (h32 G A h31 _ h1) g
    rwa [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at h2
  have hTC : T ⊓ centralizer (A : Set G) = ⊥ :=
    two_subgroup_of_odd_eq_bot _ _ hTs.isPGroup.to_inf_left hKg
      (fun x hx => mem_inf.mpr ⟨(mem_inf.mp hx).2, hTs.le (mem_inf.mp hx).1⟩)
  have hRC : R ⊓ centralizer (rightConjugate A g : Set G) = ⊥ := by
    rw [centralizer_rightConjugate]
    exact two_subgroup_of_odd_eq_bot _ _ hR.isPGroup.to_inf_left hKg
      (fun x hx => mem_inf.mpr ⟨hR.le (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩)
  obtain ⟨X, hX⟩ := Hyp46.exists_of ⟨hTe, hT4, hTN, hTC⟩ hTt
  obtain ⟨hZodd, p, f, hpF, -, hf, hq, ⟨eA⟩, -, hTle⟩ := hX.as76b_4_9_general hI hHRD hAq hL
  have hcardF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have h7 : p ^ f = 7 := by
    rcases (by simpa using hq : p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9) with h5 | h7 | h9
    · obtain ⟨e5⟩ := (CFSG.LinearGroups.five_field_linear_two_alternating_five_model
        (GaloisField p f) (by rw [hcardF, h5])).1
      exact (hA5 ⟨eA.trans e5⟩).elim
    · exact h7
    · have : Fintype (GaloisField p f) := Fintype.ofFinite _
      open CFSG.LocalAnalysis.ComponentInitial in
      obtain ⟨e6⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism
        (GaloisField p f) (by rw [← Nat.card_eq_fintype_card, hcardF, h9])
      exact (hA6 ⟨eA.trans e6⟩).elim
  have hTA : T ≤ A := hTle (by omega)
  obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp h7
  let eA7 : ↥A ⧸ center ↥A ≃* PSL(2, ZMod 7) :=
    eA.trans (CFSG.GorensteinWalter.psl2RingEquiv (GaloisField.equivZmodP 7).toRingEquiv)
  let π : ↥A →* PSL(2, ZMod 7) := eA7.toMonoidHom.comp (QuotientGroup.mk' (center A))
  have hπs : Function.Surjective π := eA7.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : π.ker = center A := by
    ext x
    rw [MonoidHom.mem_ker]
    change eA7 (QuotientGroup.mk' (center A) x) = 1 ↔ _
    rw [map_eq_one_iff _ eA7.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hinj : ∀ m : A, (m : G) ∈ T → π m = 1 → m = 1 := fun m hmT hm1 =>
    eq_one_of_sq_of_odd hZodd (hπk ▸ hm1 : m ∈ center A)
      (Subtype.ext (by simpa using hTe.2 _ hmT))
  obtain ⟨-, abar, habar2, habarN, habarC⟩ := psl27_elemAbelian (isElemAbelian_imgIn π hTe)
    (by rw [card_imgIn π hTA hinj]; exact hT4)
  obtain ⟨a, haA, ha2, haN, haC⟩ :=
    exists_involution_lift π hπs hπk hZodd hTA hTe habar2 habarN habarC
  have heven : Even (Nat.card T) := by
    rcases hTs.isPGroup.card_eq_or_dvd with h1 | h2
    · omega
    · exact even_iff_two_dvd.mpr h2
  have haNg := mem_normalizer_rightConjugate_of_tight hstd hTs.le heven haN
  set Ag := rightConjugate A g with hAg
  let eAg : ↥A ≃* ↥Ag :=
    A.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  have hAgq : Open.IsQuasisimple Ag := isQuasisimple_of_mulEquiv eAg hAq
  let eQ : ↥A ⧸ center ↥A ≃* ↥Ag ⧸ center ↥Ag :=
    QuotientGroup.congr (center A) (center Ag) eAg (map_center_mulEquiv eAg)
  have hLg : CFSG.Blueprint.OddLieType (↥Ag ⧸ center ↥Ag) := oddLieType_of_equiv eQ hL
  obtain ⟨X', hX'⟩ := Hyp46.exists_of ⟨hRe, hR4, hRN, hRC⟩ hRt
  obtain ⟨hZgodd, p', f', hp'F, -, hf', -, ⟨eAg'⟩, -, hRle⟩ :=
    hX'.as76b_4_9_general hI hHRD hAgq hLg
  have hne5 : p' ^ f' ≠ 5 := by
    intro h5
    have hc1 : Nat.card (↥Ag ⧸ center ↥Ag) = 168 := by
      rw [← Nat.card_congr eQ.toEquiv, Nat.card_congr eA7.toEquiv, card_psl27]
    have hF : Nat.card (GaloisField p' f') = 5 := by rw [GaloisField.card p' f' (by omega), h5]
    have hc2 : Nat.card PSL(2, GaloisField p' f') = 60 := by
      rw [CFSG.GorensteinWalter.psl2_card_formula _ (isOddPrimePower_of_odd (by rw [hF]; decide)),
        hF]
      norm_num
    have := Nat.card_congr eAg'.toEquiv
    omega
  have hRAg : R ≤ Ag := hRle hne5
  have haR : ∀ r ∈ R, a * r = r * a := fun r hr => mem_centralizer_iff.mp (hR.le hr) a haA
  have hainner :=
    mem_sup_centralizer_of_psl27 hAgq.1 (eQ.symm.trans eA7) hZgodd hRAg hRe hR4 haNg haR
  have hTsg : IsSylowOf 2 T (centralizer (Ag : Set G)) := by
    rw [hAg, centralizer_rightConjugate]
    exact hTs
  have hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hTe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  exact haC (mem_centralizer_of_mem_sup_of_isSylowOf hTsg hTab hainner haN ha2)


theorem rankTwoOddLieStandardNF_of_foundation (hT2 : Asc76Theorem2) (h4 : Asc75Theorem4) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
      CFSG.Open.standardComponentOddCore G = ⊥ →
        ¬ RankTwoStandard.RankTwoOddLieType (rankTwoQuot A) :=
  rankTwoOddLieStandardNF_of oddLieInputs modelHighestRootData
    (section3Config_of_asc76Theorem2 hT2 h4 asc08Lemma34) (lemma32_of_asc76Theorem2 hT2)

end CFSG.ComponentClassification.RankTwoOddLie
