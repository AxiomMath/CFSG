module

public import CFSG.LocalAnalysis.StandardType.GGCoverPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaModelMinus
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaConj
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaConjLabels
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmFieldDesc
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmRank
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsConj
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddEndMat
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular
import CFSG.LocalAnalysis.EvenBN.G2.Automorphisms
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalSymplecticField
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Reduced
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
import CFSG.Quasithin.Background.A3Structure312
import CFSG.Quasithin.Background.SmithB42G2FNat
import CFSG.Quasithin.Background.SmithB42G2FOff
import CFSG.Quasithin.H13.J4Order
import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen
import CFSG.Quasithin.Vol2.Ch11SecBFacts22
import CFSG.Quasithin.Vol2.Ch11SecBFacts22G
import CFSG.Quasithin.Vol2.Ch11StatementsF
import CFSG.Quasithin.Vol2.Ch11StatementsG
import CFSG.Quasithin.Vol2.Ch11StatementsH
import CFSG.Quasithin.Vol2.Ch11StatementsInputs
import Certificates.Certificate8026Base

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL

namespace CoverPOmMinusF

section

variable {K : Type} [Field K] [Finite K] [CharP K 2] {r n p : ℕ} {b c : K}

private noncomputable def frobPow (hn4 : 4 ≤ r) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (F : ℕ) : similarityPairs (Qm r hn4 b c) :=
  (frobPair r (by omega) b c (ne_zero_of_irreducible_tail b c hirr)) ^ (2 * F)

private theorem conjAct_frobPow (hn4 : 4 ≤ r) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (F : ℕ) :
    conjAct (Qm r hn4 b c) (frobPow hn4 hirr F) =
      AutOm.frobAut hn4 hirr ^ (2 * F) := by
  rw [AutOm.frobAut, ← map_pow]
  rfl

private theorem frobPow_isIsoPair (hn4 : 4 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (F : ℕ) :
    RecipeFieldOmega.IsIsoPair (Qm r hn4 b c)
      ((frobPow hn4 hirr F : similarityPairs (Qm r hn4 b c)) :
        coordinateSemilinearGroup (2 * r) K) := by
  rw [frobPow, SubmonoidClass.coe_pow]
  exact (RecipeFieldOmega.isIsoPair_frobPair (n := r) (by omega)
    (ne_zero_of_irreducible_tail b c hirr)).pow (2 * F)

private theorem orderOf_frobPow_right (hn4 : 4 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hf : Nat.card K = 2 ^ n) (hp : p.Prime)
    (hp2 : p ≠ 2) {v F : ℕ} (hnF : n = p ^ v * F) (hpF : ¬ p ∣ F) :
    orderOf ((frobPow hn4 hirr F : similarityPairs (Qm r hn4 b c)) :
      coordinateSemilinearGroup (2 * r) K).right = p ^ v := by
  have hn1 : 1 ≤ r := by omega
  have hF0 : F ≠ 0 := by
    rintro rfl
    exact hpF (dvd_zero p)
  have hcop : Nat.Coprime (p ^ v) 2 :=
    Nat.Coprime.pow_left v ((hp.coprime_iff_not_dvd).mpr fun hd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd))
  have hgcd : Nat.gcd (p ^ v * F) (2 * F) = F := by
    rw [Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul]
  rw [frobPow, RecipeFieldOmega.frobPair_pow_right hn1 (ne_zero_of_irreducible_tail b c hirr),
    orderOf_pow' _ (by positivity : 2 * F ≠ 0),
    CFSG.LocalAnalysis.EvenBN.G2.orderOf_frobeniusEquiv hf
      (CFSG.SeitzReduction.one_le_of_nontrivial_of_natCard_eq_two_pow hf), hnF, hgcd]
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hF0)

private theorem frobPow_pow_eq_one (hn4 : 4 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hf : Nat.card K = 2 ^ n) {v F : ℕ}
    (hnF : n = p ^ v * F) (hpF : ¬ p ∣ F) : frobPow hn4 hirr F ^ p ^ v = 1 := by
  obtain ⟨hnd, hT3⟩ := regular_coordinateQuadMinus r K b c hn4 hirr
  have hAP := coordinate_minus_point_action_properties r K b c hn4 hirr
  have hQne : ∃ v, Qm r hn4 b c v ≠ 0 :=
    exists_ne_zero_of_polar_nondegenerate (by omega : 0 < 2 * r) _ hnd
  refine RecipeFieldOmega.eq_one_of_conjAct_eq_one hnd hT3 hAP hQne ?_ ?_
  · rw [SubmonoidClass.coe_pow]
    exact (frobPow_isIsoPair hn4 hirr F).pow (p ^ v)
  · rw [map_pow, conjAct_frobPow, ← pow_mul]
    have h2n : 2 * F * p ^ v = 2 * n := by
      rw [hnF]
      ring
    rw [h2n, AutOm.frobAut_pow_two_mul (n := r) hn4 hirr hf]

private theorem frobPow_pow_coe_eq_one (hn4 : 4 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hf : Nat.card K = 2 ^ n) {v F : ℕ}
    (hnF : n = p ^ v * F) (hpF : ¬ p ∣ F) :
    ((frobPow hn4 hirr F : similarityPairs (Qm r hn4 b c)) :
      coordinateSemilinearGroup (2 * r) K) ^ p ^ v = 1 := by
  rw [← SubmonoidClass.coe_pow, frobPow_pow_eq_one hn4 hirr hf hnF hpF]
  rfl

private theorem conjAct_frobPow_apply_val (hn4 : 4 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (F : ℕ)
    (A : matrixDerived (Qm r hn4 b c)) :
    (conjAct (Qm r hn4 b c) (frobPow hn4 hirr F) A).val =
      matrixConjugation ((frobPow hn4 hirr F : similarityPairs (Qm r hn4 b c)) :
        coordinateSemilinearGroup (2 * r) K) A.val := by
  rw [conjAct_apply, matrixDerivedConjugation_val, matrixConjugation_apply]

private theorem exists_eq_conj_mul_pow_frobAut (hn4 : 4 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hf : Nat.card K = 2 ^ n) (hp : p.Prime)
    (hp2 : p ≠ 2) {v F : ℕ} (hnF : n = p ^ v * F) (hpF : ¬ p ∣ F)
    (a : MulAut (matrixDerived (Qm r hn4 b c))) (ha : ∃ k : ℕ, a ^ p ^ k = 1) :
    ∃ (ρ : matrixDerived (Qm r hn4 b c)) (t : ℕ),
      a = MulAut.conj ρ * (conjAct (Qm r hn4 b c) (frobPow hn4 hirr F)) ^ t := by
  have hF0 : F ≠ 0 := by
    rintro rfl
    exact hpF (dvd_zero p)
  have hn0' : n ≠ 0 := by
    rw [hnF]
    exact mul_ne_zero (pow_pos hp.pos v).ne' hF0
  have hn0 : 2 * n ≠ 0 := by
    intro h
    exact hn0' (by omega)
  obtain ⟨k, hk⟩ := ha
  obtain ⟨ι, hι, k', hk'⟩ := AutOm.exists_inner_mul_frobAut_pow hn4 hirr hf a
  obtain ⟨ρ, j, e, hdiv, haj⟩ :=
    CFSG.exists_eq_conj_mul_pow_of_eq_mul (G := matrixDerived (Qm r hn4 b c)) hp hn0 hι hk hk'
  have hcop : Nat.Coprime (2 * F) (p ^ e) := by
    have hpF' : Nat.Coprime p F := (hp.coprime_iff_not_dvd).mpr hpF
    have hp2' : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
    exact (hp2'.mul_right hpF').symm.pow_right e
  have h2n : 2 * n = p ^ v * (2 * F) := by
    rw [hnF]
    ring
  have h2Fdvd : 2 * F ∣ j := by
    refine hcop.dvd_of_dvd_mul_left ?_
    rw [h2n] at hdiv
    exact dvd_trans (dvd_mul_left (2 * F) (p ^ v)) hdiv
  obtain ⟨t, ht⟩ := h2Fdvd
  refine ⟨ρ, k' * t, ?_⟩
  have hkj : k' * j = 2 * F * (k' * t) := by
    rw [ht]
    ring
  rw [haj, ← pow_mul, hkj, pow_mul, ← conjAct_frobPow]

private theorem exists_fixed_maxCard (hn4 : 4 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hf : Nat.card K = 2 ^ n) (hp : p.Prime)
    (hp2 : p ≠ 2) {v F : ℕ} (hnF : n = p ^ v * F) (hpF : ¬ p ∣ F) :
    ∃ E₀ : Subgroup (GL (Fin (2 * r)) K), E₀ ≤ matrixDerived (Qm r hn4 b c) ∧
      (∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x) ∧ (∀ x ∈ E₀, x ^ p = 1) ∧
      (∀ F' : Subgroup (GL (Fin (2 * r)) K), F' ≤ matrixDerived (Qm r hn4 b c) →
        (∀ x ∈ F', ∀ y ∈ F', x * y = y * x) → (∀ x ∈ F', x ^ p = 1) →
        Nat.card F' ≤ Nat.card E₀) ∧
      (∀ e ∈ E₀, matrixConjugation ((frobPow hn4 hirr F : similarityPairs (Qm r hn4 b c)) :
        coordinateSemilinearGroup (2 * r) K) e = e) := by
  obtain ⟨hnd, hT3⟩ := regular_coordinateQuadMinus r K b c hn4 hirr
  obtain ⟨A, hA, -⟩ := OrdPNsOm.exists_genMax_le_orth hnd hT3 hp hp2 (F := ⊥)
    bot_le (by simp) (by simp)
  obtain ⟨E₀, hE₀le, hE₀c, hE₀p, hAcard, hE₀fix⟩ :=
    OrdPFieldNsOm.exists_fixed_elemAb_of_orderOf hn4 hnd hT3
      (frobPow_isIsoPair hn4 hirr F)
      (orderOf_frobPow_right hn4 hirr hf hp hp2 hnF hpF)
      (frobPow_pow_coe_eq_one hn4 hirr hf hnF hpF) hA
  refine ⟨E₀, hE₀le, hE₀c, hE₀p, ?_, hE₀fix⟩
  intro F' hF'le hF'c hF'p
  exact (OrdPNsOm.card_le_card_of_genMax_of_le hnd hT3 hA hF'le hF'p hF'c).trans hAcard

private theorem omegaMinusF_hT (hn4 : 4 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hp : p.Prime) (hpq : p ∣ Nat.card K + 1)
    (E₀ : Subgroup (GL (Fin (2 * r)) K)) (hE₀le : E₀ ≤ matrixDerived (Qm r hn4 b c))
    (hE₀c : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x) (hE₀p : ∀ x ∈ E₀, x ^ p = 1)
    (hEmax : ∀ F' : Subgroup (GL (Fin (2 * r)) K), F' ≤ matrixDerived (Qm r hn4 b c) →
      (∀ x ∈ F', ∀ y ∈ F', x * y = y * x) → (∀ x ∈ F', x ^ p = 1) →
      Nat.card F' ≤ Nat.card E₀) :
    ∀ E' : Subgroup (matrixDerived (Qm r hn4 b c)), IsElemAbelian p E' →
      p ^ 0 ≤ Nat.card E' →
      ∃ β : MulAut (matrixDerived (Qm r hn4 b c)), ∀ x ∈ E',
        β x ∈ {y : matrixDerived (Qm r hn4 b c) | (y.val : GL (Fin (2 * r)) K) ∈ E₀} := by
  intro E' hE' _
  obtain ⟨hnd, hT3⟩ := regular_coordinateQuadMinus r K b c hn4 hirr
  set F' : Subgroup (GL (Fin (2 * r)) K) := E'.map (matrixDerived (Qm r hn4 b c)).subtype
    with hF'def
  have hF'le : F' ≤ matrixDerived (Qm r hn4 b c) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hF'ea : IsElemAbelian p F' := hE'.map (matrixDerived (Qm r hn4 b c)).subtype
  obtain ⟨g, hg, hgF⟩ := OrthNs.exists_conj_le_of_maxCard hnd hT3 hp hpq hE₀le hE₀c hE₀p
    hEmax hF'le (fun a ha b hb => hF'ea.comm ha hb) hF'ea.2
  refine ⟨conjAct (Qm r hn4 b c) (matrixIsometryInclusion (Qm r hn4 b c) ⟨g, hg⟩),
    fun x hx => ?_⟩
  change ((conjAct (Qm r hn4 b c)
    (matrixIsometryInclusion (Qm r hn4 b c) ⟨g, hg⟩)) x).val ∈ E₀
  rw [conjAct_inclusion_val]
  exact hgF x.val (Subgroup.mem_map_of_mem _ hx)

private theorem omegaMinusF_hA (hn4 : 4 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hf : Nat.card K = 2 ^ n) (hp : p.Prime)
    (hp2 : p ≠ 2) {v F : ℕ} (hnF : n = p ^ v * F) (hpF : ¬ p ∣ F)
    (E₀ : Subgroup (GL (Fin (2 * r)) K))
    (hE₀fix : ∀ e ∈ E₀, matrixConjugation ((frobPow hn4 hirr F :
      similarityPairs (Qm r hn4 b c)) : coordinateSemilinearGroup (2 * r) K) e = e) :
    ∀ a : MulAut (matrixDerived (Qm r hn4 b c)), (∃ k : ℕ, a ^ p ^ k = 1) →
      ∃ (ρ₁ : matrixDerived (Qm r hn4 b c)) (φ : MulAut (matrixDerived (Qm r hn4 b c))),
        a = MulAut.conj ρ₁ * φ ∧
          ∀ x ∈ {y : matrixDerived (Qm r hn4 b c) | (y.val : GL (Fin (2 * r)) K) ∈ E₀},
            φ x = x := by
  intro a ha
  obtain ⟨ρ, t, haeq⟩ := exists_eq_conj_mul_pow_frobAut hn4 hirr hf hp hp2 hnF hpF a ha
  refine ⟨ρ, (conjAct (Qm r hn4 b c) (frobPow hn4 hirr F)) ^ t, haeq, ?_⟩
  have hfix1 : ∀ x : matrixDerived (Qm r hn4 b c),
      (x.val : GL (Fin (2 * r)) K) ∈ E₀ →
        (conjAct (Qm r hn4 b c) (frobPow hn4 hirr F)) x = x := by
    intro x hx
    apply Subtype.ext
    rw [conjAct_frobPow_apply_val]
    exact hE₀fix x.val hx
  have hpow : ∀ t : ℕ, ∀ x : matrixDerived (Qm r hn4 b c),
      (x.val : GL (Fin (2 * r)) K) ∈ E₀ →
        ((conjAct (Qm r hn4 b c) (frobPow hn4 hirr F)) ^ t) x = x := by
    intro t
    induction t with
    | zero => intro x _; rfl
    | succ t ih =>
      intro x hx
      rw [pow_succ, MulAut.mul_apply, hfix1 x hx, ih x hx]
  exact hpow t

private theorem omegaMinusF_hfix (hn4 : 4 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hf : Nat.card K = 2 ^ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) {v F : ℕ} (hnF : n = p ^ v * F)
    (hpF : ¬ p ∣ F) :
    ∀ E' : Subgroup (matrixDerived (Qm r hn4 b c)), IsElemAbelian p E' →
      p ^ 0 ≤ Nat.card E' →
      ∀ a : MulAut (matrixDerived (Qm r hn4 b c)), (∃ k : ℕ, a ^ p ^ k = 1) →
        ∃ ρ : matrixDerived (Qm r hn4 b c), ∀ x ∈ E', ((MulAut.conj ρ)⁻¹ * a) x = x := by
  obtain ⟨E₀, hE₀le, hE₀c, hE₀p, hEmax, hE₀fix⟩ :=
    exists_fixed_maxCard hn4 hirr hf hp hp2 hnF hpF
  exact fun E' hE' hcard a ha =>
    CoverPToral.forall_fix_of_toral
      {y : matrixDerived (Qm r hn4 b c) | (y.val : GL (Fin (2 * r)) K) ∈ E₀}
      (omegaMinusF_hT hn4 hirr hp hpq E₀ hE₀le hE₀c hE₀p hEmax)
      (omegaMinusF_hA hn4 hirr hf hp hp2 hnF hpF E₀ hE₀fix) hE' hcard ha

end

theorem ggCoverPTableB_omegaMinus_of_dvd_two_pow_add_one {K : Type} [Field K] [Finite K]
    {r n p : ℕ} (hK : Nat.card K = 2 ^ n) (hr : 4 ≤ r) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1) :
    GGCoverPTableB p (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))) := by
  have hn1 : 1 ≤ n := CFSG.SeitzReduction.one_le_of_nontrivial_of_natCard_eq_two_pow hK
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
    have h1 : 2 ∣ 1 := (Nat.dvd_add_iff_right h2n).mpr hpn
    omega
  have hpq : p ∣ Nat.card K + 1 := by
    rw [hK]
    exact hpn
  haveI : CharP K 2 := charP_two_of_card hK
  obtain ⟨v, F, hpF, hnF⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) p hp.ne_one
  let R := LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))
  change GGCoverPTableB p R (LargeEvenInnSet R)
  have hfixΓ := omegaMinusF_hfix hr hirr hK hp hp2 hpq hnF hpF
  have hfix : ∀ E' : Subgroup R, IsElemAbelian p E' → p ^ 0 ≤ Nat.card E' →
      ∀ a : MulAut R, (∃ k : ℕ, a ^ p ^ k = 1) →
        ∃ ρ : R, ∀ x ∈ E', ((MulAut.conj ρ)⁻¹ * a) x = x :=
    CoverPToral.forall_fix_of_mulEquiv (RecipeFieldOmega.minusEquiv hr b c) hfixΓ
  have hZΓ : Subgroup.center (matrixDerived (Qm r hr b c)) = ⊥ :=
    OrthRestOdd.center_matrixDerived_eq_bot (Q := Qm r hr b c)
      (regular_coordinateQuadMinus r K b c hr hirr).1 (by omega)
  have hZ : Subgroup.center R = ⊥ := by
    have h := Subgroup.map_center_eq (RecipeFieldOmega.minusEquiv hr b c)
    rw [hZΓ] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (RecipeFieldOmega.minusEquiv hr b c).injective).1 h
  have hI : ∀ φ ∈ LargeEvenInnSet R, φ ∈ (MulAut.conj : R →* MulAut R).range :=
    fun φ hφ => hφ
  have hcard : ∀ {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
      {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)},
      GGTableBPosition p L' E (LargeEvenInnSet R) θ hE →
        p ^ 0 ≤ Nat.card (ggLAutImage L' θ E) := by
    intro M _ _ L' E θ hE hP
    haveI : Finite (L' ⧸ Subgroup.center L') :=
      Finite.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    haveI : Finite R :=
      Finite.of_equiv (L' ⧸ Subgroup.center L') θ.symm.toEquiv.symm
    haveI : Nonempty (ggLAutImage L' θ E) := ⟨⟨1, one_mem _⟩⟩
    rw [pow_zero]
    have hpos : 0 < Nat.card (ggLAutImage L' θ E) := Nat.card_pos
    omega
  exact CoverPToral.ggCoverPTableB_of_forall_fix (r := 0) hZ hI hcard hfix

theorem largeEvenLabelAll_coverP_omegaMinus_of_dvd_two_pow_add_one {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (ht : lab.tag = .twD) (h4 : 4 ≤ lab.rank)
    (hpn : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I := by
  refine largeEvenLabelAll_omegaMinus ht h4 fun K _ _ _ hK b c hirr => ?_
  exact ggCoverPTableB_omegaMinus_of_dvd_two_pow_add_one (n := lab.n) hK h4 hirr hp hpn

end CoverPOmMinusF

end CFSG.StandardType

end
