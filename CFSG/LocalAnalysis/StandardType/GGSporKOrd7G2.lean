module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Defs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.GraphFixedF4Canonical
public import CFSG.LieType.Chevalley.PerfectSimpleRoot

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open

private lemma lr2og2_factorization_seven_eq_of_conj
    {S Q : Type} [Group S] [Finite S] [Group Q]
    (hZ : Subgroup.center S = ⊥)
    (Θ : MulAut S →* Q)
    (hker : Θ.ker = (MulAut.conj : S →* MulAut S).range)
    (hQ : ¬ 7 ∣ Nat.card Q) :
    (Nat.card (MulAut S)).factorization 7 = (Nat.card S).factorization 7 := by
  have hconj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    CFSG.LieType.Chevalley.mulAut_conj_injective_of_center_eq_bot hZ
  have hkerCard : Nat.card Θ.ker = Nat.card S := by
    rw [hker]
    exact (Nat.card_congr (MonoidHom.ofInjective hconj).toEquiv).symm
  have hcard : Nat.card (MulAut S) = Nat.card Θ.range * Nat.card Θ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Θ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange Θ).toEquiv]
  have hdvd : Nat.card Θ.range ∣ Nat.card Q := Θ.range.card_subgroup_dvd_card
  have h7range : ¬ 7 ∣ Nat.card Θ.range := fun h => hQ (h.trans hdvd)
  have hS0 : Nat.card S ≠ 0 := Nat.card_ne_zero.2 ⟨⟨1⟩, inferInstance⟩
  have hker0 : Nat.card Θ.ker ≠ 0 := by rw [hkerCard]; exact hS0
  have hrange0 : Nat.card Θ.range ≠ 0 := fun h => by
    have h0 : Nat.card Q = 0 := by
      have h' := hdvd
      rw [h] at h'
      exact zero_dvd_iff.1 h'
    exact hQ (by rw [h0]; exact dvd_zero 7)
  calc (Nat.card (MulAut S)).factorization 7
      = (Nat.card Θ.range * Nat.card Θ.ker).factorization 7 := by rw [hcard]
    _ = (Nat.card Θ.range).factorization 7 + (Nat.card Θ.ker).factorization 7 := by
          rw [Nat.factorization_mul hrange0 hker0]; simp
    _ = (Nat.card S).factorization 7 := by
          rw [Nat.factorization_eq_zero_of_not_dvd h7range, hkerCard, zero_add]

private lemma lr2opg2_card_mulAut_dvd_of_conj
    {S Q : Type} [Group S] [Group Q]
    (hZ : Subgroup.center S = ⊥)
    (Θ : MulAut S →* Q)
    (hker : Θ.ker = (MulAut.conj : S →* MulAut S).range) :
    Nat.card (MulAut S) ∣ Nat.card Q * Nat.card S := by
  have hconj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    CFSG.LieType.Chevalley.mulAut_conj_injective_of_center_eq_bot hZ
  have hkerCard : Nat.card Θ.ker = Nat.card S := by
    rw [hker]
    exact (Nat.card_congr (MonoidHom.ofInjective hconj).toEquiv).symm
  have hcard : Nat.card (MulAut S) = Nat.card Θ.range * Nat.card Θ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Θ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange Θ).toEquiv]
  have hdvd : Nat.card Θ.range ∣ Nat.card Q := Θ.range.card_subgroup_dvd_card
  rw [hcard, hkerCard]
  exact mul_dvd_mul_right hdvd (Nat.card S)

open CFSG.Blueprint.Chevalley in
theorem ord7_card_mulAut_dvd_G2
    {f : ℕ} {R : Type} [Group R] (hm : LieModel R .G2 0 2 f) :
    Nat.card (MulAut R) ∣ f * Nat.card R := by
  rcases hm with ⟨hcls, -⟩ | ⟨-, -, hce⟩ | ⟨-, hrt, -⟩ | ⟨-, htb, -⟩
  · exact absurd hcls (by decide)
  · obtain ⟨hAdm, hU⟩ := hce
    obtain ⟨K, hKfield, hKfin, hKcard, ⟨eQ⟩⟩ := hU
    letI : Field K := hKfield
    letI : Finite K := hKfin
    have h3 : 3 ≤ 2 ^ f := hAdm.2.2.2
    have hf : 2 ≤ f := by
      rcases f with _ | _ | f
      · norm_num at h3
      · norm_num at h3
      · omega
    have hcent : Subgroup.center (adjointGroup .G2 K) = ⊥ :=
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    let adjQ : AdjointQuotient .G2 K ≃* adjointGroup .G2 K :=
      (QuotientGroup.quotientMulEquivOfEq hcent).trans QuotientGroup.quotientBot
    have eR : R ≃* adjointGroup .G2 K := eQ.trans adjQ
    haveI : Finite (adjointGroup .G2 K) :=
      CFSG.LieType.Chevalley.generated_group_finite .G2 K
    obtain ⟨-, Θ, -, hsurj, hker, -⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
        hf K hKcard
    have hcore := lr2opg2_card_mulAut_dvd_of_conj hcent Θ hker
    have h1 : Nat.card (MulAut R) = Nat.card (MulAut (adjointGroup .G2 K)) :=
      Nat.card_congr (MulAut.congr eR).toEquiv
    have h2 : Nat.card R = Nat.card (adjointGroup .G2 K) := Nat.card_congr eR.toEquiv
    rw [h1, h2, ← (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
      Nat.prime_two K hKcard).1]
    exact hcore
  · exact absurd hrt (by decide)
  · exact absurd htb (by decide)

open CFSG.Blueprint.Chevalley in
theorem ord7Param_G2
    {f : ℕ} (h7 : ¬ 7 ∣ f) : Ord7Param .G2 0 2 f := by
  intro R _ _ hR hmodel
  rcases hmodel with ⟨hcls, -⟩ | ⟨-, -, hce⟩ | ⟨-, hrt, -⟩ | ⟨-, htb, -⟩
  · exact absurd hcls (by decide)
  · obtain ⟨hAdm, hU⟩ := hce
    obtain ⟨K, hKfield, hKfin, hKcard, ⟨eQ⟩⟩ := hU
    letI : Field K := hKfield
    letI : Finite K := hKfin
    have h3 : 3 ≤ 2 ^ f := hAdm.2.2.2
    have hf : 2 ≤ f := by
      rcases f with _ | _ | f
      · norm_num at h3
      · norm_num at h3
      · omega
    have hcent : Subgroup.center (adjointGroup .G2 K) = ⊥ :=
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    let adjQ : AdjointQuotient .G2 K ≃* adjointGroup .G2 K :=
      (QuotientGroup.quotientMulEquivOfEq hcent).trans QuotientGroup.quotientBot
    have eR : R ≃* adjointGroup .G2 K := eQ.trans adjQ
    haveI : Finite (adjointGroup .G2 K) :=
      CFSG.LieType.Chevalley.generated_group_finite .G2 K
    obtain ⟨-, Θ, -, hsurj, hker, -⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
        hf K hKcard
    have hQ7 : ¬ 7 ∣ Nat.card (K ≃+* K) := by
      rw [(CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
        Nat.prime_two K hKcard).1]
      exact h7
    have hcore := lr2og2_factorization_seven_eq_of_conj hcent Θ hker hQ7
    have h1 : Nat.card (MulAut R) = Nat.card (MulAut (adjointGroup .G2 K)) :=
      Nat.card_congr (MulAut.congr eR).toEquiv
    have h2 : Nat.card R = Nat.card (adjointGroup .G2 K) := Nat.card_congr eR.toEquiv
    rw [h1, h2]
    exact le_of_eq hcore
  · exact absurd hrt (by decide)
  · exact absurd htb (by decide)

end CFSG.StandardType.SporadicShape
