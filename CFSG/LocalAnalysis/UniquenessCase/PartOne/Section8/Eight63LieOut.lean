module

public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel ChevalleyExceptionalModel TwistedChevalleyModel ReeTitsModel)
open CFSG.Blueprint.Chevalley (adjointGroup Tag TwistTag)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial (card_ringAut_and_isCyclic
  finite_field_prime_power_characteristic)

theorem card_outer_dvd_of_ker_eq_inner {C F : Type*} [Group C] [Group F]
    (Θ : MulAut C →* F) (hker : Θ.ker = inner C) :
    Nat.card (Outer C) ∣ Nat.card F :=
  Subgroup.card_dvd_of_injective (QuotientGroup.lift (inner C) Θ hker.ge)
    ((QuotientGroup.injective_lift_iff (inner C) Θ hker.ge).2 hker.symm)

theorem card_outer_adjointGroup_G2_dvd
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (h3 : 3 ≤ Nat.card K) :
    Nat.card (Outer (adjointGroup .G2 K)) ∣ 2 * f := by
  by_cases hp2 : p = 2
  ·
    subst hp2
    have hK2 : Nat.card K = 2 ^ f := hK
    have hf2 : 2 ≤ f := by
      by_contra h
      have h1 : f = 1 := by omega
      rw [h1] at hK2
      norm_num at hK2
      omega
    obtain ⟨Θ, -, -, hΘker, -⟩ :=
      (even_G2_exact_automorphism_normal_form hf2 K hK2).2
    have hdvd : Nat.card (Outer (adjointGroup .G2 K)) ∣ Nat.card (K ≃+* K) :=
      card_outer_dvd_of_ker_eq_inner Θ hΘker
    rw [(card_ringAut_and_isCyclic Nat.prime_two K hK2).1] at hdvd
    exact hdvd.trans (dvd_mul_left f 2)
  · by_cases hp3 : p = 3
    ·
      subst hp3
      have hK3 : Nat.card K = 3 ^ f := hK
      haveI : CharP K CFSG.LieType.Ree.ReeTag.G2.prime :=
        finite_field_prime_power_characteristic Nat.prime_three hf hK3
      let Θ : MulAut (adjointGroup CFSG.LieType.Ree.ReeTag.G2.tag K) →*
          Multiplicative (ZMod (2 * f)) :=
        (G2_three_exact_automorphism_normal_form hf K hK3).2.2.1.choose
      have hΘker : Θ.ker = inner (adjointGroup CFSG.LieType.Ree.ReeTag.G2.tag K) :=
        (G2_three_exact_automorphism_normal_form hf K hK3).2.2.1.choose_spec.2.2
      have hdvd : Nat.card (Outer (adjointGroup .G2 K)) ∣
          Nat.card (Multiplicative (ZMod (2 * f))) :=
        card_outer_dvd_of_ker_eq_inner Θ hΘker
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at hdvd
      exact hdvd
    ·
      obtain ⟨Θ, -, -, hΘker, -⟩ :=
        (odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf K hK .G2
          (Or.inr ⟨rfl, hp3⟩)).2
      have hdvd : Nat.card (Outer (adjointGroup .G2 K)) ∣ Nat.card (K ≃+* K) :=
        card_outer_dvd_of_ker_eq_inner Θ hΘker
      rw [(card_ringAut_and_isCyclic hp K hK).1] at hdvd
      exact hdvd.trans (dvd_mul_left f 2)

theorem card_outer_twistedChevalleyModel_D4_dvd
    {X : Type} [Group X] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (h : TwistedChevalleyModel X .D4 (p ^ f)) :
    Nat.card (Outer X) ∣ 3 * f := by
  obtain ⟨K, _, _, hKcard, σ, hσ, ⟨eX⟩⟩ := h
  have hKcard3 : Nat.card K = (p ^ f) ^ 3 := hKcard
  let σ' : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσ' : σ'.toRingHom = σ := RingHom.ext fun _ => rfl
  have hσpow : ∀ c, σ' c = c ^ (p ^ f) := fun c => by
    change σ c = c ^ (p ^ f)
    exact hσ c
  by_cases hp2 : p = 2
  ·
    subst hp2
    obtain ⟨-, -, ⟨Θ, -, -, hΘker, -⟩, -, hcard, -, -, ⟨e₀⟩⟩ :=
      even_triality_exact_automorphism_normal_form hf K hKcard3 σ' hσpow
    have hdvd : Nat.card (Outer (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom)) ∣ 3 * f := by
      have h := card_outer_dvd_of_ker_eq_inner Θ hΘker
      rw [hcard] at h
      exact h
    rw [hσ'] at hdvd e₀
    rw [Nat.card_congr (equivalence (eX.trans e₀)).toEquiv]
    exact hdvd
  ·
    obtain ⟨-, -, ⟨Θ, -, -, hΘker, -⟩, -, hcard, -, -, ⟨e₀⟩⟩ :=
      odd_triality_exact_automorphism_normal_form hp hp2 hf K hKcard3 σ' hσpow
    have hdvd : Nat.card (Outer (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom)) ∣ 3 * f := by
      have h := card_outer_dvd_of_ker_eq_inner Θ hΘker
      rw [hcard] at h
      exact h
    rw [hσ'] at hdvd e₀
    rw [Nat.card_congr (equivalence (eX.trans e₀)).toEquiv]
    exact hdvd

theorem card_outer_reeTitsModel_twistedF4_dvd
    {X : Type} [Group X] {p f : ℕ} (h : ReeTitsModel X .twistedF4 p f) :
    Nat.card (Outer X) ∣ f := by
  rw [(large_Ree_model_field_outer_group_and_inner_involutions X p f h).2.2.2.2.1]

theorem not_dvd_card_outer_lieModel_G2
    {X : Type} [Group X] [Finite X] {p f r : ℕ} (h : CFSG.Blueprint.LieModel X .G2 0 p f)
    (hp : p.Prime) (hr : r.Prime) (hr3 : 3 < r) (hrd : r ∣ p ^ f - 1)
    (hrf : ¬ r ∣ f) :
    ¬ r ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := by
  have hc : ChevalleyExceptionalModel X .G2 p f :=
    LieModel.chevalleyExceptionalModel h (by decide)
  obtain ⟨K, _, _, hKcard, ⟨eX⟩⟩ :=
    nonempty_mulEquiv_adjointGroup .G2 hc.2
  have hf : 1 ≤ f := hc.1.2.1
  have h3 : 3 ≤ Nat.card K := by
    rw [hKcard]
    exact hc.1.2.2.2
  have hdvd : Nat.card (Outer (adjointGroup .G2 K)) ∣ 2 * f :=
    card_outer_adjointGroup_G2_dvd hp hf hKcard h3
  have hr2 : ¬ r ∣ 2 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have hnot : ¬ r ∣ 2 * f := hr.not_dvd_mul hr2 hrf
  have hcard : Nat.card (Outer X) = Nat.card (Outer (adjointGroup .G2 K)) :=
    Nat.card_congr (equivalence eX).toEquiv
  rw [hcard]
  exact fun hd => hnot (hd.trans hdvd)

theorem not_dvd_card_outer_lieModel_trialityD4
    {X : Type} [Group X] [Finite X] {p f r : ℕ} (h : CFSG.Blueprint.LieModel X .trialityD4 0 p f)
    (hp : p.Prime) (hr : r.Prime) (hr3 : 3 < r) (hrd : r ∣ p ^ f - 1)
    (hrf : ¬ r ∣ f) :
    ¬ r ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := by
  have hc : ChevalleyExceptionalModel X .trialityD4 p f :=
    LieModel.chevalleyExceptionalModel h (by decide)
  have hf : 1 ≤ f := hc.1.2.1
  have hdvd : Nat.card (Outer X) ∣ 3 * f :=
    card_outer_twistedChevalleyModel_D4_dvd hp hf hc.2
  have hr3' : ¬ r ∣ 3 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  exact fun hd => hr.not_dvd_mul hr3' hrf (hd.trans hdvd)

theorem not_dvd_card_outer_lieModel_twistedF4
    {X : Type} [Group X] [Finite X] {p f r : ℕ} (h : CFSG.Blueprint.LieModel X .twistedF4 0 p f)
    (hp : p.Prime) (hr : r.Prime) (hr3 : 3 < r) (hrd : r ∣ p ^ f - 1)
    (hrf : ¬ r ∣ f) :
    ¬ r ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := by
  have hRT : ReeTitsModel X .twistedF4 p f :=
    (LieModel.reeTitsModel h (by decide)).2
  have hdvd : Nat.card (Outer X) ∣ f := card_outer_reeTitsModel_twistedF4_dvd hRT
  exact fun hd => hrf (hd.trans hdvd)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
