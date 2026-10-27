module

public import CFSG.RankThree.PartOne.CTP.SeitzExc
public import CFSG.Adapters.TauCetiExceptional.EvenB1
public import CFSG.LieType.Chevalley.ExactG2FiniteOrder
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LieType.Ree.LargeReeModelSchreier

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree TauCeti
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem card_outer_eq_of_hom {X C : Type*} [Group X] [Group C] (Θ : MulAut X →* C)
    (hsurj : Function.Surjective Θ) (hker : Θ.ker = inner X) :
    Nat.card (Outer X) = Nat.card C :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)).toEquiv

theorem not_sq_dvd_G2_small {r p : ℕ} (hr : r = 3 ∨ r = 5 ∨ r = 7) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpr : p ≠ r) : ¬ p ^ 2 ∣ r ^ 6 * (r ^ 6 - 1) * (r ^ 2 - 1) := by
  intro h
  have hpd : p ∣ r ^ 6 * (r ^ 6 - 1) * (r ^ 2 - 1) := (dvd_pow_self p two_ne_zero).trans h
  have key : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hd =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 hd
  rcases hr with rfl | rfl | rfl
  · have hN : (3 ^ 6 * (3 ^ 6 - 1) * (3 ^ 2 - 1) : ℕ) = 2 ^ 6 * 3 ^ 6 * 7 * 13 := by norm_num
    rw [hN] at hpd h
    simp only [Nat.Prime.dvd_mul hp] at hpd
    rcases hpd with ((h1 | h1) | h1) | h1
    · have := key 2 Nat.prime_two (hp.dvd_of_dvd_pow h1); omega
    · exact hpr (key 3 Nat.prime_three (hp.dvd_of_dvd_pow h1))
    · have := key 7 (by norm_num) h1; subst this; norm_num at h
    · have := key 13 (by norm_num) h1; subst this; norm_num at h
  · have hN : (5 ^ 6 * (5 ^ 6 - 1) * (5 ^ 2 - 1) : ℕ) = 2 ^ 6 * 3 ^ 3 * 5 ^ 6 * 7 * 31 := by
      norm_num
    rw [hN] at hpd h
    simp only [Nat.Prime.dvd_mul hp] at hpd
    rcases hpd with (((h1 | h1) | h1) | h1) | h1
    · have := key 2 Nat.prime_two (hp.dvd_of_dvd_pow h1); omega
    · have := key 3 Nat.prime_three (hp.dvd_of_dvd_pow h1); omega
    · exact hpr (key 5 Nat.prime_five (hp.dvd_of_dvd_pow h1))
    · have := key 7 (by norm_num) h1; subst this; norm_num at h
    · have := key 31 (by norm_num) h1; subst this; norm_num at h
  · have hN : (7 ^ 6 * (7 ^ 6 - 1) * (7 ^ 2 - 1) : ℕ) = 2 ^ 8 * 3 ^ 3 * 7 ^ 6 * 19 * 43 := by
      norm_num
    rw [hN] at hpd h
    simp only [Nat.Prime.dvd_mul hp] at hpd
    rcases hpd with (((h1 | h1) | h1) | h1) | h1
    · have := key 2 Nat.prime_two (hp.dvd_of_dvd_pow h1); omega
    · have := key 3 Nat.prime_three (hp.dvd_of_dvd_pow h1); omega
    · exact hpr (key 7 (by norm_num) (hp.dvd_of_dvd_pow h1))
    · have := key 19 (by norm_num) h1; subst this; norm_num at h
    · have := key 43 (by norm_num) h1; subst this; norm_num at h

section Models


theorem extSeitzAtOuter_G2_even_of_lt_five {q : TauCeti.PrimePower} (hq : q.p = 2)
    (he : q.exponent < 5) : ExtSeitzAtOuter (.G2 q) := by
  intro K _ _ _ hnab hiso p hp hp5 hpd E hE hcard hout
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have hdvd := dvd_card_outer_of_not_inner (p := p) E hout
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  have h3 : 3 ≤ q.p ^ q.exponent := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa only [LieTypeIndex.inStandardRange_iff, PrimePower.card_def] using h
  have hf2 : 2 ≤ q.exponent := by
    by_contra hlt
    have : q.exponent = 1 := by have := q.exponent_pos; omega
    rw [hq, this] at h3
    norm_num at h3
  have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.chevalleyBridgesEven.g2 q hv hq e0
  obtain ⟨X, _, _, hX, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hmodel
  rw [hq] at hX
  obtain ⟨-, Θ, -, hsurj, hker, -⟩ := even_G2_exact_automorphism_normal_form hf2 X hX
  have hcardX := card_ringAut_and_isCyclic Nat.prime_two X hX
  have h1 : Nat.card (Outer K) = Nat.card (Outer (adjointGroup .G2 X)) :=
    Nat.card_congr (equivalence e).toEquiv
  rw [h1, card_outer_eq_of_hom Θ hsurj hker] at hdvd
  have : Nat.card (X ≃+* X) = q.exponent := hcardX.1
  rw [this] at hdvd
  have := Nat.le_of_dvd (by omega) hdvd
  omega

theorem extSeitzAtOuter_trialityD4_of_lt_five {q : TauCeti.PrimePower} (hq : q.p = 2)
    (he : q.exponent < 5) : ExtSeitzAtOuter (.trialityD4 q) := by
  intro K _ _ _ hnab hiso p hp hp5 hpd E hE hcard hout
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have hdvd := dvd_card_outer_of_not_inner (p := p) E hout
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  have hm' : TwistedChevalleyModel K .D4 (q.p ^ q.exponent) :=
    CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
      CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hq (by decide) e0
  obtain ⟨X, _, _, hcardX, σ, hσ, ⟨e⟩⟩ := hm'
  have hf1 : 1 ≤ q.exponent := q.exponent_pos
  rw [hq] at hcardX hσ
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields .D4 Nat.prime_two hf1 X hcardX
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  subst hσσ'
  obtain ⟨-, -, ⟨Θ, -, hsurj, hker, -⟩, hcyc, hord, -, -, ⟨E'⟩⟩ :=
    even_triality_exact_automorphism_normal_form hf1 X hcardX σ' hσ'
  have h1 : Nat.card (Outer K) =
      Nat.card (Outer (graphFixedRootGroup TwistTag.D4 X σ'.toRingHom)) :=
    Nat.card_congr (equivalence (e.trans E')).toEquiv
  rw [h1, card_outer_eq_of_hom Θ hsurj hker, hord] at hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · have := Nat.le_of_dvd (by norm_num) h
    omega
  · have := Nat.le_of_dvd q.exponent_pos h
    omega

theorem extSeitzAtOuter_F4_two {q : TauCeti.PrimePower} (hq : q.p = 2) (he : q.exponent = 1) :
    ExtSeitzAtOuter (.F4 q) := by
  intro K _ _ _ hnab hiso p hp hp5 hpd E hE hcard hout
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have hdvd := dvd_card_outer_of_not_inner (p := p) E hout
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.chevalleyBridgesEven.f4 q hv hq e0
  obtain ⟨X, _, _, hX, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hmodel
  rw [hq, he] at hX
  have hX' : Nat.card X = 2 ^ 1 := by simpa using hX
  have : CharP X 2 := finite_field_prime_power_characteristic Nat.prime_two (le_refl 1) hX'
  obtain ⟨-, -, ⟨Θ, -, hsurj, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form (le_refl 1) X hX'
  have h1 : Nat.card (Outer K) = Nat.card (Outer (adjointGroup ReeTag.F4.tag X)) :=
    Nat.card_congr (equivalence e).toEquiv
  rw [h1, card_outer_eq_of_hom Θ hsurj hker] at hdvd
  have hc : Nat.card (Multiplicative (ZMod (2 * 1))) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd]
    simp
  rw [hc] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem extSeitzAtOuter_reeF4_of_lt_five {m : ℕ} (hm : 2 * m + 1 < 5) :
    ExtSeitzAtOuter (.reeF4 m) := by
  intro K _ _ _ hnab hiso p hp hp5 hpd E hE hcard hout
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have hdvd := dvd_card_outer_of_not_inner (p := p) E hout
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  let e : K ≃* ValidLieTypeIndex.Group ⟨.reeF4 m, hv⟩ := e0
  have hfin : ∀ d : ReeF4LieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : ReeF4LieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin (ReeF4LieIndex.of m hv)
  have := hchar (ReeF4LieIndex.of m hv)
  have hm1 : 1 ≤ m :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hhalf : (ReeF4LieIndex.of m hv).toSuzukiReeIndex.halfExponent = m :=
    SuzukiReeIndex.halfExponent_reeF4 m hv
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at e₁
  have hK := CFSG.TauCetiBridge.ReeF4.card_fixedField_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at hK
  have hmodel : ReeTitsModel K .twistedF4 2 (2 * m + 1) :=
    ⟨⟨Nat.prime_two, by omega, ⟨rfl, rfl, ⟨m, rfl⟩, by omega⟩⟩, m, rfl,
      ⟨(ReeF4LieIndex.of m hv).1.fixedField, inferInstance, inferInstance, hK,
        ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv m).symm⟩⟩⟩
  obtain ⟨hadm, a, hfa, hmodel'⟩ := hmodel
  have ha : 1 ≤ a := by omega
  have hX := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier K 2 (2 * m + 1)
    ⟨hadm, a, hfa, hmodel'⟩
  obtain ⟨X, _, _, hK2, ⟨e2⟩⟩ := hmodel'
  have : Fintype X := Fintype.ofFinite X
  have : CharP X ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := 2 * m + 1) (by
    rw [← Nat.card_eq_fintype_card, hK2]
    rfl)
  obtain ⟨E2⟩ := hX.2.2.2.2.2 a X hfa hK2 ⟨e2⟩
  have hK' : Nat.card X = 2 ^ (2 * a + 1) := by rw [hK2, hfa]
  obtain ⟨-, -, -, -, hord, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha X hK'
  have h1 : Nat.card (Outer K) = Nat.card (Outer (ReeTag.F4.reeGamma X a)) :=
    Nat.card_congr (equivalence E2).toEquiv
  rw [h1, hord] at hdvd
  have := Nat.le_of_dvd (by omega) hdvd
  omega

theorem extSeitzAtOuter_G2_odd {q : TauCeti.PrimePower} (hq : q.p ≠ 2) (he : q.exponent = 1) :
    ExtSeitzAtOuter (.G2 q) := by
  intro K _ _ _ hnab hiso p hp hp5 hpd E hE hcard hout
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have hdvd := dvd_card_outer_of_not_inner (p := p) E hout
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  have hmodel := CFSG.TauCetiBridge.untwistedModel_of_bridge
    CFSG.TauCetiBridge.chevalleyBridges.g2 q hv hq e0
  obtain ⟨X, _, _, hX, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hmodel
  rw [he] at hX
  have hX' : Nat.card X = q.p ^ 1 := hX
  have : Fintype X := Fintype.ofFinite X
  have h1 : Nat.card (Outer K) = Nat.card (Outer (adjointGroup .G2 X)) :=
    Nat.card_congr (equivalence e).toEquiv
  by_cases h3 : q.p = 3
  · have hX3 : Nat.card X = 3 ^ 1 := by rw [hX', h3]
    have : CharP X 3 := finite_field_prime_power_characteristic Nat.prime_three (le_refl 1) hX3
    have : CharP X ReeTag.G2.prime := this
    obtain ⟨-, -, ⟨Θ, -, hsurj, hker⟩, -⟩ :=
      G2_three_exact_automorphism_normal_form (le_refl 1) X hX3
    have h1' : Nat.card (Outer K) = Nat.card (Outer (adjointGroup ReeTag.G2.tag X)) := h1
    rw [h1', card_outer_eq_of_hom Θ hsurj hker] at hdvd
    have hc : Nat.card (Multiplicative (ZMod (2 * 1))) = 2 := by
      rw [Nat.card_congr Multiplicative.toAdd]
      simp
    rw [hc] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · obtain ⟨-, Θ, -, hsurj, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form
      q.prime_p hq (le_refl 1) X hX' .G2 (Or.inr ⟨rfl, h3⟩)
    have hcardX := card_ringAut_and_isCyclic q.prime_p X hX'
    rw [h1, card_outer_eq_of_hom Θ hsurj hker] at hdvd
    have hc : Nat.card (X ≃+* X) = 1 := hcardX.1
    rw [hc] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega

theorem extSeitzAtInner_G2_odd_small {q : TauCeti.PrimePower} (hq : q.p ≠ 2)
    (he : q.exponent = 1) (h11 : q.card < 11) : ExtSeitzAtInner (.G2 q) := by
  intro K _ _ _ hnab hiso p hp hp5 hpd E hE hcard hinner
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  have hmodel := CFSG.TauCetiBridge.untwistedModel_of_bridge
    CFSG.TauCetiBridge.chevalleyBridges.g2 q hv hq e0
  obtain ⟨X, _, _, hX, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hmodel
  have h3 : 3 ≤ q.p ^ q.exponent := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa only [LieTypeIndex.inStandardRange_iff, PrimePower.card_def] using h
  have hlt : q.p < 11 := by simpa [PrimePower.card_def, he] using h11
  have hp3 : 3 ≤ q.p := by simpa [he] using h3
  have hr : q.p = 3 ∨ q.p = 5 ∨ q.p = 7 := by
    have hprime := q.prime_p
    generalize q.p = r at *
    interval_cases r <;> first | omega | (exfalso; revert hprime; decide)
  have hXr : Nat.card X = q.p := by rw [hX, he, pow_one]
  have hK : Nat.card K = q.p ^ 6 * (q.p ^ 6 - 1) * (q.p ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact (exact_G2_finite_order X hXr).2.1
  have hinj := conj_injective_of_simple hnab
  obtain ⟨hE₀, hmap⟩ := inner_preimage_data (p := p) hinj E hinner
  have hcard₀ : Nat.card (E.comap (MulAut.conj : K →* MulAut K)) = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap]
    exact hcard
  have hdvd : p ^ 2 ∣ Nat.card K := hcard₀ ▸ Subgroup.card_subgroup_dvd_card _
  rw [hK] at hdvd
  exact not_sq_dvd_G2_small hr hp hp5 (by simpa using hpd) hdvd

end Models

end CFSG.RankThree.PartOne.CTP
