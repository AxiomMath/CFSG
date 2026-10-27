module

public import CFSG.LieType.Chevalley.OddTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeCommonField
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.RankThree.PartOne.OutStructure

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Ree
  CFSG.ComponentClassification.UnbalancedCatalog

theorem multiplicative_zmod_pElement {p e : ℕ} (hp : p.Prime) (hpe : ¬ p ∣ e)
    (y : Multiplicative (ZMod e)) (hy : ∃ k : ℕ, y ^ (p ^ k) = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := hy
  have hdvd1 : orderOf y ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  have hdvd2 : orderOf y ∣ e := by
    have := orderOf_dvd_natCard y
    rwa [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at this
  have hcop : Nat.Coprime (p ^ k) e :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpe)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2)

theorem outPNice_ordinaryE_gen
    {p r f : ℕ}
    (hp : p.Prime) {X : Type} [Group X] (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hdet : ¬ p ∣ τ.cartan.det.natAbs) (hexact : ¬ p ∣ exactE τ) (hr : r.Prime) (hf1 : 1 ≤ f)
    (hm : UntwistedChevalleyModel X τ (r ^ f)) : OutPNice p X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hm
  obtain ⟨Φ, -, hkerΦ, hdvd⟩ := exists_outer_hom_E (K := K) (τ := τ) hτ
  have hring := card_ringAut_and_isCyclic hr K hK
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hring.1]; omega)
  have : IsCyclic (RingAut K) := hring.2
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hr.ne_zero)
  let Θ := Φ.comp (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
    (adjointGroup τ K)))
  refine OutPNice.of_mulEquiv e (outPNice_of_hom Θ ?_ ?_ ?_ ?_)
  · intro x y
    exact Prod.ext (ringAut_comm K _ _) (mul_comm _ _)
  · intro δ hδ
    have h1 : (QuotientGroup.mk δ : CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (adjointGroup τ K)) = 1 := (QuotientGroup.eq_one_iff _).mpr hδ
    show Φ (QuotientGroup.mk δ) = 1
    rw [h1, map_one]
  · intro δ hδ k hk
    have hx : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (adjointGroup τ K)) δ) ∈ Φ.ker := hδ
    have hfin : Finite Φ.ker := Nat.finite_of_card_ne_zero (fun h0 => by
      rw [h0] at hdvd
      have := Nat.eq_zero_of_zero_dvd hdvd
      have hpos : 0 < τ.cartan.det.natAbs := by
        rcases hτ with rfl | rfl | rfl
        · rw [det_cartan_E6]; decide
        · rw [det_cartan_E7]; decide
        · rw [det_cartan_E8]; decide
      omega)
    set x' : Φ.ker := ⟨_, hx⟩ with hx'
    have hxk : x' ^ (p ^ k) = 1 := by
      apply Subtype.ext
      show (QuotientGroup.mk' _ δ) ^ (p ^ k) = 1
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hk
    have hdvd1 : orderOf x' ∣ p ^ k := orderOf_dvd_of_pow_eq_one hxk
    have hdvd2 : orderOf x' ∣ τ.cartan.det.natAbs := (orderOf_dvd_natCard x').trans hdvd
    have hcop : Nat.Coprime (p ^ k) τ.cartan.det.natAbs :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hdet)
    have hx1 : orderOf x' = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
    have h1 : x' = 1 := orderOf_eq_one_iff.mp hx1
    have h2 : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (adjointGroup τ K)) δ) = 1 := congrArg Subtype.val h1
    exact (QuotientGroup.eq_one_iff _).mp h2
  · exact pChain_prod (pChain_of_isCyclic hp) (multiplicative_zmod_pElement hp hexact)

theorem outPNice_E6_gen
    {p r f : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) (hp2 : p ≠ 2) {X : Type} [Group X]
    (h : ChevalleyExceptionalModel X .E6 r f) : OutPNice p X := by
  obtain ⟨⟨hrp, hf1, -⟩, hm⟩ := h
  have hdet : Tag.E6.cartan.det.natAbs = 3 := by rw [det_cartan_E6]; rfl
  refine outPNice_ordinaryE_gen hp .E6 (Or.inl rfl) ?_ ?_ hrp hf1 hm
  · rw [hdet]
    exact fun h3 => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
  · have he : exactE Tag.E6 = 2 := rfl
    rw [he]
    exact fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem outPNice_E7_gen
    {p r f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    (h : ChevalleyExceptionalModel X .E7 r f) : OutPNice p X := by
  obtain ⟨⟨hrp, hf1, -⟩, hm⟩ := h
  have hdet : Tag.E7.cartan.det.natAbs = 2 := by rw [det_cartan_E7]; rfl
  refine outPNice_ordinaryE_gen hp .E7 (Or.inr (Or.inl rfl)) ?_ ?_ hrp hf1 hm
  · rw [hdet]
    exact fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  · have he : exactE Tag.E7 = 1 := rfl
    rw [he]
    exact fun h1 => hp.one_lt.ne' (Nat.dvd_one.mp h1)

theorem outPNice_E8_gen
    {p r f : ℕ}
    (hp : p.Prime) {X : Type} [Group X] (h : ChevalleyExceptionalModel X .E8 r f) :
    OutPNice p X := by
  obtain ⟨⟨hrp, hf1, -⟩, hm⟩ := h
  have hdet : Tag.E8.cartan.det.natAbs = 1 := by rw [det_cartan_E8]; rfl
  refine outPNice_ordinaryE_gen hp .E8 (Or.inr (Or.inr rfl)) ?_ ?_ hrp hf1 hm
  · rw [hdet]
    exact fun h1 => hp.one_lt.ne' (Nat.dvd_one.mp h1)
  · have he : exactE Tag.E8 = 1 := rfl
    rw [he]
    exact fun h1 => hp.one_lt.ne' (Nat.dvd_one.mp h1)

theorem outPNice_twistedE6_gen
    {p r f : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) {X : Type} [Group X]
    (h : ChevalleyExceptionalModel X .twistedE6 r f) : OutPNice p X := by
  obtain ⟨⟨hrp, hf1, -⟩, hm⟩ := h
  have hm' : TwistedChevalleyModel X .E6 (r ^ f) := hm
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hm'
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields .E6 hrp hf1 K hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  subst hσσ'
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, hcube, -⟩, -, -, -, ⟨E⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hrp hf1 K hcard σ' hσ'
  have hK2 : Nat.card K = r ^ (f * 2) := by rw [hcard, ← pow_mul]; rfl
  have hring := card_ringAut_and_isCyclic hrp K hK2
  have : Finite (RingAut K) :=
    Nat.finite_of_card_ne_zero (by rw [hring.1]; omega)
  have : IsCyclic (RingAut K) := hring.2
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact pow_ne_zero _ (pow_ne_zero _ hrp.ne_zero))
  refine OutPNice.of_mulEquiv (e.trans E) (outPNice_of_hom Θ (ringAut_comm K) ?_ ?_
    (pChain_of_isCyclic hp))
  · rw [hker]
    exact le_sup_left
  · intro δ hδ k hk
    rw [hker] at hδ
    exact mem_of_pow_mem_of_exponent hp (n := 3) (fun h3 => hp3 ((Nat.prime_dvd_prime_iff_eq hp
      Nat.prime_three).mp h3)) hcube hδ hk

theorem outPNice_F4_odd
    {p r f : ℕ}
    (hp : p.Prime) (hr2 : r ≠ 2) {X : Type} [Group X]
    (h : ChevalleyExceptionalModel X .F4 r f) : OutPNice p X := by
  obtain ⟨⟨hrp, hf1, -⟩, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hm
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form hrp hr2 hf1 K hK .F4 (Or.inl rfl)
  have hcard := card_ringAut_and_isCyclic hrp K hK
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcard.1]; omega)
  have := hcard.2
  exact OutPNice.of_mulEquiv e (outPNice_of_hom_cyclic hp Θ hker)

theorem outPNice_G2_odd
    {p r f : ℕ}
    (hp : p.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) {X : Type} [Group X]
    (h : ChevalleyExceptionalModel X .G2 r f) : OutPNice p X := by
  obtain ⟨⟨hrp, hf1, -⟩, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form hrp hr2 hf1 K hK .G2 (Or.inr ⟨rfl, hr3⟩)
  have hcard := card_ringAut_and_isCyclic hrp K hK
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcard.1]; omega)
  have := hcard.2
  exact OutPNice.of_mulEquiv e (outPNice_of_hom_cyclic hp Θ hker)

theorem outPNice_G2_three
    {p f : ℕ}
    (hp : p.Prime) {X : Type} [Group X] (h : ChevalleyExceptionalModel X .G2 3 f) :
    OutPNice p X := by
  obtain ⟨⟨-, hf1, -⟩, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
  have : CharP K ReeTag.G2.prime := finite_field_prime_power_characteristic Nat.prime_three hf1 hK
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form hf1 K hK
  have : NeZero (2 * f) := ⟨by omega⟩
  exact OutPNice.of_mulEquiv e (outPNice_of_hom_cyclic hp Θ hker)

theorem outPNice_trialityD4_odd
    {p r f : ℕ}
    (hp : p.Prime) (hr2 : r ≠ 2) {X : Type} [Group X]
    (h : ChevalleyExceptionalModel X .trialityD4 r f) : OutPNice p X := by
  obtain ⟨⟨hrp, hf1, -⟩, hm⟩ := h
  have hm' : TwistedChevalleyModel X .D4 (r ^ f) := hm
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hm'
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields .D4 hrp hf1 K hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  subst hσσ'
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, hord, -, -, ⟨E⟩⟩ :=
    odd_triality_exact_automorphism_normal_form hrp hr2 hf1 K hcard σ' hσ'
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hord]; omega)
  exact OutPNice.of_mulEquiv (e.trans E) (outPNice_of_hom_cyclic hp Θ hker)

end CFSG.RankThree.PartOne.OutStructure
