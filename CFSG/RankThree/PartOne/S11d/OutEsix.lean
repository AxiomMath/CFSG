module

public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier

public section

namespace CFSG.RankThree.PartOne.OutStructure

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial

theorem outPNice_twistedE6 {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {X : Type} [Group X] {f : ℕ}
    (h : ChevalleyExceptionalModel X .twistedE6 2 f) : OutPNice p X := by
  obtain ⟨⟨-, hf1, -⟩, hm⟩ := h
  have hm' : TwistedChevalleyModel X .E6 (2 ^ f) := hm
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hm'
  obtain ⟨σ', hσ', -⟩ := finite_graph_field_parameter_fields .E6 Nat.prime_two hf1 K hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  subst hσσ'
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, hcube, -⟩, -, -, -, ⟨E⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf1 K hcard σ' hσ'
  have hK2 : Nat.card K = 2 ^ (f * 2) := by rw [hcard, ← pow_mul]; rfl
  have hring := card_ringAut_and_isCyclic Nat.prime_two K hK2
  have : Finite (RingAut K) :=
    Nat.finite_of_card_ne_zero (by rw [hring.1]; omega)
  have : IsCyclic (RingAut K) := hring.2
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  refine OutPNice.of_mulEquiv (e.trans E) (outPNice_of_hom Θ (ringAut_comm K) ?_ ?_
    (pChain_of_isCyclic hp))
  · rw [hker]
    exact le_sup_left
  · intro δ hδ k hk
    rw [hker] at hδ
    exact mem_of_pow_mem_of_exponent hp (n := 3) (fun h3 => hp3 ((Nat.prime_dvd_prime_iff_eq hp
      Nat.prime_three).mp h3)) hcube hδ hk

theorem outPNice_E6 {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hp2 : p ≠ 2) {X : Type} [Group X]
    {f : ℕ} (h : ChevalleyExceptionalModel X .E6 2 f) : OutPNice p X := by
  obtain ⟨⟨-, hf1, -⟩, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm
  obtain ⟨Φ, -, hkerΦ, hdvd⟩ := exists_outer_hom_E (K := K) (τ := .E6) (Or.inl rfl)
  have hdet : Tag.E6.cartan.det.natAbs = 3 := by rw [det_cartan_E6]; rfl
  rw [hdet] at hdvd
  have hring := card_ringAut_and_isCyclic Nat.prime_two K hK
  have : Finite (RingAut K) :=
    Nat.finite_of_card_ne_zero (by rw [hring.1]; omega)
  have : IsCyclic (RingAut K) := hring.2
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  let Θ := Φ.comp (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
    (adjointGroup Tag.E6 K)))
  refine OutPNice.of_mulEquiv e (outPNice_of_hom Θ ?_ ?_ ?_ ?_)
  · intro x y
    exact Prod.ext (ringAut_comm K _ _) (mul_comm _ _)
  · intro δ hδ
    have h1 : (QuotientGroup.mk δ : CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (adjointGroup Tag.E6 K)) = 1 := (QuotientGroup.eq_one_iff _).mpr hδ
    show Φ (QuotientGroup.mk δ) = 1
    rw [h1, map_one]
  · intro δ hδ k hk
    have hx : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (adjointGroup Tag.E6 K)) δ) ∈ Φ.ker := hδ
    have hfin : Finite Φ.ker := Nat.finite_of_card_ne_zero (fun h0 => by
      rw [h0] at hdvd
      exact absurd (Nat.eq_zero_of_zero_dvd hdvd) (by norm_num))
    set x' : Φ.ker := ⟨_, hx⟩ with hx'
    have hxk : x' ^ (p ^ k) = 1 := by
      apply Subtype.ext
      show (QuotientGroup.mk' _ δ) ^ (p ^ k) = 1
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hk
    have hdvd1 : orderOf x' ∣ p ^ k := orderOf_dvd_of_pow_eq_one hxk
    have hdvd2 : orderOf x' ∣ 3 := (orderOf_dvd_natCard x').trans hdvd
    have hcop : Nat.Coprime (p ^ k) 3 :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h3 =>
        hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3))
    have hx1 : orderOf x' = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
    have h1 : x' = 1 := orderOf_eq_one_iff.mp hx1
    have h2 : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (adjointGroup Tag.E6 K)) δ) = 1 := congrArg Subtype.val h1
    exact (QuotientGroup.eq_one_iff _).mp h2
  · refine pChain_prod (pChain_of_isCyclic hp) fun y ⟨k, hk⟩ => ?_
    have he : exactE Tag.E6 = 2 := rfl
    have hdvd1 : orderOf y ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
    have hdvd2 : orderOf y ∣ 2 := by
      have h2 : ∀ a : Multiplicative (ZMod 2), a ^ 2 = 1 := by decide
      exact orderOf_dvd_of_pow_eq_one (h2 y)
    have hcop : Nat.Coprime (p ^ k) 2 :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h2 =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2))
    have hy1 : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
    exact orderOf_eq_one_iff.mp hy1

end CFSG.RankThree.PartOne.OutStructure
