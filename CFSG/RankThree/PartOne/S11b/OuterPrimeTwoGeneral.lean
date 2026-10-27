module

public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwo
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

namespace OuterPrimeTwo

variable {G : Type*} [Group G] [Finite G]

theorem lt_card_of_commutator_eq {p : ℕ} (hp : p.Prime) {P Q : Subgroup G} (hP : IsPGroup p P)
    (hPQ : P ≤ normalizer (Q : Set G)) (hc : ⁅Q, P⁆ = Q) (hQ : Q ≠ ⊥) : p < Nat.card Q := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let _ : MulDistribMulAction P Q := conjActionOn hPQ
  have hmod := hP.card_modEq_card_fixedPoints Q
  have hmove : ∃ q : Q, q ∉ MulAction.fixedPoints P Q := by
    by_contra hall
    push Not at hall
    apply hQ
    rw [eq_bot_iff, ← hc]
    refine Subgroup.commutator_le.mpr ?_
    intro q hq x hx
    have h1 := MulAction.mem_fixedPoints.mp (hall ⟨q, hq⟩) ⟨x, hx⟩
    have h3 : x * q * x⁻¹ = q := congrArg Subtype.val h1
    have h4 : q * x = x * q := by
      rw [mul_inv_eq_iff_eq_mul] at h3
      exact h3.symm
    rw [Subgroup.mem_bot, commutatorElement_def, h4]
    group
  obtain ⟨q₀, hq₀⟩ := hmove
  have hlt : Nat.card (MulAction.fixedPoints P Q) < Nat.card Q := Finite.card_subtype_lt hq₀
  have hpos : 0 < Nat.card (MulAction.fixedPoints P Q) := by
    have : Nonempty (MulAction.fixedPoints P Q) :=
      ⟨⟨1, MulAction.mem_fixedPoints.mpr fun g => smul_one g⟩⟩
    exact Nat.card_pos
  have hdvd : p ∣ Nat.card Q - Nat.card (MulAction.fixedPoints P Q) :=
    (Nat.modEq_iff_dvd' hlt.le).mp hmod.symm
  have : p ≤ Nat.card Q - Nat.card (MulAction.fixedPoints P Q) :=
    Nat.le_of_dvd (by omega) hdvd
  omega

theorem eq_bot_of_card_lt {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {P Q : Subgroup G}
    (hP : IsPGroup p P) (hQ : IsPGroup 2 Q) (hPQ : P ≤ normalizer (Q : Set G)) (hc : ⁅Q, P⁆ = Q)
    (hG : Nat.card G < 40) : Q = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hQne
  have hlt := lt_card_of_commutator_eq hp hP hPQ hc hQne
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  have h8 : 8 ≤ Nat.card Q := by
    rw [hk] at hlt ⊢
    by_contra h
    have hk3 : k < 3 := by
      by_contra hk3
      have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hk3)
      omega
    interval_cases k <;> omega
  have hPne : P ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.commutator_bot_right] at hc
    exact hQne hc.symm
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hPne
    rw [pow_zero, Subgroup.card_eq_one] at hm
    exact hm
  have h5 : 5 ≤ Nat.card P := by
    rw [hm]
    exact hp5.trans (Nat.le_self_pow hm0 p)
  have hdisj : Disjoint P Q := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hm, hk]
    exact Nat.Coprime.pow m k ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
  have hinj : Function.Injective (fun xq : P × Q => (xq.1 : G) * (xq.2 : G)) := by
    rintro ⟨x, q⟩ ⟨x', q'⟩ h
    simp only at h
    have h1 : ((x' : G)⁻¹ * x) = (q' : G) * (q : G)⁻¹ := by
      calc (x' : G)⁻¹ * x = (x' : G)⁻¹ * ((x : G) * q) * (q : G)⁻¹ := by group
        _ = (x' : G)⁻¹ * ((x' : G) * q') * (q : G)⁻¹ := by rw [h]
        _ = (q' : G) * (q : G)⁻¹ := by group
    have h2 : (x' : G)⁻¹ * x ∈ P ⊓ Q := ⟨P.mul_mem (P.inv_mem x'.2) x.2, by
      rw [h1]
      exact Q.mul_mem q'.2 (Q.inv_mem q.2)⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at h2
    have hx : x = x' := Subtype.ext h2.symm
    subst hx
    have : (q : G) = q' := mul_left_cancel h
    exact Prod.ext rfl (Subtype.ext this)
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at hcard
  have := Nat.mul_le_mul h5 h8
  omega

theorem centralizes_of_cyclic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P R : Subgroup G}
    (hP : IsPGroup p P) (hR : IsPGroup 2 R) [IsCyclic R] (hPR : P ≤ normalizer (R : Set G)) :
    ∀ x ∈ P, ∀ r ∈ R, x * r * x⁻¹ = r := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let _ : MulDistribMulAction P R := conjActionOn hPR
  intro x hx r hr
  let ρ : P →* MulAut R := MulDistribMulAction.toMulAut P R
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨x, hx⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR
  have hdvd1 : orderOf (ρ ⟨x, hx⟩) ∣ p ^ k := by
    refine (orderOf_map_dvd ρ ⟨x, hx⟩).trans ?_
    rw [← hk, Subgroup.orderOf_mk]
  have hdvd2 : orderOf (ρ ⟨x, hx⟩) ∣ 2 ^ (n - 1) := by
    refine (orderOf_dvd_natCard (ρ ⟨x, hx⟩)).trans ?_
    rw [IsCyclic.card_mulAut R, hn]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0]
      simp
    · rw [Nat.totient_prime_pow Nat.prime_two h0]
      simp
  have hcop : Nat.Coprime (p ^ k) (2 ^ (n - 1)) :=
    Nat.Coprime.pow k (n - 1) ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h1 : orderOf (ρ ⟨x, hx⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have h2 : ρ ⟨x, hx⟩ = 1 := orderOf_eq_one_iff.mp h1
  have h3 : ρ ⟨x, hx⟩ ⟨r, hr⟩ = ⟨r, hr⟩ := by rw [h2]; rfl
  exact congrArg Subtype.val h3

omit [Finite G] in
theorem centralizes_of_two_step {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P Q Q₁ : Subgroup G}
    (hP : IsPGroup p P) (hQ : IsPGroup 2 Q) (hQ₁ : Q₁ ≤ Q)
    (hQP : ∀ x ∈ P, ∀ q ∈ Q, x * q * x⁻¹ * q⁻¹ ∈ Q₁)
    (hcent : ∀ x ∈ P, ∀ c ∈ Q₁, x * c * x⁻¹ = c) :
    ∀ x ∈ P, ∀ q ∈ Q, x * q * x⁻¹ = q := by
  have : Fact p.Prime := ⟨hp⟩
  intro x hx q hq
  set c := x * q * x⁻¹ * q⁻¹ with hc
  have hcQ₁ : c ∈ Q₁ := hQP x hx q hq
  have hcx : x * c * x⁻¹ = c := hcent x hx c hcQ₁
  have hxq : x * q * x⁻¹ = c * q := by rw [hc]; group
  have hpow : ∀ i : ℕ, x ^ i * q * (x ^ i)⁻¹ = c ^ i * q := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hxcpow : x * c ^ i * x⁻¹ = c ^ i := by rw [← conj_pow, hcx]
      calc x ^ (i + 1) * q * (x ^ (i + 1))⁻¹ = x * (x ^ i * q * (x ^ i)⁻¹) * x⁻¹ := by
            rw [pow_succ']; group
        _ = x * (c ^ i * q) * x⁻¹ := by rw [ih]
        _ = (x * c ^ i * x⁻¹) * (x * q * x⁻¹) := by group
        _ = c ^ i * (c * q) := by rw [hxcpow, hxq]
        _ = c ^ (i + 1) * q := by group
  obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.mp hP ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at ha
  have h1 : c ^ (p ^ a) * q = q := by
    rw [← hpow, ← ha, pow_orderOf_eq_one]
    group
  have h2 : c ^ (p ^ a) = 1 := by simpa using h1
  have hcQ : c ∈ Q := hQ₁ hcQ₁
  obtain ⟨b, hb⟩ := IsPGroup.iff_orderOf.mp hQ ⟨c, hcQ⟩
  rw [Subgroup.orderOf_mk] at hb
  have hdvd : orderOf c ∣ p ^ a := orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime (2 ^ b) (p ^ a) :=
    Nat.Coprime.pow b a ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have h3 : orderOf c = 1 := by
    rw [hb] at hdvd ⊢
    exact Nat.Coprime.eq_one_of_dvd hcop hdvd
  have h4 : c = 1 := orderOf_eq_one_iff.mp h3
  rw [hxq, h4, one_mul]

omit [Finite G] in
theorem eq_bot_of_centralizes {P Q : Subgroup G} (hc : ⁅Q, P⁆ = Q)
    (hcent : ∀ x ∈ P, ∀ q ∈ Q, x * q * x⁻¹ = q) : Q = ⊥ := by
  rw [eq_bot_iff, ← hc]
  refine Subgroup.commutator_le.mpr fun q hq x hx => ?_
  have h4 : q * x = x * q := by
    have h3 := hcent x hx q hq
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  rw [Subgroup.mem_bot, commutatorElement_def, h4]
  group

omit [Finite G] in
theorem le_normalizer_of_conj_mem {P R : Subgroup G}
    (h : ∀ x ∈ P, ∀ r ∈ R, x * r * x⁻¹ ∈ R) : P ≤ normalizer (R : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨fun hr => h x hx r hr, fun hr => ?_⟩
  have := h x⁻¹ (P.inv_mem hx) _ hr
  simpa [mul_assoc] using this

end OuterPrimeTwo

open OuterPrimeTwo in
theorem outerPrimeTwoTrivial_of_card_lt {S : Type} [Group S] [Finite S]
    (h : Nat.card (Outer S) < 40) : OuterPrimeTwoTrivial S := by
  intro p P Q hp hp3 hP hQ hPQ hc
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by decide)
  exact eq_bot_of_card_lt hp hp5 hP hQ hPQ hc h

open OuterPrimeTwo in
theorem outerPrimeTwoTrivial_of_cyclic_abelian_quotient {S : Type} [Group S] [Finite S]
    (N : Subgroup (Outer S)) [N.Normal] [IsCyclic N]
    (hab : ∀ x y : Outer S ⧸ N, x * y = y * x) : OuterPrimeTwoTrivial S := by
  intro p P Q hp hp3 hP hQ hPQ hc
  have hp2 : p ≠ 2 := by omega
  have hRcyc : IsCyclic (Q ⊓ N : Subgroup (Outer S)) :=
    isCyclic_of_injective (Subgroup.inclusion (inf_le_right : Q ⊓ N ≤ N))
      (Subgroup.inclusion_injective _)
  have hR2 : IsPGroup 2 (Q ⊓ N : Subgroup (Outer S)) := hQ.to_le inf_le_left
  have hconj : ∀ x ∈ P, ∀ r ∈ (Q ⊓ N : Subgroup (Outer S)), x * r * x⁻¹ ∈ Q ⊓ N := by
    intro x hx r hr
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hPQ hx) r).mp hr.1,
      Subgroup.Normal.conj_mem inferInstance r hr.2 x⟩
  have hcentR := centralizes_of_cyclic hp hp2 hP hR2 (le_normalizer_of_conj_mem hconj)
  refine eq_bot_of_centralizes hc (centralizes_of_two_step hp hp2 hP hQ inf_le_left ?_ hcentR)
  intro x hx q hq
  refine ⟨Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPQ hx) q).mp hq) (Q.inv_mem hq), ?_⟩
  change x * q * x⁻¹ * q⁻¹ ∈ N
  rw [← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hab (x : Outer S ⧸ N) (q : Outer S ⧸ N)]
  group

open OuterPrimeTwo in
theorem outerPrimeTwoTrivial_of_two_layer {S : Type} [Group S] [Finite S]
    (E D : Subgroup (Outer S)) [E.Normal] [IsCyclic D] (hDE : D ≤ E)
    (hsq : ∀ x : Outer S, x ^ 2 ∈ E) (hED : ∀ a ∈ E, ∀ b ∈ E, ⁅a, b⁆ ∈ D) :
    OuterPrimeTwoTrivial S := by
  intro p P Q hp hp3 hP hQ hPQ hc
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hPE : ∀ x ∈ P, x ∈ E := by
    intro x hx
    obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.mp hP ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at ha
    have hodd : Odd (orderOf x) := by
      rw [ha]
      exact (hp.eq_two_or_odd'.resolve_left hp2).pow
    obtain ⟨m, hm⟩ := hodd
    have hx' : x = (x ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [hx']
    exact E.pow_mem (hsq x) _
  have hQconj : ∀ x ∈ P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q := fun x hx q hq =>
    (Subgroup.mem_normalizer_iff.mp (hPQ hx) q).mp hq
  have hRcyc : IsCyclic (Q ⊓ D : Subgroup (Outer S)) :=
    isCyclic_of_injective (Subgroup.inclusion (inf_le_right : Q ⊓ D ≤ D))
      (Subgroup.inclusion_injective _)
  have hR2 : IsPGroup 2 (Q ⊓ D : Subgroup (Outer S)) := hQ.to_le inf_le_left
  have hconj : ∀ x ∈ P, ∀ r ∈ (Q ⊓ D : Subgroup (Outer S)), x * r * x⁻¹ ∈ Q ⊓ D := by
    intro x hx r hr
    refine ⟨hQconj x hx r hr.1, ?_⟩
    have h1 : x * r * x⁻¹ = ⁅x, r⁆ * r := by rw [commutatorElement_def]; group
    rw [h1]
    exact D.mul_mem (hED x (hPE x hx) r (hDE hr.2)) hr.2
  have hcentD := centralizes_of_cyclic hp hp2 hP hR2 (le_normalizer_of_conj_mem hconj)
  have hcentE : ∀ x ∈ P, ∀ q ∈ (Q ⊓ E : Subgroup (Outer S)), x * q * x⁻¹ = q := by
    refine centralizes_of_two_step hp hp2 hP (hQ.to_le inf_le_left) (inf_le_inf_left Q hDE)
      ?_ hcentD
    intro x hx q hq
    refine ⟨hQconj x hx q hq.1 |> fun h => Q.mul_mem h (Q.inv_mem hq.1), ?_⟩
    have := hED x (hPE x hx) q hq.2
    rwa [commutatorElement_def] at this
  refine eq_bot_of_centralizes hc (centralizes_of_two_step hp hp2 hP hQ inf_le_left ?_ hcentE)
  intro x hx q hq
  refine ⟨Q.mul_mem (hQconj x hx q hq) (Q.inv_mem hq), ?_⟩
  have h1 : x * q * x⁻¹ * q⁻¹ = x * (q * x⁻¹ * q⁻¹) := by group
  rw [h1]
  exact E.mul_mem (hPE x hx) (Subgroup.Normal.conj_mem inferInstance x⁻¹ (E.inv_mem (hPE x hx)) q)

theorem outerPrimeTwoTrivial_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (h : OuterPrimeTwoTrivial T) : OuterPrimeTwoTrivial S := by
  intro p P Q hp hp3 hP hQ hPQ hc
  let φ : Outer S →* Outer T := (equivalence e).toMonoidHom
  have hφ : Function.Injective φ := (equivalence e).injective
  have h3 : P.map φ ≤ normalizer ((Q.map φ : Subgroup (Outer T)) : Set (Outer T)) :=
    (Subgroup.map_mono hPQ).trans (Subgroup.le_normalizer_map φ)
  have h4 : ⁅Q.map φ, P.map φ⁆ = Q.map φ := by rw [← Subgroup.map_commutator, hc]
  have h5 := h p (P.map φ) (Q.map φ) hp hp3 (hP.map φ) (hQ.map φ) h3 h4
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have h6 : φ x ∈ Q.map φ := Subgroup.mem_map_of_mem φ hx
  rw [h5, Subgroup.mem_bot, ← map_one φ] at h6
  exact hφ h6

theorem outerPrimeTwoTrivial_of_not_dvd {S : Type} [Group S] [Finite S]
    (h : ∀ q : ℕ, q.Prime → 5 ≤ q → ¬ q ∣ Nat.card (Outer S)) : OuterPrimeTwoTrivial S := by
  intro p P Q hp hp3 hP _ _ hcomm
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by decide)
  have hPbot : P = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hk
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0, pow_zero] at hk
      exact orderOf_eq_one_iff.mp hk
    · exfalso
      apply h p hp hp5
      have hdvd : orderOf x ∣ Nat.card (Outer S) := orderOf_dvd_natCard x
      rw [hk] at hdvd
      exact (dvd_pow_self p hk0.ne').trans hdvd
  rw [← hcomm, hPbot, Subgroup.commutator_bot_right]

theorem outerPrimeTwoTrivial_of_odd {S : Type} [Group S] [Finite S]
    (h : Odd (Nat.card (Outer S))) : OuterPrimeTwoTrivial S := by
  intro p P Q hp hp3 hP hQ hPQ hcomm
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hQ ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : orderOf x ∣ Nat.card (Outer S) := orderOf_dvd_natCard x
  rw [hk] at hdvd
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · exfalso
    have h2 : 2 ∣ Nat.card (Outer S) := (dvd_pow_self 2 hk0.ne').trans hdvd
    exact (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr h2)

open OuterPrimeTwo in
theorem outerPrimeTwoTrivial_of_odd_abelian_quotient {S : Type} [Group S] [Finite S]
    (N : Subgroup (Outer S)) [N.Normal] (hN : Odd (Nat.card N))
    (hab : ∀ x y : Outer S ⧸ N, x * y = y * x) : OuterPrimeTwoTrivial S := by
  intro p P Q hp hp3 hP hQ hPQ hc
  refine eq_bot_of_centralizes hc ?_
  intro x hx q hq
  have hQconj : x * q * x⁻¹ * q⁻¹ ∈ Q :=
    Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPQ hx) q).mp hq) (Q.inv_mem hq)
  have hNmem : x * q * x⁻¹ * q⁻¹ ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hab (x : Outer S ⧸ N) (q : Outer S ⧸ N)]
    group
  set c := x * q * x⁻¹ * q⁻¹ with hcdef
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hQ ⟨c, hQconj⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : orderOf c ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨c, hNmem⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  rw [hk] at hdvd
  have hc1 : orderOf c = 1 := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk, hk0, pow_zero]
    · exfalso
      have h2 : 2 ∣ Nat.card N := (dvd_pow_self 2 hk0.ne').trans hdvd
      exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h2)
  have hc1' : c = 1 := orderOf_eq_one_iff.mp hc1
  have : x * q * x⁻¹ = q := by
    rw [hcdef, mul_inv_eq_one] at hc1'
    exact hc1'
  exact this

theorem outerPrimeTwoTrivial_of_abelian {S : Type} [Group S] [Finite S]
    (hab : ∀ x y : Outer S, x * y = y * x) : OuterPrimeTwoTrivial S := by
  refine outerPrimeTwoTrivial_of_cyclic_abelian_quotient (⊥ : Subgroup (Outer S)) ?_
  intro x y
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hab a b]

end CFSG.RankThree.PartOne
