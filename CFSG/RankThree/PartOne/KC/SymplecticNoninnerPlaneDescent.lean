module

public import CFSG.RankThree.PartOne.KC.SymplecticInnerActorOdd

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open Polynomial CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.Classical
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

variable {r : ℕ} {K : Type} [Field K]

structure SpOuter (ℓ f r : ℕ) (K : Type) [Field K] : Prop where
  fieldAut_injective : Function.Injective (fieldAut r K)
  sup_eq : spLinearAutGroup r K ⊔ (fieldAut r K).range = spSemilinearAutGroup r K
  normal : (spLinearAutGroup r K).Normal
  index_dvd : (spSemilinearAutGroup r K).index ∣ 2
  relIndex_dvd : (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣
    Nat.gcd 2 (ℓ ^ f - 1)
  descent : ∀ p : ℕ, p.Prime → ∀ a ∈ spSemilinearAutGroup r K, a ∉ spLinearAutGroup r K →
    orderOf a = p → p ∣ f ∧ ∃ σ : K ≃+* K, orderOf σ = p ∧
      ∃ h ∈ spLinearAutGroup r K, a = h * fieldAut r K σ * h⁻¹

theorem spOuter {ℓ f r : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hr : 2 ≤ r) (hK : Nat.card K = ℓ ^ f) :
    SpOuter ℓ f r K := by
  obtain ⟨-, hinj, -, hDFE, -, hDnorm, -, hindex, hrel, hdesc⟩ :=
    SteinbergBY.symplectic_prime_semilinear_field_descent hℓ hf hr hK
  refine ⟨hinj, hDFE, hDnorm, hindex, hrel, fun p hp a haE haD hap => ?_⟩
  obtain ⟨hpf, σ, hσ, -, h, hh, hah⟩ := hdesc p hp a haE haD hap
  exact ⟨hpf, σ, hσ, h, hh, hah⟩

theorem mem_of_pow_eq_one_of_relIndex_dvd_two {M : Type*} [Group M] [Finite M]
    {H D : Subgroup M} [H.Normal] (hk : H.relIndex D ∣ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : M} (hxD : x ∈ D) (hxp : x ^ p = 1) : x ∈ H := by
  have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  set y : D := ⟨x, hxD⟩ with hydef
  have hy : y ^ p = 1 := Subtype.ext (by simpa using hxp)
  have h1 : orderOf (y : D ⧸ H.subgroupOf D) ∣ p :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hy, QuotientGroup.mk_one])
  have h2 : orderOf (y : D ⧸ H.subgroupOf D) ∣ 2 := by
    refine (orderOf_dvd_natCard _).trans ?_
    rw [← Subgroup.index_eq_card]
    exact hk
  have h3 : orderOf (y : D ⧸ H.subgroupOf D) = 1 :=
    Nat.Coprime.eq_one_of_dvd (hcop2.coprime_dvd_left h1) h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

section Plane

variable {ℓ f p : ℕ} [Finite K]

omit [Finite K] in
theorem pow_eq_one_of_mem {A : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    [IsElementaryAbelian p A] {a : MulAut (StatedProj (StatedSp r K))} (ha : a ∈ A) :
    a ^ p = 1 :=
  elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha

omit [Finite K] in
theorem mem_E_of_mem {ℓ f : ℕ} (O : SpOuter ℓ f r K) (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (MulAut (StatedProj (StatedSp r K)))} [IsElementaryAbelian p A]
    {a : MulAut (StatedProj (StatedSp r K))} (ha : a ∈ A) : a ∈ spSemilinearAutGroup r K := by
  refine mem_of_odd_orderOf_of_index_dvd_two _ O.index_dvd ?_
  exact Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one (pow_eq_one_of_mem ha))

theorem mem_inner_of_mem_D {ℓ f : ℕ} (O : SpOuter ℓ f r K) (hp : p.Prime)
    (hp2 : p ≠ 2) {A : Subgroup (MulAut (StatedProj (StatedSp r K)))} [IsElementaryAbelian p A]
    {a : MulAut (StatedProj (StatedSp r K))} (ha : a ∈ A) (haD : a ∈ spLinearAutGroup r K) :
    a ∈ inner (StatedProj (StatedSp r K)) := by
  have := inner_normal (StatedProj (StatedSp r K))
  exact mem_of_pow_eq_one_of_relIndex_dvd_two
    (O.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)) hp hp2 haD (pow_eq_one_of_mem ha)

theorem card_inf_inner_eq_prime {ℓ f : ℕ} (O : SpOuter ℓ f r K) (hr : 2 ≤ r) (hp : p.Prime)
    (hp2 : p ≠ 2) (hcyc : IsCyclic (K ≃+* K))
    {A : Subgroup (MulAut (StatedProj (StatedSp r K)))} [IsElementaryAbelian p A]
    (hAcard : Nat.card A = p ^ 2) (hAH : ¬ A ≤ inner (StatedProj (StatedSp r K))) :
    Nat.card (A ⊓ inner (StatedProj (StatedSp r K)) :
      Subgroup (MulAut (StatedProj (StatedSp r K)))) = p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero r := ⟨by omega⟩
  have := O.normal
  set E := spSemilinearAutGroup r K with hE
  set D := spLinearAutGroup r K with hD
  have hAE : A ≤ E := fun a ha => mem_E_of_mem O hp hp2 ha
  have hAD : ∀ a ∈ A, a ∈ D → a ∈ inner (StatedProj (StatedSp r K)) := fun a ha haD =>
    mem_inner_of_mem_D O hp hp2 ha haD
  have hFE : (fieldAut r K).range ≤ E := by
    rw [hE, ← O.sup_eq]
    exact le_sup_right
  have hcycQ : IsCyclic (↥E ⧸ D.subgroupOf E) := by
    let ψ : ↥(fieldAut r K).range →* ↥E ⧸ D.subgroupOf E :=
      (QuotientGroup.mk' (D.subgroupOf E)).comp (Subgroup.inclusion hFE)
    have hψ : Function.Surjective ψ := by
      intro q
      obtain ⟨⟨e, he⟩, rfl⟩ := QuotientGroup.mk_surjective q
      have he' := he
      rw [hE, ← O.sup_eq] at he'
      obtain ⟨d, hd, φ, hφ, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp he'
      refine ⟨⟨φ, hφ⟩, ?_⟩
      show (QuotientGroup.mk (⟨φ, hFE hφ⟩ : ↥E) : ↥E ⧸ D.subgroupOf E) = _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      show (φ⁻¹ * (d * φ) : MulAut (StatedProj (StatedSp r K))) ∈ D
      have : φ⁻¹ * (d * φ) = (φ⁻¹) * d * (φ⁻¹)⁻¹ := by group
      rw [this]
      exact (inferInstance : D.Normal).conj_mem d hd φ⁻¹
    have : IsCyclic ↥(fieldAut r K).range :=
      isCyclic_of_surjective (fieldAut r K).rangeRestrict (fieldAut r K).rangeRestrict_surjective
    exact isCyclic_of_surjective ψ hψ
  let φ : ↥A →* ↥E ⧸ D.subgroupOf E :=
    (QuotientGroup.mk' (D.subgroupOf E)).comp (Subgroup.inclusion hAE)
  have hker : ∀ a : ↥A, φ a = 1 ↔ (a : MulAut (StatedProj (StatedSp r K))) ∈ D := fun a => by
    show (QuotientGroup.mk (⟨(a : MulAut (StatedProj (StatedSp r K))), hAE a.2⟩ : ↥E) :
      ↥E ⧸ D.subgroupOf E) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hdvd : Nat.card (A ⊓ inner (StatedProj (StatedSp r K)) :
      Subgroup (MulAut (StatedProj (StatedSp r K)))) ∣ p ^ 2 := by
    rw [← hAcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, hcard⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  interval_cases i
  · exfalso
    have hbot : A ⊓ inner (StatedProj (StatedSp r K)) = ⊥ :=
      Subgroup.card_eq_one.mp (by simpa using hcard)
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro a ha
      have h3 : (a : MulAut (StatedProj (StatedSp r K))) ∈ A ⊓ inner (StatedProj (StatedSp r K)) :=
        ⟨a.2, hAD a a.2 ((hker a).mp ha)⟩
      rw [hbot] at h3
      exact Subtype.ext (Subgroup.mem_bot.mp h3)
    have : IsCyclic φ.range := Subgroup.isCyclic _
    have hAcyc : IsCyclic ↥A :=
      isCyclic_of_surjective (MonoidHom.ofInjective hinj).symm (MulEquiv.surjective _)
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := p) hAcard hAcyc
  · simpa using hcard
  · exfalso
    apply hAH
    have h6 : A ⊓ inner (StatedProj (StatedSp r K)) = A :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, hAcard])
    calc A = A ⊓ inner (StatedProj (StatedSp r K)) := h6.symm
      _ ≤ inner (StatedProj (StatedSp r K)) := inf_le_right

theorem noninner_element_data {ℓ f : ℕ} [NeZero r] (O : SpOuter ℓ f r K) (hp : p.Prime)
    (hp2 : p ≠ 2) {A : Subgroup (MulAut (StatedProj (StatedSp r K)))} [IsElementaryAbelian p A]
    {a : MulAut (StatedProj (StatedSp r K))} (ha : a ∈ A)
    (haH : a ∉ inner (StatedProj (StatedSp r K))) :
    p ∣ f ∧ ∃ σ : K ≃+* K, orderOf σ = p ∧ ∃ h ∈ spLinearAutGroup r K,
      a = h * fieldAut r K σ * h⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  have haE := mem_E_of_mem O hp hp2 ha
  have haD : a ∉ spLinearAutGroup r K := fun hD => haH (mem_inner_of_mem_D O hp hp2 ha hD)
  have ha1 : a ≠ 1 := fun h => haH (h ▸ one_mem _)
  exact O.descent p hp a haE haD (orderOf_eq_prime (pow_eq_one_of_mem ha) ha1)

end Plane

end CFSG.RankThree.PartOne.KCSpComm
