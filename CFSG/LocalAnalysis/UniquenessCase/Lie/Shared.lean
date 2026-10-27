module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

section Concl

@[expose] def uc22pwlie_Concl (Ep : ∀ (Y : Type) [Group Y], Subgroup Y → Prop) (X : Type) [Group X] [Finite X]
    (U : Subgroup X) (P : Type) [Group P] (ψ : P →* MulAut X) (n m' : ℕ) : Prop :=
  ∃ E : Subgroup X, E ≤ normalizer (U : Set X) ∧ Ep X E ∧ piSet E = etaSet n ∧
    (∀ g : P, ∀ x ∈ E, ψ g x ∈ E ⊔ U) ∧
    (∀ g : P, ∀ x ∈ oPi {p | p.Prime ∧ p ∣ 2 ^ m' - 1} E, ψ g x * x⁻¹ ∈ U) ∧
    ∃ w : X, w ^ 2 = 1 ∧ (∀ x ∈ E, w * x * w⁻¹ = x⁻¹) ∧ normalizer (U : Set X) ⊔ zpowers w = ⊤

variable {X Y : Type} [Group X] [Group Y]

theorem uc22pwlie_map_map_symm (e : X ≃* Y) (U : Subgroup X) :
    (U.map e.toMonoidHom).map e.symm.toMonoidHom = U := by
  ext z
  simp [Subgroup.mem_map_equiv]

theorem uc22pwlie_mem_map_iff (e : X ≃* Y) (U : Subgroup X) (y : Y) :
    y ∈ U.map e.toMonoidHom ↔ e.symm y ∈ U :=
  Subgroup.mem_map_equiv

theorem uc22pwlie_piSet_map [Finite X] [Finite Y] (e : X ≃* Y) (E : Subgroup X) :
    piSet (E.map e.toMonoidHom) = piSet E := by
  unfold piSet
  rw [Subgroup.card_map_of_injective e.injective]

theorem uc22pwlie_oPi_le_comap [Finite X] [Finite Y] (e : X ≃* Y) (α : Set ℕ) (E' : Subgroup Y) :
    oPi α (E'.map e.symm.toMonoidHom) ≤ (oPi α E').comap e.toMonoidHom := by
  refine iSup₂_le fun N hN => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  obtain ⟨hNE, hNn, hNα⟩ := hN
  have hle : N.map e.toMonoidHom ≤ E' := by
    rintro _ ⟨a, ha, rfl⟩
    have := hNE ha
    rw [Subgroup.mem_map_equiv] at this
    simpa using this
  refine le_iSup₂_of_le (N.map e.toMonoidHom) ⟨hle, ?_, ?_⟩ le_rfl
  · rw [Subgroup.normal_subgroupOf_iff hle]
    rintro _ k ⟨a, ha, rfl⟩ hk
    have hc : e.symm k ∈ E'.map e.symm.toMonoidHom := by
      rw [Subgroup.mem_map_equiv]
      simpa using hk
    have h1 := (Subgroup.normal_subgroupOf_iff hNE).1 hNn a (e.symm k) ha hc
    refine ⟨e.symm k * a * (e.symm k)⁻¹, h1, ?_⟩
    simp
  · rw [uc22pwlie_piSet_map]
    exact hNα

end Concl

theorem uc22pwlie_mem_of_mem_oPi {X : Type} [Group X] [Finite X] {α : Set ℕ} {E : Subgroup X}
    (hE : IsMulCommutative E) {x : X}
    (hx : x ∈ oPi α E) : x ∈ E ∧ ∀ p : ℕ, p.Prime → p ∣ orderOf x → p ∈ α := by
  haveI := hE
  let P : Subgroup X :=
    { carrier := {y | y ∈ E ∧ ∀ p : ℕ, p.Prime → p ∣ orderOf y → p ∈ α}
      mul_mem' := by
        rintro y z ⟨hy, hyα⟩ ⟨hz, hzα⟩
        refine ⟨E.mul_mem hy hz, fun p hp hpd => ?_⟩
        have hc : Commute y z := mul_comm_of_mem_isMulCommutative E hy hz
        have h1 : orderOf (y * z) ∣ orderOf y * orderOf z := hc.orderOf_mul_dvd_mul_orderOf
        rcases (Nat.Prime.dvd_mul hp).1 (hpd.trans h1) with h2 | h2
        · exact hyα p hp h2
        · exact hzα p hp h2
      one_mem' := ⟨E.one_mem, fun p hp hpd => by
        rw [orderOf_one] at hpd
        exact absurd (Nat.le_of_dvd one_pos hpd) (by have := hp.two_le; omega)⟩
      inv_mem' := by
        rintro y ⟨hy, hyα⟩
        exact ⟨E.inv_mem hy, fun p hp hpd => hyα p hp (by rwa [orderOf_inv] at hpd)⟩ }
  have hle : oPi α E ≤ P := by
    refine iSup₂_le fun N hN => ?_
    intro y hy
    refine ⟨hN.1 hy, fun p hp hpd => ?_⟩
    exact hN.2.2 ⟨hp, hpd.trans (Subgroup.orderOf_dvd_natCard N hy)⟩
  exact hle hx

section Arith

theorem uc22pwlie_dvd_two_pow_sub_one {p m' i k : ℕ} (hm' : Odd m') (h1 : p ∣ 2 ^ m' - 1)
    (h2 : p ∣ 2 ^ (i * 2 ^ k) - 1) : p ∣ 2 ^ i - 1 := by
  have hcast : ∀ j : ℕ, p ∣ 2 ^ j - 1 ↔ (2 : ZMod p) ^ j = 1 := fun j => by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one, sub_eq_zero]
  have d1 : orderOf (2 : ZMod p) ∣ m' := orderOf_dvd_of_pow_eq_one ((hcast m').1 h1)
  have d2 : orderOf (2 : ZMod p) ∣ i * 2 ^ k := orderOf_dvd_of_pow_eq_one ((hcast _).1 h2)
  have hodd : Odd (orderOf (2 : ZMod p)) := hm'.of_dvd_nat d1
  have hcop : Nat.Coprime (orderOf (2 : ZMod p)) (2 ^ k) :=
    Nat.Coprime.pow_right k hodd.coprime_two_right
  exact (hcast i).2 (orderOf_dvd_iff_pow_eq_one.1 (hcop.dvd_of_dvd_mul_right d2))

theorem uc22pwlie_charP_two {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [← Nat.card_eq_fintype_card]; exact hK)

theorem uc22pwlie_ringEquiv_pow {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) :
    ∃ i : ℕ, ∀ x : K, σ x = x ^ 2 ^ i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  let σ' : K ≃ₐ[ZMod 2] K := AlgEquiv.ofRingEquiv (f := σ) (fun x => by
    have : (σ.toRingHom).comp (algebraMap (ZMod 2) K) = algebraMap (ZMod 2) K :=
      RingHom.ext_zmod _ _
    exact congrArg (fun f : ZMod 2 →+* K => f x) this)
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod 2) 2 K σ'
  refine ⟨i, fun x => ?_⟩
  have h := hi x
  rw [Nat.card_zmod] at h
  exact h

end Arith

section Cyclic

theorem uc22pwlie_squarefree_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    fun p hp => (hS p hp).squarefree
  simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq

theorem uc22pwlie_exists_subgroup_of_primes {X : Type} [Group X] [Finite X] (C : Subgroup X) [IsCyclic C]
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ Nat.card C) :
    ∃ R : Subgroup X, R ≤ C ∧ Nat.card R = ∏ p ∈ S, p ∧ ∀ x ∈ C, x ^ (∏ p ∈ S, p) = 1 → x ∈ R := by
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := C)
  have hN : orderOf (c : X) = Nat.card C := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hc
  have hrdvd : ∏ p ∈ S, p ∣ Nat.card C :=
    Finset.prod_primes_dvd _ (fun p hp => (hS p hp).1.prime) (fun p hp => (hS p hp).2)
  have hrpos : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp => (hS p hp).1.pos
  obtain ⟨d, hd⟩ := hrdvd
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, mul_zero] at hd
      exact absurd hd Nat.card_pos.ne'
    · exact h0
  refine ⟨Subgroup.zpowers ((c : X) ^ d), ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem _ c.2 d
  · rw [Nat.card_zpowers, orderOf_pow_of_dvd hdpos.ne' (by rw [hN, hd]; exact Dvd.intro_left _ rfl), hN, hd,
      Nat.mul_div_cancel _ hdpos]
  · intro x hx hxr
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hc ⟨x, hx⟩)
    have hjx : (c : X) ^ j = x := by
      have := congrArg Subtype.val hj
      simpa using this
    have h1 : (c : X) ^ (j * ((∏ p ∈ S, p : ℕ) : ℤ)) = 1 := by
      rw [zpow_mul, hjx, zpow_natCast]
      exact hxr
    have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
    rw [hN, hd, Nat.cast_mul, mul_comm j] at h2
    have h3 : (d : ℤ) ∣ j := by
      have hr0 : ((∏ p ∈ S, p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hrpos.ne'
      exact (mul_dvd_mul_iff_left hr0).1 h2
    obtain ⟨j', hj'⟩ := h3
    refine Subgroup.mem_zpowers_iff.2 ⟨j', ?_⟩
    rw [← hjx, hj', zpow_mul, zpow_natCast]

theorem uc22pw_radical_subgroup {C : Type} [Group C] [Finite C] [IsCyclic C] (hodd : Odd (Nat.card C)) :
    ∃ R : Subgroup C, IsCyclic R ∧ Squarefree (Nat.card R) ∧ Odd (Nat.card R) ∧
      (∀ p : ℕ, p.Prime → (p ∣ Nat.card R ↔ p ∣ Nat.card C)) ∧
      ∀ x : C, orderOf x ∣ Nat.card R → x ∈ R := by
  haveI : IsCyclic (⊤ : Subgroup C) :=
    isCyclic_of_surjective (Subgroup.topEquiv : (⊤ : Subgroup C) ≃* C).symm.toMonoidHom
      (Subgroup.topEquiv : (⊤ : Subgroup C) ≃* C).symm.surjective
  have hS : ∀ p ∈ (Nat.card C).primeFactors, p.Prime ∧ p ∣ Nat.card (⊤ : Subgroup C) := fun p hp => by
    rw [Subgroup.card_top]
    exact ⟨Nat.prime_of_mem_primeFactors hp, Nat.dvd_of_mem_primeFactors hp⟩
  obtain ⟨R, -, hR, hRx⟩ := uc22pwlie_exists_subgroup_of_primes (⊤ : Subgroup C) (Nat.card C).primeFactors hS
  have hsq : Squarefree (Nat.card R) := by
    rw [hR]
    exact uc22pwlie_squarefree_prod_primes _ fun p hp => Nat.prime_of_mem_primeFactors hp
  have hdvd : Nat.card R ∣ Nat.card C := by
    rw [hR]
    exact Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
      (fun p hp => Nat.dvd_of_mem_primeFactors hp)
  refine ⟨R, inferInstance, hsq, hodd.of_dvd_nat hdvd, fun p hp => ⟨fun h => h.trans hdvd, fun h => ?_⟩,
    fun x hx => hRx x trivial ?_⟩
  · rw [hR]
    exact Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.2 ⟨hp, h, Nat.card_pos.ne'⟩)
  · rw [← hR]
    exact orderOf_dvd_iff_pow_eq_one.1 hx

end Cyclic

end CFSG.LocalAnalysis.UniquenessCase.UC22
