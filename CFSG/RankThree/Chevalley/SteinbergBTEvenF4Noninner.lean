module

public import CFSG.RankThree.Chevalley.SteinbergBTNoninnerLocalCore
public import CFSG.RankThree.Chevalley.SteinbergBTEvenF4AllOrders

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.LocalRank SteinbergBT

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem even_F4_noninner_odd_prime_field_descent_and_local_core_trivial {f p : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (B : Subgroup (MulAut (adjointGroup ReeTag.F4.tag K)))
    (hB : (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
      MulAut (adjointGroup ReeTag.F4.tag K)).range ≤ B) (α : B)
    (hα : (α : MulAut (adjointGroup ReeTag.F4.tag K)) ∉
      (MulAut.conj : adjointGroup ReeTag.F4.tag K →* MulAut (adjointGroup ReeTag.F4.tag K)).range)
    (hαp : orderOf α = p) (x : adjointGroup ReeTag.F4.tag K) (a : ℕ) (ha : a < 2 * f)
    (hxa : (α : MulAut (adjointGroup ReeTag.F4.tag K)) =
      MulAut.conj x * ReeTag.F4.finiteExceptionalAut K ^ a) :
    Even a ∧ p ∣ f ∧ (∃ σ : K ≃+* K, ∀ c, σ c = c ^ 2 ^ (a / 2)) ∧
      (∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ (a / 2)) → orderOf σ = p ∧
        ∃ ψ : MulAut (adjointGroup ReeTag.F4.tag K),
          ψ * (α : MulAut (adjointGroup ReeTag.F4.tag K)) * ψ⁻¹ =
            entrywiseAdjointAut ReeTag.F4.tag σ) ∧
      aschbacherSolvableCore p (Subgroup.centralizer {α} : Subgroup B) = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : NeZero (2 * f) := ⟨by omega⟩
  set α' : MulAut (adjointGroup ReeTag.F4.tag K) :=
    (α : MulAut (adjointGroup ReeTag.F4.tag K)) with hα'
  have hα'p : orderOf α' = p := by rw [hα', Subgroup.orderOf_coe, hαp]
  have hα'pow : α' ^ p = 1 := by
    rw [← hα'p]
    exact pow_orderOf_eq_one α'
  obtain ⟨-, hNF, ⟨Θ, hΘ, -, -⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  have hΘα : Θ α' = Multiplicative.ofAdd (a : ZMod (2 * f)) := hΘ α' x a hxa
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hα
    rw [hxa, pow_zero, mul_one]
    exact ⟨x, rfl⟩
  have hdvd : 2 * f ∣ p * a := by
    have h1 : Θ (α' ^ p) = 1 := by rw [hα'pow, map_one]
    rwa [map_pow, hΘα, ← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul, ← Nat.cast_mul,
      ZMod.natCast_eq_zero_iff] at h1
  have hp2f : p ∣ 2 * f := by
    by_contra hnd
    have hcop : Nat.Coprime (2 * f) p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm
    exact ha0 (Nat.eq_zero_of_dvd_of_lt (hcop.dvd_of_dvd_mul_left hdvd) ha)
  have hpf : p ∣ f :=
    Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp Nat.prime_two).2 hp2) hp2f
  obtain ⟨d, hd⟩ := hpf
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hdp : d * p = f := by rw [hd, mul_comm]
  have h2d : 2 * d ∣ a := by
    have h1 : p * (2 * d) ∣ p * a := by
      rw [show p * (2 * d) = 2 * f by rw [hd]; ring]
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos h1
  obtain ⟨j, hj⟩ := h2d
  have hjp : j < p := by
    by_contra hjp
    have h1 : 2 * d * p ≤ 2 * d * j := Nat.mul_le_mul_left _ (not_lt.1 hjp)
    have h2 : 2 * d * p = 2 * f := by rw [hd]; ring
    omega
  have hj0 : 0 < j := Nat.pos_of_ne_zero fun h => ha0 (by rw [hj, h, mul_zero])
  have ha2 : a / 2 = d * j := by
    rw [hj, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  obtain ⟨fr, hfr, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hK
  set T := fr ^ d with hTdef
  have hT : ∀ c, T c = c ^ 2 ^ d := ringAut_pow_apply_of_frobenius hfr d
  have hTord : orderOf T = p := by
    rw [hTdef, orderOf_pow_of_dvd (by omega) (by rw [hord, ← hdp]; exact Dvd.intro p rfl), hord,
      ← hdp, Nat.mul_div_cancel_left p hd0]
  have hσT : ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ (a / 2)) → σ = T ^ j := fun σ hσ =>
    RingEquiv.ext fun c => by
      rw [hσ, hTdef, ← pow_mul, ringAut_pow_apply_of_frobenius hfr, ha2]
  obtain ⟨r, hr⟩ := exists_mul_mod_eq_one hp hj0 hjp
  obtain ⟨⟨y, k⟩, hyk, -⟩ := hNF (α' ^ r)
  dsimp only at hyk
  have hk2d : (k : ℕ) = 2 * d := by
    have h1 : Θ (α' ^ r) = Multiplicative.ofAdd (((k : ℕ) : ZMod (2 * f))) := hΘ _ y k hyk
    rw [map_pow, hΘα, ← ofAdd_nsmul, nsmul_eq_mul, ← Nat.cast_mul] at h1
    have h2 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 (Multiplicative.ofAdd.injective h1)
    have ht : r * a = 2 * d + 2 * f * (r * j / p) := by
      have h3 := Nat.div_add_mod (r * j) p
      rw [hr] at h3
      rw [hj, hd]
      calc r * (2 * d * j) = 2 * d * (r * j) := by ring
        _ = 2 * d * (p * (r * j / p) + 1) := by rw [h3]
        _ = 2 * d + 2 * (p * d) * (r * j / p) := by ring
    have h2d2f : 2 * d < 2 * f := by
      have : d < f := by rw [← hdp]; exact lt_mul_right hd0 hp.one_lt
      omega
    rw [ht, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2d2f, Nat.mod_eq_of_lt k.isLt] at h2
    exact h2.symm
  have hβ : α' ^ r = MulAut.conj y * entrywiseAdjointAut ReeTag.F4.tag T := by
    rw [hyk, hk2d, finiteExceptionalAut_pow_two_mul,
      ← entrywiseAdjointAut_eq_finiteFrobeniusAut_pow hT]
  have hβp : (MulAut.conj y * entrywiseAdjointAut ReeTag.F4.tag T) ^ p = 1 := by
    rw [← hβ, ← pow_mul, mul_comm, pow_mul, hα'pow, one_pow]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MulAut (adjointGroup ReeTag.F4.tag K),
      ψ * (MulAut.conj y * entrywiseAdjointAut ReeTag.F4.tag T) * ψ⁻¹ =
        entrywiseAdjointAut ReeTag.F4.tag T := by
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact exists_conj_eq_entrywiseAdjointAut ReeTag.F4.tag K hK hd0 hp.one_lt.le hdp T hT
      (AlgebraicClosure K) y hβp
  have hψα : ψ * α' * ψ⁻¹ = entrywiseAdjointAut ReeTag.F4.tag (T ^ j) := by
    have hαβ : α' = (α' ^ r) ^ j := by rw [← pow_mul, pow_eq_self_of_mod_eq_one hα'p hr]
    rw [hαβ, ← conj_pow, hβ, hψ, ← entrywiseAdjointAut_pow]
  have hTjp : orderOf (T ^ j) = p := by
    refine orderOf_eq_prime ?_ (pow_ne_one_of_lt_orderOf hj0.ne' (by rw [hTord]; exact hjp))
    rw [← pow_mul, mul_comm, pow_mul, ← hTord, pow_orderOf_eq_one, one_pow]
  obtain ⟨-, hJC, hsimple, hnc, ⟨ι, -⟩, -, -, hNδ, hnormal, hcent, -⟩ :=
    even_F4_canonical_field_centralizer_all_orders hf hK (T ^ j)
  refine ⟨⟨d * j, by rw [hj]; ring⟩, ⟨d, hd⟩, ⟨T ^ j, fun c => by
      rw [hTdef, ← pow_mul, ringAut_pow_apply_of_frobenius hfr, ha2]⟩,
    fun σ hσ => ?_, aschbacherSolvableCore_centralizer_eq_bot_of_inner hp hJC hB α hαp ψ _ hψα
      hsimple hnc ι hNδ hnormal hcent⟩
  rw [hσT σ hσ]
  exact ⟨hTjp, ψ, hψα⟩

end CFSG.RankThree.Chevalley
