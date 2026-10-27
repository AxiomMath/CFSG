module

public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

public section

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.RankThree.PartOne.KCUnitary

section Semilinear

variable {K S S' : Type*} [CommSemiring K] [Semiring S] [Semiring S'] [Algebra K S]
  [Algebra K S']

theorem ringHom_aeval_semilinear (φ : S →+* S') (σ : K →+* K)
    (hφ : ∀ c : K, φ (algebraMap K S c) = algebraMap K S' (σ c)) (X : S) (g : K[X]) :
    φ (aeval X g) = aeval (φ X) (g.map σ) := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, Polynomial.map_add, map_add]
  | monomial n c =>
    rw [aeval_monomial, map_mul, map_pow, hφ, Polynomial.map_monomial, aeval_monomial]

end Semilinear

section Roots

variable {ℓ f : ℕ} {K E : Type*} [Field K] [Field E] [Algebra K E] {h : UnitaryFieldData ℓ f K}
  [Fact ℓ.Prime] [CharP E ℓ]

theorem aeval_dualPoly_inv_pow {a : K[X]} (h0 : a.coeff 0 ≠ 0) {μ : E} (hμ : aeval μ a = 0) :
    aeval ((μ ^ ℓ ^ f)⁻¹) (dualPoly h.bar a) = 0 := by
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [← Polynomial.coeff_zero_eq_aeval_zero'] at hμ
    exact h0 ((map_eq_zero_iff _ (algebraMap K E).injective).mp hμ)
  have hx : μ ^ ℓ ^ f ≠ 0 := pow_ne_zero _ hμ0
  let _ : Invertible (μ ^ ℓ ^ f) := invertibleOfNonzero hx
  have hfr : aeval (μ ^ ℓ ^ f) (a.map h.bar) = 0 := by
    have h1 := ringHom_aeval_semilinear (iterateFrobenius E ℓ f) h.bar (fun c => by
      rw [iterateFrobenius_def, h.bar_apply, map_pow]) μ a
    rw [hμ, map_zero, iterateFrobenius_def] at h1
    exact h1.symm
  have h1 := Polynomial.eval₂_reverse_mul_pow (algebraMap K E) (μ ^ ℓ ^ f) (a.map h.bar)
  have hfr' : eval₂ (algebraMap K E) (μ ^ ℓ ^ f) (a.map h.bar) = 0 := by
    rw [← aeval_def]
    exact hfr
  rw [hfr'] at h1
  have h2 : eval₂ (algebraMap K E) (⅟(μ ^ ℓ ^ f)) (reverse (a.map h.bar)) = 0 :=
    (mul_eq_zero.mp h1).resolve_right (pow_ne_zero _ hx)
  rw [invOf_eq_inv] at h2
  rw [dualPoly, map_mul, aeval_C, aeval_def, h2, mul_zero]

theorem aeval_pow_of_pow_card {m : ℕ} (hK : ∀ c : K, c ^ ℓ ^ m = c) {μ : E} {g : K[X]}
    (hμ : aeval μ g = 0) : aeval (μ ^ ℓ ^ m) g = 0 := by
  have h1 := ringHom_aeval_semilinear (iterateFrobenius E ℓ m) (RingHom.id K) (fun c => by
    rw [iterateFrobenius_def, ← map_pow, hK]; rfl) μ g
  rw [hμ, map_zero, iterateFrobenius_def, Polynomial.map_id] at h1
  exact h1.symm

theorem eq_of_aeval_eq_zero {a b : K[X]} (ha : Irreducible a) (ha' : a.Monic)
    (hb : Irreducible b) (hb' : b.Monic) {μ : E} (h1 : aeval μ a = 0) (h2 : aeval μ b = 0) :
    a = b :=
  (minpoly.eq_of_irreducible_of_monic ha h1 ha').trans
    (minpoly.eq_of_irreducible_of_monic hb h2 hb').symm

end Roots

section Exponent

variable {ℓ f : ℕ} {K E : Type*} [Field K] [Field E] [Algebra K E] {h : UnitaryFieldData ℓ f K}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[h.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

theorem pow_card_two_mul (hf : UnitaryFieldData ℓ f K) (i : ℕ) (c : K) :
    c ^ ℓ ^ (f * (2 * i)) = c := by
  have := hf.finite
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = ℓ ^ (2 * f) := by rw [← Nat.card_eq_fintype_card, hf.card]
  have h1 := FiniteField.pow_card_pow i c
  rw [hcard, ← pow_mul] at h1
  rwa [show f * (2 * i) = 2 * f * i by ring]

theorem eq_or_eq_dualPoly_of_exponent [Fact ℓ.Prime] [CharP E ℓ] (H : UnitaryPrimaryData h.bar B x)
    {p : ℕ} [NeZero p] (ψ : AddChar (ZMod p) E) {a b : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) (hb : b ∈ primaryFactors (x : Module.End K V))
    {ea eb : ZMod p} (hea : aeval (ψ ea) a = 0) (heb : aeval (ψ eb) b = 0) {j : ℕ}
    (hj : eb = (-((ℓ : ZMod p) ^ f)) ^ j * ea) : b = a ∨ b = dualPoly h.bar a := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
  · left
    have h1 : eb = ((ℓ ^ (f * (2 * i)) : ℕ) : ZMod p) * ea := by
      rw [hj, Nat.cast_pow, pow_mul, neg_sq, ← pow_mul, ← pow_mul]
    have h2 : ψ eb = ψ ea ^ ℓ ^ (f * (2 * i)) := by
      rw [h1, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
    have h3 : aeval (ψ eb) a = 0 := by
      rw [h2]
      exact aeval_pow_of_pow_card (pow_card_two_mul h i) hea
    exact (eq_of_aeval_eq_zero (irreducible_of_mem_primaryFactors ha)
      (monic_of_mem_primaryFactors ha) (irreducible_of_mem_primaryFactors hb)
      (monic_of_mem_primaryFactors hb) h3 heb).symm
  · right
    have h1 : eb = -(((ℓ ^ (f * (2 * i)) * ℓ ^ f : ℕ) : ZMod p) * ea) := by
      rw [hj, pow_succ, pow_mul, neg_sq, ← pow_mul, ← pow_mul]
      push_cast
      ring
    have h2 : ψ eb = ((ψ ea ^ ℓ ^ f)⁻¹) ^ ℓ ^ (f * (2 * i)) := by
      rw [h1, AddChar.map_neg_eq_inv, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, mul_comm, pow_mul,
        inv_pow]
    have hdual := dualPoly_mem_primaryFactors H ha
    have h3 : aeval (ψ eb) (dualPoly h.bar a) = 0 := by
      rw [h2]
      exact aeval_pow_of_pow_card (pow_card_two_mul h i)
        (aeval_dualPoly_inv_pow (coeff_zero_ne_zero_of_mem_primaryFactors H.squarefree ha) hea)
    exact (eq_of_aeval_eq_zero (irreducible_of_mem_primaryFactors hdual)
      (monic_of_mem_primaryFactors hdual) (irreducible_of_mem_primaryFactors hb)
      (monic_of_mem_primaryFactors hb) h3 heb).symm

end Exponent

section Count

variable {ℓ f : ℕ} {K : Type*} [Field K] {h : UnitaryFieldData ℓ f K}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[h.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

theorem exists_exponent {E : Type*} [Field E] [IsAlgClosed E] [Algebra K E] {p : ℕ} [NeZero p]
    {ζ : E} (hζ : IsPrimitiveRoot ζ p) {a : K[X]} (ha : Irreducible a) (hdvd : a ∣ X ^ p - C 1) :
    ∃ e : ZMod p, aeval (AddChar.zmodChar p hζ.pow_eq_one e) a = 0 := by
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective (k := E)
    (algebraMap K E).injective a (Polynomial.degree_pos_of_irreducible ha).ne'
  have hμp : μ ^ p = 1 := by
    obtain ⟨q, hq⟩ := hdvd
    have : aeval μ (X ^ p - C 1 : K[X]) = 0 := by rw [hq, map_mul, hμ, zero_mul]
    simpa [sub_eq_zero] using this
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hμp
  refine ⟨(i : ZMod p), ?_⟩
  rw [AddChar.zmodChar_apply', hi]
  exact hμ

theorem exponent_ne_zero {E : Type*} [Field E] [Algebra K E] {p : ℕ} [NeZero p]
    {ψ : AddChar (ZMod p) E} {a : K[X]} (ha : Irreducible a) (ha' : a.Monic) (hne : a ≠ X - C 1)
    {e : ZMod p} (he : aeval (ψ e) a = 0) : e ≠ 0 := by
  rintro rfl
  rw [AddChar.map_zero_eq_one] at he
  apply hne
  have h1 : algebraMap K E (a.eval 1) = 0 := by
    have := Polynomial.eval₂_at_apply (algebraMap K E) (1 : K) (p := a)
    rw [map_one] at this
    rw [← this, ← aeval_def]
    exact he
  have h2 : a.eval 1 = 0 := (map_eq_zero_iff _ (algebraMap K E).injective).mp h1
  have h3 : (X - C 1 : K[X]) ∣ a := by
    have := Polynomial.dvd_iff_isRoot.mpr (show a.IsRoot 1 from h2)
    simpa using this
  exact (eq_of_monic_of_associated (monic_X_sub_C 1) ha'
    ((irreducible_X_sub_C 1).associated_of_dvd ha h3)).symm

theorem card_adjointOrbits_le (H : UnitaryPrimaryData h.bar B x) {p : ℕ} (hp : p.Prime)
    (hpℓ : p ≠ ℓ) (hxp : (x : Module.End K V) ^ p = 1) :
    Nat.card (adjointOrbits h x) ≤ 1 + (p - 1) / orderOf (-((ℓ : ZMod p) ^ f)) := by
  classical
  have hfin : Finite K := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : Fact p.Prime := ⟨hp⟩
  have hcharK : CharP K ℓ := h.charP
  have hp0 : (p : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K ℓ p).mp h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq h.prime hp).mp this).symm
  have : NeZero (p : K) := ⟨hp0⟩
  have hcharE : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) p
  let ψ : AddChar (ZMod p) (AlgebraicClosure K) := AddChar.zmodChar p hζ.pow_eq_one
  have hdvd : ∀ a ∈ primaryFactors (x : Module.End K V), a ∣ X ^ p - C 1 := by
    intro a ha
    refine (mem_primaryFactors.mp ha).2.2.trans (minpoly.dvd K (x : Module.End K V) ?_)
    simp [hxp]
  have hex : ∀ a ∈ primaryFactors (x : Module.End K V), ∃ e : ZMod p, aeval (ψ e) a = 0 :=
    fun a ha => exists_exponent hζ (irreducible_of_mem_primaryFactors ha) (hdvd a ha)
  choose! ee hee using hex
  set u : ZMod p := -((ℓ : ZMod p) ^ f) with hu
  have hℓp : (ℓ : ZMod p) ≠ 0 := by
    intro h0
    have := (ZMod.natCast_eq_zero_iff ℓ p).mp h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp h.prime).mp this)
  have hu0 : u ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ hℓp)
  have hd : 0 < orderOf u := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨p - 1, by have := hp.two_le; omega, ZMod.pow_card_sub_one_eq_one hu0⟩)
  set d := orderOf u with hdd
  set F := primaryFactors (x : Module.End K V) with hF
  let pair : K[X] → Set K[X] := fun a => {a, dualPoly h.bar a}
  have hΩ : adjointOrbits h x = pair '' (F : Set K[X]) := rfl
  set F₁ : Finset K[X] := F.erase (X - C 1) with hF₁
  obtain ⟨T, hTsub, hTbij⟩ := Set.exists_subset_bijOn (↑F₁ : Set K[X]) pair
  have hTfin : T.Finite := F₁.finite_toSet.subset hTsub
  have hTF : ∀ a ∈ T, a ∈ F ∧ a ≠ X - C 1 := fun a ha => by
    have := Finset.mem_erase.mp (hTsub ha)
    exact ⟨this.2, this.1⟩
  have key : ∀ a ∈ T, ∀ a' ∈ T, ∀ k k' : ℕ, k' ≤ k → u ^ k * ee a = u ^ k' * ee a' → a = a' := by
    intro a ha a' ha' k k' hkk heq
    have h1 : ee a' = u ^ (k - k') * ee a := by
      have : u ^ k' * (u ^ (k - k') * ee a) = u ^ k' * ee a' := by
        rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hkk]
        exact heq
      exact (mul_left_cancel₀ (pow_ne_zero _ hu0) this).symm
    rcases eq_or_eq_dualPoly_of_exponent H ψ (hTF a ha).1 (hTF a' ha').1 (hee a (hTF a ha).1)
      (hee a' (hTF a' ha').1) h1 with h2 | h2
    · exact h2.symm
    · have hpa : pair a' = pair a := by
        simp only [pair]
        rw [h2, dualPoly_dualPoly_of_mem H (hTF a ha).1]
        exact Set.pair_comm _ _
      exact (hTbij.injOn ha' ha hpa).symm
  have hne : ∀ a ∈ T, ee a ≠ 0 := fun a ha =>
    exponent_ne_zero (irreducible_of_mem_primaryFactors (hTF a ha).1)
      (monic_of_mem_primaryFactors (hTF a ha).1) (hTF a ha).2 (hee a (hTF a ha).1)
  have hinj : Set.InjOn (fun q : K[X] × ℕ => u ^ q.2 * ee q.1)
      ↑(hTfin.toFinset ×ˢ Finset.range d) := by
    rintro ⟨a, k⟩ hq ⟨a', k'⟩ hq' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Set.Finite.mem_toFinset,
      Finset.mem_range] at hq hq'
    simp only at heq
    have haa : a = a' := by
      rcases le_total k' k with hle | hle
      · exact key a hq.1 a' hq'.1 k k' hle heq
      · exact (key a' hq'.1 a hq.1 k' k hle heq.symm).symm
    subst haa
    have hk : u ^ k = u ^ k' := mul_right_cancel₀ (hne a hq.1) heq
    have := pow_injOn_Iio_orderOf (x := u) hq.2 hq'.2 hk
    simp [this]
  have hcard := Finset.card_le_card_of_injOn (fun q : K[X] × ℕ => u ^ q.2 * ee q.1)
    (s := hTfin.toFinset ×ˢ Finset.range d) (t := (Finset.univ : Finset (ZMod p)).erase 0)
    (fun q hq => by
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Set.Finite.mem_toFinset,
        Finset.mem_range] at hq
      exact Finset.mem_coe.mpr (Finset.mem_erase.mpr
        ⟨mul_ne_zero (pow_ne_zero _ hu0) (hne q.1 hq.1), Finset.mem_univ _⟩)) hinj
  rw [Finset.card_product, Finset.card_range, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ZMod.card] at hcard
  have hT : hTfin.toFinset.card ≤ (p - 1) / d := (Nat.le_div_iff_mul_le hd).mpr hcard
  have hsub : pair '' (F : Set K[X]) ⊆ insert (pair (X - C 1)) (pair '' (F₁ : Set K[X])) := by
    rintro _ ⟨a, ha, rfl⟩
    by_cases hax : a = X - C 1
    · left
      rw [hax]
    · right
      exact ⟨a, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hax, ha⟩), rfl⟩
  have h1 : (pair '' (F : Set K[X])).ncard ≤ (pair '' (F₁ : Set K[X])).ncard + 1 :=
    (Set.ncard_le_ncard hsub ((F₁.finite_toSet.image pair).insert _)).trans
      (Set.ncard_insert_le _ _)
  have h2 : (pair '' (F₁ : Set K[X])).ncard = hTfin.toFinset.card := by
    rw [← hTbij.image_eq, hTbij.injOn.ncard_image, Set.ncard_eq_toFinset_card T hTfin]
  rw [hΩ, Nat.card_coe_set_eq]
  change (pair '' (F : Set K[X])).ncard ≤ 1 + (p - 1) / d
  omega

end Count

end CFSG.RankThree.PartOne.KCUnitary
