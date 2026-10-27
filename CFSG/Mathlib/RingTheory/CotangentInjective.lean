module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.Ideal.Cotangent.Localization
import TauCeti.RingTheory.FiniteType.PointSeparation

public section

namespace CFSG

open IsLocalRing Ideal

universe u v

private theorem injective_of_maximalIdeal_eq_bot {A R : Type*} [CommRing A] [CommRing R]
    [IsLocalRing A] [Nontrivial R] (f : A →+* R) (h : maximalIdeal A = ⊥) :
    Function.Injective f :=
  (RingHom.injective_iff_ker_eq_bot f).mpr
    (le_bot_iff.mp (h ▸ le_maximalIdeal (RingHom.ker_ne_top f)))

private theorem exists_mem_maximalIdeal_notMem_sq' {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (h : maximalIdeal A ≠ ⊥) :
    ∃ a ∈ maximalIdeal A, a ∉ maximalIdeal A ^ 2 := by
  by_contra! hle
  refine h (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal A) (maximalIdeal A)
    (maximalIdeal A).fg_of_isNoetherianRing (fun a ha => ?_) ?_)
  · have := hle a ha
    rwa [pow_two, ← smul_eq_mul] at this
  · rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]

private theorem injective_of_cotangent_injective_aux (n : ℕ) :
    ∀ (A : Type u) (R : Type v) [CommRing A] [CommRing R] [IsLocalRing A] [IsNoetherianRing A]
      [IsRegularLocalRing R] (f : A →+* R) [IsLocalHom f],
      (∀ r : R, ∃ c : A, r - f c ∈ maximalIdeal R) →
      (∀ a ∈ maximalIdeal A, f a ∈ maximalIdeal R ^ 2 → a ∈ maximalIdeal A ^ 2) →
      ringKrullDim R = n → Function.Injective f := by
  induction n with
  | zero =>
    intro A R _ _ _ _ _ f _ _ hf h
    have hm : maximalIdeal R = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal R).fg_of_isNoetherianRing).mp
        (by exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).trans h)
    refine injective_of_maximalIdeal_eq_bot f ?_
    by_contra hA
    obtain ⟨a, ha, ha2⟩ := exists_mem_maximalIdeal_notMem_sq' hA
    refine ha2 (hf a ha ?_)
    have hfa : f a ∈ maximalIdeal R := map_nonunit f a ha
    rw [hm, mem_bot] at hfa
    rw [hfa]
    exact zero_mem _
  | succ n ih =>
    intro A R _ _ _ _ _ f _ hres hf h
    by_cases hA : maximalIdeal A = ⊥
    · exact injective_of_maximalIdeal_eq_bot f hA
    obtain ⟨a, ha, ha2⟩ := exists_mem_maximalIdeal_notMem_sq' hA
    set x := f a with hx
    have hxm : x ∈ maximalIdeal R := map_nonunit f a ha
    have hx2 : x ∉ maximalIdeal R ^ 2 := fun h2 => ha2 (hf a ha h2)
    have hx0 : x ≠ 0 := fun h0 => hx2 (h0 ▸ zero_mem _)
    have : IsRegularLocalRing (R ⧸ span {x}) :=
      TauCeti.IsRegularLocalRing.quotient_span_singleton hxm hx2
    have hdim : ringKrullDim (R ⧸ span {x}) = n := by
      have hmin : ∀ p ∈ minimalPrimes R, x ∉ p := by
        intro p hp hxp
        rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] at hp
        exact hx0 (by simpa [hp] using hxp)
      have := open TauCeti in
ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_notMem_minimalPrimes_of_mem_jacobson
        hmin (by rwa [ringJacobson_eq_maximalIdeal R])
      rw [h, Nat.cast_succ, ENat.WithBot.add_one_cancel] at this
      exact this
    have hane : span {a} ≠ ⊤ := fun htop => (maximalIdeal.isMaximal A).ne_top
      (top_le_iff.mp (htop ▸ (span_singleton_le_iff_mem _).mpr ha))
    have : Nontrivial (A ⧸ span {a}) := Ideal.Quotient.nontrivial_iff.mpr hane
    have : IsLocalRing (A ⧸ span {a}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (span {a})) Ideal.Quotient.mk_surjective
    have hle : span {a} ≤ (span {x}).comap f := by
      rw [span_singleton_le_iff_mem, mem_comap]
      exact mem_span_singleton_self x
    let f' : A ⧸ span {a} →+* R ⧸ span {x} := Ideal.quotientMap (span {x}) f hle
    have hmA : maximalIdeal (A ⧸ span {a}) = (maximalIdeal A).map (Ideal.Quotient.mk _) :=
      (map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
    have hmR : maximalIdeal (R ⧸ span {x}) = (maximalIdeal R).map (Ideal.Quotient.mk _) :=
      (map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
    have : IsLocalHom f' := by
      refine ⟨fun y hy => ?_⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      by_contra hny
      have hy' : y ∈ maximalIdeal A := (mem_maximalIdeal _).mpr fun hu => hny (hu.map _)
      have hmem : f' (Ideal.Quotient.mk _ y) ∈ maximalIdeal (R ⧸ span {x}) := by
        rw [Ideal.quotientMap_mk, hmR]
        exact mem_map_of_mem _ (map_nonunit f y hy')
      exact (mem_maximalIdeal _).mp hmem hy
    have hres' : ∀ r : R ⧸ span {x}, ∃ c : A ⧸ span {a},
        r - f' c ∈ maximalIdeal (R ⧸ span {x}) := by
      intro r
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨c, hc⟩ := hres r
      refine ⟨Ideal.Quotient.mk _ c, ?_⟩
      rw [Ideal.quotientMap_mk, ← map_sub, hmR]
      exact mem_map_of_mem _ hc
    have hf' : ∀ u ∈ maximalIdeal (A ⧸ span {a}), f' u ∈ maximalIdeal (R ⧸ span {x}) ^ 2 →
        u ∈ maximalIdeal (A ⧸ span {a}) ^ 2 := by
      intro u hu hu2
      rw [hmA, mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hu
      obtain ⟨u, hu, rfl⟩ := hu
      rw [Ideal.quotientMap_mk, hmR, ← Ideal.map_pow,
        mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hu2
      obtain ⟨r, hr, hr'⟩ := hu2
      rw [Ideal.Quotient.eq, mem_span_singleton'] at hr'
      obtain ⟨s, hs⟩ := hr'
      obtain ⟨c, hc⟩ := hres s
      have hmem : f (u + c * a) ∈ maximalIdeal R ^ 2 := by
        have heq : f (u + c * a) = r - (s - f c) * x := by
          rw [map_add, map_mul, hx]
          linear_combination hs
        rw [heq]
        refine sub_mem hr ?_
        rw [pow_two]
        exact mul_mem_mul hc hxm
      have h2 := hf (u + c * a) (add_mem hu (mul_mem_left _ c ha)) hmem
      have heq : Ideal.Quotient.mk (span {a}) u = Ideal.Quotient.mk (span {a}) (u + c * a) := by
        rw [Ideal.Quotient.eq, sub_add_cancel_left, neg_mem_iff]
        exact mul_mem_left _ c (mem_span_singleton_self a)
      rw [heq, hmA, ← Ideal.map_pow]
      exact mem_map_of_mem _ h2
    have hinj' : Function.Injective f' := ih (A ⧸ span {a}) (R ⧸ span {x}) f' hres' hf' hdim
    have hker : ∀ p, f p = 0 → p ∈ span {a} := by
      intro p hp
      have h0 : f' (Ideal.Quotient.mk _ p) = f' 0 := by
        rw [Ideal.quotientMap_mk, hp, map_zero, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mp (hinj' h0)
    have hK : RingHom.ker f = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (span {a}) (RingHom.ker f)
        (RingHom.ker f).fg_of_isNoetherianRing (fun p hp => ?_) ?_
      · obtain ⟨q, rfl⟩ := mem_span_singleton'.mp (hker p (RingHom.mem_ker.mp hp))
        have hq : f q = 0 := by
          have h0 : f q * x = 0 := by rw [hx, ← map_mul]; exact RingHom.mem_ker.mp hp
          exact (mul_eq_zero.mp h0).resolve_right hx0
        rw [mul_comm, ← smul_eq_mul]
        exact Submodule.smul_mem_smul (mem_span_singleton_self a) (RingHom.mem_ker.mpr hq)
      · rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top, span_singleton_le_iff_mem]
        exact ha
    exact (RingHom.injective_iff_ker_eq_bot f).mpr hK

theorem injective_of_cotangent_injective {A : Type u} {R : Type v}
    [CommRing A] [CommRing R] [IsLocalRing A] [IsNoetherianRing A] [IsRegularLocalRing R]
    (f : A →+* R) [IsLocalHom f] (hres : ∀ r : R, ∃ c : A, r - f c ∈ maximalIdeal R)
    (hf : ∀ a ∈ maximalIdeal A, f a ∈ maximalIdeal R ^ 2 → a ∈ maximalIdeal A ^ 2) :
    Function.Injective f := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim R = n :=
    ⟨_, (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm⟩
  exact injective_of_cotangent_injective_aux n A R f hres hf hn

theorem injective_of_cotangent_injective_at {k : Type*} [Field k] {A : Type u} {R : Type v}
    [CommRing A] [CommRing R] [Algebra k A] [Algebra k R] [IsDomain A] [IsNoetherianRing A]
    [IsRegularRing R] (f : A →ₐ[k] R) (x : R →ₐ[k] k)
    (hf : ∀ a ∈ RingHom.ker (x.comp f), f a ∈ RingHom.ker x ^ 2 →
      a ∈ RingHom.ker (x.comp f) ^ 2) :
    Function.Injective f := by
  classical
  set m := RingHom.ker x with hm
  set n := RingHom.ker (x.comp f) with hn
  have hnm : n = m.comap (f : A →+* R) := by
    ext a
    simp [n, m, RingHom.mem_ker]
  have : m.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective x fun c => ⟨algebraMap k R c, x.commutes c⟩
  have : n.IsMaximal := RingHom.ker_isMaximal_of_surjective (x.comp f)
    fun c => ⟨algebraMap k A c, (x.comp f).commutes c⟩
  let φ := Localization.localRingHom n m (f : A →+* R) hnm
  have : IsNoetherianRing (Localization.AtPrime n) :=
    IsLocalization.isNoetherianRing n.primeCompl _ inferInstance
  have hres : ∀ r : Localization.AtPrime m, ∃ c : Localization.AtPrime n,
      r - φ c ∈ maximalIdeal (Localization.AtPrime m) := by
    intro r
    obtain ⟨⟨r₀, s⟩, rfl⟩ := IsLocalization.mk'_surjective m.primeCompl r
    have hs : x s ≠ 0 := fun h0 => s.2 (RingHom.mem_ker.mpr h0)
    set c : k := x r₀ / x s with hc
    refine ⟨algebraMap A _ (algebraMap k A c), ?_⟩
    have h1 : φ (algebraMap A _ (algebraMap k A c)) = algebraMap R _ (algebraMap k R c) := by
      simp only [φ, Localization.localRingHom_to_map, AlgHom.coe_toRingHom, AlgHom.commutes]
    have h2 : IsLocalization.mk' (Localization.AtPrime m) r₀ s -
        algebraMap R _ (algebraMap k R c) =
        algebraMap R _ (r₀ - algebraMap k R c * s) * IsLocalization.mk' _ (1 : R) s := by
      rw [map_sub, sub_mul, map_mul, mul_assoc, IsLocalization.mk'_spec', map_one, mul_one,
        ← IsLocalization.mk'_eq_mul_mk'_one]
    rw [h1, h2]
    refine Ideal.mul_mem_right _ _ ?_
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m]
    refine RingHom.mem_ker.mpr ?_
    rw [map_sub, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, hc,
      div_mul_cancel₀ _ hs, sub_self]
  have hcot : ∀ α ∈ maximalIdeal (Localization.AtPrime n),
      φ α ∈ maximalIdeal (Localization.AtPrime m) ^ 2 →
      α ∈ maximalIdeal (Localization.AtPrime n) ^ 2 := by
    intro α hα hα2
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective n.primeCompl α
    have ha : a ∈ n := by
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime n) n,
        ← IsLocalization.mk'_spec' (Localization.AtPrime n) a s]
      exact Ideal.mul_mem_left _ _ hα
    have hfa : f a ∈ m := by
      have h := ha
      rw [hnm, mem_comap] at h
      exact h
    have hfa2 : algebraMap R (Localization.AtPrime m) (f a) ∈
        maximalIdeal (Localization.AtPrime m) ^ 2 := by
      simp only [φ, Localization.localRingHom_mk'] at hα2
      rw [← IsLocalization.mk'_spec' (M := m.primeCompl) (Localization.AtPrime m) (f a)
        ⟨f s, fun h => s.2 h⟩]
      exact Ideal.mul_mem_left _ _ hα2
    have hfa_sq : f a ∈ m ^ 2 := by
      have hmem : algebraMap R (Localization.AtPrime m) (f a) ∈
          maximalIdeal (Localization.AtPrime m) :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m (f a)).mpr hfa
      have h0 : (maximalIdeal (Localization.AtPrime m)).toCotangent ⟨_, hmem⟩ = 0 :=
        (Ideal.toCotangent_eq_zero _ _).mpr hfa2
      rw [← Ideal.cotangentLocalizationEquiv_toCotangent (Rₚ := Localization.AtPrime m) m
        ⟨f a, hfa⟩, LinearEquiv.map_eq_zero_iff, Ideal.toCotangent_eq_zero] at h0
      exact h0
    have ha2 := hf a ha hfa_sq
    change IsLocalization.mk' (Localization.AtPrime n) a s ∈ maximalIdeal _ ^ 2
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    refine Ideal.mul_mem_right _ _ ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    exact mem_map_of_mem _ ha2
  have := IsRegularRing.isRegularLocalRing_localization (R := R) m
  have hφ := injective_of_cotangent_injective φ hres hcot
  have hA : Function.Injective (algebraMap A (Localization.AtPrime n)) :=
    IsLocalization.injective _ n.primeCompl_le_nonZeroDivisors
  intro p q hpq
  apply hA
  apply hφ
  simp only [φ, Localization.localRingHom_to_map]
  exact congrArg _ hpq

theorem eq_zero_of_cotangent_injective_at_of_forall_apply_eq_zero {k : Type*} [Field k]
    [IsAlgClosed k] {A : Type u} {R : Type v} [CommRing A] [CommRing R] [Algebra k A] [Algebra k R]
    [IsDomain A] [IsNoetherianRing A] [IsRegularRing R] [Algebra.FiniteType k R] [IsReduced R]
    (f : A →ₐ[k] R) (x : R →ₐ[k] k)
    (hf : ∀ a ∈ RingHom.ker (x.comp f), f a ∈ RingHom.ker x ^ 2 →
      a ∈ RingHom.ker (x.comp f) ^ 2)
    {p : A} (hp : ∀ y : R →ₐ[k] k, y (f p) = 0) : p = 0 := by
  refine injective_of_cotangent_injective_at f x hf ?_
  rw [map_zero]
  exact TauCeti.eq_of_forall_algHom_apply_eq (K := k) fun y => by rw [hp y, map_zero]

theorem pointDerivation_eq_zero_of_mem_sq {k R : Type*} [Field k] [CommRing R] [Algebra k R]
    (x : R →ₐ[k] k) (D : R →ₗ[k] k) (hD : ∀ a b, D (a * b) = x a * D b + x b * D a)
    {r : R} (hr : r ∈ RingHom.ker x ^ 2) : D r = 0 := by
  rw [pow_two] at hr
  refine Submodule.mul_induction_on (C := fun r => D r = 0) hr (fun a ha b hb => ?_)
    (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
  rw [hD, RingHom.mem_ker.mp ha, RingHom.mem_ker.mp hb, zero_mul, zero_mul, add_zero]

theorem cotangent_injective_of_forall_pointDerivation {k A R : Type*} [Field k] [CommRing A]
    [CommRing R] [Algebra k A] [Algebra k R] (f : A →ₐ[k] R) (x : R →ₐ[k] k)
    (hsurj : ∀ D : A →ₗ[k] k, (∀ a b, D (a * b) = x (f a) * D b + x (f b) * D a) →
      ∃ D' : R →ₗ[k] k, (∀ a b, D' (a * b) = x a * D' b + x b * D' a) ∧
        D = D' ∘ₗ f.toLinearMap) :
    ∀ a ∈ RingHom.ker (x.comp f), f a ∈ RingHom.ker x ^ 2 → a ∈ RingHom.ker (x.comp f) ^ 2 := by
  intro a ha hfa
  set y := x.comp f with hy
  set n := RingHom.ker y with hn
  by_contra ha2
  have hv : n.toCotangent ⟨a, ha⟩ ≠ 0 := fun h => ha2 ((n.toCotangent_eq_zero _).mp h)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual k n.Cotangent, ℓ (n.toCotangent ⟨a, ha⟩) ≠ 0 := by
    by_contra! h
    exact hv ((Module.forall_dual_apply_eq_zero_iff k _).mp h)
  have hmem : ∀ p : A, p - algebraMap k A (y p) ∈ n := fun p => RingHom.mem_ker.mpr (by simp)
  let Q : A → n := fun p => ⟨p - algebraMap k A (y p), hmem p⟩
  have hQadd : ∀ p q, Q (p + q) = Q p + Q q := fun p q => Subtype.ext (by
    simp only [Q, Submodule.coe_add, map_add]
    ring)
  have hQsmul : ∀ (c : k) p, Q (c • p) = c • Q p := fun c p => Subtype.ext (by
    simp only [Q, Submodule.coe_smul_of_tower, map_mul, Algebra.smul_def, AlgHom.commutes,
      Algebra.algebraMap_self, RingHom.id_apply]
    ring)
  let D : A →ₗ[k] k :=
    { toFun := fun p => ℓ (n.toCotangent (Q p))
      map_add' := fun p q => by simp only [hQadd, map_add]
      map_smul' := fun c p => by
        simp only [hQsmul, LinearMap.map_smul_of_tower, map_smul, RingHom.id_apply] }
  have hD : ∀ p q, D (p * q) = x (f p) * D q + x (f q) * D p := by
    intro p q
    have hpq : Q (p * q) =
        ⟨(Q p : A) * (Q q : A), n.mul_mem_left _ (Q q).2⟩ + y p • Q q + y q • Q p := by
      apply Subtype.ext
      simp only [Q, Submodule.coe_add, Submodule.coe_smul_of_tower, Algebra.smul_def, map_mul]
      ring
    have h0 : n.toCotangent ⟨(Q p : A) * (Q q : A), n.mul_mem_left _ (Q q).2⟩ = 0 :=
      (n.toCotangent_eq_zero _).mpr (by rw [pow_two]; exact Ideal.mul_mem_mul (Q p).2 (Q q).2)
    show ℓ (n.toCotangent (Q (p * q))) =
      y p * ℓ (n.toCotangent (Q q)) + y q * ℓ (n.toCotangent (Q p))
    rw [hpq]
    simp only [map_add, h0, zero_add, LinearMap.map_smul_of_tower, map_smul, smul_eq_mul]
  obtain ⟨D', hD', hDD'⟩ := hsurj D hD
  have h1 : D a = ℓ (n.toCotangent ⟨a, ha⟩) := by
    show ℓ (n.toCotangent (Q a)) = _
    congr 2
    apply Subtype.ext
    simp [Q, RingHom.mem_ker.mp ha]
  have h2 : D a = 0 := by
    rw [hDD', LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    exact pointDerivation_eq_zero_of_mem_sq x D' hD' hfa
  exact hℓ (h1 ▸ h2)

end CFSG
