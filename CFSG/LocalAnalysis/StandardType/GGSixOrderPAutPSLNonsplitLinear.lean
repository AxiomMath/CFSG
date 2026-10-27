module

public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import Mathlib

public section

open Polynomial Module

namespace CFSG.StandardType

namespace OrdPNS

@[expose] noncomputable def ordQ (K : Type*) (ℓ : ℕ) : ℕ := orderOf ((Nat.card K : ℕ) : ZMod ℓ)

theorem ordQ_def (K : Type*) (ℓ : ℕ) : ordQ K ℓ = orderOf ((Nat.card K : ℕ) : ZMod ℓ) := rfl

section Arith

variable {K : Type*} [Field K] [Finite K] {ℓ : ℕ}

theorem natDegree_eq_ordQ (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) {g : K[X]} (hg : Irreducible g)
    (hgd : g ∣ cyclotomic ℓ K) : g.natDegree = ordQ K ℓ := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨c, hcK, e, hc, hcard⟩ := FiniteField.card' K
  have : Fact c.Prime := ⟨hc⟩
  have hcℓ : c.Coprime ℓ := by
    refine (Nat.coprime_primes hc hℓ).mpr fun hce => hℓK ?_
    rw [← hce]
    exact CharP.cast_eq_zero K c
  rw [natDegree_of_dvd_cyclotomic_of_irreducible hcard hcℓ hgd hg, ordQ, Nat.card_eq_fintype_card,
    hcard, ← orderOf_units, ZMod.coe_unitOfCoprime]

theorem ordQ_pos (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) : 0 < ordQ K ℓ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hne : ¬ IsUnit (cyclotomic ℓ K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero ℓ K),
      natDegree_cyclotomic, Nat.totient_prime hℓ]
    have := hℓ.two_le
    norm_cast
    omega
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero ℓ K)
  rw [← natDegree_eq_ordQ hℓ hℓK hg hgd]
  exact natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hg)

end Arith

section Decomp

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem commute_aeval {A : Type*} [Ring A] [Algebra K A] {a b : A} (h : Commute a b)
    (P : K[X]) : Commute (aeval a P) b := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_left hq
  | monomial n c =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_left c b).mul_left (h.pow_left n)

theorem exists_irreducible_ker_ne_bot [FiniteDimensional K V] {ℓ : ℕ} (hℓ : ℓ.Prime)
    {e : Module.End K V} (he : e ^ ℓ = 1) (he1 : e ≠ 1) :
    ∃ g : K[X], Irreducible g ∧ g ∣ cyclotomic ℓ K ∧ LinearMap.ker (aeval e g) ≠ ⊥ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hΦ : ¬ Function.Injective (aeval e (cyclotomic ℓ K)) := by
    intro hinj
    have hsurj : Function.Surjective (aeval e (cyclotomic ℓ K)) :=
      LinearMap.injective_iff_surjective.mp hinj
    apply he1
    have h0 : (e - 1) * aeval e (cyclotomic ℓ K) = 0 := by
      have h1 := congrArg (aeval e) (cyclotomic_prime_mul_X_sub_one K ℓ)
      rw [map_mul, map_sub, aeval_X, map_one, map_sub, map_pow, aeval_X, map_one, he,
        sub_self] at h1
      rw [← (commute_aeval (Commute.sub_right (Commute.refl e) (Commute.one_right e))
        (cyclotomic ℓ K)).eq, h1]
    refine sub_eq_zero.mp (LinearMap.ext fun v => ?_)
    obtain ⟨w, rfl⟩ := hsurj v
    have := congrArg (fun φ : Module.End K V => φ w) h0
    simpa using this
  have key : ∀ P : K[X], P ≠ 0 → ¬ Function.Injective (aeval e P) →
      ∃ g : K[X], Irreducible g ∧ g ∣ P ∧ ¬ Function.Injective (aeval e g) := by
    intro P
    induction P using WfDvdMonoid.induction_on_irreducible with
    | zero => exact fun h => absurd rfl h
    | unit u hu =>
      intro _ hni
      exfalso
      obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.mp hu
      apply hni
      intro v w hvw
      rw [aeval_C, Algebra.algebraMap_eq_smul_one] at hvw
      simp only [LinearMap.smul_apply, Module.End.one_apply] at hvw
      exact smul_right_injective V hc.ne_zero hvw
    | mul a i ha hi ih =>
      intro _ hni
      by_cases hia : Function.Injective (aeval e a)
      · refine ⟨i, hi, dvd_mul_right i a, fun hii => hni ?_⟩
        rw [map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]
        exact hii.comp hia
      · obtain ⟨g, hg, hga, hgi⟩ := ih ha hia
        exact ⟨g, hg, dvd_mul_of_dvd_right hga i, hgi⟩
  obtain ⟨g, hg, hgd, hgi⟩ := key _ (cyclotomic_ne_zero ℓ K) hΦ
  exact ⟨g, hg, hgd, fun hbot => hgi (LinearMap.ker_eq_bot.mp hbot)⟩

theorem isCompl_ker_aeval {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) {e : Module.End K V}
    (he : e ^ ℓ = 1) {g : K[X]} (hg : Irreducible g) (hgd : g ∣ cyclotomic ℓ K) :
    ∃ h : K[X], IsCompl (LinearMap.ker (aeval e g)) (LinearMap.ker (aeval e h)) ∧
      g * h = X ^ ℓ - 1 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨h', hh'⟩ := hgd
  refine ⟨h' * (X - 1), ?_, ?_⟩
  · have hgh : g * (h' * (X - 1)) = X ^ ℓ - 1 := by
      rw [← mul_assoc, ← hh', cyclotomic_prime_mul_X_sub_one]
    have hsq : Squarefree (X ^ ℓ - 1 : K[X]) := by
      have := (separable_X_pow_sub_C (1 : K) hℓK one_ne_zero).squarefree
      rwa [map_one] at this
    have hcop : IsCoprime g (h' * (X - 1)) := by
      refine (Irreducible.coprime_iff_not_dvd hg).mpr fun hdvd => hg.not_isUnit ?_
      refine hsq g ?_
      rw [← hgh]
      exact mul_dvd_mul_left g hdvd
    refine ⟨Polynomial.disjoint_ker_aeval_of_isCoprime e hcop, ?_⟩
    rw [codisjoint_iff, Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime e hcop, hgh,
      map_sub, map_pow, aeval_X, map_one, he, sub_self, LinearMap.ker_zero]
  · rw [← mul_assoc, ← hh', cyclotomic_prime_mul_X_sub_one]

end Decomp

section Rank

variable {K : Type*} [Field K] [Finite K] {W : Type*} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem pow_apply_of_apply_eq_smul {L M : Type*} [CommRing L] [AddCommGroup M] [Module L M]
    {f : Module.End L M} {v : M} {μ : L} (h : f v = μ • v) (n : ℕ) : (f ^ n) v = μ ^ n • v := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_smul, Module.End.one_apply]
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, h, smul_smul, pow_succ]

theorem exists_rank_of_aeval_eq_zero {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0)
    {e₁ : Module.End K W} {g : K[X]} (hg : Irreducible g) (hgd : g ∣ cyclotomic ℓ K)
    (hge : aeval e₁ g = 0) :
    ∃ a : ℕ, finrank K W = ordQ K ℓ * a ∧
      (∀ T : Set (Module.End K W), (∀ x ∈ T, ∀ y ∈ T, Commute x y) → (∀ x ∈ T, Commute x e₁) →
        (∀ x ∈ T, x ^ ℓ = 1) → Nat.card T ≤ ℓ ^ a) ∧
      ∃ T : Set (Module.End K W), (∀ x ∈ T, ∀ y ∈ T, Commute x y) ∧ (∀ x ∈ T, Commute x e₁) ∧
        (∀ x ∈ T, x ^ ℓ = 1) ∧ ℓ ^ a ≤ Nat.card T := by
  have : Fact (Irreducible g) := ⟨hg⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hg0 : g ≠ 0 := hg.ne_zero
  set φ : AdjoinRoot g →ₐ[K] Module.End K W :=
    Ideal.Quotient.liftₐ (Ideal.span {g}) (aeval e₁) (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, hge, mul_zero]) with hφ
  have hφmk : ∀ P : K[X], φ (AdjoinRoot.mk g P) = aeval e₁ P := fun _ => rfl
  have hφroot : φ (AdjoinRoot.root g) = e₁ := by
    rw [← AdjoinRoot.mk_X, hφmk, aeval_X]
  let : Module (AdjoinRoot g) W := Module.compHom W φ.toRingHom
  have hsmul : ∀ (l : AdjoinRoot g) (v : W), l • v = φ l v := fun _ _ => rfl
  have : IsScalarTower K (AdjoinRoot g) W := ⟨fun a l v => by
    rw [hsmul, hsmul, map_smul, LinearMap.smul_apply]⟩
  have : Module.Finite K (AdjoinRoot g) := (AdjoinRoot.powerBasis hg0).finite
  have : Module.Finite (AdjoinRoot g) W :=
    Module.Finite.of_restrictScalars_finite K (AdjoinRoot g) W
  have hdimL : finrank K (AdjoinRoot g) = ordQ K ℓ := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis hg0), AdjoinRoot.powerBasis_dim,
      natDegree_eq_ordQ hℓ hℓK hg hgd]
  have hdim : finrank K W = ordQ K ℓ * finrank (AdjoinRoot g) W := by
    rw [← hdimL, Module.finrank_mul_finrank]
  have hζ : IsPrimitiveRoot (AdjoinRoot.root g) ℓ := by
    have : NeZero (ℓ : AdjoinRoot g) := by
      refine ⟨fun h0 => hℓK ?_⟩
      have h1 : algebraMap K (AdjoinRoot g) (ℓ : K) = 0 := by rw [map_natCast]; exact h0
      exact (injective_iff_map_eq_zero _).mp (algebraMap K (AdjoinRoot g)).injective _ h1
    rw [← isRoot_cyclotomic_iff]
    have h1 := (AdjoinRoot.isRoot_root g).dvd (map_dvd (AdjoinRoot.of g) hgd)
    rwa [map_cyclotomic] at h1
  have hcommφ : ∀ x : Module.End K W, Commute x e₁ → ∀ l, Commute x (φ l) := by
    intro x hx l
    obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective l
    rw [hφmk]
    exact (commute_aeval hx.symm P).symm
  let toL : ∀ x : Module.End K W, Commute x e₁ → Module.End (AdjoinRoot g) W := fun x hx =>
    { toFun := x
      map_add' := x.map_add
      map_smul' := fun l v => by
        rw [hsmul, hsmul, RingHom.id_apply, ← Module.End.mul_apply, (hcommφ x hx l).eq,
          Module.End.mul_apply] }
  have htoL : ∀ x hx (v : W), toL x hx v = x v := fun _ _ _ => rfl
  have : Finite (Module.End K W) := Module.finite_of_finite K
  refine ⟨finrank (AdjoinRoot g) W, hdim, fun T hTc hTe hTp => ?_, ?_⟩
  ·
    let fT : T → Module.End (AdjoinRoot g) W := fun x => toL x.1 (hTe x.1 x.2)
    have hfc : ∀ i j, Commute (fT i) (fT j) := fun i j =>
      LinearMap.ext fun v => LinearMap.congr_fun (hTc i.1 i.2 j.1 j.2).eq v
    have hfp : ∀ i, fT i ^ ℓ = 1 := fun i => LinearMap.ext fun v => by
      rw [Module.End.pow_apply, Module.End.one_apply]
      have h1 := LinearMap.congr_fun (hTp i.1 i.2) v
      rw [Module.End.pow_apply, Module.End.one_apply] at h1
      exact h1
    obtain ⟨b, μ, hb⟩ :=
      CFSG.RankThree.PartOne.exists_basis_common_eigenvectors_of_pow_eq_one hζ fT hfc hfp
    have hμp : ∀ i k, μ i k ^ ℓ = 1 := by
      intro i k
      have h1 := pow_apply_of_apply_eq_smul (hb i k) ℓ
      rw [hfp i, Module.End.one_apply] at h1
      have h2 : (μ i k ^ ℓ - 1) • b k = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right (b.ne_zero k))
    let Ψ : T → (Fin (finrank (AdjoinRoot g) W) → (nthRootsFinset ℓ (1 : AdjoinRoot g))) :=
      fun i k => ⟨μ i k, (mem_nthRootsFinset hℓ.pos 1).mpr (hμp i k)⟩
    have hΨ : Function.Injective Ψ := by
      intro i j hij
      have hf : fT i = fT j := b.ext fun k => by
        rw [hb, hb]
        have h1 : μ i k = μ j k := congrArg Subtype.val (congrFun hij k)
        rw [h1]
      exact Subtype.ext (LinearMap.ext fun v => LinearMap.congr_fun hf v)
    calc Nat.card T ≤ Nat.card (Fin (finrank (AdjoinRoot g) W) →
          (nthRootsFinset ℓ (1 : AdjoinRoot g))) := Nat.card_le_card_of_injective Ψ hΨ
      _ = (nthRootsFinset ℓ (1 : AdjoinRoot g)).card ^ finrank (AdjoinRoot g) W := by
          rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_coe]
      _ = ℓ ^ finrank (AdjoinRoot g) W := by rw [hζ.card_nthRootsFinset]
  ·
    let b := Module.finBasis (AdjoinRoot g) W
    let M : (Fin (finrank (AdjoinRoot g) W) → rootsOfUnity ℓ (AdjoinRoot g)) →
        Module.End (AdjoinRoot g) W := fun c =>
      Matrix.toLinAlgEquiv b (Matrix.diagonal fun k => (((c k : (AdjoinRoot g)ˣ)) : AdjoinRoot g))
    let D : (Fin (finrank (AdjoinRoot g) W) → rootsOfUnity ℓ (AdjoinRoot g)) →
        Module.End K W := fun c => (M c).restrictScalars K
    have hDapp : ∀ c v, D c v = M c v := fun _ _ => rfl
    have hMmul : ∀ c c', M c * M c' = M (c * c') := by
      intro c c'
      simp only [M, ← map_mul, Matrix.diagonal_mul_diagonal, Pi.mul_apply, Subgroup.coe_mul,
        Units.val_mul]
    have hDmul : ∀ c c', D c * D c' = D (c * c') := fun c c' => LinearMap.ext fun v => by
      rw [Module.End.mul_apply, hDapp, hDapp, hDapp, ← Module.End.mul_apply, hMmul]
    have hD1 : D 1 = 1 := LinearMap.ext fun v => by
      have hM1 : M 1 = 1 := by
        simp only [M, Pi.one_apply, OneMemClass.coe_one, Units.val_one, Matrix.diagonal_one,
          map_one]
      rw [hDapp, hM1, Module.End.one_apply, Module.End.one_apply]
    have hDpow : ∀ c (n : ℕ), D c ^ n = D (c ^ n) := by
      intro c n
      induction n with
      | zero => rw [pow_zero, pow_zero, hD1]
      | succ n ih => rw [pow_succ, ih, hDmul, pow_succ]
    have hcp : ∀ c : Fin (finrank (AdjoinRoot g) W) → rootsOfUnity ℓ (AdjoinRoot g), c ^ ℓ = 1 :=
      fun c => funext fun k => by
        rw [Pi.pow_apply, Pi.one_apply]
        exact Subtype.ext ((mem_rootsOfUnity ℓ _).mp (c k).2)
    have hDinj : Function.Injective D := by
      intro c c' hcc
      have hM : M c = M c' := LinearMap.ext fun v => by rw [← hDapp, ← hDapp, hcc]
      have hdiag := (Matrix.toLinAlgEquiv b).injective hM
      funext k
      have h1 := congrFun (congrFun hdiag k) k
      simp only [Matrix.diagonal_apply_eq] at h1
      exact Subtype.ext (Units.ext h1)
    refine ⟨Set.range D, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩
      change D c * D c' = D c' * D c
      rw [hDmul, hDmul, mul_comm]
    · rintro _ ⟨c, rfl⟩
      refine LinearMap.ext fun v => ?_
      rw [Module.End.mul_apply, Module.End.mul_apply, ← hφroot, ← hsmul, ← hsmul, hDapp,
        hDapp, map_smul]
    · rintro _ ⟨c, rfl⟩
      rw [hDpow, hcp, hD1]
    · rw [Nat.card_range_of_injective hDinj, Nat.card_fun, Nat.card_fin,
        hζ.card_rootsOfUnity]

theorem prodMap_pow {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : Module.End R M) (g : Module.End R N) (n : ℕ) :
    f.prodMap g ^ n = (f ^ n).prodMap (g ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, LinearMap.prodMap_one]
  | succ n ih => rw [pow_succ, ih, LinearMap.prodMap_mul, pow_succ, pow_succ]

theorem exists_ne_one_of_le_finrank {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓK : (ℓ : K) ≠ 0) (hd : ordQ K ℓ ≤ finrank K W) :
    ∃ e : Module.End K W, e ^ ℓ = 1 ∧ e ≠ 1 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hne : ¬ IsUnit (cyclotomic ℓ K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero ℓ K),
      natDegree_cyclotomic, Nat.totient_prime hℓ]
    have := hℓ.two_le
    norm_cast
    omega
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero ℓ K)
  have : Fact (Irreducible g) := ⟨hg⟩
  have hg0 : g ≠ 0 := hg.ne_zero
  have hζ : IsPrimitiveRoot (AdjoinRoot.root g) ℓ := by
    have : NeZero (ℓ : AdjoinRoot g) := by
      refine ⟨fun h0 => hℓK ?_⟩
      have h1 : algebraMap K (AdjoinRoot g) (ℓ : K) = 0 := by rw [map_natCast]; exact h0
      exact (injective_iff_map_eq_zero _).mp (algebraMap K (AdjoinRoot g)).injective _ h1
    rw [← isRoot_cyclotomic_iff]
    have h1 := (AdjoinRoot.isRoot_root g).dvd (map_dvd (AdjoinRoot.of g) hgd)
    rwa [map_cyclotomic] at h1
  have : Module.Finite K (AdjoinRoot g) := (AdjoinRoot.powerBasis hg0).finite
  have hdimL : finrank K (AdjoinRoot g) = ordQ K ℓ := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis hg0), AdjoinRoot.powerBasis_dim,
      natDegree_eq_ordQ hℓ hℓK hg hgd]
  have hfr : finrank K W = finrank K (AdjoinRoot g × (Fin (finrank K W - ordQ K ℓ) → K)) := by
    rw [Module.finrank_prod, hdimL, Module.finrank_fin_fun]
    omega
  let ι := (LinearEquiv.ofFinrankEq W (AdjoinRoot g × (Fin (finrank K W - ordQ K ℓ) → K)) hfr).symm
  let m : Module.End K (AdjoinRoot g × (Fin (finrank K W - ordQ K ℓ) → K)) :=
    (LinearMap.mulLeft K (AdjoinRoot.root g)).prodMap 1
  refine ⟨ι.conjAlgEquiv K m, ?_, fun h1 => ?_⟩
  · rw [← map_pow, prodMap_pow, LinearMap.pow_mulLeft, hζ.pow_eq_one, LinearMap.mulLeft_one,
      one_pow, ← Module.End.one_eq_id, LinearMap.prodMap_one, map_one]
  · have hm1 : m = 1 := (ι.conjAlgEquiv K).injective (by rw [h1, map_one])
    have h2 := congrArg (fun f : Module.End K _ => (f (1, 0)).1) hm1
    simp only [m, LinearMap.prodMap_apply, LinearMap.mulLeft_apply, mul_one,
      Module.End.one_apply] at h2
    exact hζ.ne_one hℓ.one_lt h2

end Rank

end OrdPNS

end CFSG.StandardType
