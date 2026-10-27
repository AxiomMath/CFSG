module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplitLinear

public section

open Polynomial Module

namespace CFSG.StandardType

namespace OrdPNS

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem coe_aeval_restrict_apply {e : Module.End K V} {p : Submodule K V}
    (hp : ∀ x ∈ p, e x ∈ p) (P : K[X]) (w : p) :
    ((aeval (e.restrict hp) P w : p) : V) = aeval e P (w : V) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      Submodule.coe_add, hP, hQ]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul,
      Module.End.pow_restrict, LinearMap.coe_restrict_apply]

theorem mapsTo_ker_aeval {e x : Module.End K V} (h : Commute e x) (P : K[X]) :
    ∀ v ∈ LinearMap.ker (aeval e P), x v ∈ LinearMap.ker (aeval e P) := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [← Module.End.mul_apply, (commute_aeval h P).eq, Module.End.mul_apply, hv, map_zero]

theorem eq_of_restrict_eq {p q : Submodule K V} (hpq : IsCompl p q) {x y : Module.End K V}
    (hp : ∀ v ∈ p, x v = y v) (hq : ∀ v ∈ q, x v = y v) : x = y := by
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ p ⊔ q := by rw [hpq.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, map_add, hp a ha, hq b hb]

theorem restrict_commute' {p : Submodule K V} {x y : Module.End K V} (h : Commute x y)
    (hx : ∀ v ∈ p, x v ∈ p) (hy : ∀ v ∈ p, y v ∈ p) : Commute (x.restrict hx) (y.restrict hy) :=
  LinearMap.restrict_commute h hx hy

theorem restrict_pow_eq_one {p : Submodule K V} {x : Module.End K V} {ℓ : ℕ} (h : x ^ ℓ = 1)
    (hx : ∀ v ∈ p, x v ∈ p) : x.restrict hx ^ ℓ = 1 := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  rw [Module.End.pow_restrict, LinearMap.coe_restrict_apply, h, Module.End.one_apply,
    Module.End.one_apply]

variable [Finite K] [FiniteDimensional K V]

theorem card_le_pow_ordQ {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0)
    (S : Set (Module.End K V)) (hSc : ∀ x ∈ S, ∀ y ∈ S, Commute x y)
    (hSp : ∀ x ∈ S, x ^ ℓ = 1) : Nat.card S ≤ ℓ ^ (finrank K V / ordQ K ℓ) := by
  induction hn : finrank K V using Nat.strong_induction_on generalizing V with
  | _ n ih =>
  have : Finite (Module.End K V) := Module.finite_of_finite K
  by_cases hS1 : ∀ x ∈ S, x = 1
  · calc Nat.card S ≤ Nat.card ({1} : Set (Module.End K V)) :=
          Nat.card_mono (Set.toFinite _) fun x hx => hS1 x hx
      _ = 1 := Nat.card_unique
      _ ≤ _ := Nat.one_le_pow _ _ hℓ.pos
  simp only [not_forall] at hS1
  obtain ⟨e, heS, he1⟩ := hS1
  obtain ⟨g, hg, hgd, hker⟩ := exists_irreducible_ker_ne_bot hℓ (hSp e heS) he1
  obtain ⟨h, hcompl, -⟩ := isCompl_ker_aeval hℓ hℓK (hSp e heS) hg hgd
  set V₁ := LinearMap.ker (aeval e g) with hV₁
  set V₂ := LinearMap.ker (aeval e h) with hV₂
  have hm : ∀ x ∈ S, ∀ P : K[X], ∀ v ∈ LinearMap.ker (aeval e P),
      x v ∈ LinearMap.ker (aeval e P) := fun x hx P => mapsTo_ker_aeval (hSc e heS x hx) P
  let r₁ : S → Module.End K V₁ := fun x => x.1.restrict (hm x.1 x.2 g)
  let r₂ : S → Module.End K V₂ := fun x => x.1.restrict (hm x.1 x.2 h)
  set e₁ : Module.End K V₁ := e.restrict (hm e heS g) with he₁
  have hge : aeval e₁ g = 0 := LinearMap.ext fun w => Subtype.ext (by
    rw [coe_aeval_restrict_apply]
    exact w.2)
  obtain ⟨a, hdim₁, hbound, -⟩ := exists_rank_of_aeval_eq_zero hℓ hℓK hg hgd hge
  have h₁ : Nat.card (Set.range r₁) ≤ ℓ ^ a := by
    refine hbound _ ?_ ?_ ?_
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      exact restrict_commute' (hSc x.1 x.2 y.1 y.2) _ _
    · rintro _ ⟨x, rfl⟩
      exact restrict_commute' (hSc x.1 x.2 e heS) _ _
    · rintro _ ⟨x, rfl⟩
      exact restrict_pow_eq_one (hSp x.1 x.2) _
  have hfr := Submodule.finrank_add_eq_of_isCompl hcompl
  have hpos : 0 < finrank K V₁ :=
    Nat.pos_of_ne_zero fun h0 => hker (Submodule.finrank_eq_zero.mp h0)
  have h₂ : Nat.card (Set.range r₂) ≤ ℓ ^ (finrank K V₂ / ordQ K ℓ) := by
    refine ih (finrank K V₂) (by omega) (Set.range r₂) ?_ ?_ rfl
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      exact restrict_commute' (hSc x.1 x.2 y.1 y.2) _ _
    · rintro _ ⟨x, rfl⟩
      exact restrict_pow_eq_one (hSp x.1 x.2) _
  let Ψ : S → Set.range r₁ × Set.range r₂ := fun x => (⟨r₁ x, x, rfl⟩, ⟨r₂ x, x, rfl⟩)
  have hΨ : Function.Injective Ψ := by
    intro x y hxy
    have h1 : r₁ x = r₁ y := congrArg (fun z => (z.1 : Module.End K V₁)) hxy
    have h2 : r₂ x = r₂ y := congrArg (fun z => (z.2 : Module.End K V₂)) hxy
    refine Subtype.ext (eq_of_restrict_eq hcompl (fun v hv => ?_) (fun v hv => ?_))
    · exact congrArg Subtype.val (LinearMap.congr_fun h1 ⟨v, hv⟩)
    · exact congrArg Subtype.val (LinearMap.congr_fun h2 ⟨v, hv⟩)
  have hpd := ordQ_pos (K := K) hℓ hℓK
  calc Nat.card S ≤ Nat.card (Set.range r₁ × Set.range r₂) := Nat.card_le_card_of_injective Ψ hΨ
    _ = Nat.card (Set.range r₁) * Nat.card (Set.range r₂) := Nat.card_prod _ _
    _ ≤ ℓ ^ a * ℓ ^ (finrank K V₂ / ordQ K ℓ) := Nat.mul_le_mul h₁ h₂
    _ = ℓ ^ (n / ordQ K ℓ) := by
      rw [← pow_add, ← hn, ← hfr, hdim₁, Nat.mul_add_div hpd]

theorem exists_card_ge_pow_ordQ {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0)
    (A : Module.End K V) (hA : A ^ ℓ = 1) :
    ∃ S : Set (Module.End K V), (∀ x ∈ S, ∀ y ∈ S, Commute x y) ∧ (∀ x ∈ S, x ^ ℓ = 1) ∧
      (∀ x ∈ S, Commute x A) ∧ ℓ ^ (finrank K V / ordQ K ℓ) ≤ Nat.card S := by
  induction hn : finrank K V using Nat.strong_induction_on generalizing V with
  | _ n ih =>
  by_cases hlt : n < ordQ K ℓ
  · refine ⟨{1}, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy
      rw [Set.mem_singleton_iff] at hx hy
      rw [hx, hy]
    · intro x hx
      rw [Set.mem_singleton_iff.mp hx, one_pow]
    · intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact Commute.one_left A
    · rw [Nat.div_eq_of_lt hlt, pow_zero, Nat.card_unique]
  obtain ⟨e, hep, he1, hAe⟩ : ∃ e : Module.End K V, e ^ ℓ = 1 ∧ e ≠ 1 ∧ (A = e ∨ A = 1) := by
    by_cases hA1 : A = 1
    · obtain ⟨e, hep, he1⟩ := exists_ne_one_of_le_finrank (W := V) hℓ hℓK (by omega)
      exact ⟨e, hep, he1, Or.inr hA1⟩
    · exact ⟨A, hA, hA1, Or.inl rfl⟩
  have hAc : Commute e A := by
    rcases hAe with hAe | hAe
    · rw [hAe]
    · rw [hAe]
      exact Commute.one_right e
  obtain ⟨g, hg, hgd, hker⟩ := exists_irreducible_ker_ne_bot hℓ hep he1
  obtain ⟨h, hcompl, -⟩ := isCompl_ker_aeval hℓ hℓK hep hg hgd
  set V₁ := LinearMap.ker (aeval e g) with hV₁
  set V₂ := LinearMap.ker (aeval e h) with hV₂
  set e₁ : Module.End K V₁ := e.restrict (mapsTo_ker_aeval (Commute.refl e) g) with he₁
  have hge : aeval e₁ g = 0 := LinearMap.ext fun w => Subtype.ext (by
    rw [coe_aeval_restrict_apply]
    exact w.2)
  obtain ⟨a, hdim₁, -, T₁, hT₁c, hT₁e, hT₁p, hT₁card⟩ :=
    exists_rank_of_aeval_eq_zero hℓ hℓK hg hgd hge
  set A₁ : Module.End K V₁ := A.restrict (mapsTo_ker_aeval hAc g) with hA₁
  set A₂ : Module.End K V₂ := A.restrict (mapsTo_ker_aeval hAc h) with hA₂
  have hT₁A : ∀ t ∈ T₁, Commute t A₁ := by
    intro t ht
    rcases hAe with hAe | hAe
    · have : A₁ = e₁ := LinearMap.ext fun w => Subtype.ext (by
        rw [LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply, hAe])
      rw [this]
      exact hT₁e t ht
    · have : A₁ = 1 := LinearMap.ext fun w => Subtype.ext (by
        rw [LinearMap.coe_restrict_apply, hAe, Module.End.one_apply, Module.End.one_apply])
      rw [this]
      exact Commute.one_right t
  have hfr := Submodule.finrank_add_eq_of_isCompl hcompl
  have hpos : 0 < finrank K V₁ :=
    Nat.pos_of_ne_zero fun h0 => hker (Submodule.finrank_eq_zero.mp h0)
  obtain ⟨T₂, hT₂c, hT₂p, hT₂A, hT₂card⟩ :=
    ih (finrank K V₂) (by omega) A₂ (restrict_pow_eq_one hA _) rfl
  set ι := Submodule.prodEquivOfIsCompl V₁ V₂ hcompl with hι
  let Φ : Module.End K V₁ × Module.End K V₂ → Module.End K V := fun t =>
    ι.conjAlgEquiv K (t.1.prodMap t.2)
  have hΦmul : ∀ t s, Φ t * Φ s = Φ (t * s) := fun t s => by
    simp only [Φ, ← map_mul, LinearMap.prodMap_mul, Prod.fst_mul, Prod.snd_mul]
  have hΦpow : ∀ t (k : ℕ), Φ t ^ k = Φ (t ^ k) := fun t k => by
    simp only [Φ, ← map_pow, prodMap_pow, Prod.pow_fst, Prod.pow_snd]
  have hΦ1 : Φ 1 = 1 := by
    simp only [Φ, Prod.fst_one, Prod.snd_one, LinearMap.prodMap_one, map_one]
  have hΦinj : Function.Injective Φ := by
    intro t s hts
    have h1 : t.1.prodMap t.2 = s.1.prodMap s.2 := (ι.conjAlgEquiv K).injective hts
    refine Prod.ext (LinearMap.ext fun w => ?_) (LinearMap.ext fun w => ?_)
    · have := congrArg Prod.fst (LinearMap.congr_fun h1 (w, 0))
      simpa using this
    · have := congrArg Prod.snd (LinearMap.congr_fun h1 (0, w))
      simpa using this
  have hΦA : Φ (A₁, A₂) = A := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨w, rfl⟩ := ι.surjective v
    change ι ((A₁.prodMap A₂) (ι.symm (ι w))) = A (ι w)
    rw [LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, hι,
      Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', map_add]
    rfl
  refine ⟨Φ '' (T₁ ×ˢ T₂), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩ _ ⟨s, hs, rfl⟩
    change Φ t * Φ s = Φ s * Φ t
    rw [hΦmul, hΦmul]
    exact congrArg Φ (Prod.ext (hT₁c _ ht.1 _ hs.1).eq (hT₂c _ ht.2 _ hs.2).eq)
  · rintro _ ⟨t, ht, rfl⟩
    rw [hΦpow, ← hΦ1]
    exact congrArg Φ (Prod.ext (hT₁p _ ht.1) (hT₂p _ ht.2))
  · rintro _ ⟨t, ht, rfl⟩
    rw [← hΦA]
    change Φ t * Φ (A₁, A₂) = Φ (A₁, A₂) * Φ t
    rw [hΦmul, hΦmul]
    exact congrArg Φ (Prod.ext (hT₁A _ ht.1).eq (hT₂A _ ht.2).eq)
  · have hpd := ordQ_pos (K := K) hℓ hℓK
    rw [Nat.card_image_of_injective hΦinj, Nat.card_congr (Equiv.Set.prod T₁ T₂), Nat.card_prod,
      ← hn, ← hfr, hdim₁, Nat.mul_add_div hpd, pow_add]
    exact Nat.mul_le_mul hT₁card hT₂card

section Matrix

variable {K : Type*} [Field K] [Finite K] {n : ℕ}

theorem card_le_pow_ordQ_matrix {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0)
    (S : Set (Matrix (Fin n) (Fin n) K)) (hSc : ∀ x ∈ S, ∀ y ∈ S, Commute x y)
    (hSp : ∀ x ∈ S, x ^ ℓ = 1) : Nat.card S ≤ ℓ ^ (n / ordQ K ℓ) := by
  have h := card_le_pow_ordQ (V := Fin n → K) hℓ hℓK (Matrix.toLinAlgEquiv' '' S)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact (hSc x hx y hy).map _)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hSp x hx, map_one])
  rwa [Nat.card_image_of_injective Matrix.toLinAlgEquiv'.injective, Module.finrank_fin_fun] at h

theorem exists_card_ge_pow_ordQ_matrix {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0)
    (A : Matrix (Fin n) (Fin n) K) (hA : A ^ ℓ = 1) :
    ∃ S : Set (Matrix (Fin n) (Fin n) K), (∀ x ∈ S, ∀ y ∈ S, Commute x y) ∧
      (∀ x ∈ S, x ^ ℓ = 1) ∧ (∀ x ∈ S, Commute x A) ∧ ℓ ^ (n / ordQ K ℓ) ≤ Nat.card S := by
  obtain ⟨S, hSc, hSp, hSA, hcard⟩ := exists_card_ge_pow_ordQ (V := Fin n → K) hℓ hℓK
    (Matrix.toLinAlgEquiv' A) (by rw [← map_pow, hA, map_one])
  refine ⟨Matrix.toLinAlgEquiv'.symm '' S, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (hSc x hx y hy).map _
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hSp x hx, map_one]
  · rintro _ ⟨x, hx, rfl⟩
    have h := (hSA x hx).map Matrix.toLinAlgEquiv'.symm
    rwa [AlgEquiv.symm_apply_apply] at h
  · rw [Module.finrank_fin_fun] at hcard
    rwa [Nat.card_image_of_injective Matrix.toLinAlgEquiv'.symm.injective]

theorem exists_card_ge_pow_ordQ_fixed {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0)
    {σ : K ≃+* K} (hσ : orderOf σ = ℓ) :
    ∃ S : Set (Matrix (Fin n) (Fin n) K), (∀ x ∈ S, ∀ y ∈ S, Commute x y) ∧
      (∀ x ∈ S, x ^ ℓ = 1) ∧ (∀ x ∈ S, x.map σ = x) ∧ ℓ ^ (n / ordQ K ℓ) ≤ Nat.card S := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite (K ≃+* K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
    fun a b hab => RingEquiv.ext (congrFun hab)
  have : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
  set K₀ := FixedPoints.subfield (Subgroup.zpowers σ) K with hK₀
  have hfr : finrank K₀ K = ℓ := by
    rw [hK₀, FixedPoints.finrank_eq_card, ← Nat.card_eq_fintype_card, Nat.card_zpowers, hσ]
  have hfix : ∀ a : K₀, σ (a : K) = a := fun a =>
    a.2 ⟨σ, Subgroup.mem_zpowers σ⟩
  have hℓK₀ : (ℓ : K₀) ≠ 0 := fun h0 => hℓK (by
    have := congrArg (fun a : K₀ => (a : K)) h0
    simpa using this)
  have hcard : Nat.card K = Nat.card K₀ ^ ℓ := by
    have : Fintype K := Fintype.ofFinite K
    have : Fintype K₀ := Fintype.ofFinite K₀
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := K₀) (V := K), hfr]
  have hord : ordQ K₀ ℓ = ordQ K ℓ := by
    rw [ordQ_def, ordQ_def, hcard, Nat.cast_pow, ZMod.pow_card]
  obtain ⟨S₀, hc, hp, -, hcard₀⟩ :=
    exists_card_ge_pow_ordQ_matrix (K := K₀) (n := n) hℓ hℓK₀ 1 (one_pow _)
  set ι : Matrix (Fin n) (Fin n) K₀ →+* Matrix (Fin n) (Fin n) K := K₀.subtype.mapMatrix
  have hι : Function.Injective ι := Matrix.map_injective Subtype.val_injective
  refine ⟨ι '' S₀, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (hc x hx y hy).map ι
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hp x hx, map_one]
  · rintro _ ⟨x, -, rfl⟩
    ext i j
    simp only [ι, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact hfix (x i j)
  · rwa [Nat.card_image_of_injective hι, ← hord]

end Matrix

end OrdPNS

end CFSG.StandardType
