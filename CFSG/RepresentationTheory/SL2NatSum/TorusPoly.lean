module

public import CFSG.LocalAnalysis.UniquenessCase.UCHigmanDesc
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.Algebra.Algebra.ZMod

public section

namespace CFSG.RepresentationTheory.SL2NatSum

open Polynomial CFSG.LocalAnalysis.UniquenessCase.UCK.Higman
open scoped MatrixGroups

section TorusPoly

variable {K : Type*} [Field K] [CharP K 2]

private lemma prod_range_shift {M : Type*} [CommMonoid M] (F : ℕ → M) :
    ∀ n : ℕ, F n = F 0 → (∏ i ∈ Finset.range n, F (i + 1)) = ∏ i ∈ Finset.range n, F i
  | 0, _ => by simp
  | m + 1, hn => by
      rw [Finset.prod_range_succ (fun i => F (i + 1)) m]
      rw [Finset.prod_range_succ' F m, hn]

private lemma torus_factor_map (t : K) (i : ℕ) :
    Polynomial.map (frobenius K 2)
        ((X - C (t ^ 2 ^ i)) * (X - C (t⁻¹ ^ 2 ^ i))) =
      (X - C (t ^ 2 ^ (i + 1))) * (X - C (t⁻¹ ^ 2 ^ (i + 1))) := by
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  have hpow : ∀ a : K, (a ^ 2 ^ i) ^ 2 = a ^ 2 ^ (i + 1) := by
    intro a
    rw [← pow_mul, pow_succ]
  rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, frobenius_def,
    frobenius_def, hpow t, hpow t⁻¹]

private lemma map_frobenius_torusProd [Fintype K] {n : ℕ}
    (hn : Fintype.card K = 2 ^ n) (t : K) :
    Polynomial.map (frobenius K 2)
        (∏ i ∈ Finset.range n, (X - C (t ^ 2 ^ i)) * (X - C (t⁻¹ ^ 2 ^ i))) =
      ∏ i ∈ Finset.range n, (X - C (t ^ 2 ^ i)) * (X - C (t⁻¹ ^ 2 ^ i)) := by
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  have hpow : ∀ a : K, a ^ 2 ^ n = a := by
    intro a
    rw [← hn, FiniteField.pow_card]
  rw [Polynomial.map_prod]
  have hcongr : (∏ i ∈ Finset.range n,
        Polynomial.map (frobenius K 2) ((X - C (t ^ 2 ^ i)) * (X - C (t⁻¹ ^ 2 ^ i)))) =
      ∏ i ∈ Finset.range n, (X - C (t ^ 2 ^ (i + 1))) * (X - C (t⁻¹ ^ 2 ^ (i + 1))) :=
    Finset.prod_congr rfl fun i _ => torus_factor_map t i
  rw [hcongr]
  exact prod_range_shift
    (fun j => (X - C (t ^ 2 ^ j)) * (X - C (t⁻¹ ^ 2 ^ j))) n (by simp [hpow t, hpow t⁻¹])

theorem exists_torusPoly {K : Type*} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (hn : Fintype.card K = 2 ^ n) (t : K) :
    ∃ p₀ : (ZMod 2)[X], p₀.map (ZMod.castHom (dvd_refl 2) K) =
      ∏ i ∈ Finset.range n, (X - C (t ^ 2 ^ i)) * (X - C (t⁻¹ ^ 2 ^ i)) := by
  classical
  let p : K[X] := ∏ i ∈ Finset.range n, (X - C (t ^ 2 ^ i)) * (X - C (t⁻¹ ^ 2 ^ i))
  have hfixed : Polynomial.map (frobenius K 2) p = p := map_frobenius_torusProd hn t
  have hcoeff : ∀ j, p.coeff j ∈ Set.range (ZMod.castHom (dvd_refl 2) K) := by
    intro j
    have h := congrArg (fun q : K[X] => q.coeff j) hfixed
    simp only [Polynomial.coeff_map, frobenius_def] at h
    have hmul : p.coeff j * (p.coeff j - 1) = 0 := by
      rw [mul_sub, mul_one, ← pow_two, sub_eq_zero]
      exact h
    rcases mul_eq_zero.1 hmul with h0 | h1
    · exact ⟨0, by simp [h0]⟩
    · exact ⟨1, by simp [sub_eq_zero.1 h1]⟩
  have hlifts : p ∈ Polynomial.lifts (ZMod.castHom (dvd_refl 2) K) :=
    (Polynomial.lifts_iff_coeff_lifts p).2 hcoeff
  obtain ⟨p₀, hp₀⟩ :=
    (Polynomial.mem_lifts (f := ZMod.castHom (dvd_refl 2) K) p).1 hlifts
  exact ⟨p₀, hp₀⟩

end TorusPoly

section Diag

variable {K : Type} [Field K] [CharP K 2]

open Matrix

private lemma zmod_two_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  decide +revert

private lemma algebraMap_zmod_two_eq_castHom [Algebra (ZMod 2) K] (a : ZMod 2) :
    algebraMap (ZMod 2) K a = ZMod.castHom (dvd_refl 2) K a := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;> simp

private lemma AmatK_hMat (i : ℕ) (t : Kˣ) :
    AmatK i (hMat t) =
      !![((t : K) ^ 2 ^ i), 0; 0, (((t : K)⁻¹) ^ 2 ^ i)] := by
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [AmatK, iterateFrobenius_def, coe_hMat]

private lemma diag_mulVec (α β : K) (w : Fin 2 → K) :
    (!![α, 0; 0, β] : Matrix (Fin 2) (Fin 2) K) *ᵥ w = ![α * w 0, β * w 1] := by
  ext j
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private def diagLin [Algebra (ZMod 2) K] (α β : K) :
    (Fin 2 → K) →ₗ[ZMod 2] (Fin 2 → K) where
  toFun w := ![α * w 0, β * w 1]
  map_add' w v := by
    ext j
    fin_cases j <;> simp [mul_add]
  map_smul' c w := by
    rcases zmod_two_eq_zero_or_one c with rfl | rfl <;> simp

private lemma diagLin_pow_apply [Algebra (ZMod 2) K] (α β : K) (n : ℕ)
    (w : Fin 2 → K) :
    ((diagLin α β) ^ n) w = ![α ^ n * w 0, β ^ n * w 1] := by
  induction n with
  | zero => ext j; fin_cases j <;> simp
  | succ n ih =>
      rw [pow_succ']
      simp only [Module.End.mul_apply]
      rw [ih]
      ext j
      fin_cases j <;> simp [diagLin, pow_succ, mul_assoc, mul_left_comm, mul_comm]

private lemma aeval_diagLin_apply [Algebra (ZMod 2) K] (p : (ZMod 2)[X]) (α β : K)
    (w : Fin 2 → K) :
    aeval (diagLin α β) p w =
      ![p.eval₂ (ZMod.castHom (dvd_refl 2) K) α * w 0,
        p.eval₂ (ZMod.castHom (dvd_refl 2) K) β * w 1] := by
  rw [Polynomial.aeval_endomorphism, Polynomial.eval₂_eq_sum, Polynomial.eval₂_eq_sum,
    Polynomial.sum_def]
  ext j
  fin_cases j <;>
    simp [Polynomial.sum_def, Finset.sum_apply, diagLin_pow_apply, Algebra.smul_def,
      algebraMap_zmod_two_eq_castHom, Finset.sum_mul, mul_assoc]

private lemma aeval_diagLin_eq_zero [Algebra (ZMod 2) K] (p : (ZMod 2)[X]) (α β : K)
    (hα : p.eval₂ (ZMod.castHom (dvd_refl 2) K) α = 0)
    (hβ : p.eval₂ (ZMod.castHom (dvd_refl 2) K) β = 0) :
    aeval (diagLin α β) p = 0 := by
  refine LinearMap.ext fun w => ?_
  rw [aeval_diagLin_apply]
  ext j
  fin_cases j <;> simp [hα, hβ]

lemma aeval_comp_apply {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (A : Module.End R M)
    (B : Module.End R N) (h : ∀ x, f (A x) = B (f x)) (p : R[X]) (x : M) :
    f (aeval A p x) = aeval B p (f x) := by
  have hpow : ∀ n : ℕ, ∀ x : M, f ((A ^ n) x) = (B ^ n) (f x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [pow_succ, Module.End.mul_apply, ih, h]
        rw [pow_succ, Module.End.mul_apply]
  rw [Polynomial.aeval_endomorphism, Polynomial.aeval_endomorphism, Polynomial.sum_def,
    Polynomial.sum_def, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_smul, hpow n x]

end Diag

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private lemma exists_atom_subrepresentation {A G V : Type*} [Semiring A] [Monoid G]
    [AddCommMonoid V] [Module A V] [Finite V] [Nontrivial V]
    (ρ : Representation A G V) : ∃ N : Subrepresentation ρ, IsAtom N := by
  haveI : Finite (Subrepresentation ρ) :=
    Finite.of_injective (fun N : Subrepresentation ρ => (N.toSubmodule : Set V))
      (fun N M h => Subrepresentation.toSubmodule_injective (SetLike.coe_injective h))
  have htop : (⊤ : Subrepresentation ρ) ≠ ⊥ := by
    intro h
    have hsub : (⊤ : Submodule A V) = ⊥ := congrArg Subrepresentation.toSubmodule h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have : v ∈ (⊥ : Submodule A V) := by
      rw [← hsub]
      exact Submodule.mem_top
    exact hv ((Submodule.mem_bot (R := A) (M := V)).1 this)
  obtain ⟨N, hNat, _⟩ :=
    (IsAtomic.eq_bot_or_exists_atom_le (⊤ : Subrepresentation ρ)).resolve_left htop
  exact ⟨N, hNat⟩

private lemma simple_toRepresentation {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (N : Subrepresentation ρ) (hNat : IsAtom N) :
    ∀ W : Submodule (ZMod 2) N.toSubmodule,
      (∀ (g : SL(2, K)), ∀ w ∈ W, N.toRepresentation g w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  let W' : Subrepresentation ρ :=
    { toSubmodule := W.map N.toSubmodule.subtype
      apply_mem_toSubmodule := by
        intro g v hv
        rw [Submodule.mem_map] at hv
        obtain ⟨w, hw, rfl⟩ := hv
        exact ⟨N.toRepresentation g w, hW g w hw, rfl⟩ }
  have hle : W' ≤ N := by
    intro v hv
    change v ∈ Submodule.map N.toSubmodule.subtype W at hv
    rw [Submodule.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.2
  rcases (hNat.le_iff.mp hle) with hbot | htop
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx' : N.toSubmodule.subtype x ∈ W'.toSubmodule := ⟨x, hx, rfl⟩
    rw [hbot] at hx'
    have hx0 : (x : V) = 0 := (Submodule.mem_bot (R := ZMod 2) (M := V)).1 hx'
    exact Subtype.ext hx0
  · right
    rw [Submodule.eq_top_iff']
    intro x
    have hx' : N.toSubmodule.subtype x ∈ W'.toSubmodule := by
      rw [htop]
      exact x.2
    change N.toSubmodule.subtype x ∈ W.map N.toSubmodule.subtype at hx'
    rw [Submodule.mem_map] at hx'
    obtain ⟨w, hw, hwx⟩ := hx'
    have hw_eq : w = x := Subtype.ext (by simpa using hwx)
    simpa [hw_eq] using hw

private lemma aeval_zero_on_atom {n : ℕ}
    (hn : Nat.card K = 2 ^ n) (t : Kˣ) (p₀ : (ZMod 2)[X])
    (hp₀ : ∀ i < n, p₀.eval₂ (ZMod.castHom (dvd_refl 2) K) ((t : K) ^ 2 ^ i) = 0 ∧
      p₀.eval₂ (ZMod.castHom (dvd_refl 2) K) ((t : K)⁻¹ ^ 2 ^ i) = 0)
    (d : SL(2, K)) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) SL(2, K) V)
    (hdV : ∀ v : V, ρ d (ρ d v) + ρ d v + v = 0)
    (N : Subrepresentation ρ) (hNat : IsAtom N) (hNne : N.toSubmodule ≠ ⊥) :
    aeval (N.toRepresentation (hMat t)) p₀ = 0 := by
  classical
  haveI : Nontrivial N.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hNne
  letI : Algebra (ZMod 2) K := ZMod.algebra' K 2 (dvd_refl 2)
  have hdN : ∀ v : N.toSubmodule,
      N.toRepresentation d (N.toRepresentation d v) + N.toRepresentation d v + v = 0 := by
    intro v
    apply Subtype.ext
    show ρ d (ρ d (v : V)) + ρ d (v : V) + (v : V) = 0
    exact hdV (v : V)
  obtain ⟨i, hi, ψ, hψ⟩ :=
    descent_natural hn N.toRepresentation (simple_toRepresentation ρ N hNat) d hd3 hd1 hdN
  let α : K := (t : K) ^ 2 ^ i
  let β : K := ((t : K)⁻¹) ^ 2 ^ i
  have hα : p₀.eval₂ (ZMod.castHom (dvd_refl 2) K) α = 0 := (hp₀ i hi).1
  have hβ : p₀.eval₂ (ZMod.castHom (dvd_refl 2) K) β = 0 := (hp₀ i hi).2
  let ψl : N.toSubmodule ≃ₗ[ZMod 2] (Fin 2 → K) :=
    ψ.toLinearEquiv (fun c x => by
      rcases zmod_two_eq_zero_or_one c with rfl | rfl <;> simp)
  have hconj : ∀ x : N.toSubmodule,
      ψl (N.toRepresentation (hMat t) x) = diagLin α β (ψl x) := by
    intro x
    change ψ (N.toRepresentation (hMat t) x) = diagLin α β (ψ x)
    rw [hψ (hMat t) x, AmatK_hMat i t, diag_mulVec]
    rfl
  have hBzero : aeval (diagLin α β) p₀ = 0 := aeval_diagLin_eq_zero p₀ α β hα hβ
  refine LinearMap.ext fun x => ?_
  have hx := aeval_comp_apply ψl.toLinearMap (N.toRepresentation (hMat t))
    (diagLin α β) hconj p₀ x
  rw [hBzero, LinearMap.zero_apply] at hx
  exact ψl.injective (by simpa using hx)

private lemma quotient_d_condition {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (d : SL(2, K))
    (hdV : ∀ v : V, ρ d (ρ d v) + ρ d v + v = 0) (N : Subrepresentation ρ) :
    ∀ x : V ⧸ N.toSubmodule,
      N.quotient d (N.quotient d x) + N.quotient d x + x = 0 := by
  intro x
  refine Submodule.Quotient.induction_on (p := N.toSubmodule) x ?_
  intro v
  have h1 : N.quotient d (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (ρ d v) :=
    Subrepresentation.quotient_apply_mk N d v
  have h2 : N.quotient d (Submodule.Quotient.mk (ρ d v)) =
      Submodule.Quotient.mk (ρ d (ρ d v)) :=
    Subrepresentation.quotient_apply_mk N d (ρ d v)
  rw [h1, h2, ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_add, hdV v,
    Submodule.Quotient.mk_zero]

private lemma aeval_pow_succ_eq_zero {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (t : Kˣ) (p₀ : (ZMod 2)[X])
    (N : Subrepresentation ρ) (k' : ℕ)
    (hNzero : aeval (N.toRepresentation (hMat t)) p₀ = 0)
    (hk' : aeval (N.quotient (hMat t)) p₀ ^ k' = 0) :
    aeval (ρ (hMat t)) p₀ ^ (k' + 1) = 0 := by
  let T : Module.End (ZMod 2) V := aeval (ρ (hMat t)) p₀
  have hTvan : ∀ x : V, x ∈ N.toSubmodule → T x = 0 := by
    intro x hx
    have hinc : ∀ y : N.toSubmodule,
        N.toSubmodule.subtype (aeval (N.toRepresentation (hMat t)) p₀ y) =
          T (N.toSubmodule.subtype y) := by
      intro y
      exact aeval_comp_apply N.toSubmodule.subtype (N.toRepresentation (hMat t))
        (ρ (hMat t)) (fun z => rfl) p₀ y
    have hy := hinc ⟨x, hx⟩
    rw [hNzero, LinearMap.zero_apply, map_zero] at hy
    exact hy.symm
  have hqT : ∀ v : V, N.toSubmodule.mkQ ((T ^ k') v) = 0 := by
    intro v
    have hconjQ := aeval_comp_apply N.toSubmodule.mkQ (ρ (hMat t))
      (N.quotient (hMat t))
      (fun x => (Subrepresentation.quotient_apply_mk N (hMat t) x).symm)
      (p₀ ^ k') v
    simpa [map_pow, hk'] using hconjQ
  change T ^ (k' + 1) = 0
  ext v
  rw [pow_succ']
  simp only [Module.End.mul_apply]
  exact hTvan _ ((Submodule.Quotient.mk_eq_zero N.toSubmodule).1 (hqT v))

theorem exists_pow_aeval_eq_zero {n : ℕ}
    (hn : Nat.card K = 2 ^ n) (t : Kˣ) (p₀ : (ZMod 2)[X])
    (hp₀ : ∀ i < n, p₀.eval₂ (ZMod.castHom (dvd_refl 2) K) ((t : K) ^ 2 ^ i) = 0 ∧
      p₀.eval₂ (ZMod.castHom (dvd_refl 2) K) ((t : K)⁻¹ ^ 2 ^ i) = 0)
    (d : SL(2, K)) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) SL(2, K) V)
    (hdV : ∀ v : V, ρ d (ρ d v) + ρ d v + v = 0) :
    ∃ k : ℕ, aeval (ρ (hMat t)) p₀ ^ k = 0 := by
  classical
  have hmain : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (ρ : Representation (ZMod 2) SL(2, K) V), Nat.card V = m →
      (∀ v : V, ρ d (ρ d v) + ρ d v + v = 0) →
      ∃ k : ℕ, aeval (ρ (hMat t)) p₀ ^ k = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro V _ _ _ ρ hcard hdVV
      by_cases hsub : Subsingleton V
      · refine ⟨1, ?_⟩
        rw [pow_one]
        ext v
        exact Subsingleton.elim _ _
      · haveI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
        obtain ⟨N, hNat⟩ := exists_atom_subrepresentation ρ
        have hNne : N.toSubmodule ≠ ⊥ := by
          intro h
          apply hNat.ne_bot
          refine Subrepresentation.toSubmodule_injective ?_
          rw [h]
          rfl
        haveI : Nontrivial N.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hNne
        have hNzero : aeval (N.toRepresentation (hMat t)) p₀ = 0 :=
          aeval_zero_on_atom hn t p₀ hp₀ d hd3 hd1 ρ hdVV N hNat hNne
        have hcardV : Nat.card V =
            Nat.card N.toSubmodule * Nat.card (V ⧸ N.toSubmodule) :=
          Submodule.card_eq_card_quotient_mul_card N.toSubmodule
        let Q := V ⧸ N.toSubmodule
        haveI : Finite Q :=
          Finite.of_surjective N.toSubmodule.mkQ (Submodule.mkQ_surjective N.toSubmodule)
        have hQlt : Nat.card Q < m := by
          have hQpos : 0 < Nat.card Q := Nat.card_pos
          have hlt : Nat.card Q < Nat.card V := by
            rw [hcardV]
            exact lt_mul_of_one_lt_left hQpos (Finite.one_lt_card (α := N.toSubmodule))
          rwa [hcard] at hlt
        obtain ⟨k', hk'⟩ :=
          ih (Nat.card Q) hQlt Q N.quotient rfl (quotient_d_condition ρ d hdVV N)
        exact ⟨k' + 1, aeval_pow_succ_eq_zero ρ t p₀ N k' hNzero hk'⟩
  exact hmain (Nat.card V) V ρ rfl hdV

end Main

end CFSG.RepresentationTheory.SL2NatSum
