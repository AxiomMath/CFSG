module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Semisimple

public section

namespace CFSG.RankThree.GF2n.Tim79a

open Polynomial

theorem card_simple_zmodTwoPoly_of_semiregular (m : ℕ) (hm : 1 ≤ m) (M : Type*)
    [AddCommGroup M] [Module (ZMod 2)[X] M] [Finite M] [IsSimpleModule (ZMod 2)[X] M]
    (h1 : ∀ y : M, (X ^ (2 ^ m - 1) : (ZMod 2)[X]) • y = y)
    (h2 : ∀ i, 0 < i → i < 2 ^ m - 1 → ∀ y : M, (X ^ i : (ZMod 2)[X]) • y = y → y = 0) :
    Nat.card M = 2 ^ m := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule (ZMod 2)[X] M›
  letI : Field ((ZMod 2)[X] ⧸ I) := Ideal.Quotient.field I
  haveI : Finite ((ZMod 2)[X] ⧸ I) := Finite.of_equiv M e.toEquiv
  letI : Fintype ((ZMod 2)[X] ⧸ I) := Fintype.ofFinite _
  have key : ∀ q : (ZMod 2)[X], (∀ y : M, q • y = y) ↔ Ideal.Quotient.mk I q = 1 := by
    intro q
    constructor
    · intro hq
      have := congrArg e (hq (e.symm 1))
      rw [map_smul, LinearEquiv.apply_symm_apply, Algebra.smul_def, mul_one,
        Ideal.Quotient.algebraMap_eq] at this
      exact this
    · intro hq y
      apply e.injective
      rw [map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, hq, one_mul]
  have h2m : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  set ζ : (ZMod 2)[X] ⧸ I := Ideal.Quotient.mk I X with hζ
  have hζn : ζ ^ (2 ^ m - 1) = 1 := by
    rw [hζ, ← map_pow]
    exact (key _).mp h1
  have hζi : ∀ i, 0 < i → i < 2 ^ m - 1 → ζ ^ i ≠ 1 := by
    intro i hi0 hin hζ1
    have hall : ∀ y : M, (X ^ i : (ZMod 2)[X]) • y = y := (key _).mpr (by rw [map_pow]; exact hζ1)
    haveI := IsSimpleModule.nontrivial (ZMod 2)[X] M
    obtain ⟨y, hy⟩ := exists_ne (0 : M)
    exact hy (h2 i hi0 hin y (hall y))
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hζn
    exact zero_ne_one hζn
  have hlow : 2 ^ m ≤ Fintype.card ((ZMod 2)[X] ⧸ I) := by
    have h := FiniteField.pow_card_sub_one_eq_one ζ hζ0
    have hc : 1 < Fintype.card ((ZMod 2)[X] ⧸ I) := Fintype.one_lt_card
    by_contra hle
    have hlt := Nat.lt_of_not_le hle
    exact hζi _ (by omega) (by omega) h
  haveI : CharP ((ZMod 2)[X] ⧸ I) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) _).injective 2
  haveI : ExpChar ((ZMod 2)[X] ⧸ I) 2 := ExpChar.prime Nat.prime_two
  have hfrob : ∀ x : (ZMod 2)[X] ⧸ I, x ^ 2 ^ m = x := by
    have hext : (iterateFrobenius ((ZMod 2)[X] ⧸ I) 2 m).comp (Ideal.Quotient.mk I) =
        Ideal.Quotient.mk I := by
      apply Polynomial.ringHom_ext
      · intro a
        rw [RingHom.comp_apply, iterateFrobenius_def, ← map_pow, ← map_pow, ZMod.pow_card_pow]
      · rw [RingHom.comp_apply, iterateFrobenius_def, ← hζ]
        have : 2 ^ m = (2 ^ m - 1) + 1 := by omega
        rw [this, pow_succ, hζn, one_mul]
    intro x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    have := RingHom.congr_fun hext g
    rwa [RingHom.comp_apply, iterateFrobenius_def] at this
  have hup : Fintype.card ((ZMod 2)[X] ⧸ I) ≤ 2 ^ m := by
    have hm0 : m ≠ 0 := by omega
    have := card_le_degree_of_subset_roots (R := (ZMod 2)[X] ⧸ I) (p := X ^ 2 ^ m - X)
      (Z := Finset.univ) (fun x _ => by
        rw [mem_roots']
        refine ⟨FiniteField.X_pow_card_pow_sub_X_ne_zero _ hm0 one_lt_two, ?_⟩
        simp [IsRoot.def, hfrob x])
    rwa [FiniteField.X_pow_card_pow_sub_X_natDegree_eq _ hm0 one_lt_two, Finset.card_univ] at this
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  exact le_antisymm hup hlow

end CFSG.RankThree.GF2n.Tim79a

namespace CFSG.RankThree.GF2n.Tim79a

open Polynomial

theorem iSupIndep_restrictScalars_of_iSupIndep {S R M ι : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]
    {N : ι → Submodule R M} (hN : iSupIndep N) :
    iSupIndep (fun i => (N i).restrictScalars S) := by
  intro i
  have h := hN i
  rw [disjoint_iff] at h ⊢
  have hsup : (⨆ (j) (_ : j ≠ i), (N j).restrictScalars S) =
      (⨆ (j) (_ : j ≠ i), N j).restrictScalars S := by
    simp only [Submodule.restrictScalars_iSup]
  rw [hsup, ← Submodule.restrictScalars_inf, h, Submodule.restrictScalars_bot]

theorem cyclicSemiregularDecomp_holds :
    ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [Finite E] (m : ℕ), 1 ≤ m →
      ∀ (h : E ≃ₗ[ZMod 2] E), orderOf h = 2 ^ m - 1 →
      (∀ i : ℕ, 0 < i → i < 2 ^ m - 1 → ∀ x : E, ((h ^ i) x = x → x = 0)) →
      ∃ (ι : Type) (_ : Fintype ι) (S : ι → Submodule (ZMod 2) E),
        (∀ j, ∀ x ∈ S j, h x ∈ S j) ∧ (∀ j, Nat.card (S j) = 2 ^ m) ∧
        iSupIndep S ∧ (⨆ j, S j) = ⊤ := by
  intro E _ _ _ m hm h hord hfpf
  classical
  obtain ⟨f, hf⟩ : ∃ f : Module.End (ZMod 2) E, f = h.toLinearMap := ⟨_, rfl⟩
  have hpow : ∀ i : ℕ, ∀ x : E, (f ^ i) x = (h ^ i) x := by
    intro i x
    rw [hf, Module.End.coe_pow, LinearEquiv.coe_pow]
    rfl
  have hfn : f ^ (2 ^ m - 1) = 1 := by
    ext x
    rw [hpow, ← hord, pow_orderOf_eq_one]
    rfl
  have hodd : ((2 ^ m - 1 : ℕ) : ZMod 2) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    obtain ⟨k, hk⟩ : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    have h2m : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    generalize 2 ^ m = t at hk h2m ⊢
    omega
  have hsq : Squarefree (X ^ (2 ^ m - 1) - 1 : (ZMod 2)[X]) := by
    have := (Polynomial.separable_X_pow_sub_C (1 : ZMod 2) hodd one_ne_zero).squarefree
    rwa [map_one] at this
  have hss : IsSemisimpleModule (ZMod 2)[X] (Module.AEval' f) :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq (by simp [hfn])
  obtain ⟨s, hind, htop, hsimple⟩ :=
    IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top (ZMod 2)[X] (Module.AEval' f)
  haveI : Finite (Module.AEval' f) := Finite.of_equiv E (Module.AEval'.of f).toEquiv
  haveI : Finite (Submodule (ZMod 2)[X] (Module.AEval' f)) :=
    Finite.of_injective (fun N : Submodule (ZMod 2)[X] (Module.AEval' f) =>
      (N : Set (Module.AEval' f))) SetLike.coe_injective
  let Ψ : Submodule (ZMod 2)[X] (Module.AEval' f) → Submodule (ZMod 2) E :=
    fun N => (Submodule.orderIsoMapComap (Module.AEval'.of f)).symm (N.restrictScalars (ZMod 2))
  have hmemΨ : ∀ N x, x ∈ Ψ N ↔ Module.AEval'.of f x ∈ N := fun N x => Iff.rfl
  refine ⟨s, Fintype.ofFinite s, fun j => Ψ j, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    rw [hmemΨ] at hx ⊢
    have h1 := (j : Submodule (ZMod 2)[X] (Module.AEval' f)).smul_mem (X : (ZMod 2)[X]) hx
    rw [Module.AEval'.X_smul_of] at h1
    have hfx : f x = h x := by rw [hf]; rfl
    rwa [hfx] at h1
  · intro j
    haveI := hsimple j.1 j.2
    have hcard := card_simple_zmodTwoPoly_of_semiregular m hm
      (↥(j : Submodule (ZMod 2)[X] (Module.AEval' f))) ?_ ?_
    · rw [← hcard]
      exact Nat.card_congr (Equiv.subtypeEquiv (Module.AEval'.of f).toEquiv (fun x => Iff.rfl))
    · intro y
      apply Subtype.ext
      obtain ⟨v, hv⟩ := y
      show (X ^ (2 ^ m - 1) : (ZMod 2)[X]) • v = v
      rw [← (Module.AEval'.of f).apply_symm_apply v, Module.AEval'.X_pow_smul_of, hfn, one_smul]
    · intro i hi0 hin y hy
      obtain ⟨v, hv⟩ := y
      have hy' : (X ^ i : (ZMod 2)[X]) • v = v := congrArg Subtype.val hy
      rw [← (Module.AEval'.of f).apply_symm_apply v, Module.AEval'.X_pow_smul_of] at hy'
      have hx := hfpf i hi0 hin ((Module.AEval'.of f).symm v) (by
        rw [← hpow]
        exact (Module.AEval'.of f).injective hy')
      apply Subtype.ext
      show v = 0
      rw [← (Module.AEval'.of f).apply_symm_apply v, hx, map_zero]
  · have h1 := (sSupIndep_iff s).mp hind
    have h2 := iSupIndep_restrictScalars_of_iSupIndep (S := ZMod 2) h1
    exact h2.map_orderIso (Submodule.orderIsoMapComap (Module.AEval'.of f)).symm
  · have hs : (⨆ j : s, (j : Submodule (ZMod 2)[X] (Module.AEval' f))) = ⊤ := by
      rw [← sSup_eq_iSup', htop]
    show (⨆ j : s, (Submodule.orderIsoMapComap (Module.AEval'.of f)).symm
      ((j : Submodule (ZMod 2)[X] (Module.AEval' f)).restrictScalars (ZMod 2))) = ⊤
    rw [← OrderIso.map_iSup, ← Submodule.restrictScalars_iSup, hs, Submodule.restrictScalars_top,
      OrderIso.map_top]

end CFSG.RankThree.GF2n.Tim79a
