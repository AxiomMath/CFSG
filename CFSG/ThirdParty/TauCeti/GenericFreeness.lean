/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.DirectSum.Basis
public import Mathlib.RingTheory.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.FiniteFlat
public import TauCeti.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Generic freeness and faithful flatness of dominant affine group morphisms

This file is adapted from the TauCeti repository at `main` commit
`3bed7e37f3c504a99e8c07e9f309540812a7aa90`. It ports the generic-freeness development and
the dominance-to-faithful-flatness theorem added after the current CFSG dependency pin
`6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380`. The declarations are reproduced in the
`CFSG.ThirdParty.TauCeti` namespace with unchanged statements, so that a later TauCeti bump
does not clash with the upstream names.

The source files and their main declarations are:

* `TauCeti/LinearAlgebra/FreeModule/Filtration.lean`:
  `CFSG.ThirdParty.TauCeti.Module.Free.of_filtration`, a module with an exhaustive filtration
  by free subquotients is free;
* `TauCeti/RingTheory/Spectrum/Prime/FreeLocus.lean`:
  `CFSG.ThirdParty.TauCeti.Module.mem_freeLocus_of_mem_minimalPrimes` and
  `CFSG.ThirdParty.TauCeti.Module.iInter_freeLocus_subquotient_subset_freeLocus`; the upstream
  `Module.freeLocus_nonempty` and `PrimeSpectrum.flat_localization_of_comap_mem_freeLocus`
  already exist at the pin and are not redeclared (only the latter is used here);
* `TauCeti/RingTheory/Spectrum/Prime/Topology.lean`:
  `CFSG.ThirdParty.TauCeti.PrimeSpectrum.dense_of_forall_mem_minimalPrimes`;
* `TauCeti/RingTheory/Spectrum/Prime/GenericFreeness.lean`:
  `CFSG.ThirdParty.TauCeti.Module.freeLocus_mem_nhds_polynomial` and
  `CFSG.ThirdParty.TauCeti.Module.freeLocus_mem_nhds_of_surjective` (private upstream, made
  public here), and the main declarations
  `CFSG.ThirdParty.TauCeti.Module.freeLocus_mem_nhds_of_mem_minimalPrimes` and
  `CFSG.ThirdParty.TauCeti.Module.dense_interior_freeLocus_of_finiteType`;
* `TauCeti/Algebra/AlgebraicGroup/CommHopfAlgCat/Flat.lean`:
  `CFSG.ThirdParty.TauCeti.CommHopfAlgCat.faithfullyFlat_of_dominant`.

The statements are unchanged. The proofs are ported verbatim except for the following
adaptations to the pinned API:

* every ported declaration is placed in a namespace rooted at `CFSG.ThirdParty.TauCeti`, and
  references to ported declarations are correspondingly qualified, namely
  `CFSG.ThirdParty.TauCeti.Module.Free.of_filtration`,
  `CFSG.ThirdParty.TauCeti.PrimeSpectrum.dense_of_forall_mem_minimalPrimes` and
  `CFSG.ThirdParty.TauCeti.Module.dense_interior_freeLocus_of_finiteType`;
* the pinned TauCeti modules `TauCeti.RingTheory.Spectrum.Prime.FreeLocus`,
  `TauCeti.RingTheory.Spectrum.Prime.Topology` and
  `TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.FiniteFlat` are imported in place of the
  3bed ones, and the pinned declarations
  `PrimeSpectrum.flat_localization_of_comap_mem_freeLocus`,
  `TauCeti.CommHopfAlgCat.flat_localization_kernel_iff`,
  `TauCeti.CommHopfAlgCat.flat_iff_flat_localization_augmentation`,
  `TauCeti.CommHopfAlgCat.faithfullyFlat_iff_flat_of_injective` and
  `TauCeti.denseRange_kernelPoint` are reused;
* the TauCeti-specific point construction `AlgHom.kernelPoint` (and
  `AlgHom.kernelPoint_asIdeal`) is written `TauCeti.AlgHom.kernelPoint` (respectively
  `TauCeti.AlgHom.kernelPoint_asIdeal`), since it lives in the pinned TauCeti namespace and
  not in the ported one;
* the two private upstream lemmas are made public with docstrings.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 24.1.
* The Stacks Project, Tag 051R (and Tag 051Z), for generic freeness.
* J. S. Milne, *Algebraic Groups* (2017), §5 and Propositions 1.65(a) and 1.70.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §14, for faithful flatness of
  dominant homomorphisms via generic flatness and translation.
-/

public section

open Module
open DirectSum
open Polynomial Topology
open PrimeSpectrum
open CategoryTheory WithConv

namespace CFSG.ThirdParty.TauCeti

namespace Module.Free

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- A module with an exhaustive increasing filtration `⊥ = N 0 ≤ N 1 ≤ ⋯`, all of whose
subquotients `N (j + 1) ⧸ N j` are free, is free. -/
theorem of_filtration (N : ℕ → Submodule R M) (hN : Monotone N) (h0 : N 0 = ⊥)
    (htop : ⨆ j, N j = ⊤)
    (hfree : ∀ j, Module.Free R (N (j + 1) ⧸ (N j).submoduleOf (N (j + 1)))) :
    Module.Free R M := by
  classical
  let Q : ℕ → Type _ := fun j ↦ N (j + 1) ⧸ (N j).submoduleOf (N (j + 1))
  -- `Q` is a local abbreviation, so its additive groups are recorded for the direct sum.
  let _ (j : ℕ) : AddCommGroup (Q j) := Submodule.Quotient.addCommGroup _
  -- Split each subquotient off the next filtration step.
  have hsplit : ∀ j, ∃ s : Q j →ₗ[R] N (j + 1),
      ((N j).submoduleOf (N (j + 1))).mkQ ∘ₗ s = LinearMap.id := fun j ↦
    LinearMap.exists_rightInverse_of_surjective _ (Submodule.range_mkQ _)
  choose s hs using hsplit
  have hs' (j : ℕ) (q : Q j) : Submodule.Quotient.mk (s j q) = q :=
    LinearMap.congr_fun (hs j) q
  let ψ : (⨁ j, Q j) →ₗ[R] M := DirectSum.toModule R ℕ M fun j ↦ (N (j + 1)).subtype ∘ₗ s j
  have hψ (j : ℕ) (q : Q j) : ψ (DFinsupp.single j q) = s j q :=
    DirectSum.toModule_lof R j q
  have hψof (j : ℕ) (q : Q j) : ψ (DirectSum.of Q j q) = s j q :=
    DirectSum.toModule_lof R j q
  -- An element supported below `J` maps into `N J`, and only `0` maps to `0`.
  have key (J : ℕ) : ∀ d : ⨁ j, Q j, (∀ j ∈ d.support, j < J) →
      ψ d ∈ N J ∧ (ψ d = 0 → d = 0) := by
    induction J with
    | zero =>
      intro d hd
      have : d = 0 := DFinsupp.support_eq_empty.mp <|
        Finset.eq_empty_of_forall_notMem fun j hj ↦ Nat.not_lt_zero _ (hd j hj)
      subst this
      simp
    | succ J ih =>
      intro d hd
      have hd' : ∀ j ∈ (d.erase J).support, j < J := by
        intro j hj
        rw [DFinsupp.support_erase, Finset.mem_erase] at hj
        exact lt_of_le_of_ne (Nat.lt_succ_iff.mp (hd j hj.2)) hj.1
      obtain ⟨hmem, hzero⟩ := ih _ hd'
      have hd_eq : d = d.erase J + DFinsupp.single J (d J) := (DFinsupp.erase_add_single J d).symm
      have hψd : ψ d = ψ (d.erase J) + (s J (d J) : M) := by
        rw [hd_eq, map_add, hψ, DFinsupp.erase_add_single]
      refine ⟨hψd ▸ add_mem (hN J.le_succ hmem) (s J (d J)).2, fun h ↦ ?_⟩
      have hJ : d J = 0 := by
        have hmemJ : (s J (d J) : M) ∈ N J := by
          have : (s J (d J) : M) = -ψ (d.erase J) :=
            eq_neg_of_add_eq_zero_right (hψd.symm.trans h)
          exact this ▸ neg_mem hmem
        rw [← hs' J (d J), Submodule.Quotient.mk_eq_zero]
        exact hmemJ
      have herase : d.erase J = 0 := hzero (by simpa [hJ] using hψd.symm.trans h)
      rw [hd_eq, herase, hJ, zero_add, DFinsupp.single_zero]
  have hinj : Function.Injective ψ := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro d hd
    refine (key (d.support.sup id + 1) d fun j hj ↦ ?_).2 (LinearMap.mem_ker.mp hd)
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)
  have hsurj : Function.Surjective ψ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← htop, iSup_le_iff]
    intro J
    induction J with
    | zero => simp [h0]
    | succ J ih =>
      intro x hx
      let y : N (J + 1) := ⟨x, hx⟩
      have hrest : y - s J (Submodule.Quotient.mk y) ∈ (N J).submoduleOf (N (J + 1)) := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hs', sub_self]
      obtain ⟨d, hd⟩ := ih hrest
      refine ⟨d + DirectSum.of Q J (Submodule.Quotient.mk y), ?_⟩
      rw [map_add, hd, hψof, Submodule.subtype_apply, Submodule.coe_sub, sub_add_cancel]
  exact Module.Free.of_equiv (LinearEquiv.ofBijective ψ ⟨hinj, hsurj⟩)

end Module.Free

namespace Module

section Reduced

variable {R : Type*} (M : Type*) [CommRing R] [IsReduced R] [AddCommGroup M] [Module R M]

/-- Over a reduced ring, every module is free at each minimal prime, where the localization of
the ring is a field. -/
theorem mem_freeLocus_of_mem_minimalPrimes {p : Ideal R} (hp : p ∈ minimalPrimes R) :
    ⟨p, hp.1.1⟩ ∈ freeLocus R M := by
  have := hp.1.1
  have : Ring.KrullDimLE 0 (Localization.AtPrime p) := .of_isLocalization p hp _
  let : Field (Localization.AtPrime p) := Ring.KrullDimLE.isField_of_isReduced.toField
  exact Module.Free.of_divisionRing _ _

end Reduced

section Filtration

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A module is free at every prime at which all subquotients `N (j + 1) ⧸ N j` of an exhaustive
increasing filtration `⊥ = N 0 ≤ N 1 ≤ ⋯` are free.

No finiteness is assumed, so this applies to filtrations of modules that are not finitely
generated over the base ring. -/
theorem iInter_freeLocus_subquotient_subset_freeLocus (N : ℕ → Submodule R M)
    (hN : Monotone N) (h0 : N 0 = ⊥) (htop : ⨆ j, N j = ⊤) :
    ⋂ j, freeLocus R (N (j + 1) ⧸ (N j).submoduleOf (N (j + 1))) ⊆ freeLocus R M := by
  intro p hp
  rw [Set.mem_iInter] at hp
  let S := p.asIdeal.primeCompl
  let Rp := Localization.AtPrime p.asIdeal
  let L : ℕ → Submodule Rp (LocalizedModule S M) := fun j ↦ (N j).localized S
  have hL : Monotone L := fun _ _ hij ↦
    (Submodule.localized'gi Rp S (LocalizedModule.mkLinearMap S M)).gc.monotone_l (hN hij)
  refine CFSG.ThirdParty.TauCeti.Module.Free.of_filtration L hL (by simp [L, h0])
    (by simp only [L]; rw [← Submodule.localized'_iSup, htop, Submodule.localized'_top])
    fun j ↦ ?_
  -- Localize the subquotient through the localization of `N (j + 1)`.
  let g := (N (j + 1)).toLocalized' Rp S (LocalizedModule.mkLinearMap S M)
  let W := (N j).submoduleOf (N (j + 1))
  have hcoe (m : N (j + 1)) (s : S) :
      ((IsLocalizedModule.mk' g m s : L (j + 1)) : LocalizedModule S M) =
        IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) (m : M) s := by
    rw [eq_comm, IsLocalizedModule.mk'_eq_iff, ← Submodule.coe_smul_of_tower,
      IsLocalizedModule.mk'_cancel', Submodule.toLocalized'_apply_coe]
  have heq : W.localized' Rp S g = (L j).submoduleOf (L (j + 1)) := by
    ext x
    rw [Submodule.mem_localized']
    constructor
    · rintro ⟨m, hm, s, rfl⟩
      exact ⟨m, hm, s, (hcoe m s).symm⟩
    · rintro ⟨m, hm, s, hx⟩
      exact ⟨⟨m, hN j.le_succ hm⟩, hm, s, Subtype.ext ((hcoe _ s).trans hx)⟩
  have hfree : Module.Free Rp (L (j + 1) ⧸ W.localized' Rp S g) :=
    (mem_freeLocus_of_isLocalization p Rp _ (W.toLocalizedQuotient' Rp S g)).mp (hp j)
  exact Module.Free.of_equiv (Submodule.quotEquivOfEq _ _ heq)

end Filtration

end Module

namespace PrimeSpectrum

variable {R : Type*} [CommSemiring R]

/-- A subset of the prime spectrum containing every minimal prime is dense: every nonempty open
set contains a minimal prime, namely a generization of any of its points. -/
theorem dense_of_forall_mem_minimalPrimes {s : Set (PrimeSpectrum R)}
    (hs : ∀ (p : Ideal R) (hp : p ∈ minimalPrimes R), ⟨p, hp.1.1⟩ ∈ s) : Dense s := by
  refine dense_iff_inter_open.mpr fun U hU ⟨x, hx⟩ ↦ ?_
  obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le (J := x.asIdeal) bot_le
  have hspec : (⟨q, hq.1.1⟩ : PrimeSpectrum R) ⤳ x := (le_iff_specializes _ _).mp hqx
  exact ⟨_, hspec.mem_open hU hx, hs q hq⟩

end PrimeSpectrum

namespace Module

universe uA uR uM

variable {A : Type uA} [CommRing A]

/-- If every finite `R`-module is free over `A` near each minimal prime of `A`, then so is every
finite module over the polynomial ring `R[X]`. -/
theorem freeLocus_mem_nhds_polynomial {R : Type uR} [CommRing R] [Algebra A R]
    [IsNoetherianRing R]
    (hR : ∀ (N : Type uR) [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower A R N]
      [Module.Finite R N] (p : Ideal A) (hp : p ∈ minimalPrimes A),
      freeLocus A N ∈ 𝓝 ⟨p, hp.1.1⟩)
    (M : Type uM) [AddCommGroup M] [Module R[X] M] [Module A M] [IsScalarTower A R[X] M]
    [Module.Finite R[X] M] (p : Ideal A) (hp : p ∈ minimalPrimes A) :
    freeLocus A M ∈ 𝓝 ⟨p, hp.1.1⟩ := by
  classical
  let _ : Module R M := Module.compHom M (algebraMap R R[X])
  -- By definition of `Module.compHom`, `r : R` acts on `M` as the constant polynomial `C r`.
  have : IsScalarTower R R[X] M := ⟨fun r p m ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩
  have : IsScalarTower A R M := ⟨fun a r m ↦ by
    change C (a • r) • m = a • (C r • m)
    rw [← smul_C, smul_assoc]⟩
  obtain ⟨t, m, hm⟩ := Module.Finite.exists_fin (R := R[X]) (M := M)
  -- `φ j c = ∑ cₖ • X ^ j • mₖ`, and `F j` is spanned by the images of `φ i` for `i < j`.
  let φ : ℕ → (Fin t → R) →ₗ[R] M := fun j ↦
    Fintype.linearCombination R fun k ↦ (X ^ j : R[X]) • m k
  let F : ℕ → Submodule R M := fun j ↦ ⨆ i < j, LinearMap.range (φ i)
  let lX : M →ₗ[R] M :=
    { toFun := fun y ↦ (X : R[X]) • y
      map_add' := smul_add _
      map_smul' := fun r y ↦ smul_comm _ r y }
  have hφX (j : ℕ) : φ (j + 1) = lX ∘ₗ φ j := by
    ext c
    simp only [φ, lX, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Fintype.linearCombination_apply, Finset.smul_sum, pow_succ', mul_smul]
    exact Finset.sum_congr rfl fun k _ ↦ (smul_comm _ _ _).symm
  have hFmono : Monotone F := fun i j hij ↦
    biSup_mono fun _ hk ↦ lt_of_lt_of_le hk hij
  have hFsucc (j : ℕ) : F (j + 1) = F j ⊔ LinearMap.range (φ j) := Nat.iSup_lt_succ _ j
  have hF0 : F 0 = ⊥ := by simp [F]
  have hFX (j : ℕ) : (F j).map lX ≤ F (j + 1) := by
    simp only [F, Submodule.map_iSup, iSup_le_iff]
    intro i hi
    rw [← LinearMap.range_comp, ← hφX]
    exact le_iSup₂_of_le (i + 1) (by omega) le_rfl
  have hFtop : ⨆ j, F j = ⊤ := by
    have hspan : Submodule.span R (Set.range fun i : ℕ ↦ (X ^ i : R[X])) = ⊤ := by
      simpa [← Polynomial.X_pow_eq_monomial] using (Polynomial.basisMonomials R).span_eq
    rw [eq_top_iff, ← Submodule.restrictScalars_top R R[X] M, ← hm,
      ← Submodule.span_smul_of_span_eq_top hspan, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨k, rfl⟩, rfl⟩
    refine Submodule.mem_iSup_of_mem (i + 1) (Submodule.mem_iSup_of_mem i
      (Submodule.mem_iSup_of_mem (Nat.lt_succ_self i) ⟨Pi.single k 1, ?_⟩))
    simp [φ, Fintype.linearCombination_apply, Pi.single_apply]
  -- `K j` is the module of relations of the `j`-th subquotient; it increases with `j`.
  let K : ℕ →o Submodule R (Fin t → R) :=
    ⟨fun j ↦ (F j).comap (φ j), monotone_nat_of_le_succ fun j c hc ↦ by
      rw [Submodule.mem_comap, hφX, LinearMap.comp_apply]
      exact hFX j (Submodule.mem_map_of_mem hc)⟩
  obtain ⟨j₀, hj₀⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance K
  -- The `j`-th subquotient of the filtration, viewed over `A`, is `Rᵗ ⧸ K j`.
  let N : ℕ → Submodule A M := fun j ↦ (F j).restrictScalars A
  have hsub (j : ℕ) : freeLocus A ((Fin t → R) ⧸ K j) =
      freeLocus A (N (j + 1) ⧸ (N j).submoduleOf (N (j + 1))) := by
    have hmem (c : Fin t → R) : φ j c ∈ N (j + 1) := by
      rw [Submodule.restrictScalars_mem, hFsucc]
      exact Submodule.mem_sup_right ⟨c, rfl⟩
    let ψ : (Fin t → R) →ₗ[A] N (j + 1) ⧸ (N j).submoduleOf (N (j + 1)) :=
      ((N j).submoduleOf (N (j + 1))).mkQ ∘ₗ ((φ j).restrictScalars A).codRestrict _ hmem
    have hψc (c : Fin t → R) : ψ c = Submodule.Quotient.mk ⟨φ j c, hmem c⟩ := by
      rw [LinearMap.comp_apply, Submodule.mkQ_apply]
      refine congrArg _ (Subtype.ext ?_)
      exact (LinearMap.codRestrict_apply _ _ c).trans (LinearMap.restrictScalars_apply _ _ c)
    have hψ : Function.Surjective ψ := by
      intro z
      obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      have hy' : y ∈ F j ⊔ LinearMap.range (φ j) := hFsucc j ▸ hy
      obtain ⟨a, ha, _, ⟨c, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hy'
      refine ⟨c, ?_⟩
      rw [hψc, Submodule.Quotient.eq]
      simpa [Submodule.submoduleOf, N] using neg_mem ha
    have hker : LinearMap.ker ψ = (K j).restrictScalars A := by
      ext c
      rw [LinearMap.mem_ker, hψc, Submodule.Quotient.mk_eq_zero]
      simp [Submodule.submoduleOf, N, K]
    exact freeLocus_congr ((Submodule.Quotient.restrictScalarsEquiv A (K j)).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ ψ.quotKerEquivOfSurjective hψ)
  -- Only the finitely many subquotients with `j ≤ j₀` matter.
  let U := ⋂ j ∈ Finset.range (j₀ + 1), interior (freeLocus A ((Fin t → R) ⧸ K j))
  have hU : U ∈ 𝓝 ⟨p, hp.1.1⟩ :=
    (isOpen_biInter_finset fun _ _ ↦ isOpen_interior).mem_nhds <| Set.mem_iInter₂.mpr
      fun j _ ↦ mem_interior_iff_mem_nhds.mpr (hR ((Fin t → R) ⧸ K j) p hp)
  refine Filter.mem_of_superset hU (subset_trans ?_ (iInter_freeLocus_subquotient_subset_freeLocus
    N (fun _ _ hij ↦ hFmono hij) (by simp [N, hF0]) ?_))
  · intro q hq
    rw [Set.mem_iInter]
    intro j
    have hK : K j = K (min j j₀) := by
      rcases le_total j j₀ with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h, hj₀ j h]
    rw [← hsub, hK]
    have hj : min j j₀ ∈ Finset.range (j₀ + 1) := Finset.mem_range.mpr (by omega)
    exact interior_subset (Set.mem_iInter₂.mp hq (min j j₀) hj)
  · simp only [N, ← Submodule.restrictScalars_iSup, hFtop, Submodule.restrictScalars_top]

/-- Freeness of finite modules near the minimal primes of `A` transfers along a surjective
algebra map. -/
theorem freeLocus_mem_nhds_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] (f : R →ₐ[A] S) (hf : Function.Surjective f)
    (hR : ∀ (N : Type uM) [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower A R N]
      [Module.Finite R N] (p : Ideal A) (hp : p ∈ minimalPrimes A),
      freeLocus A N ∈ 𝓝 ⟨p, hp.1.1⟩)
    (M : Type uM) [AddCommGroup M] [Module S M] [Module A M] [IsScalarTower A S M]
    [Module.Finite S M] (p : Ideal A) (hp : p ∈ minimalPrimes A) :
    freeLocus A M ∈ 𝓝 ⟨p, hp.1.1⟩ := by
  let _ : Algebra R S := f.toRingHom.toAlgebra
  let _ : Module R M := Module.compHom M f.toRingHom
  -- By definition of `Module.compHom`, `r : R` acts on `M` as `f r`.
  have : IsScalarTower R S M := ⟨fun r s m ↦ by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  have : IsScalarTower A R M := ⟨fun a r m ↦ by
    change f (a • r) • m = a • (f r • m)
    rw [map_smul, smul_assoc]⟩
  have : Module.Finite R S := Module.Finite.of_surjective (Algebra.linearMap R S) hf
  have : Module.Finite R M := Module.Finite.trans S M
  exact hR M p hp

/-- **Generic freeness.** Let `A` be a reduced Noetherian ring, `B` a finitely generated
`A`-algebra and `M` a finite `B`-module. Then `M` is free over `A` on a neighbourhood of every
minimal prime of `A`.

For a Noetherian domain `A` this means that there is a nonzero `a : A` such that `M_q` is free
over `A_q` for every prime `q` not containing `a`. -/
theorem freeLocus_mem_nhds_of_mem_minimalPrimes [IsNoetherianRing A] [IsReduced A]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (M : Type uM) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] {p : Ideal A} (hp : p ∈ minimalPrimes A) :
    freeLocus A M ∈ 𝓝 ⟨p, hp.1.1⟩ := by
  -- Finite modules over polynomial rings in finitely many variables.
  have key (n : ℕ) : ∀ (N : Type uA) [AddCommGroup N] [Module (MvPolynomial (Fin n) A) N]
      [Module A N] [IsScalarTower A (MvPolynomial (Fin n) A) N]
      [Module.Finite (MvPolynomial (Fin n) A) N] (p : Ideal A) (hp : p ∈ minimalPrimes A),
      freeLocus A N ∈ 𝓝 ⟨p, hp.1.1⟩ := by
    induction n with
    | zero =>
      intro N _ _ _ _ _ p hp
      have : Module.Finite A (MvPolynomial (Fin 0) A) :=
        Module.Finite.equiv (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm.toLinearEquiv
      have : Module.Finite A N := Module.Finite.trans (MvPolynomial (Fin 0) A) N
      have : FinitePresentation A N := Module.finitePresentation_of_finite A N
      exact isOpen_freeLocus.mem_nhds (mem_freeLocus_of_mem_minimalPrimes N hp)
    | succ n ih =>
      exact freeLocus_mem_nhds_of_surjective (MvPolynomial.finSuccEquiv A n).symm.toAlgHom
        (MvPolynomial.finSuccEquiv A n).symm.surjective (freeLocus_mem_nhds_polynomial ih)
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType A B›
  refine freeLocus_mem_nhds_of_surjective (aevalTower f 0) (fun b ↦ ?_)
    (freeLocus_mem_nhds_polynomial (key n)) M p hp
  obtain ⟨q, rfl⟩ := hf b
  exact ⟨C q, aevalTower_C _ _ _⟩

/-- **Generic freeness.** Let `A` be a reduced Noetherian ring, `B` a finitely generated
`A`-algebra and `M` a finite `B`-module. Then `M` is free over `A` on a dense open subset of
`Spec A`. -/
theorem dense_interior_freeLocus_of_finiteType [IsNoetherianRing A] [IsReduced A]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (M : Type uM) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] : Dense (interior (freeLocus A M)) :=
  CFSG.ThirdParty.TauCeti.PrimeSpectrum.dense_of_forall_mem_minimalPrimes fun _ hp ↦
    mem_interior_iff_mem_nhds.mpr (freeLocus_mem_nhds_of_mem_minimalPrimes (B := B) M hp)

end Module

attribute [local instance] RingHom.ker_isPrime

namespace CommHopfAlgCat

universe u v

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{v} k}

/-- A dominant homomorphism from a finite-type affine group to a reduced finite-type affine
group over an algebraically closed field is faithfully flat. The source may be nonreduced, and
the homomorphism need not be finite. -/
theorem faithfullyFlat_of_dominant [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
    [Algebra.FiniteType k K] (f : H ⟶ K)
    (hdom : DenseRange (PrimeSpectrum.comap f.hom.toAlgHom.toRingHom)) :
    f.hom.toAlgHom.toRingHom.FaithfullyFlat := by
  let := f.hom.toAlgHom.toAlgebra
  have : IsScalarTower k H K := .of_algebraMap_eq fun x ↦ (f.hom.toAlgHom.commutes x).symm
  have : Algebra.FiniteType H K := .of_restrictScalars_finiteType k H K
  have : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  have : Nontrivial H := (Bialgebra.counitAlgHom k H).toRingHom.domain_nontrivial
  have hd := hdom.comp (TauCeti.denseRange_kernelPoint (k := k) (A := K))
    (PrimeSpectrum.continuous_comap f.hom.toAlgHom.toRingHom)
  -- Generic freeness gives a dense open set over which `K` is free; dominance and density of
  -- rational points give a rational point of the source lying over it.
  obtain ⟨g, hg⟩ := hd.exists_mem_open isOpen_interior
    (CFSG.ThirdParty.TauCeti.Module.dense_interior_freeLocus_of_finiteType
      (A := H) (B := K) K).nonempty
  have := (TauCeti.AlgHom.kernelPoint g).isPrime
  have hlocal : Module.Flat H
      (Localization.AtPrime (TauCeti.AlgHom.kernelPoint g).asIdeal) :=
    PrimeSpectrum.flat_localization_of_comap_mem_freeLocus (TauCeti.AlgHom.kernelPoint g)
      (interior_subset hg)
  have hflat : f.hom.toAlgHom.toRingHom.Flat := by
    apply (TauCeti.CommHopfAlgCat.flat_iff_flat_localization_augmentation f).mpr
    apply (TauCeti.CommHopfAlgCat.flat_localization_kernel_iff f (toConv g)).mp
    rw [← RingHom.algebraMap_toAlgebra f.hom.toAlgHom.toRingHom,
      ← IsScalarTower.algebraMap_eq H K, RingHom.flat_algebraMap_iff]
    -- Transport the prime together with its primality proof, so localization instances agree.
    have hp : (TauCeti.AlgHom.kernelPoint g : PrimeSpectrum K) =
        ⟨RingHom.ker g.toRingHom, RingHom.ker_isPrime _⟩ :=
      PrimeSpectrum.ext (TauCeti.AlgHom.kernelPoint_asIdeal g)
    exact (congrArg (fun p : PrimeSpectrum K ↦
      Module.Flat H (Localization.AtPrime p.asIdeal)) hp).mp hlocal
  have hinj : Function.Injective f.hom :=
    (RingHom.denseRange_comap_iff_injective _).mp hdom
  exact (TauCeti.CommHopfAlgCat.faithfullyFlat_iff_flat_of_injective f hinj).mpr hflat

end CommHopfAlgCat

end CFSG.ThirdParty.TauCeti
