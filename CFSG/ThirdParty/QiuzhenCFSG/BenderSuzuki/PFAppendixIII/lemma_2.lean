module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basis
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.StdBasis

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi Appendix III, Lemma 2
-/

namespace CFSG.BenderSuzuki
namespace PFAppendixIII

universe u

/-- Appendix III, Lemma 2(a): field automorphisms form an F-basis of the
F₂-linear endomorphisms of F. -/
public theorem lemma2a_fieldAutomorphisms_basis_linearMaps
    (F : Type u) [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F] :
    ∃ b : Module.Basis (F ≃+* F) F (F →ₗ[ZMod 2] F),
      ∀ sigma : F ≃+* F, ∀ x : F, b sigma x = sigma x := by
  let autToAlgHom : (F ≃+* F) → (F →ₐ[ZMod 2] F) := fun sigma =>
    (AlgEquiv.ofRingEquiv (f := sigma) (by
      intro z
      have h :
          (sigma.toRingHom.comp (algebraMap (ZMod 2) F) : ZMod 2 →+* F) =
            algebraMap (ZMod 2) F :=
        RingHom.ext_zmod _ _
      exact DFunLike.congr_fun h z)).toAlgHom
  have hautToAlgHom_injective : Function.Injective autToAlgHom := by
    intro sigma tau h
    ext x
    exact DFunLike.congr_fun h x
  letI : Fintype (F ≃+* F) :=
    Fintype.ofInjective autToAlgHom hautToAlgHom_injective
  have hautToAlgHom_surjective : Function.Surjective autToAlgHom := by
    intro phi
    let e : F ≃ₐ[ZMod 2] F := AlgEquiv.ofBijective phi (AlgHom.bijective phi)
    refine ⟨e.toRingEquiv, ?_⟩
    apply AlgHom.ext
    intro x
    rfl
  have hlinearIndependent : LinearIndependent F
      (fun sigma : F ≃+* F => (autToAlgHom sigma).toLinearMap) := by
    simpa [Function.comp_def] using
      (linearIndependent_algHom_toLinearMap (ZMod 2) F F).comp
        autToAlgHom hautToAlgHom_injective
  have hcard : Fintype.card (F ≃+* F) =
      Module.finrank F (F →ₗ[ZMod 2] F) := by
    calc
      Fintype.card (F ≃+* F) = Fintype.card (F →ₐ[ZMod 2] F) :=
        Fintype.card_congr
          (Equiv.ofBijective autToAlgHom
            ⟨hautToAlgHom_injective, hautToAlgHom_surjective⟩)
      _ = Module.finrank (ZMod 2) F :=
        FiniteField.card_algHom_of_finrank_dvd (dvd_refl _)
      _ = Module.finrank F (F →ₗ[ZMod 2] F) :=
        (Module.finrank_linearMap_self (ZMod 2) F F).symm
  let b : Module.Basis (F ≃+* F) F (F →ₗ[ZMod 2] F) :=
    basisOfLinearIndependentOfCardEqFinrank hlinearIndependent hcard
  refine ⟨b, ?_⟩
  intro sigma x
  have hb : b sigma = (autToAlgHom sigma).toLinearMap := by
    exact congrFun
      (coe_basisOfLinearIndependentOfCardEqFinrank
        hlinearIndependent hcard) sigma
  rw [hb]
  rfl

/-- Appendix III, Lemma 2(b): the products sigma(x) tau(y) form an F-basis
of the F₂-bilinear maps F × F -> F. -/
public theorem lemma2b_fieldAutomorphism_products_basis_bilinearMaps
    (F : Type u) [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F] :
    ∃ b : Module.Basis ((F ≃+* F) × (F ≃+* F)) F
        (F →ₗ[ZMod 2] F →ₗ[ZMod 2] F),
      ∀ sigma tau : F ≃+* F, ∀ x y : F,
        b (sigma, tau) x y = sigma x * tau y := by
  classical
  let autToAlgHom : (F ≃+* F) → (F →ₐ[ZMod 2] F) := fun sigma =>
    (AlgEquiv.ofRingEquiv (f := sigma) (by
      intro z
      have h :
          (sigma.toRingHom.comp (algebraMap (ZMod 2) F) : ZMod 2 →+* F) =
            algebraMap (ZMod 2) F :=
        RingHom.ext_zmod _ _
      exact DFunLike.congr_fun h z)).toAlgHom
  have hautToAlgHom_injective : Function.Injective autToAlgHom := by
    intro sigma tau h
    ext x
    exact DFunLike.congr_fun h x
  letI : Finite (F ≃+* F) :=
    Finite.of_injective autToAlgHom hautToAlgHom_injective
  letI : Fintype (F ≃+* F) := Fintype.ofFinite _
  obtain ⟨autBasis, hAutBasis⟩ :=
    lemma2a_fieldAutomorphisms_basis_linearMaps F
  let bilinear : (F ≃+* F) × (F ≃+* F) →
      (F →ₗ[ZMod 2] F →ₗ[ZMod 2] F) := fun p =>
    (autBasis p.1).smulRight (autBasis p.2)
  have hbilinear_eval (sigma tau : F ≃+* F) (x y : F) :
      bilinear (sigma, tau) x y = sigma x * tau y := by
    simp [bilinear, hAutBasis]
  let innerCoord (tau : F ≃+* F) :
      (F →ₗ[ZMod 2] F →ₗ[ZMod 2] F) →ₗ[F] (F →ₗ[ZMod 2] F) :=
    { toFun := fun f =>
        (autBasis.coord tau).restrictScalars (ZMod 2) ∘ₗ f
      map_add' := by
        intro f g
        ext x
        simp
      map_smul' := by
        intro c f
        ext x
        exact map_smul (autBasis.coord tau) c (f x) }
  let coordMap (sigma tau : F ≃+* F) :
      (F →ₗ[ZMod 2] F →ₗ[ZMod 2] F) →ₗ[F] F :=
    (autBasis.coord sigma).comp (innerCoord tau)
  have hinnerCoord_apply (tau sigma' tau' : F ≃+* F) :
      innerCoord tau (bilinear (sigma', tau')) =
        if tau' = tau then autBasis sigma' else 0 := by
    ext x
    by_cases ht : tau' = tau
    · subst tau'
      simp [innerCoord, bilinear, Module.Basis.coord_apply]
    · simp [innerCoord, bilinear, Module.Basis.coord_apply, ht]
  have hcoordMap (sigma tau sigma' tau' : F ≃+* F) :
      coordMap sigma tau (bilinear (sigma', tau')) =
        if sigma' = sigma ∧ tau' = tau then 1 else 0 := by
    simp only [coordMap, LinearMap.comp_apply, Module.Basis.coord_apply,
      hinnerCoord_apply]
    by_cases ht : tau' = tau
    · subst tau'
      by_cases hs : sigma' = sigma
      · subst sigma'
        simp
      · simp [hs]
    · simp [ht]
  let allCoords :
      (F →ₗ[ZMod 2] F →ₗ[ZMod 2] F) →ₗ[F]
        (((F ≃+* F) × (F ≃+* F)) → F) :=
    LinearMap.pi fun p => coordMap p.1 p.2
  have hallCoords_bilinear (q : (F ≃+* F) × (F ≃+* F)) :
      allCoords (bilinear q) =
        Pi.basisFun F ((F ≃+* F) × (F ≃+* F)) q := by
    funext p
    by_cases hqp : q = p
    · subst p
      simp [allCoords, hcoordMap, Pi.basisFun_apply]
    · have hproj : ¬(q.1 = p.1 ∧ q.2 = p.2) := by
        intro h
        exact hqp (Prod.ext h.1 h.2)
      simp [allCoords, hcoordMap, Pi.basisFun_apply, hqp, hproj]
  have hallCoords_injective : Function.Injective allCoords := by
    intro f g hfg
    apply LinearMap.ext
    intro x
    apply autBasis.repr.injective
    ext tau
    have hinner : innerCoord tau f = innerCoord tau g := by
      apply autBasis.repr.injective
      ext sigma
      have hp := congrFun hfg (sigma, tau)
      simpa [allCoords, coordMap, Module.Basis.coord_apply] using hp
    have hx := LinearMap.congr_fun hinner x
    simpa [innerCoord, Module.Basis.coord_apply] using hx
  have hlinearIndependent : LinearIndependent F bilinear := by
    apply LinearIndependent.of_comp allCoords
    have heq : allCoords ∘ bilinear =
        (Pi.basisFun F ((F ≃+* F) × (F ≃+* F))) := by
      funext q
      exact hallCoords_bilinear q
    rw [heq]
    exact (Pi.basisFun F ((F ≃+* F) × (F ≃+* F))).linearIndependent
  have hcard : Fintype.card ((F ≃+* F) × (F ≃+* F)) =
      Module.finrank F (F →ₗ[ZMod 2] F →ₗ[ZMod 2] F) := by
    have hAutCard : Fintype.card (F ≃+* F) =
        Module.finrank F (F →ₗ[ZMod 2] F) :=
      (Module.finrank_eq_card_basis autBasis).symm
    calc
      Fintype.card ((F ≃+* F) × (F ≃+* F)) =
          Fintype.card (F ≃+* F) * Fintype.card (F ≃+* F) :=
        Fintype.card_prod _ _
      _ = Module.finrank F (F →ₗ[ZMod 2] F) *
          Module.finrank F (F →ₗ[ZMod 2] F) := by rw [hAutCard]
      _ = Module.finrank (ZMod 2) F *
          Module.finrank F (F →ₗ[ZMod 2] F) := by
        rw [Module.finrank_linearMap_self (ZMod 2) F F]
      _ = Module.finrank F (F →ₗ[ZMod 2] F →ₗ[ZMod 2] F) :=
        (Module.finrank_linearMap (ZMod 2) F F
          (F →ₗ[ZMod 2] F)).symm
  have hspan : Submodule.span F (Set.range bilinear) = ⊤ := by
    apply le_antisymm le_top
    intro f hf
    let stdBasis := Pi.basisFun F ((F ≃+* F) × (F ≃+* F))
    let coeff := stdBasis.repr (allCoords f)
    have himage :
        allCoords (∑ p, coeff p • bilinear p) = allCoords f := by
      calc
        allCoords (∑ p, coeff p • bilinear p) =
            ∑ p, coeff p • allCoords (bilinear p) := by simp
        _ = ∑ p, coeff p • stdBasis p := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [hallCoords_bilinear]
        _ = allCoords f := stdBasis.sum_repr (allCoords f)
    have hsum : (∑ p, coeff p • bilinear p) = f :=
      hallCoords_injective himage
    rw [← hsum]
    apply Submodule.sum_mem
    intro p hp
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self p))
  let b : Module.Basis ((F ≃+* F) × (F ≃+* F)) F
      (F →ₗ[ZMod 2] F →ₗ[ZMod 2] F) :=
    Module.Basis.mk hlinearIndependent hspan.ge
  have hb (p : (F ≃+* F) × (F ≃+* F)) : b p = bilinear p := by
    change Module.Basis.mk hlinearIndependent hspan.ge p = bilinear p
    exact Module.Basis.mk_apply hlinearIndependent hspan.ge p
  refine ⟨b, ?_⟩
  intro sigma tau x y
  rw [hb]
  exact hbilinear_eval sigma tau x y
/-- Appendix III, Lemma 2(c): the monomials sigma(x) tau(x), indexed by the
one- and two-element subsets of Aut(F), form an F-basis of the quadratic maps.
A singleton index represents the diagonal monomial `sigma(x)^2`. -/
public theorem lemma2c_fieldAutomorphism_products_basis_quadraticMaps
    (F : Type u) [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F] :
    ∃ b : Module.Basis {s : Finset (F ≃+* F) // s.card = 1 ∨ s.card = 2} F
        (QuadraticMap (ZMod 2) F F),
      ∀ s : {s : Finset (F ≃+* F) // s.card = 1 ∨ s.card = 2}, ∀ x : F,
        b s x = if s.1.card = 1 then
          (∏ sigma ∈ s.1, sigma x) ^ 2
        else ∏ sigma ∈ s.1, sigma x := by
  classical
  letI : Fintype (F ≃+* F) :=
    Fintype.ofInjective (fun sigma : F ≃+* F => (sigma : F → F)) (by
      intro sigma tau h
      ext x
      exact congrFun h x)
  let I := {s : Finset (F ≃+* F) // s.card = 1 ∨ s.card = 2}
  letI : Fintype I := Fintype.ofFinite I
  obtain ⟨bilinBasis, hBilinBasis⟩ :=
    lemma2b_fieldAutomorphism_products_basis_bilinearMaps F
  let diag : (F →ₗ[ZMod 2] F →ₗ[ZMod 2] F) →ₗ[F]
      QuadraticMap (ZMod 2) F F :=
    LinearMap.BilinMap.toQuadraticMapLinearMap F (ZMod 2) F
  have hpair_exists (s : I) :
      ∃ p : (F ≃+* F) × (F ≃+* F), s.1 = {p.1, p.2} := by
    rcases s.2 with hcard | hcard
    · obtain ⟨sigma, hsigma⟩ := Finset.card_eq_one.mp hcard
      exact ⟨(sigma, sigma), by simp [hsigma]⟩
    · obtain ⟨sigma, tau, hne, hst⟩ := Finset.card_eq_two.mp hcard
      exact ⟨(sigma, tau), hst⟩
  let pairOfSet : I → (F ≃+* F) × (F ≃+* F) := fun s =>
    Classical.choose (hpair_exists s)
  have hpairOfSet (s : I) :
      s.1 = {(pairOfSet s).1, (pairOfSet s).2} := by
    exact Classical.choose_spec (hpair_exists s)
  let monomial : I → QuadraticMap (ZMod 2) F F := fun s =>
    diag (bilinBasis (pairOfSet s))
  have hmonomial_eval (s : I) (x : F) :
      monomial s x = if s.1.card = 1 then
        (∏ sigma ∈ s.1, sigma x) ^ 2
      else ∏ sigma ∈ s.1, sigma x := by
    change bilinBasis (pairOfSet s) x x = _
    rw [hBilinBasis]
    change (pairOfSet s).1 x * (pairOfSet s).2 x = _
    conv_rhs => rw [hpairOfSet s]
    by_cases h : (pairOfSet s).1 = (pairOfSet s).2
    · simp [h, pow_two]
    · simp [h]
  have htwo_coefficients_zero
      (g : I → F) (hg : ∑ s, g s • monomial s = 0) :
      ∀ s : I, s.1.card = 2 → g s = 0 := by
    let swapPair : ((F ≃+* F) × (F ≃+* F)) →
        ((F ≃+* F) × (F ≃+* F)) := fun p => (p.2, p.1)
    let symBilin : I → (F →ₗ[ZMod 2] F →ₗ[ZMod 2] F) := fun s =>
      bilinBasis (pairOfSet s) + bilinBasis (swapPair (pairOfSet s))
    have hflip (p : (F ≃+* F) × (F ≃+* F)) :
        (bilinBasis p).flip = bilinBasis (swapPair p) := by
      ext x y
      change bilinBasis p y x = bilinBasis (p.2, p.1) x y
      rw [hBilinBasis, hBilinBasis, mul_comm]
    have hsame_set_of_pair_or_swap {s t : I}
        (h : pairOfSet t = pairOfSet s ∨
          swapPair (pairOfSet t) = pairOfSet s) : t = s := by
      apply Subtype.ext
      rw [hpairOfSet t, hpairOfSet s]
      rcases h with h | h
      · rw [h]
      · have hfst := congrArg Prod.fst h
        have hsnd := congrArg Prod.snd h
        change (pairOfSet t).2 = (pairOfSet s).1 at hfst
        change (pairOfSet t).1 = (pairOfSet s).2 at hsnd
        rw [← hfst, ← hsnd, Finset.pair_comm]
    have hcoord (s t : I) (hs : s.1.card = 2) :
        bilinBasis.coord (pairOfSet s) (symBilin t) =
          if t = s then 1 else 0 := by
      have hs_ne : (pairOfSet s).1 ≠ (pairOfSet s).2 := by
        intro heq
        have hs' := hs
        rw [hpairOfSet s] at hs'
        simp [heq] at hs'
      have hswap_ne : swapPair (pairOfSet s) ≠ pairOfSet s := by
        intro heq
        have hfst := congrArg Prod.fst heq
        change (pairOfSet s).2 = (pairOfSet s).1 at hfst
        exact hs_ne hfst.symm
      by_cases hts : t = s
      · subst t
        simp [symBilin, Module.Basis.coord_apply, hswap_ne]
      · have hdirect : pairOfSet t ≠ pairOfSet s := by
          intro h
          exact hts (hsame_set_of_pair_or_swap (Or.inl h))
        have hswap : swapPair (pairOfSet t) ≠ pairOfSet s := by
          intro h
          exact hts (hsame_set_of_pair_or_swap (Or.inr h))
        simp [symBilin, Module.Basis.coord_apply, hts, hdirect, hswap]
    have hpolar : ∑ s, g s • symBilin s = 0 := by
      let polarLinear : QuadraticMap (ZMod 2) F F →ₗ[F]
          (F →ₗ[ZMod 2] F →ₗ[ZMod 2] F) :=
        { toFun := fun q => q.polarBilin
          map_add' := by
            intro q r
            ext x y
            exact QuadraticMap.polar_add q r x y
          map_smul' := by
            intro c q
            ext x y
            exact QuadraticMap.polar_smul q c x y }
      have hpolar_monomial (s : I) :
          polarLinear (monomial s) = symBilin s := by
        change (LinearMap.BilinMap.toQuadraticMap
            (bilinBasis (pairOfSet s))).polarBilin =
          bilinBasis (pairOfSet s) +
            bilinBasis (swapPair (pairOfSet s))
        rw [LinearMap.BilinMap.polarBilin_toQuadraticMap, hflip]
      calc
        ∑ s, g s • symBilin s =
            ∑ s, g s • polarLinear (monomial s) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [hpolar_monomial]
        _ = polarLinear (∑ s, g s • monomial s) := by
          rw [map_sum]
          simp
        _ = 0 := by rw [hg, map_zero]
    intro s hs
    have hcoord_sum := congrArg (bilinBasis.coord (pairOfSet s)) hpolar
    simp only [map_sum, map_smul, map_zero] at hcoord_sum
    simp only [hcoord s _ hs, smul_eq_mul, mul_ite, mul_one, mul_zero] at hcoord_sum
    rw [Fintype.sum_ite_eq'] at hcoord_sum
    exact hcoord_sum
  have hsingleton_coefficients_zero
      (g : I → F) (hg : ∑ s, g s • monomial s = 0)
      (htwo : ∀ s : I, s.1.card = 2 → g s = 0) :
      ∀ s : I, s.1.card = 1 → g s = 0 := by
    let singletonIndex : (F ≃+* F) → I := fun sigma =>
      ⟨{sigma}, Or.inl (Finset.card_singleton sigma)⟩
    let J := {s : I // s.1.card = 1}
    let singletonInJ : (F ≃+* F) → J := fun sigma =>
      ⟨singletonIndex sigma, by simp [singletonIndex]⟩
    have hsingleton_bijective : Function.Bijective singletonInJ := by
      constructor
      · intro sigma tau h
        have hval := congrArg (fun j : J => j.1.1) h
        change ({sigma} : Finset (F ≃+* F)) = {tau} at hval
        simpa using hval
      · intro j
        obtain ⟨sigma, hsigma⟩ := Finset.card_eq_one.mp j.2
        refine ⟨sigma, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        simpa [singletonInJ, singletonIndex] using hsigma.symm
    let singletonEquiv : (F ≃+* F) ≃ J :=
      Equiv.ofBijective singletonInJ hsingleton_bijective
    have hsingleton_relation (x : F) :
        ∑ sigma : F ≃+* F,
          g (singletonIndex sigma) * (sigma x) ^ 2 = 0 := by
      have hgx : ∑ s : I, g s * monomial s x = 0 := by
        have hx := congrArg (fun q : QuadraticMap (ZMod 2) F F => q x) hg
        simpa using hx
      have htwo_sum :
          ∑ s : {s : I // ¬s.1.card = 1},
            g s.1 * monomial s.1 x = 0 := by
        apply Finset.sum_eq_zero
        intro s hs
        have hcard2 : s.1.1.card = 2 := s.1.2.resolve_left s.2
        rw [htwo s.1 hcard2]
        simp
      have hsplit := Fintype.sum_subtype_add_sum_subtype
        (fun s : I => s.1.card = 1) (fun s => g s * monomial s x)
      rw [htwo_sum, add_zero, hgx] at hsplit
      calc
        ∑ sigma : F ≃+* F,
            g (singletonIndex sigma) * (sigma x) ^ 2 =
            ∑ s : J, g s.1 * monomial s.1 x := by
          apply Fintype.sum_equiv singletonEquiv
          intro sigma
          change g (singletonIndex sigma) * (sigma x) ^ 2 =
            g (singletonIndex sigma) * monomial (singletonIndex sigma) x
          rw [hmonomial_eval]
          simp [singletonIndex]
        _ = 0 := hsplit
    obtain ⟨autBasis, hAutBasis⟩ :=
      lemma2a_fieldAutomorphisms_basis_linearMaps F
    have hauto_relation :
        ∑ sigma : F ≃+* F, g (singletonIndex sigma) • autBasis sigma = 0 := by
      ext y
      obtain ⟨x, hx⟩ := (surjective_frobenius F 2) y
      change x ^ 2 = y at hx
      rw [← hx]
      simpa [hAutBasis, map_pow] using hsingleton_relation x
    have hcoeff (sigma : F ≃+* F) : g (singletonIndex sigma) = 0 :=
      (Fintype.linearIndependent_iff.mp autBasis.linearIndependent
        (fun tau => g (singletonIndex tau)) hauto_relation) sigma
    intro s hs
    obtain ⟨sigma, hsigma⟩ := Finset.card_eq_one.mp hs
    have hsi : s = singletonIndex sigma := by
      apply Subtype.ext
      simpa [singletonIndex] using hsigma
    rw [hsi]
    exact hcoeff sigma
  have hlinearIndependent : LinearIndependent F monomial := by
    rw [Fintype.linearIndependent_iff]
    intro g hg s
    rcases s.2 with hcard | hcard
    · exact hsingleton_coefficients_zero g hg
        (htwo_coefficients_zero g hg) s hcard
    · exact htwo_coefficients_zero g hg s hcard
  have hdiag_mem_span (sigma tau : F ≃+* F) :
      diag (bilinBasis (sigma, tau)) ∈
        Submodule.span F (Set.range monomial) := by
    let s : I :=
      ⟨{sigma, tau}, Finset.card_pair_eq_one_or_two⟩
    have heq : diag (bilinBasis (sigma, tau)) = monomial s := by
      ext x
      change bilinBasis (sigma, tau) x x = monomial s x
      rw [hBilinBasis, hmonomial_eval]
      by_cases h : sigma = tau
      · subst tau
        simp [s, pow_two]
      · simp [s, h]
    rw [heq]
    exact Submodule.subset_span (Set.mem_range_self s)
  have hspan : Submodule.span F (Set.range monomial) = ⊤ := by
    apply le_antisymm le_top
    intro q hq
    obtain ⟨B, hB⟩ :=
      LinearMap.BilinMap.toQuadraticMap_surjective q
    let coeff := bilinBasis.repr B
    have hsum : ∑ p, coeff p • bilinBasis p = B :=
      bilinBasis.sum_repr B
    have hdiag_sum :
        ∑ p, coeff p • diag (bilinBasis p) = q := by
      calc
        ∑ p, coeff p • diag (bilinBasis p) =
            diag (∑ p, coeff p • bilinBasis p) := by
          rw [map_sum]
          simp
        _ = diag B := by rw [hsum]
        _ = q := by
          change LinearMap.BilinMap.toQuadraticMap B = q
          exact hB
    rw [← hdiag_sum]
    apply Submodule.sum_mem
    intro p hp
    exact Submodule.smul_mem _ _ (hdiag_mem_span p.1 p.2)
  let b : Module.Basis I F (QuadraticMap (ZMod 2) F F) :=
    Module.Basis.mk hlinearIndependent hspan.ge
  have hb (s : I) : b s = monomial s := by
    change Module.Basis.mk hlinearIndependent hspan.ge s = monomial s
    exact Module.Basis.mk_apply hlinearIndependent hspan.ge s
  refine ⟨b, ?_⟩
  intro s x
  rw [hb]
  exact hmonomial_eval s x

end PFAppendixIII
end CFSG.BenderSuzuki



