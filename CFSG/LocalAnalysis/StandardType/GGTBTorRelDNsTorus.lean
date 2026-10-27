module

public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenGenB
public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.FieldTheory.Finite.GaloisField
public import TauCeti.FieldTheory.Finite.FrobeniusFixed

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType

namespace RelDNs

open Polynomial QuadraticMap Module
open CFSG.RankThree.Classical2 CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.Open

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p k : ℕ} {U : Fin k → Submodule F V}
  {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)} {u : Fin k → V} {c t : F}

section PlaneFacts

variable {K : Type} [Field K] [Finite K] [CharP K 2] {U : Type} [AddCommGroup U] [Module K U]
  {Q : QuadraticForm K U}

private theorem eq_one_of_sq_eq_one_plane {a : K} (h : a ^ 2 = 1) : a = 1 := by
  have hfac : (a - 1) * (a - 1) = 0 := by
    calc (a - 1) * (a - 1) = a ^ 2 - 2 * a + 1 := by ring
      _ = 1 - 0 + 1 := by rw [h, CharTwo.two_eq_zero, zero_mul]
      _ = 0 := by rw [sub_zero, one_add_one_eq_two, CharTwo.two_eq_zero]
  rcases mul_eq_zero.mp hfac with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact sub_eq_zero.mp h0

private theorem anisotropic_no_eigenvalue_plane (c : U ≃ₗ[K] U)
    (hc : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hfix : ∀ u, c u = u → u = 0)
    (hani : ∀ u, Q u = 0 → u = 0) :
    ∀ (lam : K) (u : U), u ≠ 0 → c u = lam • u → False := by
  intro lam u hu0 h
  have huQ : Q u ≠ 0 := fun h0 => hu0 (hani u h0)
  have hiso : Q (c u) = Q u := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hc u
  rw [h, QuadraticMap.map_smul, smul_eq_mul] at hiso
  have hsq : lam ^ 2 = 1 := by
    have h0 : (lam ^ 2 - 1) * Q u = 0 := by
      rw [pow_two]
      linear_combination hiso
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' huQ
  have hlam : lam = 1 := eq_one_of_sq_eq_one_plane hsq
  rw [hlam, one_smul] at h
  exact hu0 (hfix u h)

private theorem exists_map_ne_zero_plane (hU : Module.finrank K U = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) : ∃ u : U, Q u ≠ 0 := by
  classical
  haveI : Nontrivial U := Module.nontrivial_of_finrank_pos (by rw [hU]; norm_num)
  by_contra h
  push Not at h
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  refine hu (hQ.1 u fun v => ?_)
  simp [polarBilin_apply_apply, polar, h]

private theorem not_scalar_plane (hU : Module.finrank K U = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (c : U ≃ₗ[K] U)
    (hc : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hfix : ∀ u, c u = u → u = 0) :
    ∀ a : K, (c : Module.End K U) ≠ a • 1 := by
  classical
  intro a ha
  obtain ⟨u, huQ⟩ := exists_map_ne_zero_plane (Q := Q) hU hQ
  have hcu : c u = a • u := by
    have h := congrArg (fun f : Module.End K U => f u) ha
    simpa using h
  have hiso : Q (c u) = Q u := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hc u
  rw [hcu, QuadraticMap.map_smul, smul_eq_mul] at hiso
  have hsq : a ^ 2 = 1 := by
    have h0 : (a ^ 2 - 1) * Q u = 0 := by
      rw [pow_two]
      linear_combination hiso
    rcases mul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h huQ
  have ha1 : a = 1 := by
    have hfac : (a - 1) * (a - 1) = 0 := by
      calc (a - 1) * (a - 1) = a ^ 2 - 2 * a + 1 := by ring
        _ = 1 - 0 + 1 := by rw [hsq, CharTwo.two_eq_zero, zero_mul]
        _ = 0 := by rw [sub_zero, one_add_one_eq_two, CharTwo.two_eq_zero]
    rcases mul_eq_zero.mp hfac with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact sub_eq_zero.mp h0
  haveI : Nontrivial U := Module.nontrivial_of_finrank_pos (by rw [hU]; norm_num)
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  apply hu
  apply hfix u
  have h := congrArg (fun f : Module.End K U => f u) ha
  simpa [ha1] using h

private theorem minpoly_natDegree_eq_two_plane (hU : Module.finrank K U = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (c : U ≃ₗ[K] U)
    (hc : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hfix : ∀ u, c u = u → u = 0) :
    (minpoly K (c : Module.End K U)).natDegree = 2 := by
  haveI : FiniteDimensional K U := .of_finrank_pos (by rw [hU]; norm_num)
  haveI : Nontrivial U := Module.nontrivial_of_finrank_pos (by rw [hU]; norm_num)
  have hle : (minpoly K (c : Module.End K U)).natDegree ≤ 2 := by
    have hdvd := LinearMap.minpoly_dvd_charpoly (c : Module.End K U)
    calc (minpoly K (c : Module.End K U)).natDegree ≤
          ((c : Module.End K U).charpoly).natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd (LinearMap.charpoly_monic _).ne_zero
      _ = Module.finrank K U := LinearMap.charpoly_natDegree (c : Module.End K U)
      _ = 2 := hU
  have hge : 2 ≤ (minpoly K (c : Module.End K U)).natDegree := by
    rw [minpoly.two_le_natDegree_iff (Algebra.IsIntegral.isIntegral (c : Module.End K U))]
    rintro ⟨a, ha⟩
    apply not_scalar_plane (Q := Q) hU hQ c hc hfix a
    rw [Algebra.algebraMap_eq_smul_one] at ha
    exact ha.symm
  omega

private theorem minpoly_not_isRoot_plane (hU : Module.finrank K U = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (c : U ≃ₗ[K] U)
    (hc : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hfix : ∀ u, c u = u → u = 0)
    (hani : ∀ u, Q u = 0 → u = 0) (lam : K) :
    ¬ Polynomial.IsRoot (minpoly K (c : Module.End K U)) lam := by
  haveI : FiniteDimensional K U := .of_finrank_pos (by rw [hU]; norm_num)
  haveI : Nontrivial U := Module.nontrivial_of_finrank_pos (by rw [hU]; norm_num)
  intro hroot
  have hdvd : minpoly K (c : Module.End K U) ∣ (c : Module.End K U).charpoly :=
    LinearMap.minpoly_dvd_charpoly (c : Module.End K U)
  have hchar : Polynomial.IsRoot ((c : Module.End K U).charpoly) lam := by
    rw [Polynomial.IsRoot] at hroot ⊢
    exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdvd hroot
  have hev :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly (c : Module.End K U) lam).2 hchar
  obtain ⟨u, hu⟩ := hev.exists_hasEigenvector
  exact anisotropic_no_eigenvalue_plane (Q := Q) c hc hfix hani lam u hu.2 hu.apply_eq_smul

private theorem minpoly_irreducible_plane (hU : Module.finrank K U = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (c : U ≃ₗ[K] U)
    (hc : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hfix : ∀ u, c u = u → u = 0)
    (hani : ∀ u, Q u = 0 → u = 0) :
    Irreducible (minpoly K (c : Module.End K U)) := by
  have hdeg := minpoly_natDegree_eq_two_plane (Q := Q) hU hQ c hc hfix
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [hdeg]; norm_num
  · intro x
    exact minpoly_not_isRoot_plane (Q := Q) hU hQ c hc hfix hani x

end PlaneFacts

theorem framePoly_monic (t : F) : (OmNsRootGen.framePoly t).Monic := by
  unfold OmNsRootGen.framePoly
  monicity!

theorem framePoly_natDegree (t : F) : (OmNsRootGen.framePoly t).natDegree = 2 := by
  unfold OmNsRootGen.framePoly
  compute_degree!

abbrev FrameField (t : F) : Type := AdjoinRoot (OmNsRootGen.framePoly t)

noncomputable def planeEnd (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    Module.End F ↥(U a) :=
  (((e a : V ≃ₗ[F] V) : V →ₗ[F] V)).restrict (p := U a) (q := U a) (hF.maps_to a)

theorem planeEnd_apply (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k)
    (x : ↥(U a)) :
    ((planeEnd hF a x : ↥(U a)) : V) = (e a : V ≃ₗ[F] V) x :=
  LinearMap.restrict_coe_apply (f := ((e a : V ≃ₗ[F] V) : V →ₗ[F] V)) (hF.maps_to a) x

abbrev frameU (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) : ↥(U a) :=
  ⟨u a, hF.mem a⟩

abbrev frameEU (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) : ↥(U a) :=
  ⟨(e a : V ≃ₗ[F] V) (u a), hF.maps_to a _ (hF.mem a)⟩

theorem planeEnd_frameU (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    planeEnd hF a (frameU hF a) = frameEU hF a := by
  ext
  exact planeEnd_apply hF a _

theorem planeEnd_apply_frameEU (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    ((planeEnd hF a (frameEU hF a) : ↥(U a)) : V) =
      t • (e a : V ≃ₗ[F] V) (u a) + u a := by
  rw [planeEnd_apply]
  exact hF.rot a

theorem linearIndependent_frameU (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    LinearIndependent F ![frameU hF a, frameEU hF a] := by
  rw [LinearIndependent.pair_iff]
  intro x y hxy
  have hxyV : x • u a + y • (e a : V ≃ₗ[F] V) (u a) = 0 := by
    have h := congrArg Subtype.val hxy
    simpa [frameU, frameEU] using h
  have hu0 : u a ≠ 0 := by
    intro h0
    have h1 := hF.quad_eq a
    rw [h0, map_zero] at h1
    exact hF.c_ne_zero h1.symm
  have htc : t * c ≠ 0 := mul_ne_zero hF.t_ne_zero hF.c_ne_zero
  have hpolar0 : polar Q (u a) (u a) = 0 := by
    rw [QuadraticMap.polar_self, CharTwo.two_nsmul]
  by_cases hy : y = 0
  · subst hy
    simp only [zero_smul, add_zero] at hxyV
    exact ⟨(smul_eq_zero.mp hxyV).resolve_right hu0, rfl⟩
  · exfalso
    have h1 : y • (e a : V ≃ₗ[F] V) (u a) = -(x • u a) :=
      eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hxyV)
    have hfu : (e a : V ≃ₗ[F] V) (u a) = (-(x / y)) • u a := by
      calc (e a : V ≃ₗ[F] V) (u a) = y⁻¹ • (y • (e a : V ≃ₗ[F] V) (u a)) := by
            rw [smul_smul, inv_mul_cancel₀ hy, one_smul]
        _ = y⁻¹ • (-(x • u a)) := by rw [h1]
        _ = (-(x / y)) • u a := by
            rw [smul_neg, smul_smul, ← neg_smul, div_eq_mul_inv]
            congr 1
            ring
    have h2 : polar Q (u a) ((e a : V ≃ₗ[F] V) (u a)) =
        (-(x / y)) * polar Q (u a) (u a) := by
      rw [hfu, QuadraticMap.polar_smul_right, smul_eq_mul]
    rw [hF.polar_eq a, hpolar0, mul_zero] at h2
    exact htc h2

theorem span_frameU_eq_top (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    Submodule.span F ({frameU hF a, frameEU hF a} : Set ↥(U a)) = ⊤ := by
  refine Submodule.eq_of_le_of_finrank_eq le_top ?_
  have h2 : Module.finrank F (Submodule.span F ({frameU hF a, frameEU hF a} : Set ↥(U a))) = 2 := by
    rw [show ({frameU hF a, frameEU hF a} : Set ↥(U a)) =
        Set.range ![frameU hF a, frameEU hF a] by ext; simp [or_comm]]
    simpa using finrank_span_eq_card (linearIndependent_frameU hF a)
  rw [h2, finrank_top, hF.finrank_eq a]

theorem planeEnd_aeval_framePoly (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    aeval (planeEnd hF a) (OmNsRootGen.framePoly t) = 0 := by
  set f : Module.End F ↥(U a) := planeEnd hF a with hf
  have hT : aeval f (OmNsRootGen.framePoly t) = f * f + t • f + 1 := by
    simp only [OmNsRootGen.framePoly, map_add, map_mul, map_pow, pow_two, aeval_X, aeval_C,
      aeval_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hfu : f (frameU hF a) = frameEU hF a := by
    rw [hf]
    exact planeEnd_frameU hF a
  have hfeu : ((f (frameEU hF a) : ↥(U a)) : V) =
      t • (e a : V ≃ₗ[F] V) (u a) + u a := by
    rw [hf]
    exact planeEnd_apply_frameEU hF a
  have hfeuSub : f (frameEU hF a) = t • frameEU hF a + frameU hF a := Subtype.ext hfeu
  have hTu : aeval f (OmNsRootGen.framePoly t) (frameU hF a) = 0 := by
    rw [hT]
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply]
    rw [hfu, hfeuSub]
    calc t • frameEU hF a + frameU hF a + t • frameEU hF a + frameU hF a
        = (t • frameEU hF a + t • frameEU hF a) + (frameU hF a + frameU hF a) := by abel
      _ = 0 := by
          rw [← two_smul F (t • frameEU hF a), ← two_smul F (frameU hF a),
            CharTwo.two_eq_zero, zero_smul, zero_smul, add_zero]
  have hTeu : aeval f (OmNsRootGen.framePoly t) (frameEU hF a) = 0 := by
    have hcomm : f * aeval f (OmNsRootGen.framePoly t) = aeval f (OmNsRootGen.framePoly t) * f :=
      CFSG.RankThree.PartOne.KCPrimary.commute_aeval (r := f) (x := f) (Commute.refl f)
        (OmNsRootGen.framePoly t)
    calc aeval f (OmNsRootGen.framePoly t) (frameEU hF a)
        = aeval f (OmNsRootGen.framePoly t) (f (frameU hF a)) := by rw [hfu]
      _ = (aeval f (OmNsRootGen.framePoly t) * f) (frameU hF a) :=
          (Module.End.mul_apply _ _ _).symm
      _ = (f * aeval f (OmNsRootGen.framePoly t)) (frameU hF a) := by rw [hcomm]
      _ = f (aeval f (OmNsRootGen.framePoly t) (frameU hF a)) := Module.End.mul_apply _ _ _
      _ = 0 := by rw [hTu, map_zero]
  refine LinearMap.ext_on (span_frameU_eq_top hF a) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · simpa using hTu
  · simpa using hTeu

@[expose] noncomputable def planeEquiv (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    ↥(U a) ≃ₗ[F] ↥(U a) :=
  LinearEquiv.ofInjectiveOfFinrankEq (planeEnd hF a)
    (by
      intro x y hxy
      apply Subtype.ext
      have h : (e a : V ≃ₗ[F] V) (x : V) = (e a : V ≃ₗ[F] V) (y : V) := by
        have h' := congrArg Subtype.val hxy
        simpa only [planeEnd_apply] using h'
      exact (e a : V ≃ₗ[F] V).injective h)
    rfl

theorem planeEquiv_toLinearMap (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    (planeEquiv hF a : ↥(U a) →ₗ[F] ↥(U a)) = planeEnd hF a := rfl

theorem planeEquiv_apply (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k)
    (x : ↥(U a)) :
    ((planeEquiv hF a x : ↥(U a)) : V) = (e a : V ≃ₗ[F] V) x :=
  planeEnd_apply hF a x

theorem planeEquiv_mem_orthogonalGroup (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (a : Fin k) :
    planeEquiv hF a ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U a).subtype) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  show Q (↑(planeEquiv hF a x) : V) = Q (↑x : V)
  rw [planeEquiv_apply]
  exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
    (CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Q (e a).2) (x : V)

theorem planeEquiv_eq_self_imp_eq_zero (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (a : Fin k) : ∀ x : ↥(U a), planeEquiv hF a x = x → x = 0 := by
  intro x hx
  apply Subtype.ext
  apply hF.eq_zero_of_apply_eq a x x.2
  have h := congrArg Subtype.val hx
  simpa [planeEquiv_apply] using h

theorem planeEquiv_anisotropic (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    ∀ x : ↥(U a), (Q.comp (U a).subtype) x = 0 → x = 0 := by
  intro x hx
  refine Subtype.ext (OmNsRootGen.eq_zero_of_quad_eq_zero_of_not_isPlusType
    (Q := Q) (W := U a) (hF.finrank_eq a) (hF.not_isPlusType a) x.2 ?_)
  simpa using hx

theorem framePoly_irreducible (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    Irreducible (OmNsRootGen.framePoly t) := by
  have hdvd : minpoly F (planeEquiv hF a : ↥(U a) →ₗ[F] ↥(U a)) ∣ OmNsRootGen.framePoly t := by
    rw [planeEquiv_toLinearMap]
    exact minpoly.dvd F (planeEquiv hF a : ↥(U a) →ₗ[F] ↥(U a))
      (p := OmNsRootGen.framePoly t) (planeEnd_aeval_framePoly hF a)
  have hdeg : (minpoly F (planeEquiv hF a : ↥(U a) →ₗ[F] ↥(U a))).natDegree = 2 := by
    rw [planeEquiv_toLinearMap]
    exact minpoly_natDegree_eq_two_plane (Q := Q.comp (U a).subtype) (hF.finrank_eq a)
      (hF.nondeg a) (planeEquiv hF a) (planeEquiv_mem_orthogonalGroup hF a)
      (planeEquiv_eq_self_imp_eq_zero hF a)
  have hmin : minpoly F (planeEquiv hF a : ↥(U a) →ₗ[F] ↥(U a)) = OmNsRootGen.framePoly t := by
    haveI : FiniteDimensional F ↥(U a) :=
      FiniteDimensional.of_finrank_pos (by rw [hF.finrank_eq a]; norm_num)
    have hint : IsIntegral F (planeEquiv hF a : ↥(U a) →ₗ[F] ↥(U a)) :=
      (Module.End.isIntegral (R := F) (M := ↥(U a))).isIntegral _
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (framePoly_monic t) hdvd ?_).symm
    rw [hdeg, framePoly_natDegree]
  have hdec := minpoly_irreducible_plane (Q := Q.comp (U a).subtype) (hF.finrank_eq a)
    (hF.nondeg a) (planeEquiv hF a) (planeEquiv_mem_orthogonalGroup hF a)
    (planeEquiv_eq_self_imp_eq_zero hF a) (planeEquiv_anisotropic hF a)
  rwa [hmin] at hdec

theorem natCard_frameField [Fact (Irreducible (OmNsRootGen.framePoly t))] :
    Nat.card (FrameField t) = Nat.card F ^ 2 := by
  haveI : Module.Finite F (FrameField t) :=
    (AdjoinRoot.isAdjoinRootMonic (OmNsRootGen.framePoly t) (framePoly_monic t)).finite
  have hdim : Module.finrank F (FrameField t) = 2 := by
    rw [(AdjoinRoot.isAdjoinRootMonic (OmNsRootGen.framePoly t) (framePoly_monic t)).finrank,
      framePoly_natDegree]
  rw [Module.natCard_eq_pow_finrank (K := F) (V := FrameField t), hdim]

noncomputable def normOne (t : F) : Subgroup (FrameField t)ˣ :=
  (powMonoidHom (Nat.card F + 1)).ker

theorem isCyclic_normOne [Fact (Irreducible (OmNsRootGen.framePoly t))] :
    IsCyclic (normOne t) := by
  haveI : Module.Finite F (FrameField t) :=
    (AdjoinRoot.isAdjoinRootMonic (OmNsRootGen.framePoly t) (framePoly_monic t)).finite
  haveI : Finite (FrameField t) := Module.finite_of_finite F
  haveI : Finite (FrameField t)ˣ := Finite.of_injective Units.val (fun _ _ h => Units.ext h)
  exact Subgroup.isCyclic (normOne t)

theorem natCard_normOne [Fact (Irreducible (OmNsRootGen.framePoly t))] :
    Nat.card (normOne t) = Nat.card F + 1 := by
  haveI : IsCyclic (normOne t) := isCyclic_normOne
  rw [normOne, IsCyclic.card_powMonoidHom_ker, Nat.card_units, natCard_frameField]
  have hdvd : (Nat.card F + 1) ∣ Nat.card F ^ 2 - 1 := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card F = m + 1 :=
      ⟨Nat.card F - 1, by have := Nat.card_pos (α := F); omega⟩
    rw [hm]
    refine ⟨m, ?_⟩
    have h : (m + 1 + 1) * m + 1 = (m + 1) ^ 2 := by ring
    omega
  exact Nat.gcd_eq_right hdvd

section Root

variable [Fact (Irreducible (OmNsRootGen.framePoly t))]

instance instCharP_frameField : CharP (FrameField t) 2 := by
  refine charP_of_injective_ringHom
    (f := algebraMap F (FrameField t)) (RingHom.injective _) 2

instance instExpChar_frameField : ExpChar (FrameField t) 2 :=
  ExpChar.prime Nat.prime_two

theorem root_sq_add_mul_add_one :
    (AdjoinRoot.root (OmNsRootGen.framePoly t)) ^ 2 +
        t * AdjoinRoot.root (OmNsRootGen.framePoly t) + 1 = 0 := by
  have hpoly : OmNsRootGen.framePoly t = X ^ 2 + C t * X + 1 := rfl
  have h : (AdjoinRoot.mk (OmNsRootGen.framePoly t)) (X ^ 2 + C t * X + 1) = 0 := by
    rw [show X ^ 2 + C t * X + 1 = OmNsRootGen.framePoly t from hpoly.symm,
      AdjoinRoot.mk_self]
  rw [map_add, map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_one] at h
  exact h

theorem root_mul_add :
    (AdjoinRoot.root (OmNsRootGen.framePoly t)) *
        (AdjoinRoot.root (OmNsRootGen.framePoly t) + t) = 1 := by
  calc (AdjoinRoot.root (OmNsRootGen.framePoly t)) *
        (AdjoinRoot.root (OmNsRootGen.framePoly t) + t)
      = (AdjoinRoot.root (OmNsRootGen.framePoly t)) ^ 2 +
          t * AdjoinRoot.root (OmNsRootGen.framePoly t) := by ring
    _ = 1 := CharTwo.add_eq_zero.mp (root_sq_add_mul_add_one (F := F) (t := t))

theorem root_not_mem_fieldRange :
    AdjoinRoot.root (OmNsRootGen.framePoly t) ∉
      (algebraMap F (FrameField t)).fieldRange := by
  intro hmem
  obtain ⟨a, ha⟩ := RingHom.mem_fieldRange.mp hmem
  have hmin : minpoly F (AdjoinRoot.root (OmNsRootGen.framePoly t)) =
      OmNsRootGen.framePoly t :=
    (minpoly.eq_of_irreducible_of_monic (Fact.out : Irreducible (OmNsRootGen.framePoly t))
      (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]) (framePoly_monic t)).symm
  have hdvd : minpoly F (AdjoinRoot.root (OmNsRootGen.framePoly t)) ∣
      (Polynomial.X - Polynomial.C a) := by
    refine minpoly.dvd F (AdjoinRoot.root (OmNsRootGen.framePoly t))
      (p := Polynomial.X - Polynomial.C a) ?_
    rw [← ha]
    simp
  have hle := Polynomial.natDegree_le_of_dvd hdvd (Polynomial.monic_X_sub_C a).ne_zero
  rw [hmin, framePoly_natDegree, Polynomial.natDegree_X_sub_C] at hle
  omega

theorem root_pow_card_eq_add :
    (AdjoinRoot.root (OmNsRootGen.framePoly t)) ^ Nat.card F =
      AdjoinRoot.root (OmNsRootGen.framePoly t) + t := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  let K := FrameField t
  let θ : K := AdjoinRoot.root (OmNsRootGen.framePoly t)
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have hq : Nat.card F = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hfixed : ∀ z : K, z ^ Nat.card F = z ↔ ∃ a : F, algebraMap F K a = z := by
    intro z
    constructor
    · intro hz
      have hmem : z ∈ TauCeti.frobeniusFixedSubfield K 2 (n : ℕ) := by
        rw [TauCeti.mem_frobeniusFixedSubfield, ← hq]
        exact hz
      have hE : (algebraMap F K).fieldRange =
          TauCeti.frobeniusFixedSubfield K 2 (n : ℕ) := by
        refine TauCeti.eq_frobeniusFixedSubfield_of_natCard (K := K) (p := 2) (n := (n : ℕ)) ?_
        have hcard : Nat.card (algebraMap F K).fieldRange = Nat.card F := by
          refine (Nat.card_congr ?_).symm
          refine Equiv.ofBijective
            (fun a : F => (⟨algebraMap F K a,
              RingHom.mem_fieldRange_self (algebraMap F K) a⟩ : (algebraMap F K).fieldRange)) ?_
          refine ⟨?_, ?_⟩
          · intro a b hab
            have h : algebraMap F K a = algebraMap F K b := by
              simpa using Subtype.ext_iff.mp hab
            exact RingHom.injective (algebraMap F K) h
          · rintro ⟨x, hx⟩
            obtain ⟨a, ha⟩ := RingHom.mem_fieldRange.mp hx
            exact ⟨a, Subtype.ext ha⟩
        rw [hcard, hq]
      rw [← hE] at hmem
      exact RingHom.mem_fieldRange.mp hmem
    · rintro ⟨a, rfl⟩
      rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hrootq : (θ ^ Nat.card F) ^ 2 + t * (θ ^ Nat.card F) + 1 = 0 := by
    let φ : K →ₐ[F] K := FiniteField.frobeniusAlgHom F K
    have hφ : ∀ x : K, φ x = x ^ Nat.card F := by
      intro x
      rw [FiniteField.frobeniusAlgHom_apply, Nat.card_eq_fintype_card]
    have h : φ (θ ^ 2 + algebraMap F K t * θ + 1) = 0 := by
      rw [show θ ^ 2 + algebraMap F K t * θ + 1 = 0 from
        root_sq_add_mul_add_one (F := F) (t := t), map_zero]
    have h' : (φ θ) ^ 2 + algebraMap F K t * φ θ + 1 = 0 := by
      simpa only [map_add, map_mul, map_pow, map_one, AlgHom.commutes] using h
    rwa [hφ θ] at h'
  have hθq_ne : θ ^ Nat.card F ≠ θ := by
    intro heq
    obtain ⟨a, ha⟩ := (hfixed θ).mp heq
    have hmem' : algebraMap F K a ∈ (algebraMap F K).fieldRange :=
      RingHom.mem_fieldRange_self (algebraMap F K) a
    rw [ha] at hmem'
    exact root_not_mem_fieldRange (F := F) (t := t) hmem'
  have hsum : θ + (θ + t) = t := by
    calc θ + (θ + t) = (θ + θ) + t := by abel
      _ = t := by rw [CharTwo.add_self_eq_zero, zero_add]
  have hfac : (θ ^ Nat.card F + θ) * (θ ^ Nat.card F + θ + t) = 0 := by
    have hy1 : (θ ^ Nat.card F) ^ 2 + t * (θ ^ Nat.card F) = 1 :=
      CharTwo.add_eq_zero.mp hrootq
    have hθ1 : θ ^ 2 + t * θ = 1 :=
      CharTwo.add_eq_zero.mp (root_sq_add_mul_add_one (F := F) (t := t))
    calc (θ ^ Nat.card F + θ) * (θ ^ Nat.card F + θ + t)
        = ((θ ^ Nat.card F) ^ 2 + t * (θ ^ Nat.card F)) + (θ ^ 2 + t * θ) := by
          rw [show (θ ^ Nat.card F + θ) * (θ ^ Nat.card F + θ + t) =
              (θ ^ Nat.card F + θ) ^ 2 + (θ ^ Nat.card F + θ) * t from by ring,
            CharTwo.add_sq]
          ring
      _ = 1 + 1 := by rw [hy1, hθ1]
      _ = 0 := CharTwo.add_self_eq_zero 1
  rw [mul_eq_zero] at hfac
  rcases hfac with h | h
  · exact absurd (CharTwo.add_eq_zero.mp h) hθq_ne
  · have hy : θ ^ Nat.card F = algebraMap F K t + θ :=
      CharTwo.add_eq_iff_eq_add.mp (CharTwo.add_eq_zero.mp h)
    rw [hy]
    exact add_comm _ _

theorem root_pow_card_add_one :
    (AdjoinRoot.root (OmNsRootGen.framePoly t)) ^ (Nat.card F + 1) = 1 := by
  rw [pow_succ, mul_comm, root_pow_card_eq_add, root_mul_add]

theorem root_ne_zero : AdjoinRoot.root (OmNsRootGen.framePoly t) ≠ 0 := by
  intro h0
  have h := root_pow_card_add_one (F := F) (t := t)
  rw [h0, zero_pow (by omega : Nat.card F + 1 ≠ 0)] at h
  exact zero_ne_one h

noncomputable def rootNormOne : normOne t :=
  ⟨Units.mk0 (AdjoinRoot.root (OmNsRootGen.framePoly t)) (root_ne_zero (F := F) (t := t)), by
    refine MonoidHom.mem_ker.mpr (Units.ext ?_)
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0]
    exact root_pow_card_add_one (F := F) (t := t)⟩

theorem val_rootNormOne :
    (((rootNormOne (F := F) (t := t) : normOne t) : (FrameField t)ˣ) : FrameField t) =
      AdjoinRoot.root (OmNsRootGen.framePoly t) := by
  rw [show ((rootNormOne (F := F) (t := t) : normOne t) : (FrameField t)ˣ) =
      Units.mk0 (AdjoinRoot.root (OmNsRootGen.framePoly t))
        (root_ne_zero (F := F) (t := t)) from rfl, Units.val_mk0]

end Root

section Plane

variable [Fact (Irreducible (OmNsRootGen.framePoly t))]

theorem finrank_frameField : Module.finrank F (FrameField t) = 2 := by
  haveI : Module.Finite F (FrameField t) :=
    (AdjoinRoot.isAdjoinRootMonic (OmNsRootGen.framePoly t) (framePoly_monic t)).finite
  rw [(AdjoinRoot.isAdjoinRootMonic (OmNsRootGen.framePoly t) (framePoly_monic t)).finrank,
    framePoly_natDegree]

theorem planeAlg_aeval_zero (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (a : Fin k) :
    (OmNsRootGen.framePoly t).eval₂
      (↑(Algebra.ofId F (Algebra.adjoin F ({planeEnd hF a} :
        Set (Module.End F ↥(U a))))))
      (⟨planeEnd hF a, Algebra.self_mem_adjoin_singleton F (planeEnd hF a)⟩ :
        Algebra.adjoin F ({planeEnd hF a} : Set (Module.End F ↥(U a)))) = 0 := by
  apply Subtype.ext
  change (Subalgebra.val (Algebra.adjoin F ({planeEnd hF a} :
      Set (Module.End F ↥(U a)))))
    ((OmNsRootGen.framePoly t).eval₂
      (↑(Algebra.ofId F (Algebra.adjoin F ({planeEnd hF a} :
        Set (Module.End F ↥(U a))))))
      (⟨planeEnd hF a, Algebra.self_mem_adjoin_singleton F (planeEnd hF a)⟩ :
        Algebra.adjoin F ({planeEnd hF a} : Set (Module.End F ↥(U a))))) = 0
  have hof : (↑(Algebra.ofId F (Algebra.adjoin F ({planeEnd hF a} :
      Set (Module.End F ↥(U a))))) : F →+* Algebra.adjoin F ({planeEnd hF a} :
        Set (Module.End F ↥(U a)))) =
      algebraMap F (Algebra.adjoin F ({planeEnd hF a} : Set (Module.End F ↥(U a)))) := rfl
  rw [hof, ← Polynomial.aeval_def]
  rw [← Polynomial.aeval_algHom_apply
    (Subalgebra.val (Algebra.adjoin F ({planeEnd hF a} : Set (Module.End F ↥(U a)))))
    (⟨planeEnd hF a, Algebra.self_mem_adjoin_singleton F (planeEnd hF a)⟩ :
      Algebra.adjoin F ({planeEnd hF a} : Set (Module.End F ↥(U a))))
    (OmNsRootGen.framePoly t)]
  rw [show (Subalgebra.val (Algebra.adjoin F ({planeEnd hF a} :
      Set (Module.End F ↥(U a)))))
      (⟨planeEnd hF a, Algebra.self_mem_adjoin_singleton F (planeEnd hF a)⟩ :
        Algebra.adjoin F ({planeEnd hF a} : Set (Module.End F ↥(U a)))) = planeEnd hF a from rfl]
  exact planeEnd_aeval_framePoly hF a

@[expose] noncomputable def planeAlg (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (a : Fin k) : FrameField t →ₐ[F] Module.End F ↥(U a) :=
  (Subalgebra.val (Algebra.adjoin F ({planeEnd hF a} : Set (Module.End F ↥(U a))))).comp
    (AdjoinRoot.liftAlgHom (OmNsRootGen.framePoly t)
      (Algebra.ofId F (Algebra.adjoin F ({planeEnd hF a} :
        Set (Module.End F ↥(U a)))))
      (⟨planeEnd hF a, Algebra.self_mem_adjoin_singleton F (planeEnd hF a)⟩ :
        Algebra.adjoin F ({planeEnd hF a} : Set (Module.End F ↥(U a))))
      (planeAlg_aeval_zero hF a))

theorem planeAlg_root (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    planeAlg hF a (AdjoinRoot.root (OmNsRootGen.framePoly t)) = planeEnd hF a := by
  change (Subalgebra.val (Algebra.adjoin F ({planeEnd hF a} :
      Set (Module.End F ↥(U a)))))
    ((AdjoinRoot.liftAlgHom (OmNsRootGen.framePoly t)
      (Algebra.ofId F (Algebra.adjoin F ({planeEnd hF a} :
        Set (Module.End F ↥(U a)))))
      (⟨planeEnd hF a, Algebra.self_mem_adjoin_singleton F (planeEnd hF a)⟩ :
        Algebra.adjoin F ({planeEnd hF a} : Set (Module.End F ↥(U a))))
      (planeAlg_aeval_zero hF a)) (AdjoinRoot.root (OmNsRootGen.framePoly t))) = planeEnd hF a
  rw [AdjoinRoot.liftAlgHom_root]
  rfl

theorem planeAlg_commute_planeEnd (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k)
    (z : FrameField t) : Commute (planeAlg hF a z) (planeEnd hF a) := by
  rw [← planeAlg_root hF a]
  show planeAlg hF a z * planeAlg hF a (AdjoinRoot.root (OmNsRootGen.framePoly t)) =
    planeAlg hF a (AdjoinRoot.root (OmNsRootGen.framePoly t)) * planeAlg hF a z
  rw [← map_mul, ← map_mul, mul_comm z (AdjoinRoot.root (OmNsRootGen.framePoly t))]

theorem planeAlg_injective (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    Function.Injective (planeAlg hF a) := by
  haveI : Nontrivial ↥(U a) :=
    Module.nontrivial_of_finrank_pos (by rw [hF.finrank_eq a]; norm_num)
  haveI : Nontrivial (Module.End F ↥(U a)) := by
    obtain ⟨v, hv⟩ := exists_ne (0 : ↥(U a))
    exact ⟨1, 0, fun h => hv (by
      simpa using congrArg (fun f : Module.End F ↥(U a) => f v) h)⟩
  exact RingHom.injective (planeAlg hF a).toRingHom

theorem planeEnd_frameEU (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    planeEnd hF a (frameEU hF a) = t • frameEU hF a + frameU hF a :=
  Subtype.ext (planeEnd_apply_frameEU hF a)

theorem planeAlg_eq_zero_of_apply_frameU (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (a : Fin k) {z : FrameField t} (hz : planeAlg hF a z (frameU hF a) = 0) :
    planeAlg hF a z = 0 := by
  set T : Module.End F ↥(U a) := planeAlg hF a z with hT
  have hTu : T (frameU hF a) = 0 := by rw [hT]; exact hz
  have hcomm : T * planeEnd hF a = planeEnd hF a * T := by
    rw [hT]; exact (planeAlg_commute_planeEnd hF a z).eq
  have hTeu : T (frameEU hF a) = 0 := by
    calc T (frameEU hF a) = T (planeEnd hF a (frameU hF a)) := by rw [planeEnd_frameU]
      _ = (T * planeEnd hF a) (frameU hF a) := (Module.End.mul_apply _ _ _).symm
      _ = (planeEnd hF a * T) (frameU hF a) := by rw [hcomm]
      _ = planeEnd hF a (T (frameU hF a)) := Module.End.mul_apply _ _ _
      _ = 0 := by rw [hTu, map_zero]
  refine LinearMap.ext_on (span_frameU_eq_top hF a) ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · simpa using hTu
  · simpa using hTeu

noncomputable def planeToField (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    FrameField t →ₗ[F] ↥(U a) where
  toFun z := planeAlg hF a z (frameU hF a)
  map_add' z w := by simp
  map_smul' r z := by simp

theorem planeToField_injective (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    Function.Injective (planeToField hF a) := by
  intro z w hzw
  have hkill : planeAlg hF a (z - w) (frameU hF a) = 0 := by
    rw [map_sub, LinearMap.sub_apply]
    have h' : planeAlg hF a z (frameU hF a) = planeAlg hF a w (frameU hF a) := hzw
    rw [h', sub_self]
  have hzero : planeAlg hF a (z - w) = 0 := planeAlg_eq_zero_of_apply_frameU hF a hkill
  exact sub_eq_zero.mp (planeAlg_injective hF a (by rw [hzero, map_zero]))

@[expose] noncomputable def planeFieldEquiv (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (a : Fin k) : FrameField t ≃ₗ[F] ↥(U a) :=
  LinearEquiv.ofBijective (planeToField hF a)
    ⟨planeToField_injective hF a,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by rw [finrank_frameField, hF.finrank_eq a])).mp (planeToField_injective hF a)⟩

theorem planeFieldEquiv_apply (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k)
    (z : FrameField t) :
    planeFieldEquiv hF a z = planeAlg hF a z (frameU hF a) := by
  simp only [planeFieldEquiv, LinearEquiv.ofBijective_apply, planeToField]
  rfl

theorem planeFieldEquiv_one (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    planeFieldEquiv hF a 1 = frameU hF a := by
  rw [planeFieldEquiv_apply, map_one]
  rfl

theorem planeFieldEquiv_root (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    planeFieldEquiv hF a (AdjoinRoot.root (OmNsRootGen.framePoly t)) = frameEU hF a := by
  rw [planeFieldEquiv_apply, planeAlg_root, planeEnd_frameU]

theorem root_linearIndependent :
    LinearIndependent F ![(1 : FrameField t),
      AdjoinRoot.root (OmNsRootGen.framePoly t)] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  by_cases hb : b = 0
  · subst hb
    simp only [zero_smul, add_zero] at hab
    exact ⟨(smul_eq_zero.mp hab).resolve_right one_ne_zero, rfl⟩
  · exfalso
    have hbθ : b • AdjoinRoot.root (OmNsRootGen.framePoly t) = a • (1 : FrameField t) :=
      (CharTwo.add_eq_zero.mp hab).symm
    have hθ : AdjoinRoot.root (OmNsRootGen.framePoly t) =
        algebraMap F (FrameField t) (a / b) := by
      calc AdjoinRoot.root (OmNsRootGen.framePoly t) =
            b⁻¹ • (b • AdjoinRoot.root (OmNsRootGen.framePoly t)) := by
              rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
        _ = b⁻¹ • (a • (1 : FrameField t)) := by rw [hbθ]
        _ = (b⁻¹ * a) • (1 : FrameField t) := by rw [smul_smul]
        _ = algebraMap F (FrameField t) (a / b) := by
              rw [Algebra.smul_def, mul_one, div_eq_mul_inv, mul_comm b⁻¹ a]
    apply root_not_mem_fieldRange (F := F) (t := t)
    rw [hθ]
    exact RingHom.mem_fieldRange_self (algebraMap F (FrameField t)) (a / b)

noncomputable def rootBasis : Basis (Fin 2) F (FrameField t) :=
  basisOfLinearIndependentOfCardEqFinrank
    (b := ![(1 : FrameField t), AdjoinRoot.root (OmNsRootGen.framePoly t)])
    root_linearIndependent (by simp [finrank_frameField])

theorem rootBasis_zero : rootBasis (0 : Fin 2) = (1 : FrameField t) := by
  dsimp only [rootBasis]; simp

theorem rootBasis_one :
    rootBasis (1 : Fin 2) = AdjoinRoot.root (OmNsRootGen.framePoly t) := by
  dsimp only [rootBasis]; simp

theorem exists_coord_field (z : FrameField t) :
    ∃ x y : F, z = x • (1 : FrameField t) +
      y • AdjoinRoot.root (OmNsRootGen.framePoly t) := by
  refine ⟨rootBasis.repr z 0, rootBasis.repr z 1, ?_⟩
  conv_lhs => rw [← rootBasis.sum_repr z, Fin.sum_univ_two]
  rw [rootBasis_zero, rootBasis_one]

theorem exists_coord (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k)
    (w : ↥(U a)) :
    ∃ x y : F, w = x • frameU hF a + y • frameEU hF a := by
  obtain ⟨z, rfl⟩ := (planeFieldEquiv hF a).surjective w
  obtain ⟨x, y, hz⟩ := exists_coord_field (F := F) (t := t) z
  refine ⟨x, y, ?_⟩
  rw [hz, map_add, map_smul, map_smul, planeFieldEquiv_one, planeFieldEquiv_root]

theorem mul_pow_card_coord (x y : F) :
    (x • (1 : FrameField t) + y • AdjoinRoot.root (OmNsRootGen.framePoly t)) *
        (x • (1 : FrameField t) +
          y • AdjoinRoot.root (OmNsRootGen.framePoly t)) ^ Nat.card F =
      algebraMap F (FrameField t) (x ^ 2 + t * x * y + y ^ 2) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  let K := FrameField t
  let θ : K := AdjoinRoot.root (OmNsRootGen.framePoly t)
  let φ : K →ₐ[F] K := FiniteField.frobeniusAlgHom F K
  have hφ : ∀ z : K, φ z = z ^ Nat.card F := by
    intro z
    rw [FiniteField.frobeniusAlgHom_apply, Nat.card_eq_fintype_card]
  have hφθ : φ θ = θ + t := by
    rw [hφ θ, root_pow_card_eq_add]
  have hzq : (x • (1 : K) + y • θ) ^ Nat.card F = x • (1 : K) + y • (θ + t) := by
    rw [← hφ, map_add, map_smul, map_smul, map_one, hφθ]
  have hsum : θ + (θ + t) = t := by
    calc θ + (θ + t) = (θ + θ) + t := by abel
      _ = t := by rw [CharTwo.add_self_eq_zero, zero_add]
  have hmul : θ * (θ + t) = 1 := root_mul_add (F := F) (t := t)
  rw [hzq]
  simp only [Algebra.smul_def, mul_one]
  calc (algebraMap F K x + algebraMap F K y * θ) *
        (algebraMap F K x + algebraMap F K y * (θ + t))
      = algebraMap F K x * algebraMap F K x +
          algebraMap F K x * algebraMap F K y * (θ + (θ + t)) +
          algebraMap F K y * algebraMap F K y * (θ * (θ + t)) := by ring
    _ = algebraMap F K x * algebraMap F K x +
          algebraMap F K x * algebraMap F K y * t +
          algebraMap F K y * algebraMap F K y * 1 := by simp [hsum, hmul]
    _ = algebraMap F K (x ^ 2 + t * x * y + y ^ 2) := by
        have hx2 : algebraMap F K x * algebraMap F K x = algebraMap F K (x ^ 2) := by
          rw [← pow_two, ← map_pow]
        have hy2 : algebraMap F K y * algebraMap F K y * 1 = algebraMap F K (y ^ 2) := by
          rw [mul_one, ← pow_two, ← map_pow]
        have hxy : algebraMap F K x * algebraMap F K y * t = algebraMap F K (x * y * t) := by
          rw [← AdjoinRoot.algebraMap_eq, ← map_mul, ← map_mul]
        rw [hx2, hy2, hxy, ← map_add, ← map_add]
        congr 1
        ring

abbrev normOneVal (z : normOne t) : FrameField t :=
  ((z : (FrameField t)ˣ) : FrameField t)

theorem norm_coord_eq_one (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k)
    (z : normOne t) {x y : F}
    (hz : normOneVal (F := F) (t := t) z = x • (1 : FrameField t) +
      y • AdjoinRoot.root (OmNsRootGen.framePoly t)) :
    x ^ 2 + t * x * y + y ^ 2 = 1 := by
  have hmem : ((z : (FrameField t)ˣ) : FrameField t) ^ (Nat.card F + 1) = 1 := by
    have h := MonoidHom.mem_ker.mp z.2
    rw [powMonoidHom_apply] at h
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hzq : normOneVal (F := F) (t := t) z *
      normOneVal (F := F) (t := t) z ^ Nat.card F = 1 := by
    rw [pow_succ, mul_comm] at hmem
    exact hmem
  have h2 := mul_pow_card_coord (F := F) (t := t) x y
  rw [← hz, hzq] at h2
  have h2' : algebraMap F (FrameField t) (x ^ 2 + t * x * y + y ^ 2) = 1 := h2.symm
  exact RingHom.injective (algebraMap F (FrameField t)) (h2'.trans (map_one _).symm)

theorem quad_frameU_add (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k)
    (x y : F) :
    Q (x • u a + y • (e a : V ≃ₗ[F] V) (u a)) =
      c * (x ^ 2 + t * x * y + y ^ 2) := by
  have hQeu : Q ((e a : V ≃ₗ[F] V) (u a)) = c := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
      (CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Q (e a).2), hF.quad_eq a]
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hF.quad_eq a, hQeu,
    hF.polar_eq a]
  simp only [smul_eq_mul]
  ring

theorem planeAlg_frameU (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k)
    (z : FrameField t) {x y : F}
    (hz : z = x • (1 : FrameField t) +
      y • AdjoinRoot.root (OmNsRootGen.framePoly t)) :
    planeAlg hF a z (frameU hF a) = x • frameU hF a + y • frameEU hF a := by
  rw [hz, map_add, map_smul, map_smul, map_one, planeAlg_root]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    planeEnd_frameU]

theorem planeAlg_frameEU (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k)
    (z : FrameField t) {x y : F}
    (hz : z = x • (1 : FrameField t) +
      y • AdjoinRoot.root (OmNsRootGen.framePoly t)) :
    planeAlg hF a z (frameEU hF a) = y • frameU hF a + (x + t * y) • frameEU hF a := by
  rw [hz, map_add, map_smul, map_smul, map_one, planeAlg_root]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    planeEnd_frameEU]
  module

theorem quad_planeEnd (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k)
    (w : ↥(U a)) :
    (Q.comp (U a).subtype) (planeEnd hF a w) = (Q.comp (U a).subtype) w := by
  have h := planeEquiv_mem_orthogonalGroup hF a
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at h
  have := h w
  rwa [show (planeEquiv hF a) w = planeEnd hF a w from rfl] at this

theorem quad_planeAlg (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k)
    (z : normOne t) (w : ↥(U a)) :
    (Q.comp (U a).subtype) (planeAlg hF a (normOneVal (F := F) (t := t) z) w) =
      (Q.comp (U a).subtype) w := by
  obtain ⟨α, β, hz⟩ := exists_coord_field (F := F) (t := t)
    (normOneVal (F := F) (t := t) z)
  have hzu := planeAlg_frameU hF a (normOneVal (F := F) (t := t) z) hz
  have hzeu := planeAlg_frameEU hF a (normOneVal (F := F) (t := t) z) hz
  have hn := norm_coord_eq_one hF a z hz
  have hQzu : (Q.comp (U a).subtype)
      (planeAlg hF a (normOneVal (F := F) (t := t) z) (frameU hF a)) = c := by
    rw [hzu]
    change Q ((α • frameU hF a + β • frameEU hF a : ↥(U a)) : V) = c
    rw [show ((α • frameU hF a + β • frameEU hF a : ↥(U a)) : V) =
        α • u a + β • (e a : V ≃ₗ[F] V) (u a) by simp [frameU, frameEU]]
    rw [quad_frameU_add (t := t) hF a α β, hn, mul_one]
  have hQzeu : (Q.comp (U a).subtype)
      (planeAlg hF a (normOneVal (F := F) (t := t) z) (frameEU hF a)) = c := by
    have hstep : planeAlg hF a (normOneVal (F := F) (t := t) z) (frameEU hF a) =
        planeEnd hF a (planeAlg hF a (normOneVal (F := F) (t := t) z) (frameU hF a)) := by
      simp only [hzeu, hzu, map_add, map_smul, planeEnd_frameU, planeEnd_frameEU]
      module
    rw [hstep, quad_planeEnd, hQzu]
  have hpuu : polar Q (u a) (u a) = 0 := by
    rw [QuadraticMap.polar_self, CharTwo.two_nsmul]
  have hpeu : polar Q ((e a : V ≃ₗ[F] V) (u a)) ((e a : V ≃ₗ[F] V) (u a)) = 0 := by
    rw [QuadraticMap.polar_self, CharTwo.two_nsmul]
  have hpeuu : polar Q ((e a : V ≃ₗ[F] V) (u a)) (u a) = t * c := by
    rw [QuadraticMap.polar_comm, hF.polar_eq a]
  have hB : polar (Q.comp (U a).subtype)
      (planeAlg hF a (normOneVal (F := F) (t := t) z) (frameU hF a))
      (planeAlg hF a (normOneVal (F := F) (t := t) z) (frameEU hF a)) = t * c := by
    rw [hzu, hzeu]
    change polar Q (α • u a + β • (e a : V ≃ₗ[F] V) (u a))
      (β • u a + (α + t * β) • (e a : V ≃ₗ[F] V) (u a)) = t * c
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right]
    simp only [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hpuu, hpeu,
      hF.polar_eq a, hpeuu, smul_eq_mul, mul_zero, add_zero, zero_add]
    calc β * (β * (t * c)) + (α + t * β) * (α * (t * c))
        = (α ^ 2 + t * α * β + β ^ 2) * (t * c) := by ring
      _ = 1 * (t * c) := by rw [hn]
      _ = t * c := by rw [one_mul]
  obtain ⟨s, r, hw⟩ := exists_coord hF a w
  have hQw : (Q.comp (U a).subtype) w = c * (s ^ 2 + t * s * r + r ^ 2) := by
    rw [hw]
    change Q ((s • frameU hF a + r • frameEU hF a : ↥(U a)) : V) = _
    rw [show ((s • frameU hF a + r • frameEU hF a : ↥(U a)) : V) =
        s • u a + r • (e a : V ≃ₗ[F] V) (u a) by simp [frameU, frameEU]]
    exact quad_frameU_add hF a s r
  rw [hQw, hw, map_add, map_smul, map_smul]
  rw [QuadraticMap.map_add (Q.comp (U a).subtype),
    QuadraticMap.map_smul (Q.comp (U a).subtype),
    QuadraticMap.map_smul (Q.comp (U a).subtype),
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hQzu, hQzeu, hB]
  simp only [smul_eq_mul]
  ring

noncomputable def planeUnit (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    normOne t →* (↥(U a) →ₗ[F] ↥(U a))ˣ :=
  (Units.map (planeAlg hF a).toRingHom.toMonoidHom).comp (Subgroup.subtype (normOne t))

noncomputable def planeLinEquiv (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    normOne t →* (↥(U a) ≃ₗ[F] ↥(U a)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F ↥(U a)).toMonoidHom.comp (planeUnit hF a)

theorem planeLinEquiv_apply (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k)
    (z : normOne t) (x : ↥(U a)) :
    (planeLinEquiv hF a z) x = planeAlg hF a (normOneVal (F := F) (t := t) z) x := by
  simp only [planeLinEquiv, MonoidHom.comp_apply,
    LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap]
  rfl

theorem planeLinEquiv_mem_orthogonalGroup (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (a : Fin k) (z : normOne t) :
    planeLinEquiv hF a z ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U a).subtype) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro w
  rw [planeLinEquiv_apply]
  exact quad_planeAlg hF a z w

theorem planeNondeg (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q (U a) := by
  intro x hx h
  have h1 : (⟨x, hx⟩ : ↥(U a)) = 0 :=
    (hF.nondeg a).1 ⟨x, hx⟩ fun y => by
      rw [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype_cent]
      exact h y y.2
  exact congrArg Subtype.val h1

theorem mem_orthBlk_perp_iff {W : Submodule F V} {x : V} :
    x ∈ CFSG.LieType.SeitzGeneration.OrthBlk.perp Q W ↔ x ∈ polarPerp Q W := by
  rw [CFSG.LieType.SeitzGeneration.OrthBlk.mem_perp, mem_polarPerp_iff]

noncomputable def planeRot (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    normOne t →* (V ≃ₗ[F] V) :=
  (CFSG.LieType.SeitzGeneration.OrthNS.extU (planeNondeg hF a)).comp (planeLinEquiv hF a)

theorem planeRot_apply_mem (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k)
    (z : normOne t) {w : V} (hw : w ∈ U a) :
    planeRot hF a z w = ((planeAlg hF a (normOneVal (F := F) (t := t) z)) ⟨w, hw⟩ : V) := by
  change CFSG.LieType.SeitzGeneration.OrthNS.extU (planeNondeg hF a)
    (planeLinEquiv hF a z) w = _
  rw [CFSG.LieType.SeitzGeneration.OrthNS.extU_apply_mem (planeNondeg hF a) _ hw]
  rw [planeLinEquiv_apply]

theorem planeRot_apply_perp (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k)
    (z : normOne t) {w : V} (hw : w ∈ polarPerp Q (U a)) :
    planeRot hF a z w = w := by
  change CFSG.LieType.SeitzGeneration.OrthNS.extU (planeNondeg hF a)
    (planeLinEquiv hF a z) w = w
  refine CFSG.LieType.SeitzGeneration.OrthNS.extU_apply_perp (planeNondeg hF a) _ ?_
  rwa [mem_orthBlk_perp_iff]

theorem planeRot_mem_orthogonalGroup (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (a : Fin k) (z : normOne t) :
    planeRot hF a z ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  have hφ : planeLinEquiv hF a z ∈
      TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (U a)) := by
    rw [show Q.restrict (U a) = Q.comp (U a).subtype from by
      ext u
      rw [QuadraticMap.restrict_apply]
      rfl]
    exact planeLinEquiv_mem_orthogonalGroup hF a z
  change CFSG.LieType.SeitzGeneration.OrthNS.extU (planeNondeg hF a)
    (planeLinEquiv hF a z) ∈ TauCeti.QuadraticMap.orthogonalGroup Q
  exact OmNsRootGen.extU_mem_orthogonalGroup (hU := planeNondeg hF a) hφ

theorem planeRot_commute (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) {a b : Fin k}
    (hab : a ≠ b) (z z' : normOne t) :
    Commute (planeRot hF a z) (planeRot hF b z') := by
  have hg : planeRot hF b z' ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    planeRot_mem_orthogonalGroup hF b z'
  have hfix : ∀ w ∈ U a, planeRot hF b z' w = w := by
    intro w hw
    refine planeRot_apply_perp hF b z' ?_
    rw [mem_polarPerp_iff]
    intro y hy
    exact hF.perp b a (fun h => hab h.symm) y hy w hw
  change CFSG.LieType.SeitzGeneration.OrthNS.extU (planeNondeg hF a) (planeLinEquiv hF a z) *
    planeRot hF b z' = planeRot hF b z' *
      CFSG.LieType.SeitzGeneration.OrthNS.extU (planeNondeg hF a) (planeLinEquiv hF a z)
  exact OmNsRootGen.extU_commute_of_fixes (hU := planeNondeg hF a) hg hfix (planeLinEquiv hF a z)

theorem planeRot_pow_card_add_one (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (a : Fin k) (z : normOne t) :
    planeRot hF a z ^ (Nat.card F + 1) = 1 := by
  have hz : z ^ (Nat.card F + 1) = 1 := by
    apply Subtype.ext
    have h := MonoidHom.mem_ker.mp z.2
    rwa [powMonoidHom_apply] at h
  rw [← map_pow (planeRot hF a) z (Nat.card F + 1), hz, map_one]

theorem planeRot_rootNormOne (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    planeRot hF a (rootNormOne (F := F) (t := t)) = (e a : V ≃ₗ[F] V) := by
  change CFSG.LieType.SeitzGeneration.OrthNS.extU (planeNondeg hF a)
    (planeLinEquiv hF a (rootNormOne (F := F) (t := t))) = (e a : V ≃ₗ[F] V)
  refine CFSG.LieType.SeitzGeneration.OrthNS.extU_eq_of_agree (planeNondeg hF a) ?_ ?_
  · intro u
    rw [planeLinEquiv_apply]
    rw [show normOneVal (F := F) (t := t) (rootNormOne (F := F) (t := t)) =
        AdjoinRoot.root (OmNsRootGen.framePoly t) from val_rootNormOne]
    rw [planeAlg_root]
    rfl
  · intro r hr
    exact hF.apply_of_perp a r (by rwa [mem_orthBlk_perp_iff] at hr)

theorem odd_natCard_add_one : Odd (Nat.card F + 1) := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have hq : Nat.card F = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  rw [hq]
  obtain ⟨m, hm⟩ : ∃ m, (n : ℕ) = m + 1 := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
  have heven : Even (2 ^ (n : ℕ)) := by
    rw [hm, pow_succ]
    exact ⟨2 ^ m, by ring⟩
  exact Even.add_one heven

noncomputable def planeRotDerived (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0) (a : Fin k) :
    normOne t →* ↥(orthDerived Q) :=
  MonoidHom.codRestrict (planeRot hF a) (orthDerived Q) fun z =>
    CFSG.LieType.SeitzGeneration.mem_orthDerived_of_odd_pow hQ hT
      (odd_natCard_add_one (F := F))
      (planeRot_mem_orthogonalGroup hF a z) (planeRot_pow_card_add_one hF a z)

theorem planeRotDerived_commute (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {a b : Fin k} (hab : a ≠ b) (x y : normOne t) :
    Commute (planeRotDerived hF hQ hT a x) (planeRotDerived hF hQ hT b y) :=
  Subtype.ext (planeRot_commute hF hab x y).eq

noncomputable def frameTorusFull (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    (Fin k → normOne t) →* ↥(orthDerived Q) :=
  MonoidHom.noncommPiCoprod (fun a => planeRotDerived hF hQ hT a)
    (show Pairwise (fun i j => ∀ x y : normOne t,
        Commute ((fun a => planeRotDerived hF hQ hT a) i x)
          ((fun a => planeRotDerived hF hQ hT a) j y)) from
      fun {a b : Fin k} hab x y => planeRotDerived_commute hF hQ hT hab x y)

private theorem noncommProd_apply_of_eq_of_ne {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (g : ι → V ≃ₗ[F] V)
    (hcomm : (s : Set ι).Pairwise fun x y => Commute (g x) (g y)) {c : ι} (hc : c ∈ s)
    {x : V} (h : ∀ i ∈ s, i ≠ c → g i x = x) :
    (s.noncommProd g hcomm) x = g c x := by
  induction s using Finset.induction_on with
  | empty => exact absurd hc (Finset.notMem_empty c)
  | insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem s a g hcomm ha]
    have hcomm' : (s : Set ι).Pairwise fun x y => Commute (g x) (g y) :=
      hcomm.mono fun _ hy => Finset.mem_insert_of_mem hy
    by_cases hac : a = c
    · subst hac
      have h1 : (s.noncommProd g hcomm') x = x := by
        refine Finset.noncommProd_induction s g hcomm' (fun y => y x = x) ?_ rfl ?_
        · intro u v hu hv
          rw [LinearEquiv.mul_apply, hv, hu]
        · intro i hi
          exact h i (Finset.mem_insert_of_mem hi) (fun hia => ha (hia ▸ hi))
      rw [LinearEquiv.mul_apply, h1]
    · have hcs : c ∈ s := by
        rcases Finset.mem_insert.mp hc with hca | hcs
        · exact absurd hca.symm hac
        · exact hcs
      have h1 : (s.noncommProd g hcomm') x = g c x :=
        ih hcomm' hcs fun i hi hic => h i (Finset.mem_insert_of_mem hi) hic
      rw [LinearEquiv.mul_apply, h1]
      have hcomm_ac : Commute (g a) (g c) :=
        hcomm (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hcs) hac
      rw [← LinearEquiv.mul_apply, hcomm_ac.eq, LinearEquiv.mul_apply,
        h a (Finset.mem_insert_self a s) hac]

theorem frameTorusFull_coe (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (x : Fin k → normOne t) :
    ((frameTorusFull hF hQ hT x : ↥(orthDerived Q)) : V ≃ₗ[F] V) =
      (Finset.univ.noncommProd (fun i => planeRot hF i (x i))
        (fun {i} _ {j} _ hij => (planeRot_commute hF hij (x i) (x j)).eq)) := by
  classical
  simp only [frameTorusFull, MonoidHom.noncommPiCoprod_apply]
  change (Subgroup.subtype (orthDerived Q))
      (Finset.univ.noncommProd (fun i => planeRotDerived hF hQ hT i (x i)) _) =
    Finset.univ.noncommProd (fun i => planeRot hF i (x i)) _
  rw [Finset.map_noncommProd]
  congr 1

theorem frameTorusFull_apply_mem (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (x : Fin k → normOne t) (a : Fin k) {w : V} (hw : w ∈ U a) :
    ((frameTorusFull hF hQ hT x : ↥(orthDerived Q)) : V ≃ₗ[F] V) w =
      planeRot hF a (x a) w := by
  classical
  rw [frameTorusFull_coe]
  refine noncommProd_apply_of_eq_of_ne (Finset.univ : Finset (Fin k))
    (fun i => planeRot hF i (x i)) _ (Finset.mem_univ a) ?_
  intro i _ hia
  refine planeRot_apply_perp hF i (x i) ?_
  rw [mem_polarPerp_iff]
  intro y hy
  exact hF.perp i a hia y hy w hw

theorem frameTorusFull_apply_perp (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (x : Fin k → normOne t) {w : V} (hw : w ∈ polarPerp Q (⨆ j, U j)) :
    ((frameTorusFull hF hQ hT x : ↥(orthDerived Q)) : V ≃ₗ[F] V) w = w := by
  classical
  rw [frameTorusFull_coe]
  refine Finset.noncommProd_induction (Finset.univ : Finset (Fin k))
    (fun i => planeRot hF i (x i)) _ (fun g : V ≃ₗ[F] V => g w = w) ?_ rfl ?_
  · intro f g hf hg
    rw [LinearEquiv.mul_apply, hg, hf]
  · intro i _
    refine planeRot_apply_perp hF i (x i) ?_
    rw [mem_polarPerp_iff]
    intro y hy
    exact mem_polarPerp_iff.mp hw y (le_iSup U i hy)

theorem planeRot_injective (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    Function.Injective (planeRot hF a) := by
  intro z z' hzz'
  have hlin : planeLinEquiv hF a z = planeLinEquiv hF a z' :=
    CFSG.LieType.SeitzGeneration.OrthNS.extU_injective (planeNondeg hF a) hzz'
  have hval : normOneVal (F := F) (t := t) z = normOneVal (F := F) (t := t) z' := by
    have happ := congrArg (fun (g : ↥(U a) ≃ₗ[F] ↥(U a)) => g (frameU hF a)) hlin
    rw [planeLinEquiv_apply, planeLinEquiv_apply] at happ
    have hkill : planeAlg hF a (normOneVal (F := F) (t := t) z -
        normOneVal (F := F) (t := t) z') (frameU hF a) = 0 := by
      rw [map_sub, LinearMap.sub_apply, happ, sub_self]
    have hzero : planeAlg hF a (normOneVal (F := F) (t := t) z -
        normOneVal (F := F) (t := t) z') = 0 :=
      planeAlg_eq_zero_of_apply_frameU hF a hkill
    exact sub_eq_zero.mp (planeAlg_injective hF a (by rw [hzero, map_zero]))
  apply Subtype.ext
  apply Units.ext
  exact hval

theorem orderOf_rootNormOne (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    orderOf (rootNormOne (F := F) (t := t)) = p := by
  rw [← orderOf_injective (planeRot hF a) (planeRot_injective hF a)
    (rootNormOne (F := F) (t := t))]
  rw [planeRot_rootNormOne]
  exact (orderOf_injective (Subgroup.subtype (orthDerived Q)) Subtype.coe_injective
    (e a)).trans (hF.orderOf_eq a)

theorem mem_zpowers_rootNormOne (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t) (a : Fin k)
    {z : normOne t} (hz : z ^ p = 1) :
    z ∈ Subgroup.zpowers (rootNormOne (F := F) (t := t)) := by
  classical
  haveI : IsCyclic (normOne t) := isCyclic_normOne (F := F) (t := t)
  let H : Subgroup (normOne t) := (powMonoidHom p : normOne t →* normOne t).ker
  have hdvd : p ∣ Nat.card F + 1 := by
    have h := Subgroup.orderOf_dvd_natCard (normOne t)
      (rootNormOne (F := F) (t := t)).2
    rw [Subgroup.orderOf_coe, orderOf_rootNormOne hF a,
      natCard_normOne (F := F) (t := t)] at h
    exact h
  have hHcard : Nat.card H = p := by
    show Nat.card ((powMonoidHom p : normOne t →* normOne t).ker) = p
    rw [IsCyclic.card_powMonoidHom_ker, natCard_normOne (F := F) (t := t)]
    exact Nat.gcd_eq_right hdvd
  have hle : Subgroup.zpowers (rootNormOne (F := F) (t := t)) ≤ H := by
    rw [Subgroup.zpowers_le]
    exact MonoidHom.mem_ker.mpr (by
      rw [← orderOf_rootNormOne hF a]
      exact pow_orderOf_eq_one _)
  have hcard2 : Nat.card (Subgroup.zpowers (rootNormOne (F := F) (t := t))) = p := by
    rw [Nat.card_zpowers, orderOf_rootNormOne hF a]
  have heq : Subgroup.zpowers (rootNormOne (F := F) (t := t)) = H :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard2, hHcard])
  have hzH : z ∈ H := MonoidHom.mem_ker.mpr hz
  rwa [← heq] at hzH

theorem frameTorusFull_injective (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    Function.Injective (frameTorusFull hF hQ hT) := by
  classical
  intro x y hxy
  funext a
  have hrot : planeRot hF a (x a) = planeRot hF a (y a) := by
    refine CFSG.LieType.SeitzGeneration.OrthNS.extU_eq_of_agree (planeNondeg hF a) ?_ ?_
    · intro u
      have hx' := frameTorusFull_apply_mem hF hQ hT x a u.2
      have hy' := frameTorusFull_apply_mem hF hQ hT y a u.2
      rw [← hy', ← hxy, hx', planeRot_apply_mem hF a (x a) u.2, planeLinEquiv_apply]
    · intro r hr
      exact planeRot_apply_perp hF a (y a) (by rwa [mem_orthBlk_perp_iff] at hr)
  have hlin : planeLinEquiv hF a (x a) = planeLinEquiv hF a (y a) :=
    CFSG.LieType.SeitzGeneration.OrthNS.extU_injective (planeNondeg hF a) hrot
  have hval : normOneVal (F := F) (t := t) (x a) = normOneVal (F := F) (t := t) (y a) := by
    have happ := congrArg (fun (g : ↥(U a) ≃ₗ[F] ↥(U a)) => g (frameU hF a)) hlin
    rw [planeLinEquiv_apply, planeLinEquiv_apply] at happ
    have hkill : planeAlg hF a (normOneVal (F := F) (t := t) (x a) -
        normOneVal (F := F) (t := t) (y a)) (frameU hF a) = 0 := by
      rw [map_sub, LinearMap.sub_apply, happ, sub_self]
    have hzero : planeAlg hF a (normOneVal (F := F) (t := t) (x a) -
        normOneVal (F := F) (t := t) (y a)) = 0 :=
      planeAlg_eq_zero_of_apply_frameU hF a hkill
    exact sub_eq_zero.mp (planeAlg_injective hF a (by rw [hzero, map_zero]))
  apply Subtype.ext
  apply Units.ext
  exact hval

theorem frameTorusFull_mulSingle (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0) (a : Fin k) :
    frameTorusFull hF hQ hT (Pi.mulSingle a (rootNormOne (F := F) (t := t))) = e a := by
  classical
  change ((MonoidHom.noncommPiCoprod (fun a => planeRotDerived hF hQ hT a) _)
    (Pi.mulSingle a (rootNormOne (F := F) (t := t))) : ↥(orthDerived Q)) = e a
  rw [MonoidHom.noncommPiCoprod_mulSingle]
  exact Subtype.ext (planeRot_rootNormOne hF a)

theorem mem_iff_frameTorusFull (hF : OmNsRootGen.IsCoherentFrame Q p U e E u c t)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (g : ↥(orthDerived Q)) :
    g ∈ E ↔ g ^ p = 1 ∧ g ∈ (frameTorusFull hF hQ hT).range := by
  classical
  constructor
  · intro hg
    refine ⟨hF.isElemAbelian.2 g hg, ?_⟩
    have hclos : Subgroup.closure (Set.range e) ≤ (frameTorusFull hF hQ hT).range := by
      refine (Subgroup.closure_le (frameTorusFull hF hQ hT).range).mpr ?_
      rintro _ ⟨a, rfl⟩
      exact ⟨Pi.mulSingle a (rootNormOne (F := F) (t := t)),
        frameTorusFull_mulSingle hF hQ hT a⟩
    rw [← hF.closure_eq] at hg
    exact hclos hg
  · rintro ⟨hgp, x, rfl⟩
    have hxp : x ^ p = 1 := by
      apply frameTorusFull_injective hF hQ hT
      rw [map_pow, hgp, map_one]
    have hmem : ∀ a, planeRotDerived hF hQ hT a (x a) ∈ E := by
      intro a
      have hz : x a ∈ Subgroup.zpowers (rootNormOne (F := F) (t := t)) :=
        mem_zpowers_rootNormOne hF a (congrFun hxp a)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hroot : planeRotDerived hF hQ hT a (rootNormOne (F := F) (t := t)) = e a := by
        refine Subtype.ext ?_
        exact planeRot_rootNormOne hF a
      have hEa : e a ∈ E := by
        rw [← hF.closure_eq]
        exact Subgroup.subset_closure ⟨a, rfl⟩
      rw [← hk, map_zpow, hroot]
      exact E.zpow_mem hEa k
    simp only [frameTorusFull, MonoidHom.noncommPiCoprod_apply]
    refine Finset.noncommProd_induction (Finset.univ : Finset (Fin k))
      (fun i => planeRotDerived hF hQ hT i (x i))
      (fun {i} _ {j} _ hij => planeRotDerived_commute hF hQ hT hij (x i) (x j))
      (fun y => y ∈ E) (fun a b ha hb => E.mul_mem ha hb) E.one_mem ?_
    intro i _
    exact hmem i

end Plane

end RelDNs

end CFSG.StandardType

end
