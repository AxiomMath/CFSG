module

public import CFSG.Quasithin.Background.E11End
public import CFSG.Quasithin.Background.E11Norm
public import CFSG.Quasithin.Background.E11Sub
public import CFSG.Quasithin.Background.E11Scalar

public section

namespace CFSG.Quasithin

namespace G11

namespace E11

open scoped LinearAlgebra.Projectivization

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {H : Subgroup (GLV V)}

theorem endAlgEquiv_apply {I : Submodule (ZMod 2) V} (hI : Invariant H I) (f : endOn H I)
    (i : ↥I) :
    (((endAlgEquiv hI f) ⟨i.1, i.2⟩ : ↥(ofInvariant I hI)) : V) = ((f.1 i : ↥I) : V) := by
  have h := (endAlgEquiv hI).symm_apply_apply f
  exact congrArg (fun T : endOn H I => ((T.1 i : ↥I) : V)) h

end E11

open E11 in
theorem e11 : E11Stmt := by
  intro V _ _ _ H I hhom hI hfix hsum
  classical
  have hsimple : IsSimpleModule (HRing H) (ofInvariant I hI.1) :=
    isSimpleModule_ofInvariant hI hfix
  have hsemi : IsSemisimpleModule (HRing H) V := isSemisimple_V hsum
  have hiso : IsIsotypicOfType (HRing H) V (ofInvariant I hI.1) :=
    isIsotypic_V hI hfix hhom
  have : Module.Finite (HRing H) V := Module.Finite.of_finite
  obtain ⟨n, ⟨e⟩⟩ := hiso.linearEquiv_fun
  have : Finite (Module.End (HRing H) (ofInvariant I hI.1)) := FunLike.finite _
  have : Finite (ofInvariant I hI.1 →ₗ[HRing H] V) := finite_hom
  have : Nontrivial (ofInvariant I hI.1) := IsSimpleModule.nontrivial (HRing H) _
  have : Nontrivial V := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne (ofInvariant I hI.1)
    exact ⟨⟨a, b, fun h => hab (Subtype.ext h)⟩⟩
  refine ⟨{ F := Module.End (HRing H) (ofInvariant I hI.1)
            instField := inferInstance
            instAlgebra := inferInstance
            instFiniteF := inferInstance
            instCharP := inferInstance
            U := ofInvariant I hI.1 →ₗ[HRing H] V
            instAddCommGroup := inferInstance
            instModule := inferInstance
            instFiniteU := finite_hom
            instModuleFinite := inferInstance
            ψ := (pointEquiv hfix _ hiso).symm
            endEquiv := endAlgEquiv hI.1
            finrank_mul := ?_
            θ := thetaEquiv e
            θ_acts := ?_
            semilinear := ?_
            exists_subspace := ?_
            κ := kappa e
            κ_injective := ?_
            κ_comm := ?_
            κ_stable := ?_
            κ_apply := ?_
            κ_conj := ?_ }⟩
  · show Module.finrank (Module.End (HRing H) (ofInvariant I hI.1))
        (ofInvariant I hI.1 →ₗ[HRing H] V) * Module.finrank (ZMod 2) I =
      Module.finrank (ZMod 2) V
    rw [finrank_hom_eq e]
    have := finrank_eq_mul_of_card (M := V) (N := ↥I) (k := n)
      (by rw [natCard_eq_pow e]; rfl)
    exact this.symm
  · exact fun c => actsOnPoints_of hfix _ hiso c _ (fun p => pointSub_smul e c p)
  · intro g hg
    obtain ⟨T⟩ := nonempty_twist hiso hg
    refine ⟨tauEquiv T, sigmaLin T, sigmaLin_bijective T, ?_, ?_⟩
    · exact actsOnPoints_of hfix _ hiso g _ (fun p => pointSub_map_sigma T p)
    · intro c c' hcc' u
      refine LinearMap.ext fun i => ?_
      show (c' : GLV V) (g (u (T.ρ i))) = g ((c : GLV V) (u (T.ρ i)))
      exact congrArg (fun x : GLV V => x (u (T.ρ i))) hcc'
  · intro M hM
    refine ⟨homInto (ofInvariant M hM), fun J hJ => ?_, ?_⟩
    · exact le_iff_submodule_le_homInto hfix _ hiso (ofInvariant M hM) J hJ
    · have hc := natCard_eq_pow_finrank_homInto hiso (ofInvariant M hM)
      have := finrank_eq_mul_of_card (M := ↥M) (N := ↥I) (k := _) hc
      exact this.symm
  · exact (kappa e).toRingHom.injective
  · exact fun f h hh => kappa_comm e f h hh
  · exact fun f J hJ => kappa_stable e hfix hiso f hJ
  · intro f i
    have h1 := kappa_apply_mem e (endAlgEquiv hI.1 f) ⟨i.1, i.2⟩
    rw [show (i : V) = ((⟨i.1, i.2⟩ : ofInvariant I hI.1) : V) from rfl, h1]
    exact endAlgEquiv_apply hI.1 f i
  · exact fun g hg τ σ hσ hcompat f => kappa_conj e hg τ σ hσ hcompat f

end G11

end CFSG.Quasithin
