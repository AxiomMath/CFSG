module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinberg
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergE6Root
public import CFSG.LocalAnalysis.StandardType.GGRootDetectTwE6
public import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.StandardType

namespace AutSt

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional

abbrev twE6Top : Fin (Tag.rank .E6) → ℤ := ![1, 2, 2, 3, 2, 1]

theorem rho_twE6Top : rho twE6Top = twE6Top := by
  funext i
  fin_cases i <;> decide

theorem proj_twE6Top : proj twE6Top = ![2, 3, 4, 2] := by
  funext i
  fin_cases i <;> decide


theorem isRoot_twE6Top : IsRoot .E6 twE6Top :=
  isRoot_iff_mem_artifactRoots.2 (by decide +kernel)

theorem not_isRoot_twE6Top_add_single : ¬IsRoot .E6 (twE6Top + Pi.single (e6Node 3) 1) :=
  fun h => by
    have := isRoot_iff_mem_artifactRoots.1 h
    revert this
    decide +kernel

theorem not_isRoot_twE6Top_add_neg_single : ¬IsRoot .E6 (twE6Top + -Pi.single (e6Node 3) 1) :=
  fun h => by
    have := isRoot_iff_mem_artifactRoots.1 h
    revert this
    decide +kernel

theorem eq_twF4Top_of_maxHeight {γ₀ : Fin (Tag.rank .F4) → ℤ} (hγ₀ : IsRoot .F4 γ₀)
    (hmax : IsRoot .F4 ![2, 3, 4, 2] → ∑ i, (![2, 3, 4, 2] : Fin (Tag.rank .F4) → ℤ) i ≤
      ∑ i, γ₀ i) :
    γ₀ = ![2, 3, 4, 2] := by
  have htop : IsRoot .F4 ![2, 3, 4, 2] := isRoot_iff_mem_artifactRoots.2 (by decide +kernel)
  have h11 := hmax htop
  have hs : ∑ i, (![2, 3, 4, 2] : Fin (Tag.rank .F4) → ℤ) i = 11 := by decide +kernel
  have key : ∀ l ∈ Tag.F4.artifactRoots, 11 ≤ l.sum → l = [2, 3, 4, 2] := by decide +kernel
  have hl := key _ (isRoot_iff_mem_artifactRoots.1 hγ₀) (by rw [List.sum_ofFn]; omega)
  exact List.ofFn_injective (hl.trans (by decide +kernel))

section Comm


variable {K : Type} [Field K] {F : RootOperatorFamily .E6}

theorem commute_twE6Top_single (s d : K) :
    Commute (xPar F twE6Top s) (xPar F (Pi.single (e6Node 3) 1) d) :=
  commute_xPar e6AdjData_valid noG2_E6 isRoot_twE6Top (isRoot_single _ _)
    (fun h => by
      have := congrFun h (e6Node 0)
      revert this
      decide)
    not_isRoot_twE6Top_add_single s d

theorem commute_twE6Top_neg_single (s d : K) :
    Commute (xPar F twE6Top s) (xPar F (-Pi.single (e6Node 3) 1) d) :=
  commute_xPar e6AdjData_valid noG2_E6 isRoot_twE6Top (isRoot_neg_single _ _)
    (fun h => by
      have := congrFun h (e6Node 0)
      revert this
      decide)
    not_isRoot_twE6Top_add_neg_single s d

end Comm

section Model


variable (f : ℕ) {C : Subgroup (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))}
  (π : twistedE6Group 2 f →* C)

theorem exists_conj_twTop_of_modelRoot (hf : 1 ≤ f)
    (hπval : ∀ z, ((π z : C) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6Isogeny (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup .E6 (GaloisField 2 (2 * f))) : ModGL .E6 (GaloisField 2 (2 * f))))
    {r : C} (hr : GGModelRoot (twistedE6Datum 2 f) .twistedE6 π r) :
    ∃ (g : C) (s : GaloisField 2 (2 * f)), frobQ 2 f s = s ∧
      ((g * r * g⁻¹ : C) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        ((xPar (rootOperatorFamily .E6) twE6Top s : adjointGroup .E6 (GaloisField 2 (2 * f))) :
          ModGL .E6 (GaloisField 2 (2 * f))) := by
  have hθ := frobQ_frobQ 2 f hf
  obtain ⟨-, γ, hγ, u, z, hz, rfl⟩ := hr
  obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := hγ.2 (Or.inr (Or.inr rfl))
  have h0 : γ₀ = ![2, 3, 4, 2] :=
    eq_twF4Top_of_maxHeight (isRoot_of_mem_twistedDatum_roots _ hγ₀)
      (fun h => hmax _ (by rw [twistedDatum_roots]; exact h))
  subst h0
  let hct := twistedDatum_isCTGroupDatum (frobQ 2 f) hθ (iSup_twistedDatum_rootGroup _ hθ)
  have hx := actsAs_nrep hct w _ hγ₀
  rw [← hx] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  obtain ⟨c, hc, hcz⟩ := (mem_twistedRootGroup_iff_of_fixed (frobQ 2 f) isRoot_twE6Top
    proj_twE6Top rho_twE6Top z₀).1 hz₀
  have e : (u * nrep hct w)⁻¹ * (u * (nrep hct w * z₀ * (nrep hct w)⁻¹) * u⁻¹) *
      ((u * nrep hct w)⁻¹)⁻¹ = z₀ := by group
  refine ⟨π (u * nrep hct w)⁻¹, (relSignOr (rootOperatorFamily .E6) e6AdjData_valid twE6Top :
    GaloisField 2 (2 * f)) * c, ?_, ?_⟩
  · rw [map_mul, map_intCast, hc]
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← map_inv π, ← map_mul, ← map_mul, e, hπval, hcz, e6Isogeny_xm _ isRoot_twE6Top]
    rfl

end Model

end AutSt

end CFSG.StandardType
