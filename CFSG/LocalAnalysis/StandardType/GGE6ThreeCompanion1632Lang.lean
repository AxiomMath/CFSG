module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632Defs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang

public section

namespace CFSG.StandardType.S2MathAs1E6Companion1625

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.E6Centralizer1585
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem fixed_representative_of_lang {G : Type*} [Group G] (F : G →* G) (H K : Subgroup G)
    (hHK : H ≤ K) (hLang : ∀ h ∈ H, ∃ z ∈ H, F z = z * h)
    {x : G} (hx : x ∈ K) (hcoset : F x * x⁻¹ ∈ H) :
    ∃ y ∈ K, F y = y ∧ y * x⁻¹ ∈ H := by
  obtain ⟨z, hzH, hz⟩ := hLang (F x * x⁻¹)⁻¹ (H.inv_mem hcoset)
  refine ⟨z * x, K.mul_mem (hHK hzH) hx, ?_, ?_⟩
  · rw [map_mul, hz, mul_inv_rev, inv_inv]
    group
  · have hzx : (z * x) * x⁻¹ = z := by group
    rw [hzx]
    exact hzH

theorem langOnConnectedAt_producer
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi) :
    LangOnConnectedAt ρ := by
  have hclosure : Subgroup.closure (Set.range (fun b : Fin ρ.tau.rank → Omegaˣ =>
      rootDiagUnit ρ.tau b)) = torusGroup ρ.tau Omega := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.closure_le]
      rintro _ ⟨b, rfl⟩
      exact rootDiagUnit_mem_torusGroup (τ := ρ.tau) b
    · intro g hg
      obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (τ := ρ.tau) hg
      exact Subgroup.subset_closure ⟨l, rfl⟩
  have hconn : connectedCentralizer ρ =
      torusGroup ρ.tau Omega ⊔ rootSpan ρ.tau Omega (kernelRoots (rootCharHom ρ.a)) := by
    unfold connectedCentralizer
    rw [hclosure]
  intro h hh
  rw [hconn] at hh
  obtain ⟨z, hzZ, hz⟩ := exists_lang_torus_sup_kernelRoots (S := ρ.setup) (χ := rootCharHom ρ.a)
    (s := 1) (by norm_num)
    (fun γ hγ => by simpa using outer_rho_mem_kernelRoots ρ.setup ρ.a_torus hγ)
    (y := h) hh
  refine ⟨z, by rw [hconn]; exact hzZ, ?_⟩
  change iterHom ρ.setup.D.step (0 + 1) z = z * h at hz
  rw [iterHom_succ, iterHom_zero] at hz
  exact hz

end CFSG.StandardType.S2MathAs1E6Companion1625

end
