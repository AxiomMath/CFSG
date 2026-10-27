module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs
public import CFSG.HardMathSupport.C14IdxCorootTorus

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.C14Idx
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen (coordTuple)

noncomputable section

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}
  {T₀ : Subgroup (ModGL τ L)} {m : Fin 6} {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {J : Set (KernelComponent χ)}

theorem exists_coordTuple_of_mem_codeComponent (d : ExcCoordDatum S T₀ m)
    {c : Finset (ExcRaw.Root m)} (hJ : unionRoots χ J = codeRoots d.γ c) {t : ModGL τ L}
    (htT : t ∈ T₀) (ht : t ∈ codeComponent S d.γ c) :
    ∃ (Δ : Finset (Fin τ.rank → ℤ)) (x : (Fin τ.rank → ℤ) → Lˣ),
      (∀ β ∈ Δ, β ∈ codeRoots d.γ c) ∧ t = rootDiagUnit τ (coordTuple Δ x) := by
  classical
  have htRoot : t ∈ rootSpan τ L (codeRoots d.γ c) :=
    ((Subgroup.commutator_le_self _).trans inf_le_left) ht
  have htUnionRoot : t ∈ unionRootSpan L χ J := by
    change t ∈ rootSpan τ L (unionRoots χ J)
    rw [hJ]
    exact htRoot
  have htTorus : t ∈ torusGroup τ L := by
    have h1 : t ∈ fullThreeTorus S := d.le_fullThreeTorus htT
    have h2 : t ∈ S.D.torus := h1.1
    exact (inf_le_left : S.D.torus ≤ torusGroup τ L) h2
  have htUnionTorus : t ∈ unionTorus L χ J := by
    rw [unionTorus]
    exact Subgroup.mem_inf.2 ⟨htUnionRoot, htTorus⟩
  set Δ : Finset (Fin τ.rank → ℤ) := (rootFinset τ).filter (· ∈ unionSimpleRoots χ J) with hΔdef
  have hΔ : (Δ : Set (Fin τ.rank → ℤ)) = unionSimpleRoots χ J := by
    ext β
    simp only [hΔdef, Finset.mem_coe, Finset.mem_filter, mem_rootFinset]
    constructor
    · rintro ⟨_, hβ⟩
      exact hβ
    · intro hβ
      simp only [unionSimpleRoots] at hβ
      obtain ⟨i, hi, hβi⟩ := hβ
      exact ⟨simpleRoots_isRoot hβi, ⟨i, hi, hβi⟩⟩
  obtain ⟨x, hx⟩ := exists_coordTuple_of_mem_unionTorus Δ hΔ htUnionTorus
  refine ⟨Δ, x, ?_, hx⟩
  intro β hβ
  rw [← hJ]
  exact mem_unionRoots_of_mem_unionSimpleRoots (by
    rw [← hΔ, hΔdef]
    simpa [hΔdef] using hβ)

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
