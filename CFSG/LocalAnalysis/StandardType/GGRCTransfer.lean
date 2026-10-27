module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGRCLinRefl

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggRC_weylReflGroup_of_linWeyl {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (A : Subgroup (MulAut ↥Bs))
    (h : ZS.LinWeyl p (A.map (ggLin (p := p) ι))) : GGWeylReflectionGroup p A := by
  obtain ⟨ι', M, hM, f, hf⟩ := h
  let e : ↥A ≃* ↥(A.map (ggLin (p := p) ι)) :=
    Subgroup.equivMapOfInjective A (ggLin (p := p) ι) (ggLin_injective ι)
  have he : ∀ x : ↥A, (e x : V ≃ₗ[ZMod p] V) = ggLin (p := p) ι (x : MulAut ↥Bs) :=
    fun x => Subgroup.coe_equivMapOfInjective_apply A _ _ x
  let f' : M.Group ≃* ↥A := f.trans e.symm
  have hf' : ∀ i : ι',
      ggLin (p := p) ι ((f' (M.simple i) : ↥A) : MulAut ↥Bs) =
        (f (M.simple i) : V ≃ₗ[ZMod p] V) := by
    intro i
    have h1 : e (f' (M.simple i)) = f (M.simple i) := by
      dsimp [f']
      exact e.apply_symm_apply _
    have h2 := congrArg (fun x : ↥(A.map (ggLin (p := p) ι)) => (x : V ≃ₗ[ZMod p] V)) h1
    rw [he] at h2
    exact h2
  refine ⟨ι', M, hM, f', ?_⟩
  intro i
  have hlin : GGLinRefl (ggLin (p := p) ι ((f' (M.simple i) : ↥A) : MulAut ↥Bs)) := by
    rw [hf' i]
    exact hf i
  exact (ggRC_isReflection_iff_linRefl (p := p) ι
    ((f' (M.simple i) : ↥A) : MulAut ↥Bs)).mpr hlin

end CFSG.StandardType
