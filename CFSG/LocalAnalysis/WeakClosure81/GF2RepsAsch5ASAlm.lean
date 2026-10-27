module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASSec
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Alm

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

theorem generalizedFitting_eq_innAutOf_subgroupOf {L₀ : Type} [Group L₀] [Finite L₀]
    (hs : IsSimpleGroup L₀) (hnab : ∃ a b : L₀, a * b ≠ b * a) {A : Subgroup (MulAut L₀)}
    (h : innAutOf L₀ ≤ A) :
    CFSG.generalizedFitting ↥A = (innAutOf L₀).subgroupOf A := by
  have hZ : Subgroup.center L₀ = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
  haveI : Finite (MulAut L₀) :=
    Finite.of_injective (fun α : MulAut L₀ => (α : L₀ → L₀)) DFunLike.coe_injective
  set F : Subgroup ↥A := (innAutOf L₀).subgroupOf A with hF
  haveI hFn : F.Normal := normal_innAutOf_subgroupOf h
  obtain ⟨e⟩ := nonempty_mulEquiv_innAutOf_subgroupOf hZ h
  haveI : IsSimpleGroup ↥F := by
    haveI := hs
    exact e.isSimpleGroup
  have hnab' : ∃ a b : ↥F, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun hh => hab (by simpa using congrArg e hh)⟩
  have hC : Subgroup.centralizer (F : Set ↥A) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hx' : ((x : ↥A) : MulAut L₀) ∈
        Subgroup.centralizer (CFSG.Quasithin.H13.P31Sec.innGroup L₀ : Set (MulAut L₀)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hgA : g ∈ A := h hg
      have hgF : (⟨g, hgA⟩ : ↥A) ∈ F := hg
      have := Subgroup.mem_centralizer_iff.mp hx _ hgF
      exact congrArg (fun y : ↥A => (y : MulAut L₀)) this
    rw [CFSG.Quasithin.H13.P31Sec.centralizer_innGroup hZ, Subgroup.mem_bot] at hx'
    exact Subtype.ext hx'
  rw [← CFSG.Adapters.genFittingFStar_eq_foundations]
  exact CFSG.ClassicalInvolution.genFittingFStar_eq_of_normal_simple F hnab' hC

theorem shapeInEAS_of_ambient {j : ℕ} {P : ∀ (X : Type) [Group X], Prop} (hP : IsoInvPred P)
    (h : ∀ (Q : Type) [Group Q] [Finite Q] (L T : Subgroup Q), L.Normal →
      CFSG.generalizedFitting Q = L → IsSimpleGroup ↥L → (∃ a b : ↥L, a * b ≠ b * a) →
      IsSylowIn 2 T ⊤ → L ⊔ T = ⊤ → P ↥L → E1.InE j (⊤ : Subgroup Q)) :
    ShapeInEAS j P := by
  intro L₀ _ _ hs hnab hP₀ A S hAS
  obtain ⟨hInn, hSyl, hsup⟩ := hAS
  haveI : Finite (MulAut L₀) :=
    Finite.of_injective (fun α : MulAut L₀ => (α : L₀ → L₀)) DFunLike.coe_injective
  haveI : Finite ↥A := inferInstance
  have hZ : Subgroup.center L₀ = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
  obtain ⟨e⟩ := nonempty_mulEquiv_innAutOf_subgroupOf hZ hInn
  haveI : ((innAutOf L₀).subgroupOf A).Normal := normal_innAutOf_subgroupOf hInn
  haveI : IsSimpleGroup ↥((innAutOf L₀).subgroupOf A) := by
    haveI := hs
    exact e.isSimpleGroup
  refine (E1.inE_subgroupOf j A).mpr (h ↥A ((innAutOf L₀).subgroupOf A) (S.subgroupOf A)
    inferInstance (generalizedFitting_eq_innAutOf_subgroupOf hs hnab hInn) inferInstance ?_
    (isSylowIn_top_subgroupOf hSyl) (sup_subgroupOf_eq_top hSyl.le hsup)
    (hP L₀ _ ⟨e.symm⟩ hP₀))
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e.symm a, e.symm b, fun hh => hab (by simpa using congrArg e hh)⟩

theorem shapeInEAS_of_ambient_fstar {j : ℕ} {P : ∀ (X : Type) [Group X], Prop}
    (hP : IsoInvPred P)
    (h : ∀ (Q : Type) [Group Q] [Finite Q] (T : Subgroup Q),
      IsSimpleGroup ↥(CFSG.generalizedFitting Q) →
      (∃ a b : ↥(CFSG.generalizedFitting Q), a * b ≠ b * a) → IsSylowIn 2 T ⊤ →
      CFSG.generalizedFitting Q ⊔ T = ⊤ → P ↥(CFSG.generalizedFitting Q) →
      E1.InE j (⊤ : Subgroup Q)) :
    ShapeInEAS j P :=
  shapeInEAS_of_ambient hP fun Q _ _ L T _ hF hs hnab hT hLT hPL => by
    subst hF
    exact h Q T hs hnab hT hLT hPL

end CFSG.LocalAnalysis.WeakClosure81

end
