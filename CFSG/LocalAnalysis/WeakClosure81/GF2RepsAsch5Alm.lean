module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs
public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecIn

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Fstar)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (InEGroup)

theorem normal_innAutOf_subgroupOf {L₀ : Type} [Group L₀] {A : Subgroup (MulAut L₀)}
    (_h : innAutOf L₀ ≤ A) : ((innAutOf L₀).subgroupOf A).Normal := by
  haveI : (innAutOf L₀).Normal := CFSG.Quasithin.H13.P31Sec.normal_innGroup
  exact Subgroup.Normal.subgroupOf inferInstance A

theorem nonempty_mulEquiv_innAutOf_subgroupOf {L₀ : Type} [Group L₀]
    (hZ : Subgroup.center L₀ = ⊥) {A : Subgroup (MulAut L₀)} (h : innAutOf L₀ ≤ A) :
    Nonempty (↥((innAutOf L₀).subgroupOf A) ≃* L₀) :=
  ⟨(Subgroup.subgroupOfEquivOfLe h).trans (CFSG.Quasithin.H13.P31Sec.innEquiv hZ).symm⟩

theorem isSylowIn_top_subgroupOf {L₀ : Type} [Group L₀] {A S : Subgroup (MulAut L₀)}
    (h : IsSylowIn 2 S A) : IsSylowIn 2 (S.subgroupOf A) ⊤ := by
  have := (E1.isSylowIn_subgroupOf_iff (p := 2) (H := A) h.le le_rfl).mpr h
  rwa [Subgroup.subgroupOf_self] at this

theorem sup_subgroupOf_eq_top {L₀ : Type} [Group L₀] {A S : Subgroup (MulAut L₀)}
    (hS : S ≤ A) (h : innAutOf L₀ ⊔ S = A) :
    (innAutOf L₀).subgroupOf A ⊔ S.subgroupOf A = ⊤ := by
  have hI : innAutOf L₀ ≤ A := h ▸ le_sup_left
  rw [← Subgroup.subgroupOf_sup hI hS, h]
  exact Subgroup.subgroupOf_self A

end CFSG.LocalAnalysis.WeakClosure81
