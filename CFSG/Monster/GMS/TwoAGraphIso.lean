module

public import CFSG.Monster.GMS.TwoAGraph
public import CFSG.Monster.B.GSide.HomotopyLocal
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Monster.GMS

open CFSG.Monster.B.Recog

variable {G G' : Type*} [Group G] [Group G']

theorem isConj_mulEquiv_iff (e : G ≃* G') {a x : G} : IsConj (e a) (e x) ↔ IsConj a x := by
  refine ⟨fun h => ?_, fun h => e.toMonoidHom.map_isConj h⟩
  simpa using e.symm.toMonoidHom.map_isConj h

@[expose] def twoAGraphIsoOfMulEquiv (e : G ≃* G') {a : G} {a' : G'} (ha : e a = a') :
    twoAGraph a ≃g twoAGraph a' where
  toFun x := ⟨e x, ha ▸ (isConj_mulEquiv_iff e).mpr x.2⟩
  invFun y := ⟨e.symm y, (isConj_mulEquiv_iff e).mp (by simpa [ha] using y.2)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_rel_iff' {x y} := by
    subst ha
    simp only [Equiv.coe_fn_mk, twoAGraph_adj, ne_eq, Subtype.ext_iff,
      EmbeddingLike.apply_eq_iff_eq, ← map_mul, isConj_mulEquiv_iff]

theorem triangulable_twoAGraph_iff_of_mulEquiv (e : G ≃* G') {a : G} {a' : G'} (ha : e a = a') :
    Triangulable (twoAGraph a) ↔ Triangulable (twoAGraph a') :=
  CFSG.Monster.B.GSide.triangulable_iff_of_iso (twoAGraphIsoOfMulEquiv e ha)

theorem triangulable_twoAGraph_of_eq {M : Type*} [Group M] {H₁ H₂ : Subgroup M} (h : H₁ = H₂)
    {a₁ : H₁} {a₂ : H₂} (ha : (a₁ : M) = a₂) :
    Triangulable (twoAGraph a₁) ↔ Triangulable (twoAGraph a₂) :=
  triangulable_twoAGraph_iff_of_mulEquiv (MulEquiv.subgroupCongr h) (Subtype.ext ha)

end CFSG.Monster.GMS
