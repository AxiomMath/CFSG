module

public import CFSG.LocalAnalysis.StandardType.GGOrthKStructDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfTorusFrame
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen
import CFSG.LocalAnalysis.StandardType.GGOrthKStructWeylBCount
import CFSG.LocalAnalysis.StandardType.GGOrthKStructWeylBIso
import CFSG.LocalAnalysis.StandardType.GGOrthKStructEquiv

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.GGHalf CFSG.StandardType.SpJoin
  CFSG.LieType.Universal.SpecialLinear Matrix

theorem ggOrthKStruct_weylB {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G}
    (hψ : GGHalfTorusFrame Bs K (halfTorus n) ψ) (hk : 2 ≤ (n + 1) / 2)
    (hprod : Bs = (halfTorus n).map ψ ⊔ (Bs ⊓ Subgroup.centralizer (K : Set G)))
    (Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)) (hΦ : IsTorusCoord n Φ)
    (hup : ∀ σ ∈ ggAutomizer K Bs, ∃ h ∈ spSignedGroup ((n + 1) / 2) 3, InducesSigned K ψ Φ σ h)
    (hlow : ∀ h ∈ spSignedGroup ((n + 1) / 2) 3, ∃ σ ∈ ggAutomizer K Bs, InducesSigned K ψ Φ σ h) :
    GGWeylOfType 3 (CoxeterMatrix.B ((n + 1) / 2)) (ggAutomizer K Bs) := by
  obtain ⟨e1, he1⟩ := ggOrthKStruct_coxeterB_equiv hk
  obtain ⟨E, hE⟩ := ggOrthKStruct_equiv hψ hprod Φ hup hlow
  refine ⟨e1.trans E.symm, fun i => ?_⟩
  have hEσ : InducesSigned K ψ Φ
      (((e1.trans E.symm) ((CoxeterMatrix.B ((n + 1) / 2)).simple i)) : MulAut ↥Bs)
      (spReflPerm ((n + 1) / 2) 3 i) := by
    have h := hE ((e1.trans E.symm) ((CoxeterMatrix.B ((n + 1) / 2)).simple i))
    have harg : E ((e1.trans E.symm) ((CoxeterMatrix.B ((n + 1) / 2)).simple i)) =
        e1 ((CoxeterMatrix.B ((n + 1) / 2)).simple i) := by
      rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [harg] at h
    rw [he1 i] at h
    exact h
  exact (ggOrthKStruct_isRefl_iff hψ hprod hEσ).mpr (ggOrthKStruct_refl_count i)

end CFSG.StandardType

end
