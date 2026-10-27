module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearTriv
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearConj

public section

namespace CFSG.StandardType.LinearFieldFix

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.FQ
open scoped commutatorElement

@[expose] noncomputable def ggFixDerRestrict {R : Type} [Group R] {x φ : MulAut R}
    (h : φ * x = x * φ) : ggFixDer x ≃* ggFixDer x where
  toFun g := ⟨φ g, ggFixDer_map_mem h g.2⟩
  invFun g := ⟨φ⁻¹ g, ggFixDer_map_mem (φ := φ⁻¹) (by
    calc φ⁻¹ * x = φ⁻¹ * (x * φ) * φ⁻¹ := by group
      _ = φ⁻¹ * (φ * x) * φ⁻¹ := by rw [h]
      _ = x * φ⁻¹ := by group) g.2⟩
  left_inv g := Subtype.ext (by simp)
  right_inv g := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (map_mul φ _ _)

theorem coe_ggFixDerRestrict {R : Type} [Group R] {x φ : MulAut R} (h : φ * x = x * φ)
    (g : ggFixDer x) : ((ggFixDerRestrict h g : ggFixDer x) : R) = φ g :=
  rfl

variable {d : ℕ} {K : Type} [Field K] [Finite K]

theorem ggFixGeom_linear (hd : 3 ≤ d) {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    {σ : K ≃+* K} {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))} (hf : Induced σ f) :
    GGFixGeom (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) f
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) (fixF σ))) Set.univ)
      (subfieldEquiv hd hm hK hf).symm := by
  set e := subfieldEquiv hd hm hK hf with he
  refine ⟨fun φ hφ hc => ?_, fun φ hφ _ htriv => ?_⟩
  · obtain ⟨B, hB⟩ := exists_conj_of_commute hd hf hφ hc
    refine ⟨(e.trans (ggFixDerRestrict hc)).trans e.symm, ⟨B, Set.mem_univ _, ?_⟩, ?_⟩
    · intro g g' hg
      change ((e.trans (ggFixDerRestrict hc)).trans e.symm) (QuotientGroup.mk g) =
        QuotientGroup.mk g'
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_eq]
      exact Subtype.ext (hB g g' hg)
    · intro g hg
      simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rfl
  · refine eq_one_of_fixes_subfield hd σ hφ fun g => htriv _ ?_
    rw [← range_subfieldHom hd hm hK hf]
    exact ⟨g, rfl⟩

end CFSG.StandardType.LinearFieldFix

end
