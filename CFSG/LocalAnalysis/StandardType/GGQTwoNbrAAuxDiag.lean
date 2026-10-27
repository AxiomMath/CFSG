module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAuxModel

public section

namespace CFSG.StandardType.QTwo

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
open CFSG.StandardType CFSG.Blueprint CFSG.ClassicalInvolution.Phan

theorem qTwoNbrA_diag_aut {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    (hF : Nat.card F0 = (2 ^ 1) ^ 2) {m : ℕ} {L0 : Type} [Group L0] (πSU : Su F0 2 1 m →* L0)
    {ρy : MulAut L0}
    (hdiag : ∃ g : GL (Fin m) F0, ggIsDiagMat g ∧ ∀ u : Su F0 2 1 m, ∃ u' : Su F0 2 1 m,
      (u' : GL (Fin m) F0) = g * (u : GL (Fin m) F0) * g⁻¹ ∧ ρy (πSU u) = πSU u') :
    ∃ (t : Fin m → F0) (δ : MulAut ↥(unitarySU 2 1 F0 m)), (∀ i, t i ≠ 0) ∧
      (∀ s : ↥(unitarySU 2 1 F0 m),
        (((δ s : ↥(unitarySU 2 1 F0 m)) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
            Matrix.diagonal t =
          Matrix.diagonal t * ((s : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) ∧
      ∀ s : ↥(unitarySU 2 1 F0 m),
        ρy ((πSU.comp (qTwoNbrRec_suEquiv hF m).symm.toMonoidHom) s) =
          (πSU.comp (qTwoNbrRec_suEquiv hF m).symm.toMonoidHom) (δ s) := by
  classical
  obtain ⟨g, hgdiag, hgact⟩ := hdiag
  obtain ⟨t, ht⟩ := hgdiag
  have htne : ∀ i, t i ≠ 0 := fun i => LineU.diag_ne_zero_of_eq ht i
  have hgunit : ggIsUnitaryMat (p := 2) (f := 1) g :=
    qTwoNbrRec_isUnitaryMat_of_isDiag (F := F0) (d := m) hF ⟨t, ht⟩
  have hgN : g ∈ Subgroup.normalizer (unitarySU 2 1 F0 m : Set (GL (Fin m) F0)) :=
    MpStdSU.mem_normalizer_of_isIdUnitary (f := 1) hF hgunit
  let δ : MulAut ↥(unitarySU 2 1 F0 m) :=
    (unitarySU 2 1 F0 m).normalizerMonoidHom ⟨g, hgN⟩
  have hδcoe : ∀ s : ↥(unitarySU 2 1 F0 m),
      (((δ s : ↥(unitarySU 2 1 F0 m)) : GL (Fin m) F0)) =
        g * (s : GL (Fin m) F0) * g⁻¹ := by
    intro s
    exact Subgroup.normalizerMonoidHom_apply_apply_coe _ ⟨g, hgN⟩ s
  refine ⟨t, δ, htne, ?_, ?_⟩
  · intro s
    have hginv_diag : ((g⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
        Matrix.diagonal t = 1 := by
      rw [← ht, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hδcoe s, Units.val_mul, Units.val_mul, ht]
    rw [Matrix.mul_assoc, hginv_diag, Matrix.mul_one]
  · intro s
    obtain ⟨u', hu'mat, hu'act⟩ := hgact ((qTwoNbrRec_suEquiv hF m).symm s)
    have hcoe_s : (s : GL (Fin m) F0) =
        ((qTwoNbrRec_suEquiv hF m).symm s : GL (Fin m) F0) := by
      rw [← qTwoNbrRec_coe_suEquiv hF ((qTwoNbrRec_suEquiv hF m).symm s),
        MulEquiv.apply_symm_apply]
    have heu' : qTwoNbrRec_suEquiv hF m u' = δ s := by
      apply Subtype.ext
      rw [qTwoNbrRec_coe_suEquiv hF u', hδcoe s, hu'mat, hcoe_s]
    have hu'eq : u' = (qTwoNbrRec_suEquiv hF m).symm (δ s) := by
      rw [← heu', MulEquiv.symm_apply_apply]
    change ρy (πSU ((qTwoNbrRec_suEquiv hF m).symm s)) =
      πSU ((qTwoNbrRec_suEquiv hF m).symm (δ s))
    rw [hu'act, hu'eq]

end CFSG.StandardType.QTwo

end
