module

public import CFSG.Monster.B.CTIB.Rep4371Trace
public import CFSG.Monster.B.CTIB.Rep4371End

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Griess CFSG.Monster.Visible
  CFSG.Monster.SpinLattice CFSG.Monster.Spin CFSG.Monster.B CFSG.Monster.B.Short
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.Rep4371
  Matrix
open CFSG.Monster.B.Co2 (v0)

theorem rational_4371_extraspecial_constituents_and_vertex_trace :
    Module.finrank ℚ Vst = 4371 ∧
    (∀ c : Cbar, (cbarEquiv c : Dfull) = iotaD c ∧ rhoV (cbarEquiv c) = chi c) ∧
    Function.Surjective psiW ∧ (∀ e : Ehat, psiW e = 0 ↔ e = 1 ∨ e = xhatE) ∧
    (∀ e f : Ehat, (e : Dfull) * f = f * e * xhat ^ (bV (psiW e) (psiW f)).val) ∧
    psiW cE = Unitary.sigmaW ∧ Unitary.OmegaW = wOrbit Unitary.sigmaW ∧
    Unitary.OmegaW.ncard = 2300 ∧
    Module.finrank ℚ V23 = 23 ∧ Module.finrank ℚ V2300 = 2300 ∧ Module.finrank ℚ V2048 = 2048 ∧
    iSupIndep ![V23, V2300, V2048] ∧ V23 ⊔ V2300 ⊔ V2048 = ⊤ ∧
    (∀ h : Shat, (h : Dfull) ∈ Jhat → (∀ v ∈ V23, rhoV h v ∈ V23) ∧
      (∀ v ∈ V2300, rhoV h v ∈ V2300) ∧ ∀ v ∈ V2048, rhoV h v ∈ V2048) ∧
    (∀ e : Ehat, ∀ v ∈ V23, rhoV (ehatS e) v = v) ∧
    (∀ a : Unitary.OmegaPt, Module.finrank ℚ (lineV a) = 1) ∧ iSupIndep lineV ∧
    ⨆ a, lineV a = V2300 ∧
    (∀ e : Ehat, ∀ a : Unitary.OmegaPt, ∀ v ∈ lineV a,
      rhoV (ehatS e) v = sgn (bV (psiW e) a) • v) ∧
    (∀ a a' : Unitary.OmegaPt, a ≠ a' → ∃ e : Ehat, sgn (bV (psiW e) a) ≠ sgn (bV (psiW e) a')) ∧
    (∀ h : Shat, ∀ hh : (h : Dfull) ∈ Jhat, ∀ a : Unitary.OmegaPt, ∀ v ∈ lineV a,
      rhoV h v ∈ lineV (jhatToKv0 ⟨h, hh⟩ • a)) ∧
    (∀ v ∈ V2048, rhoV (ehatS xhatE) v = -v) ∧
    (∀ sec : Wv v0 → Ehat, (∀ w, psiW (sec w) = w) →
      LinearIndependent ℚ (fun w => resE (sec w)) ∧
      Submodule.span ℚ (Set.range fun w => resE (sec w)) = ⊤ ∧
      (∀ w w', w ≠ w' → LinearMap.trace ℚ V2048 (resE (sec w) * resE (sec w')) = 0) ∧
      ∀ w, LinearMap.trace ℚ V2048 (resE (sec w) * resE (sec w)) = 2048 ∨
        LinearMap.trace ℚ V2048 (resE (sec w) * resE (sec w)) = -2048) ∧
    LinearIndependent ℚ (fun t : Fin 2048 => Rbasis (tIdx t)) ∧
    V2048 = Submodule.span ℚ (Set.range fun t : Fin 2048 => Rbasis (tIdx t)) ∧
    (∀ h : Shat, ∀ v ∈ V2048, spinCrd (rhoV h v) = blkM h *ᵥ spinCrd v) ∧
    (∀ t, (basisV2048 t : Vst) = Rbasis (tIdx t)) ∧
    (∀ h : Shat, ∀ hh : (h : Dfull) ∈ Jhat,
      LinearMap.toMatrix basisV2048 basisV2048 (resV2048 hh) = blkM h) ∧
    (∀ sec : Wv v0 → Ehat, (∀ w, psiW (sec w) = w) →
      LinearIndependent ℚ (fun w => blkM (ehatS (sec w))) ∧
      Submodule.span ℚ (Set.range fun w => blkM (ehatS (sec w))) = ⊤ ∧
      (∀ w w', w ≠ w' → Matrix.trace (blkM (ehatS (sec w)) * blkM (ehatS (sec w'))) = 0) ∧
      (∀ w, Matrix.trace (blkM (ehatS (sec w)) * blkM (ehatS (sec w))) = 2048 ∨
        Matrix.trace (blkM (ehatS (sec w)) * blkM (ehatS (sec w))) = -2048) ∧
      (∀ w w', w ≠ w' →
        Matrix.trace (blkM (ehatS (sec w)) * (blkM (ehatS (sec w')))ᵀ) = 0) ∧
      ∀ w, Matrix.trace (blkM (ehatS (sec w)) * (blkM (ehatS (sec w)))ᵀ) = 2048) ∧
    (∀ U : Submodule ℚ Vst, U ≤ V2048 → (∀ e : Ehat, ∀ v ∈ U, rhoV (ehatS e) v ∈ U) →
      U = ⊥ ∨ U = V2048) ∧
    (∀ z : CVert, (∃ s : Shat, (s : Dfull) = clabel z) ∧ ∀ s : Shat, (s : Dfull) = clabel z →
      LinearMap.trace ℚ Vst (rhoV s : Vst →ₗ[ℚ] Vst) = -493) ∧
    ∀ h : Shat, ∀ hh : (h : Dfull) ∈ Jhat, |LinearMap.trace ℚ V23 (resV23 hh)| ≤ 23 ∧
      |LinearMap.trace ℚ V2300 (resV2300 hh)| ≤
        {x | x ∈ Unitary.OmegaW ∧ wAct v0 (jhatToKv0 ⟨h, hh⟩) x = x}.ncard :=
  ⟨finrank_Vst, fun c => ⟨rfl, rhoV_cbarEquiv c⟩, psiW_surjective, psiW_eq_zero_iff, Ehat_comm,
    psiW_cE, rfl, Unitary.ncard_OmegaW, finrank_V23, finrank_V2300, finrank_V2048, iSupIndep_V,
    sup_V, fun _ hh => Jhat_preserves hh, fun e _ hv => Ehat_trivial_V23 (e := ehatS e) e.2 hv,
    finrank_lineV, iSupIndep_lineV, iSup_lineV, fun _ _ _ hv => rhoV_lineB hv,
    fun _ _ h => by
      obtain ⟨e, he⟩ := exists_char_ne h
      exact ⟨e, fun h' => he (sgn_zmod_injective h')⟩,
    fun _ hh _ _ hv => rhoV_mem_lineB hh hv,
    fun v hv => (rhoV_xhat_V2048 hv).trans (neg_one_smul ℚ v),
    fun sec hsec => ⟨linearIndependent_resE sec hsec, span_resE sec hsec,
      fun w w' hw => trace_resE_mul_eq_zero (by rw [hsec, hsec]; exact hw),
      fun w => trace_resE_mul_self (sec w)⟩,
    linearIndependent_RbT, V2048_eq_span, fun h _ hv => spinCrd_rhoV h hv, coe_basisV2048,
    fun _ hh => toMatrix_resV2048 hh,
    fun sec hsec => ⟨linearIndependent_blkM sec hsec, span_blkM sec hsec,
      fun w w' hw => trace_blkM_mul_eq_zero (by rw [hsec, hsec]; exact hw),
      fun w => trace_blkM_mul_self (sec w),
      fun w w' hw => trace_blkM_mul_transpose_eq_zero (by rw [hsec, hsec]; exact hw),
      fun w => trace_blkM_mul_transpose_self (sec w)⟩,
    V2048_irreducible, fun z => trace_rhoV_clabel' z,
    fun _ hh => ⟨abs_trace_resV23_le hh, abs_trace_resV2300_le hh⟩⟩

end CFSG.Monster.B.CTIB
