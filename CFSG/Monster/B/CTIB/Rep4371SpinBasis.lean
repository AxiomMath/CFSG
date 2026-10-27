module

public import CFSG.Monster.B.CTIB.Rep4371Spin

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Griess CFSG.Monster.Visible
  CFSG.Monster.SpinLattice CFSG.Monster.Spin CFSG.Monster.ScalarKernel CFSG.Monster.B
  CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.Rep4371 Matrix
open CFSG.Monster.B.Co2 (v0)

@[expose] def ehatS (e : Ehat) : Shat := ⟨e, Ehat_le_Shat' e.2⟩

theorem coe_ehatS (e : Ehat) : ((ehatS e : Shat) : Dfull) = e := rfl

theorem ehatS_mul (e f : Ehat) : ehatS (e * f) = ehatS e * ehatS f := rfl

theorem ehatS_one : ehatS 1 = 1 := rfl

theorem psiW_eq_zero_iff_coordOf {q : Q} (hq : q ∈ Subgroup.centralizer {rStar}) {e : Ehat}
    (hqe : iotaD (kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩) = e) :
    psiW e = 0 ↔ coordOf q = 0 ∨ coordOf q = coordOf rStar := by
  have he : iotaD (kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩) ∈ Ehat := by rw [hqe]; exact e.2
  have e1 : e = ⟨_, he⟩ := Subtype.ext hqe.symm
  rw [e1, psiW_iotaD_rho hq he, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
  show phi0 (coordOf q) ∈ vLineL (phi0 (coordOf rStar)) ↔ _
  exact mem_vLineL.trans (or_congr (phi0_injective.eq_iff' (map_zero phi0)) phi0_injective.eq_iff)

theorem trace_blkM_Ehat_eq_zero
    {e : Ehat} (he : psiW e ≠ 0) :
    Matrix.trace (blkM (ehatS e)) = 0 := by
  obtain ⟨q, hq, hqe⟩ := exists_of_mem_Ehat e.2
  have e1 : ehatS e = shatQ q hq := Subtype.ext hqe.symm
  rw [e1]
  have h := mt (psiW_eq_zero_iff_coordOf hq hqe).2 he
  rw [not_or] at h
  exact trace_blkM_shatQ_eq_zero hq h.1 h.2

theorem blkM_xhat :
    blkM (ehatS xhatE) = -1 := by
  have e1 : ehatS xhatE = shatQ zQ zQ_mem_centralizer_rStar := Subtype.ext rfl
  ext s t
  rw [e1, blkM_shatQ, Rq, coe_zQ, coe_zU, zmat, Matrix.neg_apply, Matrix.neg_apply,
    Matrix.one_apply, Matrix.one_apply]
  by_cases h : s = t
  · rw [ite_eq_left (congrArg spinIdx h.symm), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (spinIdx_injective h').symm), ite_eq_right h]

theorem blkM_mul_Jhat
    (h : Shat) {h' : Shat} (hh' : (h' : Dfull) ∈ Jhat) :
    blkM (h * h') = blkM h * blkM h' :=
  blkM_mul h h' fun v hv => (Jhat_preserves hh').2.2 v hv

theorem blkM_ehatS_mul
    (e f : Ehat) : blkM (ehatS (e * f)) = blkM (ehatS e) * blkM (ehatS f) := by
  rw [ehatS_mul]
  exact blkM_mul_Jhat _ (Ehat_le_Jhat f.2)

theorem trace_blkM_mul_eq_zero
    {e f : Ehat} (h : psiW e ≠ psiW f) :
    Matrix.trace (blkM (ehatS e) * blkM (ehatS f)) = 0 := by
  rw [← blkM_ehatS_mul]
  refine trace_blkM_Ehat_eq_zero fun h' => h ?_
  rw [psiW_mul] at h'
  rw [← sub_eq_zero, sub_eq_add_neg, ZModModule.neg_eq_self]
  exact h'

theorem trace_blkM_mul_self
    (e : Ehat) :
    Matrix.trace (blkM (ehatS e) * blkM (ehatS e)) = 2048 ∨
      Matrix.trace (blkM (ehatS e) * blkM (ehatS e)) = -2048 := by
  rw [← blkM_ehatS_mul]
  have h0 : psiW (e * e) = 0 := by rw [psiW_mul, ZModModule.add_self]
  rcases (psiW_eq_zero_iff (e * e)).1 h0 with h | h
  · left
    rw [h, ehatS_one, blkM_one, Matrix.trace_one, Fintype.card_fin]
    norm_num
  · right
    rw [h, blkM_xhat, Matrix.trace_neg, Matrix.trace_one, Fintype.card_fin]
    norm_num

theorem trace_blkM_mul_self_ne_zero
    (e : Ehat) :
    Matrix.trace (blkM (ehatS e) * blkM (ehatS e)) ≠ 0 := by
  rcases trace_blkM_mul_self e with h | h <;> rw [h] <;> norm_num

theorem Rq_one : Rq 1 = 1 := by
  rw [Rq, Subgroup.coe_one, Units.val_one]

theorem Rq_inv (q : Q) : Rq q⁻¹ = (Rq q)ᵀ := by
  have h1 : Rq q * (Rq q)ᵀ = 1 := by
    rw [Rq_eq]
    exact qmatR_mul_transpose_self _ _ _
  calc Rq q⁻¹ = Rq q⁻¹ * (Rq q * (Rq q)ᵀ) := by rw [h1, Matrix.mul_one]
    _ = (Rq q)ᵀ := by rw [← Matrix.mul_assoc, Rq_mul, inv_mul_cancel, Rq_one, Matrix.one_mul]

theorem shatQ_inv {q : Q} (hq : q ∈ Subgroup.centralizer {rStar}) :
    (shatQ q hq)⁻¹ = shatQ q⁻¹ (Subgroup.inv_mem _ hq) := by
  rw [shatQ, shatQ, ← map_inv, ← map_inv]
  congr 2

theorem blkM_transpose
    (e : Ehat) : (blkM (ehatS e))ᵀ = blkM (ehatS e⁻¹) := by
  obtain ⟨q, hq, hqe⟩ := exists_of_mem_Ehat e.2
  have e1 : ehatS e = shatQ q hq := Subtype.ext hqe.symm
  have e2 : ehatS e⁻¹ = shatQ q⁻¹ (Subgroup.inv_mem _ hq) := by
    rw [show ehatS e⁻¹ = (ehatS e)⁻¹ from rfl, e1, shatQ_inv]
  ext s t
  rw [Matrix.transpose_apply, e1, e2, blkM_shatQ, blkM_shatQ, Rq_inv, Matrix.transpose_apply]

theorem trace_blkM_mul_transpose_eq_zero
    {e f : Ehat} (h : psiW e ≠ psiW f) :
    Matrix.trace (blkM (ehatS e) * (blkM (ehatS f))ᵀ) = 0 := by
  rw [blkM_transpose, ← blkM_ehatS_mul]
  refine trace_blkM_Ehat_eq_zero fun h' => h ?_
  rw [psiW_mul, psiW_inv, ← sub_eq_add_neg, sub_eq_zero] at h'
  exact h'

theorem trace_blkM_mul_transpose_self
    (e : Ehat) :
    Matrix.trace (blkM (ehatS e) * (blkM (ehatS e))ᵀ) = 2048 := by
  rw [blkM_transpose, ← blkM_ehatS_mul, mul_inv_cancel, ehatS_one, blkM_one, Matrix.trace_one,
    Fintype.card_fin]
  norm_num

theorem linearIndependent_blkM
    (sec : Wv v0 → Ehat) (hsec : ∀ w, psiW (sec w) = w) :
    LinearIndependent ℚ (fun w => blkM (ehatS (sec w))) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congrArg (fun A => Matrix.trace (A * blkM (ehatS (sec i)))) hg
  simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.zero_mul, Matrix.trace_zero,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at h
  rw [Finset.sum_eq_single i (fun j _ hj => by
      rw [trace_blkM_mul_eq_zero (by rw [hsec, hsec]; exact hj), mul_zero])
    (fun h' => absurd hi h')] at h
  exact (mul_eq_zero.1 h).resolve_right (trace_blkM_mul_self_ne_zero _)

theorem card_Wv
    [Fintype (Wv v0)] : Fintype.card (Wv v0) = 2 ^ 22 := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, Co2.finrank_W]

theorem span_blkM
    (sec : Wv v0 → Ehat) (hsec : ∀ w, psiW (sec w) = w) :
    Submodule.span ℚ (Set.range fun w => blkM (ehatS (sec w))) = ⊤ := by
  have : Fintype (Wv v0) := Fintype.ofFinite _
  refine (linearIndependent_blkM sec hsec).span_eq_top_of_card_eq_finrank' ?_
  rw [card_Wv, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self]
  norm_num

@[expose] noncomputable def spinCrd
    (v : Vst) : Fin 2048 → ℚ := fun s => Rbasis.repr v (tIdx s)

theorem spinCrd_rhoV
    (h : Shat) {v : Vst} (hv : v ∈ V2048) :
    spinCrd (rhoV h v) = blkM h *ᵥ spinCrd v := by
  funext s
  rw [spinCrd, repr_rhoV_blk h hv s]
  rfl

theorem repr_eq_zero_of_mem_span {v : Vst}
    (hv : v ∈ Submodule.span ℚ (Set.range fun t => Rbasis (tIdx t))) {k : Fin 4371}
    (hk : ∀ t, tIdx t ≠ k) : Rbasis.repr v k = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    rw [Module.Basis.repr_self, Finsupp.single_apply, ite_eq_right (hk t)]
  | zero => exact repr_zero' k
  | add x y _ _ hx hy => rw [repr_add, hx, hy, add_zero]
  | smul c x _ hx => rw [repr_smul, hx, mul_zero]

theorem eq_of_spinCrd {v w : Vst} (hv : v ∈ V2048) (hw : w ∈ V2048)
    (h : spinCrd v = spinCrd w) : v = w := by
  apply Rbasis.ext_elem
  intro k
  by_cases hk : ∃ t, tIdx t = k
  · obtain ⟨t, rfl⟩ := hk
    exact congrFun h t
  · push Not at hk
    rw [repr_eq_zero_of_mem_span (Tplus_span_Vst hv) hk,
      repr_eq_zero_of_mem_span (Tplus_span_Vst hw) hk]

theorem spinCrd_Rbasis
    (t : Fin 2048) : spinCrd (Rbasis (tIdx t)) = Pi.single t 1 := by
  funext s
  rw [spinCrd, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : s = t
  · rw [ite_eq_left (congrArg tIdx h.symm), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (tIdx_injective h').symm), ite_eq_right h]

theorem spinCrd_zero : spinCrd 0 = 0 := funext fun _ => repr_zero' _

theorem spinCrd_add
    (x y : Vst) : spinCrd (x + y) = spinCrd x + spinCrd y :=
  funext fun _ => repr_add x y _

theorem spinCrd_smul
    (c : ℚ) (x : Vst) : spinCrd (c • x) = c • spinCrd x :=
  funext fun _ => repr_smul c x _

theorem V2048_irreducible
    (U : Submodule ℚ Vst) (hU : U ≤ V2048)
    (hinv : ∀ e : Ehat, ∀ v ∈ U, rhoV (ehatS e) v ∈ U) : U = ⊥ ∨ U = V2048 := by
  by_cases h0 : U = ⊥
  · exact .inl h0
  right
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hcrd : ∃ s₀, spinCrd u s₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hu0 (eq_of_spinCrd (hU hu) (Submodule.zero_mem _) (by rw [spinCrd_zero]; exact funext hc))
  obtain ⟨s₀, hs₀⟩ := hcrd
  choose sec hsec using psiW_surjective
  have hall : ∀ A : Matrix (Fin 2048) (Fin 2048) ℚ, ∃ y ∈ U, spinCrd y = A *ᵥ spinCrd u := by
    intro A
    have hA : A ∈ Submodule.span ℚ (Set.range fun w => blkM (ehatS (sec w))) := by
      rw [span_blkM sec hsec]
      exact Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact ⟨rhoV (ehatS (sec w)) u, hinv _ u hu, spinCrd_rhoV _ (hU hu)⟩
    | zero => exact ⟨0, U.zero_mem, by rw [Matrix.zero_mulVec, spinCrd_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      exact ⟨a + b, U.add_mem ha hb, by rw [Matrix.add_mulVec, ← hax, ← hby, spinCrd_add]⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, hax⟩ := hx
      exact ⟨c • a, U.smul_mem c ha, by rw [Matrix.smul_mulVec, ← hax, spinCrd_smul]⟩
  have hbasis : ∀ t, Rbasis (tIdx t) ∈ U := by
    intro t
    obtain ⟨y, hy, hyc⟩ := hall (Matrix.single t s₀ (spinCrd u s₀)⁻¹)
    have hyt : y = Rbasis (tIdx t) := by
      refine eq_of_spinCrd (hU hy) (Rbasis_tIdx_mem t) ?_
      rw [hyc, spinCrd_Rbasis, Matrix.single_mulVec, inv_mul_cancel₀ hs₀]
      funext s
      rw [Function.update_apply, Pi.single_apply]
      rfl
    rw [← hyt]
    exact hy
  refine le_antisymm hU fun v hv => ?_
  exact Submodule.span_le.2 (by rintro _ ⟨t, rfl⟩; exact hbasis t) (Tplus_span_Vst hv)

theorem rhoV_xhat_V2048
    {v : Vst} (hv : v ∈ V2048) : rhoV (ehatS xhatE) v = (-1 : ℚ) • v := by
  have hmem : rhoV (ehatS xhatE) v ∈ V2048 :=
    (Jhat_preserves (Ehat_le_Jhat xhatE.2)).2.2 v hv
  refine eq_of_spinCrd hmem (V2048.smul_mem _ hv) ?_
  rw [spinCrd_rhoV _ hv, blkM_xhat, spinCrd_smul, Matrix.neg_mulVec, Matrix.one_mulVec,
    neg_one_smul]

theorem linearIndependent_RbT :
    LinearIndependent ℚ fun t : Fin 2048 => Rbasis (tIdx t) :=
  Rbasis.linearIndependent.comp _ tIdx_injective

theorem V2048_eq_span :
    V2048 = Submodule.span ℚ (Set.range fun t : Fin 2048 => Rbasis (tIdx t)) :=
  le_antisymm (fun _ hv => Tplus_span_Vst hv)
    (Submodule.span_le.2 (by rintro _ ⟨t, rfl⟩; exact Rbasis_tIdx_mem t))

end CFSG.Monster.B.CTIB
