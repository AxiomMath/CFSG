module

public import CFSG.Monster.Visible.Action
public import CFSG.Monster.Griess.Product

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.ScalarKernel Matrix Subgroup

theorem dotProduct_vecMul_vecMul {n : Type*} [Fintype n] [DecidableEq n] {g : Matrix n n ℚ}
    (hg : g * gᵀ = 1) (a b : n → ℚ) : (a ᵥ* g) ⬝ᵥ (b ᵥ* g) = a ⬝ᵥ b := by
  rw [← dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hg, one_mulVec]

theorem conj_dotProduct {g : Matrix (Fin 24) (Fin 24) ℚ} (hg : g * gᵀ = 1)
    (A : Matrix (Fin 24) (Fin 24) ℚ) (v w : Fin 24 → ℚ) :
    (v ᵥ* g) ⬝ᵥ ((gᵀ * A * g) *ᵥ (w ᵥ* g)) = v ⬝ᵥ (A *ᵥ w) := by
  have h1 : g *ᵥ (w ᵥ* g) = w := by rw [← mulVec_transpose, mulVec_mulVec, hg, one_mulVec]
  rw [← mulVec_mulVec, h1, ← mulVec_mulVec, mulVec_transpose, dotProduct_vecMul_vecMul hg]

theorem trace_conj {g : Matrix (Fin 24) (Fin 24) ℚ} (hg : g * gᵀ = 1)
    (A : Matrix (Fin 24) (Fin 24) ℚ) : trace (gᵀ * A * g) = trace A := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, hg, Matrix.one_mul]

theorem trace_conj3 {g : Matrix (Fin 24) (Fin 24) ℚ} (hg : g * gᵀ = 1)
    (A A' A'' : Matrix (Fin 24) (Fin 24) ℚ) :
    trace (gᵀ * A * g * (gᵀ * A' * g) * (gᵀ * A'' * g)) = trace (A * A' * A'') := by
  have h : ∀ M : Matrix (Fin 24) (Fin 24) ℚ, g * (gᵀ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hg, Matrix.one_mul]
  have e : gᵀ * A * g * (gᵀ * A' * g) * (gᵀ * A'' * g) = gᵀ * (A * A' * A'') * g := by
    simp only [Matrix.mul_assoc, h]
  rw [e, trace_conj hg]

theorem spin_mul_transpose (p : Pvis) :
    (p.1.1 : Matrix SpinIdx SpinIdx ℚ) * (p.1.1 : Matrix SpinIdx SpinIdx ℚ)ᵀ = 1 :=
  (mem_orthogonalGroup_iff _ _).1 (isDyadicSpinNormalizer p).1

theorem uQ_conjQ (p : Pvis) {r : Q} (hr : IsShortCoord (coordOf r)) :
    uQ ⟨coordOf r, hr⟩ ᵥ* mat p.1.2 = uQ ⟨coordOf (conjQ p r), isShortCoord_conjQ p hr⟩ ∨
      uQ ⟨coordOf r, hr⟩ ᵥ* mat p.1.2 = -uQ ⟨coordOf (conjQ p r), isShortCoord_conjQ p hr⟩ := by
  have hu := uvec_mem ⟨coordOf r, hr⟩
  have hu' := uvec_mem ⟨coordOf (conjQ p r), isShortCoord_conjQ p hr⟩
  have hcl : classOf (latVec (mat p.1.2) (uvec ⟨coordOf r, hr⟩)) =
      classOf (uvec ⟨coordOf (conjQ p r), isShortCoord_conjQ p hr⟩) :=
    calc classOf (latVec (mat p.1.2) (uvec ⟨coordOf r, hr⟩))
        = modTwoEnd p.1.2 (classOf (uvec ⟨coordOf r, hr⟩)) := classOf_latVec p.1.2 hu.1
      _ = modTwoEnd p.1.2 (phi0 (coordOf r)) :=
          congrArg (modTwoEnd p.1.2) (classOf_uvec ⟨coordOf r, hr⟩)
      _ = modTwoEnd p.1.2 (Multiplicative.toAdd (phi (QuotientGroup.mk r))) :=
          congrArg (modTwoEnd p.1.2) (toAdd_phi_mk r).symm
      _ = Multiplicative.toAdd (phi (QuotientGroup.mk (conjQ p r))) := (phi_conjQ p r).symm
      _ = phi0 (coordOf (conjQ p r)) := toAdd_phi_mk (conjQ p r)
      _ = classOf (uvec ⟨coordOf (conjQ p r), isShortCoord_conjQ p hr⟩) :=
          (classOf_uvec ⟨coordOf (conjQ p r), isShortCoord_conjQ p hr⟩).symm
  have e : uQ ⟨coordOf r, hr⟩ ᵥ* mat p.1.2 = ratVec (latVec (mat p.1.2) (uvec ⟨coordOf r, hr⟩)) :=
    (latVec_spec p.1.2 hu.1).2.symm
  rcases (classOf_eq_iff (latVec_mem_minVecs p.1.2 hu) hu').1 hcl with h | h
  · exact Or.inl (e.trans (congrArg ratVec h.symm))
  · have h' : latVec (mat p.1.2) (uvec ⟨coordOf r, hr⟩) =
        -uvec ⟨coordOf (conjQ p r), isShortCoord_conjQ p hr⟩ :=
      (neg_neg _).symm.trans (congrArg Neg.neg h.symm)
    exact Or.inr ((e.trans (congrArg ratVec h')).trans (ratVec_neg _))

theorem qf_conjQ (p : Pvis) {r : Q} (hr : IsShortCoord (coordOf r)) (A : Matrix (Fin 24) (Fin 24) ℚ) :
    qf ⟨coordOf (conjQ p r), isShortCoord_conjQ p hr⟩ ((mat p.1.2)ᵀ * A * mat p.1.2) =
      qf ⟨coordOf r, hr⟩ A := by
  have hg := mat_mul_transpose p.1.2
  rcases uQ_conjQ p hr with h | h
  · exact (congrArg (fun x => x ⬝ᵥ (((mat p.1.2)ᵀ * A * mat p.1.2) *ᵥ x)) h).symm.trans
      (conj_dotProduct hg A _ _)
  · have h' : uQ ⟨coordOf (conjQ p r), isShortCoord_conjQ p hr⟩ =
        -(uQ ⟨coordOf r, hr⟩ ᵥ* mat p.1.2) := (neg_neg _).symm.trans (congrArg Neg.neg h.symm)
    refine (congrArg (fun x => x ⬝ᵥ (((mat p.1.2)ᵀ * A * mat p.1.2) *ᵥ x)) h').trans ?_
    simp only [mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
    exact conj_dotProduct hg A _ _

theorem dot_uQ_conjQ_sq (p : Pvis) {r : Q} (hr : IsShortCoord (coordOf r)) (v w : Fin 24 → ℚ) :
    ((v ᵥ* mat p.1.2) ⬝ᵥ uQ ⟨coordOf (conjQ p r), isShortCoord_conjQ p hr⟩) *
      ((w ᵥ* mat p.1.2) ⬝ᵥ uQ ⟨coordOf (conjQ p r), isShortCoord_conjQ p hr⟩) =
    (v ⬝ᵥ uQ ⟨coordOf r, hr⟩) * (w ⬝ᵥ uQ ⟨coordOf r, hr⟩) := by
  have hg := mat_mul_transpose p.1.2
  rcases uQ_conjQ p hr with h | h
  · refine (congrArg (fun x => ((v ᵥ* mat p.1.2) ⬝ᵥ x) * ((w ᵥ* mat p.1.2) ⬝ᵥ x)) h).symm.trans ?_
    simp only [dotProduct_vecMul_vecMul hg]
  · have h' : uQ ⟨coordOf (conjQ p r), isShortCoord_conjQ p hr⟩ =
        -(uQ ⟨coordOf r, hr⟩ ᵥ* mat p.1.2) := (neg_neg _).symm.trans (congrArg Neg.neg h.symm)
    refine (congrArg (fun x => ((v ᵥ* mat p.1.2) ⬝ᵥ x) * ((w ᵥ* mat p.1.2) ⬝ᵥ x)) h').trans ?_
    simp only [dotProduct_neg, dotProduct_vecMul_vecMul hg, neg_mul_neg]

theorem conjQ_zQ_pow (p : Pvis) (n : ℕ) : conjQ p (zQ ^ n) = zQ ^ n := by
  rw [map_pow, conjQ_zQ]

theorem theta_inA (p : Pvis) (A : symMat) : theta p (inA A) = inA (thetaA (mat p.1.2) A) :=
  theta_symMat p A

theorem theta_inX (p : Pvis) (x : SpaceX) : theta p (inX x) = inX (thetaX p x) := by
  rw [theta_apply, map_zero, map_zero]

theorem theta_inW (p : Pvis) (N : SpaceW) :
    theta p (inW N) = inW (thetaW (p.1.1 : Matrix SpinIdx SpinIdx ℚ) (mat p.1.2) N) := by
  rw [theta_apply, map_zero, map_zero]

theorem theta_inX_Xlift (p : Pvis) (r : Q) : theta p (inX (Xlift r)) = inX (Xlift (conjQ p r)) :=
  theta_Xlift p r

theorem theta_inW_tensor (p : Pvis) (q : SpinIdx → ℚ) (v : Fin 24 → ℚ) :
    theta p (inW (tensor q v)) =
      inW (tensor (q ᵥ* (p.1.1 : Matrix SpinIdx SpinIdx ℚ)) (v ᵥ* mat p.1.2)) :=
  theta_tensor p q v

@[expose] noncomputable def thetaT (p : Pvis) : SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] ℚ :=
  (T.compl₁₂ (theta p) (theta p)).compr₂ (LinearMap.lcomp ℚ ℚ (theta p))

theorem thetaT_apply (p : Pvis) (u v w : SpaceB) :
    thetaT p u v w = T (theta p u) (theta p v) (theta p w) := rfl

theorem T_congr {u u' v v' w w' : SpaceB} (hu : u = u') (hv : v = v') (hw : w = w') :
    T u v w = T u' v' w' := by
  subst hu hv hw
  rfl

theorem conjQ_mat (p : Pvis) (r : Q) :
    ((conjQ p r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      ((p.1.1⁻¹ : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) *
        ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) *
        ((p.1.1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) := by
  rw [coe_conjQ, Units.val_mul, Units.val_mul]

theorem vecMul_conjQ_dotProduct (p : Pvis) (r : Q) (q q' : SpinIdx → ℚ) :
    ((q ᵥ* (p.1.1 : Matrix SpinIdx SpinIdx ℚ)) ᵥ*
        ((conjQ p r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)) ⬝ᵥ
      (q' ᵥ* (p.1.1 : Matrix SpinIdx SpinIdx ℚ)) =
    (q ᵥ* ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)) ⬝ᵥ q' := by
  have hsinv : ((p.1.1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) *
      ((p.1.1⁻¹ : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = 1 := Units.mul_inv _
  rw [conjQ_mat, vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hsinv, Matrix.one_mul,
    ← vecMul_vecMul, dotProduct_vecMul_vecMul (spin_mul_transpose p)]

theorem isGriessForm_thetaT (p : Pvis) : IsGriessForm (thetaT p) := by
  have hg := mat_mul_transpose p.1.2
  have hs := spin_mul_transpose p
  obtain ⟨sA, sXXA, sXXX, sWWA, sWWX, sAAX, sAAW, sAXW, sXXW, sWWW⟩ := isGriessForm_T
  refine ⟨fun A A' A'' => ?_, fun r s hr hs' A => ?_, fun r s t hr hs' ht => ?_,
    fun q q' v w A => ?_, fun q q' v w r hr => ?_, fun A A' x => ?_, fun A A' N => ?_,
    fun A x N => ?_, fun x x' N => ?_, fun N N' N'' => ?_⟩
  · refine ((thetaT_apply p _ _ _).trans
      (T_congr (theta_inA p A) (theta_inA p A') (theta_inA p A''))).trans ?_
    rw [sA, coe_thetaA, coe_thetaA, coe_thetaA, trace_conj3 hg]
  · have e1 : thetaT p (inX (Xlift r)) (inX (Xlift s)) (inA A) =
        T (inX (Xlift (conjQ p r))) (inX (Xlift (conjQ p s))) (inA (thetaA (mat p.1.2) A)) :=
      (thetaT_apply p _ _ _).trans
        (T_congr (theta_inX_Xlift p r) (theta_inX_Xlift p s) (theta_inA p A))
    obtain ⟨h1, h2⟩ := sXXA (conjQ p r) (conjQ p s) (isShortCoord_conjQ p hr)
      (isShortCoord_conjQ p hs') (thetaA (mat p.1.2) A)
    refine ⟨fun e he => e1.trans ?_, fun hn => e1.trans ?_⟩
    · have he' : conjQ p r * conjQ p s = zQ ^ e.val :=
        ((map_mul (conjQ p) r s).symm.trans (congrArg (conjQ p) he)).trans (conjQ_zQ_pow p _)
      exact (h1 e he').trans (congrArg (fun t => sgn e * t / 8)
        ((congrArg (qf _) (coe_thetaA _ _)).trans (qf_conjQ p hr A)))
    · have hn' : conjQ p r * conjQ p s ∉ zpowers zQ := fun h =>
        hn ((conjQ_mem_zpowers_iff p (r * s)).1 ((map_mul (conjQ p) r s).symm ▸ h))
      exact h2 hn'
  · have e1 : thetaT p (inX (Xlift r)) (inX (Xlift s)) (inX (Xlift t)) =
        T (inX (Xlift (conjQ p r))) (inX (Xlift (conjQ p s))) (inX (Xlift (conjQ p t))) :=
      (thetaT_apply p _ _ _).trans
        (T_congr (theta_inX_Xlift p r) (theta_inX_Xlift p s) (theta_inX_Xlift p t))
    obtain ⟨h1, h2⟩ := sXXX (conjQ p r) (conjQ p s) (conjQ p t) (isShortCoord_conjQ p hr)
      (isShortCoord_conjQ p hs') (isShortCoord_conjQ p ht)
    have hm : conjQ p r * conjQ p s * conjQ p t = conjQ p (r * s * t) :=
      ((congrArg (· * conjQ p t) (map_mul (conjQ p) r s).symm).trans
        (map_mul (conjQ p) (r * s) t).symm)
    refine ⟨fun e he => e1.trans (h1 e ?_), fun hn => e1.trans (h2 ?_)⟩
    · exact hm.trans ((congrArg (conjQ p) he).trans (conjQ_zQ_pow p _))
    · exact fun h => hn ((conjQ_mem_zpowers_iff p _).1 (hm ▸ h))
  · refine ((thetaT_apply p _ _ _).trans
      (T_congr (theta_inW_tensor p q v) (theta_inW_tensor p q' w) (theta_inA p A))).trans ?_
    refine (sWWA _ _ _ _ _).trans ?_
    have e1 : (q ᵥ* (p.1.1 : Matrix SpinIdx SpinIdx ℚ)) ⬝ᵥ (q' ᵥ* (p.1.1 : Matrix SpinIdx SpinIdx ℚ))
        = q ⬝ᵥ q' := dotProduct_vecMul_vecMul hs q q'
    have e2 : (v ᵥ* mat p.1.2) ⬝ᵥ (w ᵥ* mat p.1.2) = v ⬝ᵥ w := dotProduct_vecMul_vecMul hg v w
    have e3 : trace (thetaA (mat p.1.2) A : Matrix (Fin 24) (Fin 24) ℚ) =
        trace (A : Matrix (Fin 24) (Fin 24) ℚ) :=
      (congrArg trace (coe_thetaA _ _)).trans (trace_conj hg _)
    have e4 : (v ᵥ* mat p.1.2) ⬝ᵥ ((thetaA (mat p.1.2) A : Matrix (Fin 24) (Fin 24) ℚ) *ᵥ
        (w ᵥ* mat p.1.2)) = v ⬝ᵥ ((A : Matrix (Fin 24) (Fin 24) ℚ) *ᵥ w) :=
      (congrArg (fun M => (v ᵥ* mat p.1.2) ⬝ᵥ (M *ᵥ (w ᵥ* mat p.1.2))) (coe_thetaA _ _)).trans
        (conj_dotProduct hg _ v w)
    simp only [e1, e2, e3, e4]
  · refine ((thetaT_apply p _ _ _).trans (T_congr (theta_inW_tensor p q v)
      (theta_inW_tensor p q' w) (theta_inX_Xlift p r))).trans ?_
    refine (sWWX _ _ _ _ (conjQ p r) (isShortCoord_conjQ p hr)).trans ?_
    simp only [vecMul_conjQ_dotProduct p r q q', dotProduct_vecMul_vecMul hg v w,
      dot_uQ_conjQ_sq p hr v w]
  · exact ((thetaT_apply p _ _ _).trans (T_congr (theta_inA p A) (theta_inA p A') (theta_inX p x))).trans
      (sAAX _ _ _)
  · exact ((thetaT_apply p _ _ _).trans (T_congr (theta_inA p A) (theta_inA p A') (theta_inW p N))).trans
      (sAAW _ _ _)
  · exact ((thetaT_apply p _ _ _).trans (T_congr (theta_inA p A) (theta_inX p x) (theta_inW p N))).trans
      (sAXW _ _ _)
  · exact ((thetaT_apply p _ _ _).trans (T_congr (theta_inX p x) (theta_inX p x') (theta_inW p N))).trans
      (sXXW _ _ _)
  · exact ((thetaT_apply p _ _ _).trans (T_congr (theta_inW p N) (theta_inW p N') (theta_inW p N''))).trans
      (sWWW _ _ _)

theorem T_theta (p : Pvis) (u v w : SpaceB) :
    T (theta p u) (theta p v) (theta p w) = T u v w := by
  have h := T_unique (thetaT p) (fun u v w => by rw [thetaT_apply, thetaT_apply, T_swap12])
    (fun u v w => by rw [thetaT_apply, thetaT_apply, T_swap23]) (isGriessForm_thetaT p)
  exact (thetaT_apply p u v w).symm.trans (congrArg (fun f => f u v w) h)

theorem theta_inv_apply (p : Pvis) (x : SpaceB) : theta p (theta p⁻¹ x) = x := by
  rw [← theta_mul_apply, inv_mul_cancel, theta_one_apply]

theorem theta_gmul (p : Pvis) (u v : SpaceB) :
    theta p (gmul u v) = gmul (theta p u) (theta p v) := by
  refine eq_of_bform_eq fun w => ?_
  calc bform (theta p (gmul u v)) w = bform (theta p (gmul u v)) (theta p (theta p⁻¹ w)) := by
        rw [theta_inv_apply]
    _ = bform (gmul u v) (theta p⁻¹ w) := bform_theta p _ _
    _ = T u v (theta p⁻¹ w) := bform_gmul _ _ _
    _ = T (theta p u) (theta p v) (theta p (theta p⁻¹ w)) := (T_theta p u v _).symm
    _ = T (theta p u) (theta p v) w := by rw [theta_inv_apply]
    _ = bform (gmul (theta p u) (theta p v)) w := (bform_gmul _ _ _).symm

theorem mem_Gvis_gmul {f : SpaceB ≃ₗ[ℚ] SpaceB} (hf : f ∈ Gvis) (u v : SpaceB) :
    f (gmul u v) = gmul (f u) (f v) ∧ bform (f u) (f v) = bform u v := by
  obtain ⟨p, rfl⟩ := hf
  rw [thetaEquiv_apply, thetaEquiv_apply, thetaEquiv_apply]
  exact ⟨theta_gmul p u v, bform_theta p u v⟩

theorem compatible_pair_algebra_action :
    (∀ (p : Pvis) (u v : SpaceB), theta p (gmul u v) = gmul (theta p u) (theta p v)) ∧
    (∀ (p : Pvis) (u v w : SpaceB), T (theta p u) (theta p v) (theta p w) = T u v w) ∧

    (∀ (p : Pvis) (u v : SpaceB), bform (theta p u) (theta p v) = bform u v) ∧
    (∀ p : Pvis, BR.map ((theta p).restrictScalars dyadic) = BR) ∧
    (∀ (p : Pvis) (u : SpaceB), theta p u ∈ BR ↔ u ∈ BR) ∧
    (negPair : GL SpinIdx ℚ × latticeO) = (zU, negOneO) ∧
    (zU : Matrix SpinIdx SpinIdx ℚ) = -1 ∧ mat negOneO = -1 ∧
    (thetaHom.ker : Set Pvis) = {1, negPair} ∧
    thetaHom.ker = Subgroup.zpowers negPair ∧ Nat.card thetaHom.ker = 2 ∧
    thetaHom.ker ≤ Subgroup.center Pvis ∧
    (∀ p : Pvis, quotEquivGvis (QuotientGroup.mk p) =
      MulOpposite.op ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩) ∧
    (∀ r : Q, ((r : GL SpinIdx ℚ), (1 : latticeO)) ∈ Pvis) ∧
    (∀ r : Q, (rhoPair r : GL SpinIdx ℚ × latticeO) = ((r : GL SpinIdx ℚ), 1) ∧
      rhoEquiv r = thetaEquiv (rhoPair r) ∧ rho r = MulOpposite.op (rhoEquiv r) ∧
      rhoEquiv r ∈ Gvis) ∧
    (∀ r r' : Q, rhoEquiv (r * r') = rhoEquiv r' * rhoEquiv r) ∧
    Function.Injective rhoEquiv ∧ Function.Injective rho ∧
    (∀ (r : Q) (A : symMat), rhoEquiv r (A, 0, 0) = (A, 0, 0)) ∧
    (∀ r t : Q, rhoEquiv r (0, Xlift t, 0) = (0, Xlift (r⁻¹ * t * r), 0)) ∧
    (∀ (r : Q) (q : SpinIdx → ℚ) (v : Fin 24 → ℚ), rhoEquiv r (0, 0, tensor q v) =
      (0, 0, tensor (q ᵥ* ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)) v)) ∧
    (∀ f : SpaceB ≃ₗ[ℚ] SpaceB, f ∈ rhoQ ↔ ∃ r : Q, rhoEquiv r = f) ∧ rhoQ ≤ Gvis ∧
    rhoEquiv zQ = xB :=
  ⟨theta_gmul, T_theta, compatible_pair_algebra_action_data⟩

end CFSG.Monster.Visible
