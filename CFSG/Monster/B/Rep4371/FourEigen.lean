module

public import CFSG.Monster.Griess.AxisSpectrum
public import CFSG.Monster.Griess.TrialityBasis

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Griess
  Matrix
open scoped commutatorElement

variable {r : Q}

@[expose] def crossMat (u w : Fin 24 → ℚ) : symMat :=
  ⟨vecMulVec u w + vecMulVec w u, by
    rw [mem_symMat, transpose_add, transpose_vecMulVec, transpose_vecMulVec, add_comm]⟩

theorem coe_crossMat (u w : Fin 24 → ℚ) :
    (crossMat u w : Matrix (Fin 24) (Fin 24) ℚ) = vecMulVec u w + vecMulVec w u := rfl

@[expose] def crossLin (u : Fin 24 → ℚ) : (Fin 24 → ℚ) →ₗ[ℚ] SpaceB where
  toFun w := inA (crossMat u w)
  map_add' w w' := by
    refine Prod.ext (Subtype.ext ?_) (by simp)
    change vecMulVec u (w + w') + vecMulVec (w + w') u =
      (vecMulVec u w + vecMulVec w u) + (vecMulVec u w' + vecMulVec w' u)
    rw [vecMulVec_add, add_vecMulVec]
    abel
  map_smul' c w := by
    refine Prod.ext (Subtype.ext ?_) (by simp)
    change vecMulVec u (c • w) + vecMulVec (c • w) u = c • (vecMulVec u w + vecMulVec w u)
    rw [vecMulVec_smul, smul_vecMulVec, smul_add]

@[expose] def uPerp (u : Fin 24 → ℚ) : Submodule ℚ (Fin 24 → ℚ) where
  carrier := {w | w ⬝ᵥ u = 0}
  add_mem' {w w'} hw hw' := by
    change (w + w') ⬝ᵥ u = 0
    rw [add_dotProduct, show w ⬝ᵥ u = 0 from hw, show w' ⬝ᵥ u = 0 from hw', add_zero]
  zero_mem' := zero_dotProduct u
  smul_mem' c w hw := by
    change (c • w) ⬝ᵥ u = 0
    rw [smul_dotProduct, show w ⬝ᵥ u = 0 from hw, smul_zero]

theorem mem_uPerp {u w : Fin 24 → ℚ} : w ∈ uPerp u ↔ w ⬝ᵥ u = 0 := Iff.rfl

@[expose] noncomputable def Across (hr : IsShortCoord (coordOf r)) : Submodule ℚ SpaceB :=
  (uPerp (uQ (shortCls hr))).map (crossLin (uQ (shortCls hr)))

@[expose] noncomputable def Splus (r : Q) : Submodule ℚ (SpinIdx → ℚ) where
  carrier := {q | q ᵥ* ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = q}
  add_mem' {q q'} hq hq' := by
    change (q + q') ᵥ* _ = q + q'
    rw [add_vecMul, show q ᵥ* _ = q from hq, show q' ᵥ* _ = q' from hq']
  zero_mem' := zero_vecMul _
  smul_mem' c q hq := by
    change (c • q) ᵥ* _ = c • q
    rw [smul_vecMul, show q ᵥ* _ = q from hq]

@[expose] def tensorLin (u : Fin 24 → ℚ) : (SpinIdx → ℚ) →ₗ[ℚ] SpaceB where
  toFun q := inW (tensor q u)
  map_add' q q' := by
    refine Prod.ext (by simp) (Prod.ext (by simp) ?_)
    change vecMulVec (q + q') u = vecMulVec q u + vecMulVec q' u
    rw [add_vecMulVec]
  map_smul' c q := by
    refine Prod.ext (by simp) (Prod.ext (by simp) ?_)
    change vecMulVec (c • q) u = c • vecMulVec q u
    rw [smul_vecMulVec]

@[expose] noncomputable def Tplus (hr : IsShortCoord (coordOf r)) : Submodule ℚ SpaceB :=
  (Splus r).map (tensorLin (uQ (shortCls hr)))

@[expose] def IsPartner (hr : IsShortCoord (coordOf r)) (s : Q) : Prop :=
  ∃ hs : IsShortCoord (coordOf s), coordOf s ≠ coordOf r ∧
    (alphaS (shortCls hr) ⟨coordOf s, hs⟩ = 2 ∨ alphaS (shortCls hr) ⟨coordOf s, hs⟩ = -2)

@[expose] noncomputable def Xdiff (hr : IsShortCoord (coordOf r)) : Submodule ℚ SpaceB :=
  Submodule.span ℚ {v | ∃ s : Q, IsPartner hr s ∧ v = inX (Xlift s - Xlift (r * s))}

@[expose] noncomputable def V4 (r : Q) : Submodule ℚ SpaceB :=
  LinearMap.ker (gmul (axis r) - (4 : ℚ) • LinearMap.id)

theorem mem_V4 {v : SpaceB} : v ∈ V4 r ↔ gmul (axis r) v = (4 : ℚ) • v := by
  rw [V4, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]

theorem vecMulVec_mulVec' (a b c : Fin 24 → ℚ) : vecMulVec a b *ᵥ c = (b ⬝ᵥ c) • a := by
  funext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

@[simp] theorem Am_crossLin (u w : Fin 24 → ℚ) :
    Am (crossLin u w) = vecMulVec u w + vecMulVec w u := rfl

@[simp] theorem xs_crossLin (u w : Fin 24 → ℚ) : xs (crossLin u w) = 0 := rfl

@[simp] theorem Nm_crossLin (u w : Fin 24 → ℚ) : Nm (crossLin u w) = 0 := rfl

section Cross

variable (hr : IsShortCoord (coordOf r))

theorem axisE_mul_cross {w : Fin 24 → ℚ} (hw : w ⬝ᵥ uQ (shortCls hr) = 0) :
    (axisE r : Matrix (Fin 24) (Fin 24) ℚ) *
        (vecMulVec (uQ (shortCls hr)) w + vecMulVec w (uQ (shortCls hr))) +
      (vecMulVec (uQ (shortCls hr)) w + vecMulVec w (uQ (shortCls hr))) *
        (axisE r : Matrix (Fin 24) (Fin 24) ℚ) =
      vecMulVec (uQ (shortCls hr)) w + vecMulVec w (uQ (shortCls hr)) := by
  have hw' : uQ (shortCls hr) ⬝ᵥ w = 0 := by rw [dotProduct_comm]; exact hw
  set u := uQ (shortCls hr)
  have h1 : vecMulVec u u * vecMulVec u w = (32 : ℚ) • vecMulVec u w := by
    rw [vecMulVec_mul_vecMulVec, uQ_dotProduct_uQ_self, vecMulVec_smul]
  have h2 : vecMulVec u u * vecMulVec w u = 0 := by
    rw [vecMulVec_mul_vecMulVec, hw', zero_smul, vecMulVec_zero]
  have h3 : vecMulVec u w * vecMulVec u u = 0 := by
    rw [vecMulVec_mul_vecMulVec, hw, zero_smul, vecMulVec_zero]
  have h4 : vecMulVec w u * vecMulVec u u = (32 : ℚ) • vecMulVec w u := by
    rw [vecMulVec_mul_vecMulVec, uQ_dotProduct_uQ_self, vecMulVec_smul]
  rw [axisE_coe hr, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, h1, h2, h3,
    h4]
  module

theorem qf_cross {w : Fin 24 → ℚ} (hw : w ⬝ᵥ uQ (shortCls hr) = 0) :
    qf (shortCls hr) (vecMulVec (uQ (shortCls hr)) w + vecMulVec w (uQ (shortCls hr))) = 0 := by
  have hw' : uQ (shortCls hr) ⬝ᵥ w = 0 := by rw [dotProduct_comm]; exact hw
  rw [qf, add_mulVec, vecMulVec_mulVec', vecMulVec_mulVec', dotProduct_add, dotProduct_smul,
    dotProduct_smul, hw, hw', smul_eq_mul, smul_eq_mul, mul_zero, zero_mul, add_zero]

theorem gmul_axis_cross {w : Fin 24 → ℚ} (hw : w ⬝ᵥ uQ (shortCls hr) = 0) :
    gmul (axis r) (crossLin (uQ (shortCls hr)) w) =
      (4 : ℚ) • crossLin (uQ (shortCls hr)) w := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (funext fun d => ?_) ?_)
  · rw [axisMul_A hr, Am_crossLin, xs_crossLin, axisE_mul_cross hr hw, Pi.zero_apply, mul_zero,
      zero_smul, sub_zero]
    rfl
  · rw [axisMul_X hr, Am_crossLin, xs_crossLin]
    split_ifs with h
    · subst h
      rw [qf_cross hr hw]
      simp
    · simp
  · rw [axisMul_W hr, Nm_crossLin]
    simp

end Cross

@[simp] theorem Am_tensorLin (u : Fin 24 → ℚ) (q : SpinIdx → ℚ) : Am (tensorLin u q) = 0 := rfl

@[simp] theorem xs_tensorLin (u : Fin 24 → ℚ) (q : SpinIdx → ℚ) : xs (tensorLin u q) = 0 := rfl

@[simp] theorem Nm_tensorLin (u : Fin 24 → ℚ) (q : SpinIdx → ℚ) :
    Nm (tensorLin u q) = vecMulVec q u := rfl

theorem mul_vecMulVec' {m n o : Type*} [Fintype n] (M : Matrix m n ℚ) (a : n → ℚ) (b : o → ℚ) :
    M * vecMulVec a b = vecMulVec (M *ᵥ a) b := by
  ext i j
  simp only [mul_apply, vecMulVec_apply, mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

section Tensor

variable (hr : IsShortCoord (coordOf r))

theorem Rmat_mulVec_of_mem_Splus {q : SpinIdx → ℚ} (hq : q ∈ Splus r) :
    Rmat (shortCls hr) *ᵥ q = sgn (centralCoord r) • q := by
  have hq' : q ᵥ* (sgn (centralCoord r) • Rmat (shortCls hr)) = q := by
    rw [← coe_Q_eq_sgn_smul_Rmat hr]
    exact hq
  rw [← vecMul_transpose, Rmat_symm]
  have hσ := sgn_sq (centralCoord r)
  calc q ᵥ* Rmat (shortCls hr)
      = (sgn (centralCoord r) * sgn (centralCoord r)) • (q ᵥ* Rmat (shortCls hr)) := by
        rw [hσ, one_smul]
    _ = sgn (centralCoord r) • (q ᵥ* (sgn (centralCoord r) • Rmat (shortCls hr))) := by
        rw [vecMul_smul, smul_smul]
    _ = sgn (centralCoord r) • q := by rw [hq']

theorem gmul_axis_tensor {q : SpinIdx → ℚ} (hq : q ∈ Splus r) :
    gmul (axis r) (tensorLin (uQ (shortCls hr)) q) =
      (4 : ℚ) • tensorLin (uQ (shortCls hr)) q := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (funext fun d => ?_) ?_)
  · rw [axisMul_A hr, Am_tensorLin, xs_tensorLin]
    simp
  · rw [axisMul_X hr, Am_tensorLin, xs_tensorLin]
    simp [qf_zero]
  · rw [axisMul_W hr, Nm_tensorLin, mul_vecMulVec', Rmat_mulVec_of_mem_Splus hr hq, axisE_coe hr]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_vecMulVec, vecMulVec_mul_vecMulVec,
      uQ_dotProduct_uQ_self, vecMulVec_smul]
    change _ = (4 : ℚ) • vecMulVec q (uQ (shortCls hr))
    rcases sgn_eq_one_or (centralCoord r) with h | h <;> rw [h] <;> module

end Tensor

section Partner

variable (hr : IsShortCoord (coordOf r))

theorem Xlift_apply_of_short {s : Q} (hs : IsShortCoord (coordOf s)) (d : ShortIdx) :
    Xlift s d = if d = ⟨coordOf s, hs⟩ then sgn (centralCoord s) else 0 := by
  rw [Xlift_eq hs, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem isShortCoord_mul_of_partner {s : Q} (hs : IsPartner hr s) :
    IsShortCoord (coordOf (r * s)) := by
  obtain ⟨hs', hne, hα⟩ := hs
  rw [coordOf_mul]
  have hcd : shortCls hr ≠ ⟨coordOf s, hs'⟩ := fun h => hne (congrArg Subtype.val h).symm
  exact (isShortCoord_add_iff hcd).2 hα

theorem sgn_mul_tau_eq_Xlift {s : Q} (hs : IsPartner hr s) (d : ShortIdx) :
    sgn (centralCoord r) * sgn (centralCoord s) * tau (shortCls hr) ⟨coordOf s, hs.1⟩ d =
      Xlift (r * s) d := by
  rw [Xlift_apply_of_short (isShortCoord_mul_of_partner hr hs), tau]
  by_cases h : d.1 = (shortCls hr).1 + (⟨coordOf s, hs.1⟩ : ShortIdx).1
  · have hd : d = ⟨coordOf (r * s), isShortCoord_mul_of_partner hr hs⟩ :=
      Subtype.ext (h.trans (coordOf_mul r s).symm)
    rw [ite_eq_left h, ite_eq_left hd, centralCoord_mul, sgn_add, sgn_add]
  · have hd : d ≠ ⟨coordOf (r * s), isShortCoord_mul_of_partner hr hs⟩ := fun hd =>
      h ((congrArg Subtype.val hd).trans (coordOf_mul r s))
    rw [ite_eq_right h, ite_eq_right hd, mul_zero]

theorem gmul_axis_Xlift_partner {s : Q} (hs : IsPartner hr s) :
    gmul (axis r) (inX (Xlift s)) = (2 : ℚ) • inX (Xlift s) - (2 : ℚ) • inX (Xlift (r * s)) := by
  obtain ⟨hs', hne, hα⟩ := hs
  have hcs : (⟨coordOf s, hs'⟩ : ShortIdx) ≠ shortCls hr := fun h =>
    hne (congrArg Subtype.val h)
  have hα2 : (alphaS (shortCls hr) ⟨coordOf s, hs'⟩ : ℚ) ^ 2 = 4 := by
    rcases hα with h | h <;> rw [h] <;> norm_num
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (funext fun d => ?_) ?_)
  · rw [axisMul_A hr]
    simp only [Am_inX, xs_inX, Xlift_apply_of_short hs', ite_eq_right (Ne.symm hcs)]
    simp
  · rw [axisMul_X hr]
    simp only [Am_inX, xs_inX, qf_zero, mul_zero, zero_div, ite_self, sub_zero]
    have hsum : ∑ f, Xlift s f * tau (shortCls hr) f d =
        sgn (centralCoord s) * tau (shortCls hr) ⟨coordOf s, hs'⟩ d := by
      rw [Finset.sum_eq_single (⟨coordOf s, hs'⟩ : ShortIdx)]
      · rw [Xlift_apply_of_short hs', ite_eq_left rfl]
      · intro f _ hf
        rw [Xlift_apply_of_short hs', ite_eq_right hf, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsum]
    have hX := sgn_mul_tau_eq_Xlift hr ⟨hs', hne, hα⟩ d
    change _ = 2 * Xlift s d - 2 * Xlift (r * s) d
    rw [← hX, Xlift_apply_of_short hs']
    split_ifs with h
    · subst h
      rw [uQ_dotProduct_uQ, alphaS_comm, mul_pow, hα2]
      ring
    · ring
  · rw [axisMul_W hr]
    simp

end Partner

section PartnerProps

variable (hr : IsShortCoord (coordOf r))

theorem partner_ne_zero {s : Q} (hs : IsPartner hr s) : coordOf s ≠ 0 := by
  intro h
  obtain ⟨hs', -, -⟩ := hs
  exact not_isShortCoord_zero (h ▸ hs')

theorem pair_coordOf_add_eq_alphaS {s : Q} (hs : IsShortCoord (coordOf s)) :
    pair (coordOf r).1 (coordOf s).2 + pair (coordOf s).1 (coordOf r).2 =
      ((alphaS (shortCls hr) ⟨coordOf s, hs⟩ : ℤ) : ZMod 2) := by
  have h1 := bL_phi0 (coordOf r).1 (coordOf s).1 (coordOf r).2 (coordOf s).2
  rw [← classOf_uvec (shortCls hr), ← classOf_uvec ⟨coordOf s, hs⟩] at h1
  rw [← h1, classOf_eq_cls (uvec_mem (shortCls hr)).1, classOf_eq_cls (uvec_mem _).1, bL_cls]
  rfl

theorem mul_comm_of_partner {s : Q} (hs : IsPartner hr s) : r * s = s * r := by
  obtain ⟨hs', -, hα⟩ := hs
  have h0 : pair (coordOf r).1 (coordOf s).2 + pair (coordOf s).1 (coordOf r).2 = 0 := by
    rw [pair_coordOf_add_eq_alphaS hr hs']
    rcases hα with h | h <;> rw [h] <;> decide
  have hx : spinEquiv (spinEquiv.symm r) = r := spinEquiv.apply_symm_apply r
  have hy : spinEquiv (spinEquiv.symm s) = s := spinEquiv.apply_symm_apply s
  have hc : ⁅spinEquiv.symm r, spinEquiv.symm s⁆ = 1 := by
    rw [SpinCoord.commutatorElement_eq]
    exact SpinCoord.ext h0 rfl rfl
  have hc' : ⁅r, s⁆ = 1 := by
    rw [← hx, ← hy, ← map_commutatorElement, hc, map_one]
  exact commutatorElement_eq_one_iff_mul_comm.1 hc'

include hr in
theorem mul_mul_self_left (s : Q) : r * (r * s) = s := by
  rw [← mul_assoc, ← sq, sq_eq_one_of_isShort hr, one_mul]

theorem isPartner_mul {s : Q} (hs : IsPartner hr s) : IsPartner hr (r * s) := by
  have hrs := isShortCoord_mul_of_partner hr hs
  have hs0 := partner_ne_zero hr hs
  obtain ⟨hs', hne, hα⟩ := hs
  have hcd : shortCls hr ≠ ⟨coordOf s, hs'⟩ := fun h => hne (congrArg Subtype.val h).symm
  have hsum : IsShortCoord ((shortCls hr).1 + (⟨coordOf s, hs'⟩ : ShortIdx).1) := by
    rw [← coordOf_mul]
    exact hrs
  have hsq := alphaS_add_sq hcd hsum
  have he : (⟨(shortCls hr).1 + (⟨coordOf s, hs'⟩ : ShortIdx).1, hsum⟩ : ShortIdx) =
      ⟨coordOf (r * s), hrs⟩ := Subtype.ext (coordOf_mul r s).symm
  rw [he] at hsq
  refine ⟨hrs, fun h => hs0 ?_, ?_⟩
  · have h2 : coordOf r + coordOf s = coordOf r + 0 := by
      rw [add_zero, ← coordOf_mul]
      exact h
    exact add_left_cancel h2
  · have h4 : (alphaS (shortCls hr) ⟨coordOf (r * s), hrs⟩ - 2) *
        (alphaS (shortCls hr) ⟨coordOf (r * s), hrs⟩ + 2) = 0 := by nlinarith
    rcases mul_eq_zero.1 h4 with h | h
    · exact .inl (by linarith)
    · exact .inr (by linarith)

end PartnerProps

section WPart

variable (hr : IsShortCoord (coordOf r))

theorem W_part_of_mem_V4 {v : SpaceB} (hv : gmul (axis r) v = (4 : ℚ) • v) :
    ∃ q ∈ Splus r, Nm v = vecMulVec q (uQ (shortCls hr)) := by
  have eqW : (gmul (axis r) v).2.2 = (4 : ℚ) • Nm v := congrArg (fun w : SpaceB => w.2.2) hv
  rw [axisMul_W hr] at eqW
  set N := Nm v with hN
  set E := (axisE r : Matrix (Fin 24) (Fin 24) ℚ) with hEdef
  set R := Rmat (shortCls hr) with hRdef
  have hE2 : E * E = E := axisE_mul_self hr
  have hR2 : R * R = 1 := Rmat_mul_self _
  have eq2 : (4 : ℚ)⁻¹ • (N * E) + (2 : ℚ) • (N * E) - (sgn (centralCoord r) / 4) •
      (R * N * E - (8 : ℚ) • (R * N * E)) = (4 : ℚ) • (N * E) := by
    have h := congrArg (· * E) eqW
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul] at h
    rw [Matrix.mul_assoc N E E, hE2, Matrix.mul_assoc (R * N) E E, hE2] at h
    exact h
  have eq3 : (4 : ℚ)⁻¹ • (R * N) + (2 : ℚ) • (R * N * E) - (sgn (centralCoord r) / 4) •
      (N - (8 : ℚ) • (N * E)) = (4 : ℚ) • (R * N) := by
    have := congrArg (R * ·) eqW
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, hR2,
      Matrix.one_mul] at this
    exact this
  have key : N * E = N ∧ sgn (centralCoord r) • (R * N) = N := by
    rcases sgn_eq_one_or (centralCoord r) with h | h <;> rw [h] at eqW eq2 eq3 ⊢
    · have h1 : R * N = N := by linear_combination (norm := module) (2 / 7 : ℚ) • (eqW - eq3)
      have h2 : R * N * E = N * E := by rw [h1]
      refine ⟨?_, by rw [one_smul, h1]⟩
      linear_combination (norm := module) (1 / 4 : ℚ) • eqW + (1 / 16 : ℚ) • h1 -
        (1 / 2 : ℚ) • h2
    · have h1 : -(R * N) = N := by
        linear_combination (norm := module) (2 / 7 : ℚ) • (eqW + eq3)
      have h2 : -(R * N * E) = N * E := by rw [← Matrix.neg_mul, h1]
      refine ⟨?_, by rw [neg_one_smul, h1]⟩
      linear_combination (norm := module) (1 / 4 : ℚ) • eqW + (1 / 16 : ℚ) • h1 -
        (1 / 2 : ℚ) • h2
  obtain ⟨hNE, hRN⟩ := key
  refine ⟨(32 : ℚ)⁻¹ • (N *ᵥ uQ (shortCls hr)), ?_, ?_⟩
  · set q := (32 : ℚ)⁻¹ • (N *ᵥ uQ (shortCls hr)) with hq
    have hσ := sgn_sq (centralCoord r)
    have hRN' : R * N = sgn (centralCoord r) • N := by
      calc R * N = (sgn (centralCoord r) * sgn (centralCoord r)) • (R * N) := by
            rw [hσ, one_smul]
        _ = sgn (centralCoord r) • (sgn (centralCoord r) • (R * N)) := by rw [smul_smul]
        _ = sgn (centralCoord r) • N := by rw [hRN]
    have hRq : R *ᵥ q = sgn (centralCoord r) • q := by
      rw [hq, mulVec_smul, mulVec_mulVec, hRN', smul_mulVec, smul_comm]
    have hsymm : q ᵥ* R = R *ᵥ q := by
      rw [← vecMul_transpose, hRdef, Rmat_symm]
    change q ᵥ* ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = q
    rw [coe_Q_eq_sgn_smul_Rmat hr, vecMul_smul]
    change sgn (centralCoord r) • (q ᵥ* R) = q
    rw [hsymm, hRq, smul_smul, hσ, one_smul]
  · conv_lhs => rw [← hNE]
    rw [hEdef, axisE_coe hr, Matrix.mul_smul, mul_vecMulVec', smul_vecMulVec]

end WPart

theorem vecMulVec_mul' {m n o : Type*} [Fintype n] (a : m → ℚ) (b : n → ℚ) (M : Matrix n o ℚ) :
    vecMulVec a b * M = vecMulVec a (b ᵥ* M) := by
  ext i j
  simp only [mul_apply, vecMulVec_apply, vecMul, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

section APart

variable (hr : IsShortCoord (coordOf r))

theorem axisE_mulVec (y : Fin 24 → ℚ) :
    (axisE r : Matrix (Fin 24) (Fin 24) ℚ) *ᵥ y =
      ((32 : ℚ)⁻¹ * (uQ (shortCls hr) ⬝ᵥ y)) • uQ (shortCls hr) := by
  rw [axisE_coe hr, smul_mulVec, vecMulVec_mulVec', smul_smul]

theorem A_part_of_mem_V4 {v : SpaceB} (hv : gmul (axis r) v = (4 : ℚ) • v) :
    xs v (shortCls hr) = 0 ∧ ∃ w ∈ uPerp (uQ (shortCls hr)),
      Am v = vecMulVec (uQ (shortCls hr)) w + vecMulVec w (uQ (shortCls hr)) := by
  set u := uQ (shortCls hr) with hu
  set A := Am v with hA
  set σ := sgn (centralCoord r) with hσdef
  have hσ : σ * σ = 1 := sgn_sq _
  have huu : u ⬝ᵥ u = 32 := uQ_dotProduct_uQ_self _
  have eqA : (4 : ℚ) • ((axisE r : Matrix (Fin 24) (Fin 24) ℚ) * A +
      A * (axisE r : Matrix (Fin 24) (Fin 24) ℚ)) -
      (8 * σ * xs v (shortCls hr)) • (axisE r : Matrix (Fin 24) (Fin 24) ℚ) = (4 : ℚ) • A := by
    rw [← axisMul_A hr]
    exact congrArg (fun w : SpaceB => (w.1 : Matrix (Fin 24) (Fin 24) ℚ)) hv
  have eqX : xs v (shortCls hr) * (u ⬝ᵥ u) ^ 2 / 128 - σ * qf (shortCls hr) A / 4 =
      4 * xs v (shortCls hr) := by
    have h : (gmul (axis r) v).2.1 (shortCls hr) = 4 * xs v (shortCls hr) :=
      congrArg (fun w : SpaceB => w.2.1 (shortCls hr)) hv
    rw [axisMul_X hr, ite_eq_left rfl] at h
    have hsum : ∑ f, xs v f * tau (shortCls hr) f (shortCls hr) = 0 :=
      Finset.sum_eq_zero fun f _ => by rw [tau_self_right, mul_zero]
    rw [hsum, mul_zero, sub_zero] at h
    exact h
  rw [huu] at eqX
  have hqf1 : σ * qf (shortCls hr) A = 16 * xs v (shortCls hr) := by linarith
  have hsymA : Aᵀ = A := (v.1).2
  have hEu : (axisE r : Matrix (Fin 24) (Fin 24) ℚ) *ᵥ u = u := by
    rw [axisE_mulVec hr, huu]
    norm_num
    rfl
  have hfun := congrArg (fun M : Matrix (Fin 24) (Fin 24) ℚ => u ⬝ᵥ (M *ᵥ u)) eqA
  simp only [sub_mulVec, smul_mulVec, add_mulVec, ← mulVec_mulVec, hEu, dotProduct_sub,
    dotProduct_smul, dotProduct_add, smul_eq_mul] at hfun
  rw [axisE_mulVec hr, dotProduct_smul, huu, smul_eq_mul] at hfun
  have hqf : qf (shortCls hr) A = u ⬝ᵥ (A *ᵥ u) := rfl
  rw [← hqf] at hfun
  have hqf2 : qf (shortCls hr) A = 64 * σ * xs v (shortCls hr) := by linarith
  have hx0 : xs v (shortCls hr) = 0 := by
    have h1 : 64 * (σ * σ) * xs v (shortCls hr) = 16 * xs v (shortCls hr) := by
      rw [← hqf1, hqf2]
      ring
    rw [hσ] at h1
    linarith
  have hq0 : qf (shortCls hr) A = 0 := by rw [hqf2, hx0, mul_zero]
  refine ⟨hx0, (32 : ℚ)⁻¹ • (A *ᵥ u), ?_, ?_⟩
  · change ((32 : ℚ)⁻¹ • (A *ᵥ u)) ⬝ᵥ u = 0
    rw [smul_dotProduct, dotProduct_comm, ← hqf, hq0, smul_zero]
  · rw [hx0, mul_zero, zero_smul, sub_zero] at eqA
    have eqA' : (axisE r : Matrix (Fin 24) (Fin 24) ℚ) * A +
        A * (axisE r : Matrix (Fin 24) (Fin 24) ℚ) = A := smul_right_injective _
      (by norm_num : (4 : ℚ) ≠ 0) eqA
    have hvm : u ᵥ* A = A *ᵥ u := by rw [← vecMul_transpose, hsymA]
    conv_lhs => rw [← eqA']
    rw [axisE_coe hr, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul', mul_vecMulVec', hvm,
      smul_vecMulVec, vecMulVec_smul]

end APart

section XPart

variable (hr : IsShortCoord (coordOf r))

@[expose] def PartnerCls (d : ShortIdx) : Prop :=
  d ≠ shortCls hr ∧ (alphaS (shortCls hr) d = 2 ∨ alphaS (shortCls hr) d = -2)

theorem isPartner_rep {d : ShortIdx} (hd : PartnerCls hr d) : IsPartner hr (rep d.1) := by
  have he : (⟨coordOf (rep d.1), isShortCoord_rep d⟩ : ShortIdx) = d :=
    Subtype.ext (coordOf_rep d.1)
  refine ⟨isShortCoord_rep d, fun h => hd.1 (Subtype.ext ((coordOf_rep d.1).symm.trans h)), ?_⟩
  rw [he]
  exact hd.2

theorem isShortCoord_add_of_partnerCls {d : ShortIdx} (hd : PartnerCls hr d) :
    IsShortCoord ((shortCls hr).1 + d.1) :=
  (isShortCoord_add_iff (Ne.symm hd.1)).2 hd.2

@[expose] noncomputable def partnerOf {d : ShortIdx} (hd : PartnerCls hr d) : ShortIdx :=
  ⟨(shortCls hr).1 + d.1, isShortCoord_add_of_partnerCls hr hd⟩

theorem tau_eq_zero_of_ne {d e : ShortIdx} (h : e.1 ≠ (shortCls hr).1 + d.1) :
    tau (shortCls hr) d e = 0 := by
  rw [tau, ite_eq_right h]

theorem eqX_of_mem_V4 {v : SpaceB} (hv : gmul (axis r) v = (4 : ℚ) • v) {d : ShortIdx}
    (hd : d ≠ shortCls hr) :
    xs v d * (alphaS (shortCls hr) d : ℚ) ^ 2 / 2 -
      2 * sgn (centralCoord r) * ∑ f, xs v f * tau (shortCls hr) f d = 4 * xs v d := by
  have h : (gmul (axis r) v).2.1 d = 4 * xs v d :=
    congrArg (fun w : SpaceB => w.2.1 d) hv
  rw [axisMul_X hr, ite_eq_right hd, sub_zero, uQ_dotProduct_uQ, alphaS_comm] at h
  rw [← h]
  ring

theorem partnerOf_ne {d : ShortIdx} (hd : PartnerCls hr d) : partnerOf hr hd ≠ shortCls hr := by
  intro h
  have h1 : (shortCls hr).1 + d.1 = (shortCls hr).1 + 0 := by
    rw [add_zero]
    exact congrArg Subtype.val h
  exact not_isShortCoord_zero ((add_left_cancel h1) ▸ d.2)

theorem partnerCls_partnerOf {d : ShortIdx} (hd : PartnerCls hr d) :
    PartnerCls hr (partnerOf hr hd) := by
  refine ⟨partnerOf_ne hr hd, ?_⟩
  have hsq := alphaS_add_sq (Ne.symm hd.1) (isShortCoord_add_of_partnerCls hr hd)
  have h4 : (alphaS (shortCls hr) (partnerOf hr hd) - 2) *
      (alphaS (shortCls hr) (partnerOf hr hd) + 2) = 0 := by
    have : alphaS (shortCls hr) (partnerOf hr hd) ^ 2 = 4 := hsq
    nlinarith
  rcases mul_eq_zero.1 h4 with h | h
  · exact .inl (by linarith)
  · exact .inr (by linarith)

theorem eq_partnerOf_of_tau_ne_zero {d e : ShortIdx} (he : PartnerCls hr e)
    (h : tau (shortCls hr) d e ≠ 0) : d = partnerOf hr he := by
  have h1 : e.1 = (shortCls hr).1 + d.1 := by
    by_contra h'
    exact h (tau_eq_zero_of_ne hr h')
  apply Subtype.ext
  change d.1 = (shortCls hr).1 + e.1
  rw [h1, ← add_assoc, add_self_coord, zero_add]

@[expose] def inXLin : SpaceX →ₗ[ℚ] SpaceB :=
  (LinearMap.inr ℚ symMat (SpaceX × SpaceW)).comp (LinearMap.inl ℚ SpaceX SpaceW)

theorem inXLin_apply (x : SpaceX) : inXLin x = inX x := rfl

theorem Xlift_rep_apply (d e : ShortIdx) : Xlift (rep d.1) e = if e = d then 1 else 0 := by
  rw [Xlift_rep_eq, Pi.single_apply]

theorem Xlift_mul_rep_apply {d : ShortIdx} (hd : PartnerCls hr d) (e : ShortIdx) :
    Xlift (r * rep d.1) e = sgn (centralCoord r) * tau (shortCls hr) d e := by
  have h := sgn_mul_tau_eq_Xlift hr (isPartner_rep hr hd) e
  have he : (⟨coordOf (rep d.1), (isPartner_rep hr hd).1⟩ : ShortIdx) = d :=
    Subtype.ext (coordOf_rep d.1)
  rw [he, centralCoord_rep, sgn_zero, mul_one] at h
  exact h.symm

theorem X_part_of_mem_V4 {v : SpaceB} (hv : gmul (axis r) v = (4 : ℚ) • v)
    (hx0 : xs v (shortCls hr) = 0) : inX (xs v) ∈ Xdiff hr := by
  classical
  set x := xs v with hxdef
  set σ := sgn (centralCoord r) with hσdef
  have hσ : σ * σ = 1 := sgn_sq _
  have hsum_partner : ∀ {d : ShortIdx} (hd : PartnerCls hr d),
      ∑ f, x f * tau (shortCls hr) f d = x (partnerOf hr hd) * tau (shortCls hr) (partnerOf hr hd) d := by
    intro d hd
    rw [Finset.sum_eq_single (partnerOf hr hd)]
    · intro f _ hf
      rw [tau_eq_zero_of_ne hr, mul_zero]
      intro h
      apply hf
      apply Subtype.ext
      change f.1 = (shortCls hr).1 + d.1
      rw [h, ← add_assoc, add_self_coord, zero_add]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hsum_non : ∀ {d : ShortIdx}, d ≠ shortCls hr → ¬ PartnerCls hr d →
      ∑ f, x f * tau (shortCls hr) f d = 0 := by
    intro d hd hnp
    refine Finset.sum_eq_zero fun f _ => ?_
    rw [tau_eq_zero_of_ne hr, mul_zero]
    intro h
    apply hnp
    refine ⟨hd, (isShortCoord_add_iff (Ne.symm hd)).1 ?_⟩
    have : (shortCls hr).1 + d.1 = f.1 := by rw [h, ← add_assoc, add_self_coord, zero_add]
    rw [this]
    exact f.2
  have hx_non : ∀ {d : ShortIdx}, ¬ PartnerCls hr d → x d = 0 := by
    intro d hnp
    by_cases hd : d = shortCls hr
    · rw [hd]
      exact hx0
    have e := eqX_of_mem_V4 hr hv hd
    rw [hsum_non hd hnp, mul_zero, sub_zero] at e
    have hα := alphaS_mem (Ne.symm hd)
    have hα' : (alphaS (shortCls hr) d : ℚ) ^ 2 ≤ 1 := by
      rcases hα with h | h | h | h | h
      · exact absurd ⟨hd, .inr h⟩ hnp
      · rw [h]; norm_num
      · rw [h]; norm_num
      · rw [h]; norm_num
      · exact absurd ⟨hd, .inl h⟩ hnp
    nlinarith [sq_nonneg (x d)]
  have hx_partner : ∀ {d : ShortIdx} (hd : PartnerCls hr d),
      σ * (x (partnerOf hr hd) * tau (shortCls hr) (partnerOf hr hd) d) = -x d := by
    intro d hd
    have e := eqX_of_mem_V4 hr hv hd.1
    rw [hsum_partner hd] at e
    have hα2 : (alphaS (shortCls hr) d : ℚ) ^ 2 = 4 := by
      rcases hd.2 with h | h <;> rw [h] <;> norm_num
    rw [hα2] at e
    linarith
  let coef : ShortIdx → ℚ := fun d => if PartnerCls hr d then x d / 2 else 0
  have hcoef : ∀ d, coef d = if PartnerCls hr d then x d / 2 else 0 := fun d => rfl
  have hcomb : x = ∑ d, coef d • (Xlift (rep d.1) - Xlift (r * rep d.1)) := by
    funext e
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    have h1 : ∑ d, coef d * Xlift (rep d.1) e = coef e := by
      rw [Finset.sum_eq_single e]
      · rw [Xlift_rep_apply, ite_eq_left rfl, mul_one]
      · intro d _ hd
        rw [Xlift_rep_apply, ite_eq_right (Ne.symm hd), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have h2 : ∀ d, coef d * Xlift (r * rep d.1) e =
        if PartnerCls hr d then x d / 2 * (σ * tau (shortCls hr) d e) else 0 := by
      intro d
      by_cases hd : PartnerCls hr d
      · rw [hcoef, ite_eq_left hd, ite_eq_left hd, Xlift_mul_rep_apply hr hd]
      · rw [hcoef, ite_eq_right hd, ite_eq_right hd, zero_mul]
    rw [h1, Finset.sum_congr rfl fun d _ => h2 d]
    by_cases he : PartnerCls hr e
    · rw [Finset.sum_eq_single (partnerOf hr he)]
      · rw [ite_eq_left (partnerCls_partnerOf hr he), hcoef, ite_eq_left he]
        have := hx_partner he
        linear_combination (1 / 2 : ℚ) * this
      · intro d _ hd
        split_ifs with hdp
        · have ht : tau (shortCls hr) d e = 0 := by
            by_contra ht
            exact hd (eq_partnerOf_of_tau_ne_zero hr he ht)
          rw [ht, mul_zero, mul_zero]
        · rfl
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [hcoef, ite_eq_right he, hx_non he, zero_sub, zero_eq_neg]
      refine Finset.sum_eq_zero fun d _ => ?_
      split_ifs with hdp
      · have ht : tau (shortCls hr) d e = 0 := by
          by_contra ht
          apply he
          have h1 : e.1 = (shortCls hr).1 + d.1 := by
            by_contra h'
            exact ht (tau_eq_zero_of_ne hr h')
          have : e = partnerOf hr hdp := Subtype.ext h1
          rw [this]
          exact partnerCls_partnerOf hr hdp
        rw [ht, mul_zero, mul_zero]
      · rfl
  rw [← inXLin_apply, hcomb, map_sum]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [map_smul]
  by_cases hd : PartnerCls hr d
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨rep d.1, isPartner_rep hr hd, rfl⟩)
  · rw [hcoef, ite_eq_right hd, zero_smul]
    exact Submodule.zero_mem _

end XPart

section Main

variable (hr : IsShortCoord (coordOf r))

@[expose] noncomputable def xdiffVec (r s : Q) : SpaceB := inX (Xlift s - Xlift (r * s))

theorem Across_le_V4 : Across hr ≤ V4 r := by
  rintro _ ⟨w, hw, rfl⟩
  exact mem_V4.2 (gmul_axis_cross hr hw)

theorem Tplus_le_V4 : Tplus hr ≤ V4 r := by
  rintro _ ⟨q, hq, rfl⟩
  exact mem_V4.2 (gmul_axis_tensor hr hq)

theorem gmul_axis_Xlift_mul_partner {s : Q} (hs : IsPartner hr s) :
    gmul (axis r) (inX (Xlift (r * s))) =
      (-2 : ℚ) • inX (Xlift s) + (2 : ℚ) • inX (Xlift (r * s)) := by
  rw [gmul_axis_Xlift_partner hr (isPartner_mul hr hs), mul_mul_self_left hr]
  module

theorem gmul_axis_xdiffVec {s : Q} (hs : IsPartner hr s) :
    gmul (axis r) (xdiffVec r s) = (4 : ℚ) • xdiffVec r s := by
  rw [xdiffVec, ← inXLin_apply, map_sub, inXLin_apply, inXLin_apply, map_sub,
    gmul_axis_Xlift_partner hr hs, gmul_axis_Xlift_mul_partner hr hs]
  module

theorem xdiffVec_mem {s : Q} (hs : IsPartner hr s) : xdiffVec r s ∈ Xdiff hr :=
  Submodule.subset_span ⟨s, hs, rfl⟩

theorem Xdiff_le_V4 : Xdiff hr ≤ V4 r := by
  rw [Xdiff, Submodule.span_le]
  rintro _ ⟨s, hs, rfl⟩
  exact mem_V4.2 (gmul_axis_xdiffVec hr hs)

theorem Xdiff_le_range : Xdiff hr ≤ LinearMap.range inXLin := by
  rw [Xdiff, Submodule.span_le]
  rintro _ ⟨s, -, rfl⟩
  exact ⟨_, rfl⟩

theorem V4_le_sup : V4 r ≤ Across hr ⊔ Xdiff hr ⊔ Tplus hr := by
  intro v hv
  rw [mem_V4] at hv
  obtain ⟨hx0, w, hw, hA⟩ := A_part_of_mem_V4 hr hv
  obtain ⟨q, hq, hN⟩ := W_part_of_mem_V4 hr hv
  have hX := X_part_of_mem_V4 hr hv hx0
  have hv' : v = crossLin (uQ (shortCls hr)) w + inX (xs v) +
      tensorLin (uQ (shortCls hr)) q := by
    refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
    · change Am v = vecMulVec (uQ (shortCls hr)) w + vecMulVec w (uQ (shortCls hr)) + 0 + 0
      rw [hA, add_zero, add_zero]
    · change xs v = 0 + xs v + 0
      rw [zero_add, add_zero]
    · change Nm v = 0 + 0 + vecMulVec q (uQ (shortCls hr))
      rw [hN, zero_add, zero_add]
  rw [hv']
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left ⟨w, hw, rfl⟩)
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right hX)
  · exact Submodule.mem_sup_right ⟨q, hq, rfl⟩

theorem V4_eq_sup : V4 r = Across hr ⊔ Xdiff hr ⊔ Tplus hr :=
  le_antisymm (V4_le_sup hr)
    (sup_le (sup_le (Across_le_V4 hr) (Xdiff_le_V4 hr)) (Tplus_le_V4 hr))

theorem bform_eq_zero_of_blocks {u v : SpaceB} (h1 : Am u = 0 ∨ Am v = 0)
    (h2 : xs u = 0 ∨ xs v = 0) (h3 : Nm u = 0 ∨ Nm v = 0) : bform u v = 0 := by
  rw [bform_apply]
  have e1 : trace ((u.1 : Matrix (Fin 24) (Fin 24) ℚ) * (v.1 : Matrix (Fin 24) (Fin 24) ℚ)) =
      0 := by
    rcases h1 with h | h
    · rw [show (u.1 : Matrix (Fin 24) (Fin 24) ℚ) = 0 from h, Matrix.zero_mul, trace_zero]
    · rw [show (v.1 : Matrix (Fin 24) (Fin 24) ℚ) = 0 from h, Matrix.mul_zero, trace_zero]
  have e2 : ∑ c, u.2.1 c * v.2.1 c = 0 := by
    rcases h2 with h | h
    · simp [show u.2.1 = 0 from h]
    · simp [show v.2.1 = 0 from h]
  have e3 : ∑ j, ∑ i, u.2.2 j i * v.2.2 j i = 0 := by
    rcases h3 with h | h
    · simp [show u.2.2 = 0 from h]
    · simp [show v.2.2 = 0 from h]
  rw [e1, e2, e3, add_zero, add_zero]

theorem bform_Across_Xdiff {x y : SpaceB} (hx : x ∈ Across hr) (hy : y ∈ Xdiff hr) :
    bform x y = 0 := by
  obtain ⟨w, -, rfl⟩ := hx
  obtain ⟨z, rfl⟩ := Xdiff_le_range hr hy
  exact bform_eq_zero_of_blocks (.inr rfl) (.inl rfl) (.inl rfl)

theorem bform_Across_Tplus {x y : SpaceB} (hx : x ∈ Across hr) (hy : y ∈ Tplus hr) :
    bform x y = 0 := by
  obtain ⟨w, -, rfl⟩ := hx
  obtain ⟨q, -, rfl⟩ := hy
  exact bform_eq_zero_of_blocks (.inr rfl) (.inl rfl) (.inl rfl)

theorem bform_Xdiff_Tplus {x y : SpaceB} (hx : x ∈ Xdiff hr) (hy : y ∈ Tplus hr) :
    bform x y = 0 := by
  obtain ⟨z, rfl⟩ := Xdiff_le_range hr hx
  obtain ⟨q, -, rfl⟩ := hy
  exact bform_eq_zero_of_blocks (.inl rfl) (.inr rfl) (.inl rfl)

theorem eq_zero_of_bform_self {v : SpaceB} (h : bform v v = 0) : v = 0 := by
  by_contra hv
  exact (bform_self_pos hv).ne' h

theorem disjoint_Across_Xdiff : Disjoint (Across hr) (Xdiff hr) := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  exact eq_zero_of_bform_self (bform_Across_Xdiff hr hx hy)

theorem disjoint_sup_Tplus : Disjoint (Across hr ⊔ Xdiff hr) (Tplus hr) := by
  rw [Submodule.disjoint_def]
  intro x hx hT
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  apply eq_zero_of_bform_self
  rw [LinearMap.map_add₂, bform_Across_Tplus hr hy hT, bform_Xdiff_Tplus hr hz hT, add_zero]

include hr in
theorem coordOf_mul_ne (s : Q) : coordOf (r * s) ≠ coordOf s := by
  intro h
  have h1 : coordOf r + coordOf s = 0 + coordOf s := by rw [zero_add, ← coordOf_mul, h]
  exact not_isShortCoord_zero ((add_right_cancel h1) ▸ hr)

theorem partnerCls_of_isPartner {s : Q} (hs : IsPartner hr s) :
    PartnerCls hr ⟨coordOf s, hs.1⟩ :=
  ⟨fun h => hs.2.1 (congrArg Subtype.val h), hs.2.2⟩

theorem xdiff_coord {s : Q} (hs : IsPartner hr s) (e : ShortIdx) :
    (Xlift s - Xlift (r * s)) e = sgn (centralCoord s) *
      ((if e = ⟨coordOf s, hs.1⟩ then 1 else 0) -
        sgn (centralCoord r) * tau (shortCls hr) ⟨coordOf s, hs.1⟩ e) := by
  rw [Pi.sub_apply, Xlift_apply_of_short hs.1, ← sgn_mul_tau_eq_Xlift hr hs]
  split_ifs <;> ring

theorem xdiffVec_eq_smul {s s' : Q} (hs : IsPartner hr s) (hs' : IsPartner hr s')
    (h : coordOf s' = coordOf s) :
    xdiffVec r s' = (sgn (centralCoord s') * sgn (centralCoord s)) • xdiffVec r s := by
  have hx : Xlift s' - Xlift (r * s') =
      (sgn (centralCoord s') * sgn (centralCoord s)) • (Xlift s - Xlift (r * s)) := by
    funext e
    have hc : (⟨coordOf s', hs'.1⟩ : ShortIdx) = ⟨coordOf s, hs.1⟩ := Subtype.ext h
    have e1 := xdiff_coord hr hs e
    have e2 := xdiff_coord hr hs' e
    rw [hc] at e2
    rw [Pi.smul_apply, smul_eq_mul, e1, e2]
    have hσ := sgn_sq (centralCoord s)
    set K := (if e = (⟨coordOf s, hs.1⟩ : ShortIdx) then (1 : ℚ) else 0) -
      sgn (centralCoord r) * tau (shortCls hr) ⟨coordOf s, hs.1⟩ e
    linear_combination (-(sgn (centralCoord s') * K)) * hσ
  rw [xdiffVec, xdiffVec, hx, ← inXLin_apply, ← inXLin_apply, map_smul]

include hr in
theorem xdiffVec_mul (s : Q) : xdiffVec r (r * s) = -xdiffVec r s := by
  rw [xdiffVec, xdiffVec, mul_mul_self_left hr, ← neg_sub, ← inXLin_apply, ← inXLin_apply,
    map_neg]

theorem xdiff_apply_eq_zero {s : Q} (hs : IsPartner hr s) {e : ShortIdx}
    (h1 : e.1 ≠ coordOf s) (h2 : e.1 ≠ coordOf (r * s)) : (Xlift s - Xlift (r * s)) e = 0 := by
  rw [Pi.sub_apply, Xlift_apply_of_short hs.1,
    Xlift_apply_of_short (isShortCoord_mul_of_partner hr hs),
    ite_eq_right (fun h => h1 (congrArg Subtype.val h)),
    ite_eq_right (fun h => h2 (congrArg Subtype.val h)), sub_zero]

theorem bform_inX_inX' (x y : SpaceX) : bform (inX x) (inX y) = x ⬝ᵥ y := by
  rw [bform_mk]
  simp

theorem bform_xdiffVec_self_ne_zero {s : Q} (hs : IsPartner hr s) :
    bform (xdiffVec r s) (xdiffVec r s) ≠ 0 := by
  apply ne_of_gt
  apply bform_self_pos
  intro h0
  have h1 : (Xlift s - Xlift (r * s)) ⟨coordOf s, hs.1⟩ = 0 :=
    congrArg (fun v : SpaceB => v.2.1 ⟨coordOf s, hs.1⟩) h0
  have hne : (⟨coordOf s, hs.1⟩ : ShortIdx) ≠
      ⟨coordOf (r * s), isShortCoord_mul_of_partner hr hs⟩ := fun h =>
    coordOf_mul_ne hr s (congrArg Subtype.val h).symm
  rw [Pi.sub_apply, Xlift_apply_of_short hs.1, ite_eq_left rfl,
    Xlift_apply_of_short (isShortCoord_mul_of_partner hr hs), ite_eq_right hne, sub_zero] at h1
  rcases sgn_eq_one_or (centralCoord s) with h | h <;> rw [h] at h1 <;> norm_num at h1

theorem xdiff_representatives {ι : Type*} (s : ι → Q) (hs : ∀ i, IsPartner hr (s i))
    (huniq : ∀ d : ShortIdx, PartnerCls hr d →
      ∃! i, coordOf (s i) = d.1 ∨ coordOf (r * s i) = d.1) :
    LinearIndependent ℚ (fun i => xdiffVec r (s i)) ∧
    Submodule.span ℚ (Set.range fun i => xdiffVec r (s i)) = Xdiff hr ∧
    Pairwise fun i j => bform (xdiffVec r (s i)) (xdiffVec r (s j)) = 0 := by
  have hidx : ∀ i j (e : ShortIdx), (e.1 = coordOf (s i) ∨ e.1 = coordOf (r * s i)) →
      (e.1 = coordOf (s j) ∨ e.1 = coordOf (r * s j)) → i = j := by
    intro i j e hi hj
    have hpe : PartnerCls hr e := by
      rcases hi with h | h
      · have hp := partnerCls_of_isPartner hr (hs i)
        rwa [show (⟨coordOf (s i), (hs i).1⟩ : ShortIdx) = e from Subtype.ext h.symm] at hp
      · have hp := partnerCls_of_isPartner hr (isPartner_mul hr (hs i))
        rwa [show (⟨coordOf (r * s i), (isPartner_mul hr (hs i)).1⟩ : ShortIdx) = e from
          Subtype.ext h.symm] at hp
    obtain ⟨k, -, hk⟩ := huniq e hpe
    rw [hk i (hi.imp Eq.symm Eq.symm), hk j (hj.imp Eq.symm Eq.symm)]
  have horth : Pairwise fun i j => bform (xdiffVec r (s i)) (xdiffVec r (s j)) = 0 := by
    intro i j hij
    rw [xdiffVec, xdiffVec, bform_inX_inX', dotProduct]
    refine Finset.sum_eq_zero fun e _ => ?_
    by_cases hi : e.1 = coordOf (s i) ∨ e.1 = coordOf (r * s i)
    · by_cases hj : e.1 = coordOf (s j) ∨ e.1 = coordOf (r * s j)
      · exact absurd (hidx i j e hi hj) hij
      · push Not at hj
        rw [xdiff_apply_eq_zero hr (hs j) hj.1 hj.2, mul_zero]
    · push Not at hi
      rw [xdiff_apply_eq_zero hr (hs i) hi.1 hi.2, zero_mul]
  have hspan : Submodule.span ℚ (Set.range fun i => xdiffVec r (s i)) = Xdiff hr := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact xdiffVec_mem hr (hs i)
    · rw [Xdiff, Submodule.span_le]
      rintro _ ⟨t, ht, rfl⟩
      obtain ⟨i, hi, -⟩ := huniq ⟨coordOf t, ht.1⟩ (partnerCls_of_isPartner hr ht)
      have hmem : xdiffVec r (s i) ∈ Submodule.span ℚ (Set.range fun i => xdiffVec r (s i)) :=
        Submodule.subset_span ⟨i, rfl⟩
      change xdiffVec r t ∈ _
      rcases hi with h | h
      · rw [xdiffVec_eq_smul hr (hs i) ht h.symm]
        exact Submodule.smul_mem _ _ hmem
      · rw [xdiffVec_eq_smul hr (isPartner_mul hr (hs i)) ht h.symm, xdiffVec_mul hr, smul_neg]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hmem)
  exact ⟨LinearMap.BilinForm.linearIndependent_of_iIsOrtho horth
    (fun i => bform_xdiffVec_self_ne_zero hr (hs i)), hspan, horth⟩

end Main

theorem short_axis_four_eigenspace_summands (hr : IsShortCoord (coordOf r)) :
    V4 r = Across hr ⊔ Xdiff hr ⊔ Tplus hr ∧
    (∀ x ∈ Across hr, ∀ y ∈ Xdiff hr, bform x y = 0) ∧
    (∀ x ∈ Across hr, ∀ y ∈ Tplus hr, bform x y = 0) ∧
    (∀ x ∈ Xdiff hr, ∀ y ∈ Tplus hr, bform x y = 0) ∧
    Disjoint (Across hr) (Xdiff hr) ∧ Disjoint (Across hr ⊔ Xdiff hr) (Tplus hr) ∧
    (∀ s : Q, IsPartner hr s →
      r * s = s * r ∧ IsShortCoord (coordOf (r * s)) ∧ IsPartner hr (r * s) ∧
      coordOf (r * s) ≠ coordOf s ∧
      gmul (axis r) (inX (Xlift s)) = (2 : ℚ) • inX (Xlift s) + (-2 : ℚ) • inX (Xlift (r * s)) ∧
      gmul (axis r) (inX (Xlift (r * s))) =
        (-2 : ℚ) • inX (Xlift s) + (2 : ℚ) • inX (Xlift (r * s))) ∧
    (∀ (ι : Type) (s : ι → Q), (∀ i, IsPartner hr (s i)) →
      (∀ d : ShortIdx, PartnerCls hr d →
        ∃! i, coordOf (s i) = d.1 ∨ coordOf (r * s i) = d.1) →
      LinearIndependent ℚ (fun i => xdiffVec r (s i)) ∧
      Submodule.span ℚ (Set.range fun i => xdiffVec r (s i)) = Xdiff hr ∧
      Pairwise fun i j => bform (xdiffVec r (s i)) (xdiffVec r (s j)) = 0) := by
  refine ⟨V4_eq_sup hr, fun x hx y hy => bform_Across_Xdiff hr hx hy,
    fun x hx y hy => bform_Across_Tplus hr hx hy, fun x hx y hy => bform_Xdiff_Tplus hr hx hy,
    disjoint_Across_Xdiff hr, disjoint_sup_Tplus hr, fun s hs => ?_,
    fun ι s hs huniq => xdiff_representatives hr s hs huniq⟩
  refine ⟨mul_comm_of_partner hr hs, isShortCoord_mul_of_partner hr hs, isPartner_mul hr hs,
    coordOf_mul_ne hr s, ?_, gmul_axis_Xlift_mul_partner hr hs⟩
  rw [gmul_axis_Xlift_partner hr hs]
  module

end CFSG.Monster.B
