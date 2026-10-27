module

public import CFSG.Monster.Griess.Space
public import CFSG.Monster.ScalarKernel

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.ScalarKernel Matrix

theorem image_conj_eq_Q_iff (s : GL SpinIdx ℚ) :
    (fun r => s⁻¹ * r * s) '' (Q : Set (GL SpinIdx ℚ)) = Q ↔
      ∀ r : GL SpinIdx ℚ, r ∈ Q ↔ s⁻¹ * r * s ∈ Q := by
  constructor
  · intro h r
    constructor
    · intro hr
      have : s⁻¹ * r * s ∈ (fun r => s⁻¹ * r * s) '' (Q : Set (GL SpinIdx ℚ)) := ⟨r, hr, rfl⟩
      rw [h] at this
      exact this
    · intro hr
      have hr' : s⁻¹ * r * s ∈ (fun r => s⁻¹ * r * s) '' (Q : Set (GL SpinIdx ℚ)) := by
        rw [h]
        exact hr
      obtain ⟨r₀, hr₀, he⟩ := hr'
      have : r₀ = r := by simpa using he
      exact this ▸ hr₀
  · intro h
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact (h r).1 hr
    · intro hx
      refine ⟨s * x * s⁻¹, (h _).2 ?_, ?_⟩
      · simpa [mul_assoc] using hx
      · simp [mul_assoc]

@[expose] def IsDyadicSpinNormalizer (s : GL SpinIdx ℚ) : Prop :=
  (s : Matrix SpinIdx SpinIdx ℚ) ∈ orthogonalGroup SpinIdx ℚ ∧
    (∀ i j, (s : Matrix SpinIdx SpinIdx ℚ) i j ∈ dyadic) ∧
    (fun r => s⁻¹ * r * s) '' (Q : Set (GL SpinIdx ℚ)) = Q

@[expose] def IsCompatible (s : GL SpinIdx ℚ) (g : latticeO) : Prop :=
  ∀ r r' : Q, (r' : GL SpinIdx ℚ) = s⁻¹ * r * s →
    Multiplicative.toAdd (phi (QuotientGroup.mk r')) =
      modTwoEnd g (Multiplicative.toAdd (phi (QuotientGroup.mk r)))

namespace IsDyadicSpinNormalizer

variable {s t : GL SpinIdx ℚ}

theorem mul_transpose (hs : IsDyadicSpinNormalizer s) :
    (s : Matrix SpinIdx SpinIdx ℚ) * (s : Matrix SpinIdx SpinIdx ℚ)ᵀ = 1 :=
  (mem_orthogonalGroup_iff _ _).1 hs.1

theorem transpose_mul (hs : IsDyadicSpinNormalizer s) :
    (s : Matrix SpinIdx SpinIdx ℚ)ᵀ * (s : Matrix SpinIdx SpinIdx ℚ) = 1 :=
  (mem_orthogonalGroup_iff' _ _).1 hs.1

theorem coe_inv (hs : IsDyadicSpinNormalizer s) :
    ((s⁻¹ : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = (s : Matrix SpinIdx SpinIdx ℚ)ᵀ :=
  Units.inv_eq_of_mul_eq_one_right hs.mul_transpose

theorem mem_Q_iff (hs : IsDyadicSpinNormalizer s) (r : GL SpinIdx ℚ) :
    r ∈ Q ↔ s⁻¹ * r * s ∈ Q :=
  (image_conj_eq_Q_iff s).1 hs.2.2 r

theorem one : IsDyadicSpinNormalizer 1 := by
  refine ⟨one_mem _, fun i j => ?_, (image_conj_eq_Q_iff 1).2 fun r => by simp⟩
  rw [Units.val_one, one_apply]
  split_ifs
  · exact dyadic.one_mem
  · exact dyadic.zero_mem

theorem mul (hs : IsDyadicSpinNormalizer s) (ht : IsDyadicSpinNormalizer t) :
    IsDyadicSpinNormalizer (s * t) := by
  refine ⟨?_, fun i j => ?_, (image_conj_eq_Q_iff _).2 fun r => ?_⟩
  · rw [Units.val_mul]
    exact mul_mem hs.1 ht.1
  · rw [Units.val_mul, mul_apply]
    exact dyadic.sum_mem fun k _ => dyadic.mul_mem (hs.2.1 i k) (ht.2.1 k j)
  · rw [hs.mem_Q_iff, ht.mem_Q_iff]
    simp only [_root_.mul_inv_rev, mul_assoc]

theorem inv (hs : IsDyadicSpinNormalizer s) : IsDyadicSpinNormalizer s⁻¹ := by
  refine ⟨?_, fun i j => ?_, (image_conj_eq_Q_iff _).2 fun r => ?_⟩
  · rw [hs.coe_inv, mem_orthogonalGroup_iff, transpose_transpose]
    exact hs.transpose_mul
  · rw [hs.coe_inv, transpose_apply]
    exact hs.2.1 j i
  · rw [hs.mem_Q_iff (s⁻¹⁻¹ * r * s⁻¹)]
    simp only [inv_inv, mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left]

end IsDyadicSpinNormalizer

namespace IsCompatible

variable {s t : GL SpinIdx ℚ} {g k : latticeO}

theorem modTwoEnd_mul_apply (g k : latticeO) (x : L2) :
    modTwoEnd (g * k) x = modTwoEnd k (modTwoEnd g x) :=
  LinearMap.congr_fun (modTwoEnd_mul g k) x

theorem one : IsCompatible 1 1 := by
  intro r r' h
  have hr : r' = r := Subtype.ext (by rw [h, inv_one, one_mul, mul_one])
  exact (congrArg (fun x : Q => Multiplicative.toAdd (phi (QuotientGroup.mk x))) hr).trans
    (LinearMap.congr_fun modTwoEnd_one _).symm

theorem mul (hs : IsDyadicSpinNormalizer s) (hsg : IsCompatible s g) (htk : IsCompatible t k) :
    IsCompatible (s * t) (g * k) := by
  intro r r'' h
  let r' : Q := ⟨s⁻¹ * r * s, (hs.mem_Q_iff r).1 r.2⟩
  have h1 := hsg r r' rfl
  have h2 := htk r' r'' (by rw [h]; simp only [r', _root_.mul_inv_rev, mul_assoc])
  exact h2.trans ((congrArg (modTwoEnd k) h1).trans (modTwoEnd_mul_apply g k _).symm)

theorem inv (hsg : IsCompatible s g) : IsCompatible s⁻¹ g⁻¹ := by
  intro r r' h
  have h1 := hsg r' r (by rw [h]; simp only [inv_inv, mul_assoc, inv_mul_cancel_left,
    inv_mul_cancel, mul_one])
  have h2 : modTwoEnd g⁻¹ (modTwoEnd g (Multiplicative.toAdd (phi (QuotientGroup.mk r')))) =
      Multiplicative.toAdd (phi (QuotientGroup.mk r')) :=
    (modTwoEnd_mul_apply g g⁻¹ _).symm.trans
      ((LinearMap.congr_fun (congrArg modTwoEnd (mul_inv_cancel g)) _).trans
        (LinearMap.congr_fun modTwoEnd_one _))
  exact h2.symm.trans (congrArg (modTwoEnd g⁻¹) h1.symm)

end IsCompatible

@[expose] def Pvis : Subgroup (GL SpinIdx ℚ × latticeO) where
  carrier := {p | IsDyadicSpinNormalizer p.1 ∧ IsCompatible p.1 p.2}
  one_mem' := ⟨IsDyadicSpinNormalizer.one, IsCompatible.one⟩
  mul_mem' := fun hp hq => ⟨hp.1.mul hq.1, IsCompatible.mul hp.1 hp.2 hq.2⟩
  inv_mem' := fun hp => ⟨hp.1.inv, hp.2.inv⟩

theorem mem_Pvis {p : GL SpinIdx ℚ × latticeO} :
    p ∈ Pvis ↔ IsDyadicSpinNormalizer p.1 ∧ IsCompatible p.1 p.2 := Iff.rfl

theorem isDyadicSpinNormalizer (p : Pvis) : IsDyadicSpinNormalizer p.1.1 := p.2.1

theorem isCompatible (p : Pvis) : IsCompatible p.1.1 p.1.2 := p.2.2

@[expose] def conjQOf (s : GL SpinIdx ℚ) (hs : ∀ r : GL SpinIdx ℚ, r ∈ Q ↔ s⁻¹ * r * s ∈ Q) :
    Q ≃* Q where
  toFun r := ⟨s⁻¹ * r * s, (hs r).1 r.2⟩
  invFun r := ⟨s * r * s⁻¹, (hs _).2 (by
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using r.2)⟩
  left_inv r := Subtype.ext (by simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel,
    mul_one])
  right_inv r := Subtype.ext (by simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel,
    mul_one])
  map_mul' r r' := Subtype.ext (by
    simp only [Subgroup.coe_mul, mul_assoc, mul_inv_cancel_left])

theorem coe_conjQOf (s : GL SpinIdx ℚ) (hs : ∀ r : GL SpinIdx ℚ, r ∈ Q ↔ s⁻¹ * r * s ∈ Q)
    (r : Q) : (conjQOf s hs r : GL SpinIdx ℚ) = s⁻¹ * r * s := rfl

@[expose] def conjQ (p : Pvis) : Q ≃* Q :=
  conjQOf p.1.1 (isDyadicSpinNormalizer p).mem_Q_iff

theorem coe_conjQ (p : Pvis) (r : Q) :
    (conjQ p r : GL SpinIdx ℚ) = p.1.1⁻¹ * r * p.1.1 := rfl

theorem phi_conjQ (p : Pvis) (r : Q) :
    Multiplicative.toAdd (phi (QuotientGroup.mk (conjQ p r))) =
      modTwoEnd p.1.2 (Multiplicative.toAdd (phi (QuotientGroup.mk r))) :=
  isCompatible p r (conjQ p r) rfl

theorem conjQ_one (r : Q) : conjQ 1 r = r :=
  Subtype.ext (by
    show (1 : GL SpinIdx ℚ)⁻¹ * r * 1 = r
    rw [inv_one, one_mul, mul_one])

theorem conjQ_mul (p q : Pvis) (r : Q) : conjQ (p * q) r = conjQ q (conjQ p r) :=
  Subtype.ext (by
    show (p.1.1 * q.1.1)⁻¹ * r * (p.1.1 * q.1.1) = q.1.1⁻¹ * (p.1.1⁻¹ * r * p.1.1) * q.1.1
    simp only [_root_.mul_inv_rev, mul_assoc])

theorem conj_zU (s : GL SpinIdx ℚ) : s⁻¹ * zU * s = zU := by
  rw [zU, mul_neg_one, neg_mul, inv_mul_cancel]

theorem conjQ_zQ (p : Pvis) : conjQ p zQ = zQ :=
  Subtype.ext (by
    show p.1.1⁻¹ * (zQ : GL SpinIdx ℚ) * p.1.1 = zQ
    rw [coe_zQ, conj_zU])

theorem conjQ_zQ_pow_mul (p : Pvis) (n : ℕ) (r : Q) :
    conjQ p (zQ ^ n * r) = zQ ^ n * conjQ p r :=
  (map_mul (conjQ p) _ _).trans
    (congrArg (· * conjQ p r) ((map_pow (conjQ p) zQ n).trans (congrArg (· ^ n) (conjQ_zQ p))))

theorem classOf_latVec (g : latticeO) {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    classOf (latVec (mat g) u) = modTwoEnd g (classOf u) := by
  rw [classOf_of_mem (latVec_spec g hu).1, classOf_of_mem hu, modTwoEnd_mk]
  rfl

theorem isShortCoord_conjQ (p : Pvis) {r : Q} (h : IsShortCoord (coordOf r)) :
    IsShortCoord (coordOf (conjQ p r)) := by
  obtain ⟨u, hu, hcl⟩ := (isShort_mk_iff r).2 h
  refine (isShort_mk_iff (conjQ p r)).1 ⟨latVec (mat p.1.2) u, latVec_mem_minVecs p.1.2 hu, ?_⟩
  exact (classOf_latVec p.1.2 hu.1).trans ((congrArg (modTwoEnd p.1.2) hcl).trans
    (phi_conjQ p r).symm)

theorem isShortCoord_conjQ_iff (p : Pvis) (r : Q) :
    IsShortCoord (coordOf (conjQ p r)) ↔ IsShortCoord (coordOf r) := by
  refine ⟨fun h => ?_, isShortCoord_conjQ p⟩
  have h' := isShortCoord_conjQ p⁻¹ h
  have e : conjQ p⁻¹ (conjQ p r) = r := by
    rw [← conjQ_mul, mul_inv_cancel, conjQ_one]
  rwa [e] at h'

theorem Xlift_eq_zero {r : Q} (h : ¬ IsShortCoord (coordOf r)) : Xlift r = 0 := by
  unfold Xlift
  simp only [h, ↓reduceDIte]

theorem Xlift_eq_sgn_smul {r r' : Q} {e : ZMod 2} (hc : coordOf r' = coordOf r)
    (hs : centralCoord r' = e + centralCoord r) : Xlift r' = sgn e • Xlift r := by
  by_cases h : IsShortCoord (coordOf r)
  · have h' : IsShortCoord (coordOf r') := hc ▸ h
    rw [Xlift_eq h', Xlift_eq h, hs, sgn_add, mul_smul]
    exact congrArg (fun x => sgn e • sgn (centralCoord r) • (Pi.single x 1 : SpaceX))
      (Subtype.ext hc)
  · have h' : ¬ IsShortCoord (coordOf r') := hc ▸ h
    rw [Xlift_eq_zero h', Xlift_eq_zero h, smul_zero]

private theorem coord_of_symm_eq {r r' : Q} {e : ZMod 2}
    (h : spinEquiv.symm r' = ⟨e, 0, 0⟩ * spinEquiv.symm r) :
    coordOf r' = coordOf r ∧ centralCoord r' = e + centralCoord r := by
  unfold coordOf centralCoord
  rw [h]
  simp

theorem symm_zQ_pow_mul (e : ZMod 2) (r : Q) :
    spinEquiv.symm (zQ ^ e.val * r) = ⟨e, 0, 0⟩ * spinEquiv.symm r :=
  (map_mul spinEquiv.symm _ _).trans
    (congrArg (· * spinEquiv.symm r) ((congrArg spinEquiv.symm (zQ_pow_val e)).trans
      (spinEquiv.symm_apply_apply _)))

theorem Xlift_zQ_pow_mul (e : ZMod 2) (r : Q) : Xlift (zQ ^ e.val * r) = sgn e • Xlift r :=
  have h := coord_of_symm_eq (symm_zQ_pow_mul e r)
  Xlift_eq_sgn_smul h.1 h.2

theorem Xlift_rep (c : ShortIdx) : Xlift (rep c.1) = Pi.single c 1 := by
  have h : IsShortCoord (coordOf (rep c.1)) := (coordOf_rep c.1).symm ▸ c.2
  rw [Xlift_eq h, centralCoord_rep, sgn_zero, one_smul]
  exact congrArg (fun x => (Pi.single x 1 : SpaceX)) (Subtype.ext (coordOf_rep c.1))

@[expose] def thetaA (g : Matrix (Fin 24) (Fin 24) ℚ) : symMat →ₗ[ℚ] symMat where
  toFun A := ⟨gᵀ * (A : Matrix (Fin 24) (Fin 24) ℚ) * g, by
    rw [mem_symMat, transpose_mul, transpose_mul, transpose_transpose, A.2, Matrix.mul_assoc]⟩
  map_add' A B := Subtype.ext (by
    simp only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul])
  map_smul' c A := Subtype.ext (by
    simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply])

theorem coe_thetaA (g : Matrix (Fin 24) (Fin 24) ℚ) (A : symMat) :
    (thetaA g A : Matrix (Fin 24) (Fin 24) ℚ) = gᵀ * (A : Matrix (Fin 24) (Fin 24) ℚ) * g := rfl

@[expose] def thetaW (s : Matrix SpinIdx SpinIdx ℚ) (g : Matrix (Fin 24) (Fin 24) ℚ) :
    SpaceW →ₗ[ℚ] SpaceW where
  toFun N := sᵀ * N * g
  map_add' N N' := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c N := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

theorem thetaW_apply (s : Matrix SpinIdx SpinIdx ℚ) (g : Matrix (Fin 24) (Fin 24) ℚ)
    (N : SpaceW) : thetaW s g N = sᵀ * N * g := rfl

theorem thetaW_tensor (s : Matrix SpinIdx SpinIdx ℚ) (g : Matrix (Fin 24) (Fin 24) ℚ)
    (q : SpinIdx → ℚ) (v : Fin 24 → ℚ) :
    thetaW s g (tensor q v) = tensor (q ᵥ* s) (v ᵥ* g) := by
  rw [thetaW_apply, tensor, tensor, mul_vecMulVec, vecMulVec_mul, mulVec_transpose]

@[expose] def thetaX (p : Pvis) : SpaceX →ₗ[ℚ] SpaceX :=
  (Pi.basisFun ℚ ShortIdx).constr ℚ fun c => Xlift (conjQ p (rep c.1))

theorem thetaX_single (p : Pvis) (c : ShortIdx) :
    thetaX p (Pi.single c 1) = Xlift (conjQ p (rep c.1)) := by
  have h := (Pi.basisFun ℚ ShortIdx).constr_basis ℚ (fun c => Xlift (conjQ p (rep c.1))) c
  rw [Pi.basisFun_apply] at h
  exact h

theorem thetaX_Xlift (p : Pvis) (r : Q) : thetaX p (Xlift r) = Xlift (conjQ p r) := by
  by_cases h : IsShortCoord (coordOf r)
  · have h1 : thetaX p (Xlift r) =
        sgn (centralCoord r) • Xlift (conjQ p (rep (coordOf r))) :=
      calc thetaX p (Xlift r)
          = thetaX p (sgn (centralCoord r) • Pi.single (⟨coordOf r, h⟩ : ShortIdx) 1) :=
            congrArg (thetaX p) (Xlift_eq h)
        _ = sgn (centralCoord r) • thetaX p (Pi.single (⟨coordOf r, h⟩ : ShortIdx) 1) :=
            map_smul _ _ _
        _ = sgn (centralCoord r) • Xlift (conjQ p (rep (coordOf r))) :=
            congrArg (sgn (centralCoord r) • ·) (thetaX_single p ⟨coordOf r, h⟩)
    have h2 : Xlift (conjQ p r) = sgn (centralCoord r) • Xlift (conjQ p (rep (coordOf r))) :=
      (congrArg (fun x => Xlift (conjQ p x)) (eq_zQ_pow_mul_rep r)).trans
        ((congrArg Xlift (conjQ_zQ_pow_mul p _ _)).trans (Xlift_zQ_pow_mul _ _))
    exact h1.trans h2.symm
  · have h' : ¬ IsShortCoord (coordOf (conjQ p r)) := fun h' =>
      h ((isShortCoord_conjQ_iff p r).1 h')
    exact (congrArg (thetaX p) (Xlift_eq_zero h)).trans
      ((map_zero (thetaX p)).trans (Xlift_eq_zero h').symm)

@[expose] def theta (p : Pvis) : SpaceB →ₗ[ℚ] SpaceB :=
  (thetaA (mat p.1.2)).prodMap
    ((thetaX p).prodMap (thetaW (p.1.1 : Matrix SpinIdx SpinIdx ℚ) (mat p.1.2)))

theorem theta_apply (p : Pvis) (x : SpaceB) :
    theta p x = (thetaA (mat p.1.2) x.1, thetaX p x.2.1,
      thetaW (p.1.1 : Matrix SpinIdx SpinIdx ℚ) (mat p.1.2) x.2.2) := rfl

theorem theta_symMat (p : Pvis) (A : symMat) :
    theta p (A, 0, 0) = (thetaA (mat p.1.2) A, 0, 0) := by
  rw [theta_apply, map_zero, map_zero]

theorem theta_Xlift (p : Pvis) (r : Q) :
    theta p (0, Xlift r, 0) = (0, Xlift (conjQ p r), 0) := by
  rw [theta_apply, map_zero, map_zero, thetaX_Xlift]

theorem theta_tensor (p : Pvis) (q : SpinIdx → ℚ) (v : Fin 24 → ℚ) :
    theta p (0, 0, tensor q v) =
      (0, 0, tensor (q ᵥ* (p.1.1 : Matrix SpinIdx SpinIdx ℚ)) (v ᵥ* mat p.1.2)) := by
  rw [theta_apply, map_zero, map_zero, thetaW_tensor]

theorem thetaA_mul (g k : Matrix (Fin 24) (Fin 24) ℚ) (A : symMat) :
    thetaA (g * k) A = thetaA k (thetaA g A) :=
  Subtype.ext (by
    simp only [coe_thetaA, Matrix.transpose_mul, Matrix.mul_assoc])

theorem thetaW_mul (s t : Matrix SpinIdx SpinIdx ℚ) (g k : Matrix (Fin 24) (Fin 24) ℚ)
    (N : SpaceW) : thetaW (s * t) (g * k) N = thetaW t k (thetaW s g N) := by
  simp only [thetaW_apply, Matrix.transpose_mul, Matrix.mul_assoc]

theorem thetaX_mul_apply (p q : Pvis) (x : SpaceX) :
    thetaX (p * q) x = thetaX q (thetaX p x) := by
  have h : thetaX (p * q) = thetaX q ∘ₗ thetaX p := by
    refine (Pi.basisFun ℚ ShortIdx).ext fun c => ?_
    rw [Pi.basisFun_apply, LinearMap.comp_apply, thetaX_single, thetaX_single, thetaX_Xlift]
    exact congrArg Xlift (conjQ_mul p q _)
  exact LinearMap.congr_fun h x

theorem thetaX_one_apply (x : SpaceX) : thetaX 1 x = x := by
  have h : thetaX 1 = LinearMap.id := by
    refine (Pi.basisFun ℚ ShortIdx).ext fun c => ?_
    rw [Pi.basisFun_apply, LinearMap.id_apply, thetaX_single]
    exact (congrArg Xlift (conjQ_one _)).trans (Xlift_rep c)
  exact LinearMap.congr_fun h x

theorem theta_mul_apply (p q : Pvis) (x : SpaceB) : theta (p * q) x = theta q (theta p x) := by
  rw [theta_apply, theta_apply, theta_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact thetaA_mul _ _ _
  · exact thetaX_mul_apply p q _
  · exact thetaW_mul _ _ _ _ _

theorem theta_mul (p q : Pvis) : theta (p * q) = theta q ∘ₗ theta p :=
  LinearMap.ext (theta_mul_apply p q)

theorem theta_one_apply (x : SpaceB) : theta 1 x = x := by
  rw [theta_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact Subtype.ext (by
      show (mat (1 : latticeO))ᵀ * (x.1 : Matrix (Fin 24) (Fin 24) ℚ) * mat 1 = x.1
      rw [mat_one, transpose_one, Matrix.one_mul, Matrix.mul_one])
  · exact thetaX_one_apply _
  · show ((1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)ᵀ * x.2.2 * mat 1 = x.2.2
    rw [mat_one, Units.val_one, transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem theta_one : theta 1 = LinearMap.id := LinearMap.ext theta_one_apply

@[expose] def thetaEquiv (p : Pvis) : SpaceB ≃ₗ[ℚ] SpaceB :=
  { theta p with
    invFun := theta p⁻¹
    left_inv := fun x => by
      show theta p⁻¹ (theta p x) = x
      rw [← theta_mul_apply, mul_inv_cancel, theta_one_apply]
    right_inv := fun x => by
      show theta p (theta p⁻¹ x) = x
      rw [← theta_mul_apply, inv_mul_cancel, theta_one_apply] }

theorem thetaEquiv_apply (p : Pvis) (x : SpaceB) : thetaEquiv p x = theta p x := rfl

theorem thetaEquiv_symm_apply (p : Pvis) (x : SpaceB) :
    (thetaEquiv p).symm x = theta p⁻¹ x := rfl

theorem thetaEquiv_one : thetaEquiv 1 = 1 := LinearEquiv.ext theta_one_apply

theorem thetaEquiv_mul (p q : Pvis) : thetaEquiv (p * q) = thetaEquiv q * thetaEquiv p :=
  LinearEquiv.ext (theta_mul_apply p q)

theorem thetaEquiv_inv (p : Pvis) : thetaEquiv p⁻¹ = (thetaEquiv p)⁻¹ := by
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.coe_inv, thetaEquiv_symm_apply, thetaEquiv_apply]

@[expose] def thetaHom : Pvis →* (SpaceB ≃ₗ[ℚ] SpaceB)ᵐᵒᵖ where
  toFun p := MulOpposite.op (thetaEquiv p)
  map_one' := congrArg MulOpposite.op thetaEquiv_one
  map_mul' p q := by
    rw [thetaEquiv_mul, MulOpposite.op_mul]

theorem thetaHom_apply (p : Pvis) : thetaHom p = MulOpposite.op (thetaEquiv p) := rfl

@[expose] def Gvis : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) where
  carrier := Set.range thetaEquiv
  one_mem' := ⟨1, thetaEquiv_one⟩
  mul_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨q * p, thetaEquiv_mul q p⟩
  inv_mem' := by
    rintro _ ⟨p, rfl⟩
    exact ⟨p⁻¹, thetaEquiv_inv p⟩

theorem mem_Gvis {f : SpaceB ≃ₗ[ℚ] SpaceB} : f ∈ Gvis ↔ ∃ p : Pvis, thetaEquiv p = f :=
  Iff.rfl

theorem Gvis_eq_unop_range : Gvis = thetaHom.range.unop := by
  ext f
  rw [mem_Gvis, Subgroup.mem_unop, MonoidHom.mem_range]
  simp only [thetaHom_apply, MulOpposite.op_inj]

theorem compatible_spin_lattice_pair_data :
    (∀ p : GL SpinIdx ℚ × latticeO, p ∈ Pvis ↔
      ((p.1 : Matrix SpinIdx SpinIdx ℚ) ∈ orthogonalGroup SpinIdx ℚ ∧
        (∀ i j, (p.1 : Matrix SpinIdx SpinIdx ℚ) i j ∈ dyadic) ∧
        (fun r => p.1⁻¹ * r * p.1) '' (Q : Set (GL SpinIdx ℚ)) = Q) ∧
      ∀ r r' : Q, (r' : GL SpinIdx ℚ) = p.1⁻¹ * r * p.1 →
        Multiplicative.toAdd (phi (QuotientGroup.mk r')) =
          modTwoEnd p.2 (Multiplicative.toAdd (phi (QuotientGroup.mk r)))) ∧
    (∀ g : GL (Fin 24) ℚ, g ∈ latticeO ↔
      (g : Matrix (Fin 24) (Fin 24) ℚ) ∈ orthogonalGroup (Fin 24) ℚ ∧
        (fun x => x ᵥ* (g : Matrix (Fin 24) (Fin 24) ℚ)) '' latticeQ = latticeQ) ∧
    (∀ p q : Pvis, ((p * q : Pvis) : GL SpinIdx ℚ × latticeO) = (p.1.1 * q.1.1, p.1.2 * q.1.2)) ∧
    (∀ (p : Pvis) (A : symMat), theta p (A, 0, 0) = (thetaA (mat p.1.2) A, 0, 0) ∧
      (thetaA (mat p.1.2) A : Matrix (Fin 24) (Fin 24) ℚ) =
        (mat p.1.2)ᵀ * (A : Matrix (Fin 24) (Fin 24) ℚ) * mat p.1.2) ∧
    (∀ (p : Pvis) (r r' : Q), (r' : GL SpinIdx ℚ) = p.1.1⁻¹ * r * p.1.1 →
      theta p (0, Xlift r, 0) = (0, Xlift r', 0)) ∧
    (∀ (p : Pvis) (c : ShortIdx),
      theta p (0, Pi.single c 1, 0) = (0, Xlift (conjQ p (rep c.1)), 0)) ∧
    (∀ (p : Pvis) (q : SpinIdx → ℚ) (v : Fin 24 → ℚ), theta p (0, 0, tensor q v) =
      (0, 0, tensor (q ᵥ* (p.1.1 : Matrix SpinIdx SpinIdx ℚ)) (v ᵥ* mat p.1.2))) ∧
    (∀ (p : Pvis) (N : SpaceW),
      theta p (0, 0, N) = (0, 0, (p.1.1 : Matrix SpinIdx SpinIdx ℚ)ᵀ * N * mat p.1.2)) ∧
    (∀ (p q : Pvis) (x : SpaceB), theta (p * q) x = theta q (theta p x)) ∧
    (∀ x : SpaceB, theta 1 x = x) ∧
    (∀ (p : Pvis) (x : SpaceB), thetaEquiv p x = theta p x ∧ (thetaEquiv p).symm x = theta p⁻¹ x) ∧
    (∀ p : Pvis, thetaHom p = MulOpposite.op (thetaEquiv p)) ∧
    (∀ f : SpaceB ≃ₗ[ℚ] SpaceB, f ∈ Gvis ↔ ∃ p : Pvis, thetaEquiv p = f) ∧
    Gvis = thetaHom.range.unop :=
  ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ _ => rfl,
    fun p A => ⟨theta_symMat p A, coe_thetaA _ A⟩,
    fun p r r' h => (theta_Xlift p r).trans
      (congrArg (fun x => ((0 : symMat), Xlift x, (0 : SpaceW)))
        (Subtype.ext (h.trans (coe_conjQ p r).symm)).symm),
    fun p c => by rw [theta_apply, map_zero, map_zero, thetaX_single],
    theta_tensor,
    fun p N => by rw [theta_apply, map_zero, map_zero, thetaW_apply],
    theta_mul_apply, theta_one_apply,
    fun p x => ⟨thetaEquiv_apply p x, thetaEquiv_symm_apply p x⟩, thetaHom_apply,
    fun _ => mem_Gvis, Gvis_eq_unop_range⟩

end CFSG.Monster.Visible
