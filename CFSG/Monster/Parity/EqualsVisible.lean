module

public import CFSG.Monster.Parity.SpinPart
public import CFSG.Monster.Visible.AlgebraAction
import CFSG.Monster.Visible.ShortGen
public import CFSG.Monster.Parity.RecoversLattice

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Parity

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.ScalarKernel CFSG.Monster.Visible Matrix Module

theorem coe_rep_mat (c : ShortIdx) :
    (((rep c.1 : Q) : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = Rmat c := by
  rw [coe_Q_eq, centralCoord_rep, coordOf_rep]
  rfl

theorem coordOf_one' : coordOf (1 : Q) = 0 := by
  have h := coordOf_mul (1 : Q) 1
  rw [mul_one] at h
  exact left_eq_add.1 h

theorem coordOf_inv' (r : Q) : coordOf r⁻¹ = -coordOf r := by
  have h := coordOf_mul r⁻¹ r
  rw [inv_mul_cancel, coordOf_one'] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem coordOf_zQ_pow (n : ℕ) : coordOf (zQ ^ n) = 0 :=
  (mem_zpowers_zQ_iff _).1 (Subgroup.pow_mem _ (Subgroup.mem_zpowers zQ) n)

theorem conj_zU_pow_mul (S X : GL SpinIdx ℚ) (n : ℕ) :
    S⁻¹ * (zU ^ n * X) * S = zU ^ n * (S⁻¹ * X * S) := by
  have hz : Commute zU S⁻¹ := Commute.neg_one_left S⁻¹
  have hc : Commute (zU ^ n) S⁻¹ := hz.pow_left n
  calc S⁻¹ * (zU ^ n * X) * S = (S⁻¹ * zU ^ n) * X * S := by simp only [mul_assoc]
    _ = (zU ^ n * S⁻¹) * X * S := by rw [hc.eq]
    _ = zU ^ n * (S⁻¹ * X * S) := by simp only [mul_assoc]

theorem theta_xB (p : Pvis) (u : SpaceB) : theta p (xB u) = xB (theta p u) := by
  rw [theta_apply, theta_apply, xB_apply, xB_apply]
  exact Prod.ext rfl (Prod.ext rfl (map_neg _ _))

theorem thetaEquiv_eq_iff (p p' : Pvis) :
    thetaEquiv p' = thetaEquiv p ↔ p' = p ∨ p' = p * negPair := by
  constructor
  · intro h
    have hker : p⁻¹ * p' ∈ thetaHom.ker := by
      rw [MonoidHom.mem_ker, thetaHom_apply, thetaEquiv_mul, thetaEquiv_inv, h, mul_inv_cancel,
        MulOpposite.op_one]
    rcases (mem_ker_thetaHom_iff _).1 hker with h1 | h1
    · left
      calc p' = p * (p⁻¹ * p') := (mul_inv_cancel_left p p').symm
        _ = p := by rw [h1, mul_one]
    · right
      calc p' = p * (p⁻¹ * p') := (mul_inv_cancel_left p p').symm
        _ = p * negPair := by rw [h1]
  · rintro (rfl | rfl)
    · rfl
    · exact thetaEquiv_mul_negPair p

theorem mul_negPair_eq (p : Pvis) :
    (((p * negPair : Pvis).1.1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
        -((p.1.1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) ∧
      mat (p * negPair : Pvis).1.2 = -mat p.1.2 := by
  refine ⟨?_, ?_⟩
  · change (((p.1.1 * zU : GL SpinIdx ℚ)) : Matrix SpinIdx SpinIdx ℚ) = _
    rw [Units.val_mul, coe_zU, zmat, mul_neg_one]
  · change mat (p.1.2 * negOneO) = _
    rw [mat_mul, mat_negOneO, mul_neg_one]

theorem conj_mem_Q_of_short (S : GL SpinIdx ℚ)
    (h : ∀ r : Q, IsShortCoord (coordOf r) → S⁻¹ * (r : GL SpinIdx ℚ) * S ∈ Q) (q : Q) :
    S⁻¹ * (q : GL SpinIdx ℚ) * S ∈ Q := by
  have hq : q ∈ Subgroup.closure {r : Q | IsShortCoord (coordOf r)} := by
    rw [closure_isShortCoord_eq_top]
    exact Subgroup.mem_top q
  induction hq using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one =>
    rw [OneMemClass.coe_one, mul_one, inv_mul_cancel]
    exact Q.one_mem
  | mul x y _ _ hx hy =>
    have e : S⁻¹ * ((x * y : Q) : GL SpinIdx ℚ) * S =
        (S⁻¹ * (x : GL SpinIdx ℚ) * S) * (S⁻¹ * (y : GL SpinIdx ℚ) * S) := by
      rw [Subgroup.coe_mul]
      group
    rw [e]
    exact Q.mul_mem hx hy
  | inv x _ hx =>
    have e : S⁻¹ * ((x⁻¹ : Q) : GL SpinIdx ℚ) * S = (S⁻¹ * (x : GL SpinIdx ℚ) * S)⁻¹ := by
      rw [Subgroup.coe_inv]
      group
    rw [e]
    exact Q.inv_mem hx

@[expose] def conjMap (S : GL SpinIdx ℚ) (h : ∀ q : Q, S⁻¹ * (q : GL SpinIdx ℚ) * S ∈ Q)
    (q : Q) : Q :=
  ⟨S⁻¹ * q * S, h q⟩

theorem coe_conjMap (S : GL SpinIdx ℚ) (h : ∀ q : Q, S⁻¹ * (q : GL SpinIdx ℚ) * S ∈ Q) (q : Q) :
    ((conjMap S h q : Q) : GL SpinIdx ℚ) = S⁻¹ * q * S := rfl

theorem mem_Q_iff_conj_of_forall (S : GL SpinIdx ℚ)
    (h : ∀ q : Q, S⁻¹ * (q : GL SpinIdx ℚ) * S ∈ Q) (x : GL SpinIdx ℚ) :
    x ∈ Q ↔ S⁻¹ * x * S ∈ Q := by
  refine ⟨fun hx => h ⟨x, hx⟩, fun hx => ?_⟩
  have hinj : Function.Injective (conjMap S h) := fun a b hab => by
    have h' : S⁻¹ * (a : GL SpinIdx ℚ) * S = S⁻¹ * (b : GL SpinIdx ℚ) * S := by
      rw [← coe_conjMap S h a, ← coe_conjMap S h b, hab]
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
  obtain ⟨q, hq⟩ := Finite.injective_iff_surjective.1 hinj ⟨S⁻¹ * x * S, hx⟩
  have h' : S⁻¹ * (q : GL SpinIdx ℚ) * S = S⁻¹ * x * S := by
    rw [← coe_conjMap S h q, hq]
  have hqx : (q : GL SpinIdx ℚ) = x := mul_left_cancel (mul_right_cancel h')
  exact hqx ▸ q.2

theorem phi0_coordOf_mul (e : Q ≃* Q) (g : latticeO) (x y : Q)
    (hx : phi0 (coordOf (e x)) = modTwoEnd g (phi0 (coordOf x)))
    (hy : phi0 (coordOf (e y)) = modTwoEnd g (phi0 (coordOf y))) :
    phi0 (coordOf (e (x * y))) = modTwoEnd g (phi0 (coordOf (x * y))) := by
  rw [map_mul, coordOf_mul, coordOf_mul, map_add, map_add, map_add, hx, hy]

theorem phi0_coordOf_inv (e : Q ≃* Q) (g : latticeO) (x : Q)
    (hx : phi0 (coordOf (e x)) = modTwoEnd g (phi0 (coordOf x))) :
    phi0 (coordOf (e x⁻¹)) = modTwoEnd g (phi0 (coordOf x⁻¹)) := by
  rw [map_inv, coordOf_inv', coordOf_inv', map_neg, map_neg, map_neg, hx]

theorem phi0_coordOf_one (e : Q ≃* Q) (g : latticeO) :
    phi0 (coordOf (e 1)) = modTwoEnd g (phi0 (coordOf 1)) := by
  rw [map_one, coordOf_one', map_zero, map_zero]

theorem phi0_coordOf_of_short (e : Q ≃* Q) (g : latticeO)
    (hgen : ∀ r : Q, IsShortCoord (coordOf r) →
      phi0 (coordOf (e r)) = modTwoEnd g (phi0 (coordOf r))) (q : Q) :
    phi0 (coordOf (e q)) = modTwoEnd g (phi0 (coordOf q)) := by
  have hq : q ∈ Subgroup.closure {r : Q | IsShortCoord (coordOf r)} := by
    rw [closure_isShortCoord_eq_top]
    exact Subgroup.mem_top q
  induction hq using Subgroup.closure_induction with
  | mem x hx => exact hgen x hx
  | one => exact phi0_coordOf_one e g
  | mul x y _ _ hx hy => exact phi0_coordOf_mul e g x y hx hy
  | inv x _ hx => exact phi0_coordOf_inv e g x hx

theorem isCompatible_of_short (S : GL SpinIdx ℚ) (hS : ∀ x : GL SpinIdx ℚ, x ∈ Q ↔ S⁻¹ * x * S ∈ Q)
    (g : latticeO)
    (hgen : ∀ r r' : Q, IsShortCoord (coordOf r) → (r' : GL SpinIdx ℚ) = S⁻¹ * r * S →
      phi0 (coordOf r') = modTwoEnd g (phi0 (coordOf r))) :
    IsCompatible S g := by
  have key := phi0_coordOf_of_short (conjQOf S hS) g fun r hr =>
    hgen r _ hr (coe_conjQOf S hS r)
  intro r r' h
  have hr' : r' = conjQOf S hS r := Subtype.ext (h.trans (coe_conjQOf S hS r).symm)
  subst hr'
  exact (toAdd_phi_mk (conjQOf S hS r)).trans ((key r).trans
    (congrArg (modTwoEnd g) (toAdd_phi_mk r).symm))

namespace IsParityAut

variable {f : SpaceB ≃ₗ[ℚ] SpaceB}

@[expose] def tElt (hf : IsParityAut f) (c : ShortIdx) : Q :=
  open Classical in
  if hf.lineSign c = 1 then rep (hf.lineMap c).1 else zQ * rep (hf.lineMap c).1

theorem coe_tElt (hf : IsParityAut f) (c : ShortIdx) :
    (((hf.tElt c : Q) : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      hf.lineSign c • Rmat (hf.lineMap c) := by
  unfold tElt
  split_ifs with h
  · rw [coe_rep_mat, h, one_smul]
  · have h' : hf.lineSign c = -1 := (hf.lineSign_eq c).resolve_left h
    rw [Subgroup.coe_mul, Units.val_mul, coe_coe_zQ, coe_rep_mat, h', neg_one_smul, neg_one_mul]

theorem Xlift_tElt (hf : IsParityAut f) (c : ShortIdx) :
    Xlift (hf.tElt c) = hf.lineSign c • Pi.single (hf.lineMap c) 1 := by
  unfold tElt
  split_ifs with h
  · rw [Xlift_rep_eq, h, one_smul]
  · have h' : hf.lineSign c = -1 := (hf.lineSign_eq c).resolve_left h
    have hz := Xlift_zQ_pow_mul (1 : ZMod 2) (rep (hf.lineMap c).1)
    rw [show (1 : ZMod 2).val = 1 from rfl, pow_one] at hz
    rw [hz, Xlift_rep_eq, h']
    rfl

theorem coordOf_tElt (hf : IsParityAut f) (c : ShortIdx) :
    coordOf (hf.tElt c) = (hf.lineMap c).1 := by
  unfold tElt
  split_ifs
  · exact coordOf_rep _
  · rw [coordOf_mul, coordOf_rep, show coordOf zQ = 0 from
      (mem_zpowers_zQ_iff zQ).1 (Subgroup.mem_zpowers zQ), zero_add]

theorem apply_eq (hf : IsParityAut f) (x : SpaceB) :
    f x = (resA f x.1, resX f x.2.1, resW f x.2.2) := by
  have hx : x = inA x.1 + inX x.2.1 + inW x.2.2 := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
  conv_lhs => rw [hx]
  rw [map_add, map_add, hf.apply_inA, hf.apply_inX, hf.apply_inW]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

end IsParityAut

section Visible

variable {f : SpaceB ≃ₗ[ℚ] SpaceB} (hf : IsParityAut f) {g : latticeO}
  (hA : ∀ A : symMat, resA f A = thetaA (mat g) A)
  (hu : ∀ c : ShortIdx, uQ c ᵥ* mat g = uQ (hf.lineMap c) ∨ uQ c ᵥ* mat g = -uQ (hf.lineMap c))

@[expose] def spinGL : GL SpinIdx ℚ :=
  ⟨spinMat f (mat g), (spinMat f (mat g))ᵀ, spinMat_mul_transpose hf hA,
    spinMat_transpose_mul hf hA⟩

theorem coe_spinGL :
    ((spinGL hf hA : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = spinMat f (mat g) := rfl

theorem coe_spinGL_inv :
    (((spinGL hf hA)⁻¹ : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = (spinMat f (mat g))ᵀ := rfl

include hu

theorem conj_rep (c : ShortIdx) :
    (spinGL hf hA)⁻¹ * ((rep c.1 : Q) : GL SpinIdx ℚ) * spinGL hf hA =
      ((hf.tElt c : Q) : GL SpinIdx ℚ) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_spinGL_inv, coe_spinGL, coe_rep_mat, hf.coe_tElt,
    spin_conj_Rmat hf hu hA]

theorem conj_short {r : Q} (hr : IsShortCoord (coordOf r)) :
    (spinGL hf hA)⁻¹ * (r : GL SpinIdx ℚ) * spinGL hf hA =
      ((zQ ^ (centralCoord r).val * hf.tElt ⟨coordOf r, hr⟩ : Q) : GL SpinIdx ℚ) := by
  have hr' : (r : GL SpinIdx ℚ) =
      zU ^ (centralCoord r).val * ((rep (coordOf r) : Q) : GL SpinIdx ℚ) := by
    calc (r : GL SpinIdx ℚ) = ((zQ ^ (centralCoord r).val * rep (coordOf r) : Q) : GL SpinIdx ℚ) :=
          congrArg Subtype.val (eq_zQ_pow_mul_rep r)
      _ = zU ^ (centralCoord r).val * ((rep (coordOf r) : Q) : GL SpinIdx ℚ) := by
          rw [Subgroup.coe_mul, Subgroup.coe_pow, coe_zQ]
  rw [hr', conj_zU_pow_mul, Subgroup.coe_mul, Subgroup.coe_pow, coe_zQ]
  congr 1
  exact conj_rep hf hA hu ⟨coordOf r, hr⟩

theorem conj_mem_Q (q : Q) : (spinGL hf hA)⁻¹ * (q : GL SpinIdx ℚ) * spinGL hf hA ∈ Q :=
  conj_mem_Q_of_short (spinGL hf hA) (fun r hr => by
    rw [conj_short hf hA hu hr]
    exact SetLike.coe_mem _) q

theorem mem_Q_iff_conj (r : GL SpinIdx ℚ) :
    r ∈ Q ↔ (spinGL hf hA)⁻¹ * r * spinGL hf hA ∈ Q :=
  mem_Q_iff_conj_of_forall (spinGL hf hA) (conj_mem_Q hf hA hu) r

theorem isDyadicSpinNormalizer_spinGL : IsDyadicSpinNormalizer (spinGL hf hA) := by
  have hst := spinMat_transpose_mul hf hA
  have hinv : (spinMat f (mat g))⁻¹ = (spinMat f (mat g))ᵀ := Matrix.inv_eq_left_inv hst
  have hiff := mem_Q_iff_conj hf hA hu
  refine ⟨(mem_orthogonalGroup_iff _ _).2 (spinMat_mul_transpose hf hA), fun i j => ?_,
    (image_conj_eq_Q_iff _).2 hiff⟩
  refine dyadic_of_conj_Q (spinMat f (mat g)) hst ?_ i j
  ext M
  constructor
  · rintro ⟨M', ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨(spinGL hf hA)⁻¹ * q * spinGL hf hA, (hiff q).1 hq, ?_⟩
    show (((spinGL hf hA)⁻¹ * q * spinGL hf hA : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      (spinMat f (mat g))⁻¹ * (q : Matrix SpinIdx SpinIdx ℚ) * spinMat f (mat g)
    rw [Units.val_mul, Units.val_mul, coe_spinGL_inv, coe_spinGL, hinv]
  · rintro ⟨q, hq, rfl⟩
    refine ⟨((spinGL hf hA * q * (spinGL hf hA)⁻¹ : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ),
      ⟨spinGL hf hA * q * (spinGL hf hA)⁻¹, (hiff _).2 ?_, rfl⟩, ?_⟩
    · have e : (spinGL hf hA)⁻¹ * (spinGL hf hA * q * (spinGL hf hA)⁻¹) * spinGL hf hA = q := by
        group
      rw [e]
      exact hq
    · show (spinMat f (mat g))⁻¹ *
          ((spinGL hf hA * q * (spinGL hf hA)⁻¹ : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) *
          spinMat f (mat g) = (q : Matrix SpinIdx SpinIdx ℚ)
      rw [Units.val_mul, Units.val_mul, coe_spinGL_inv, coe_spinGL, hinv]
      simp only [Matrix.mul_assoc, hst, Matrix.mul_one]
      rw [← Matrix.mul_assoc, hst, Matrix.one_mul]

theorem latVec_uvec (c : ShortIdx) :
    latVec (mat g) (uvec c) = uvec (hf.lineMap c) ∨
      latVec (mat g) (uvec c) = -uvec (hf.lineMap c) := by
  have hs := (latVec_spec g (uvec_mem c).1).2
  rcases hu c with h | h
  · left
    apply ratVec_injective
    rw [hs]
    exact h
  · right
    apply ratVec_injective
    rw [hs, ratVec_neg]
    exact h

theorem isCompatible_spinGL : IsCompatible (spinGL hf hA) g := by
  refine isCompatible_of_short (spinGL hf hA) (mem_Q_iff_conj hf hA hu) g fun r r' hr h => ?_
  have hcQ : r' = zQ ^ (centralCoord r).val * hf.tElt ⟨coordOf r, hr⟩ :=
    Subtype.ext (h.trans (conj_short hf hA hu hr))
  have hco : coordOf r' = (hf.lineMap ⟨coordOf r, hr⟩).1 :=
    calc coordOf r' = coordOf (zQ ^ (centralCoord r).val * hf.tElt ⟨coordOf r, hr⟩) :=
          congrArg coordOf hcQ
      _ = coordOf (zQ ^ (centralCoord r).val) + coordOf (hf.tElt ⟨coordOf r, hr⟩) :=
          coordOf_mul _ _
      _ = 0 + (hf.lineMap ⟨coordOf r, hr⟩).1 :=
          congrArg₂ (· + ·) (coordOf_zQ_pow _) (hf.coordOf_tElt _)
      _ = (hf.lineMap ⟨coordOf r, hr⟩).1 := zero_add _
  have hlat : classOf (latVec (mat g) (uvec ⟨coordOf r, hr⟩)) =
      classOf (uvec (hf.lineMap ⟨coordOf r, hr⟩)) := by
    rcases latVec_uvec hf hu ⟨coordOf r, hr⟩ with h1 | h1
    · exact congrArg classOf h1
    · exact (congrArg classOf h1).trans ((classOf_eq_iff (uvec_mem _)
        (neg_mem_minVecs (uvec_mem _))).2 (Or.inr rfl)).symm
  calc phi0 (coordOf r') = phi0 (hf.lineMap ⟨coordOf r, hr⟩).1 := congrArg phi0 hco
    _ = classOf (uvec (hf.lineMap ⟨coordOf r, hr⟩)) := (classOf_uvec _).symm
    _ = classOf (latVec (mat g) (uvec ⟨coordOf r, hr⟩)) := hlat.symm
    _ = modTwoEnd g (classOf (uvec ⟨coordOf r, hr⟩)) := classOf_latVec g (uvec_mem _).1
    _ = modTwoEnd g (phi0 (coordOf r)) := congrArg (modTwoEnd g) (classOf_uvec ⟨coordOf r, hr⟩)

@[expose] def visPair : Pvis :=
  ⟨(spinGL hf hA, g), isDyadicSpinNormalizer_spinGL hf hA hu, isCompatible_spinGL hf hA hu⟩

theorem conjQ_visPair_rep (c : ShortIdx) : conjQ (visPair hf hA hu) (rep c.1) = hf.tElt c :=
  Subtype.ext ((coe_conjQ _ _).trans (conj_rep hf hA hu c))

theorem thetaX_visPair : thetaX (visPair hf hA hu) = resX f := by
  refine (Pi.basisFun ℚ ShortIdx).ext fun c => ?_
  rw [Pi.basisFun_apply, thetaX_single, hf.resX_single, conjQ_visPair_rep, hf.Xlift_tElt]

theorem visPair_snd : (visPair hf hA hu).1.2 = g := rfl

theorem coe_visPair_fst :
    (((visPair hf hA hu).1.1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = spinMat f (mat g) := rfl

theorem thetaEquiv_visPair : thetaEquiv (visPair hf hA hu) = f := by
  refine LinearEquiv.ext fun x => ?_
  rw [thetaEquiv_apply, theta_apply, hf.apply_eq x, thetaX_visPair, thetaW_apply, coe_visPair_fst,
    visPair_snd, hA, resW_eq hf hA]

end Visible

theorem exists_pair_of_parity (f : SpaceB ≃ₗ[ℚ] SpaceB)
    (hmul : ∀ u v, f (gmul u v) = gmul (f u) (f v))
    (hiso : ∀ u v, bform (f u) (f v) = bform u v) (hcomm : ∀ u, f (xB u) = xB (f u)) :
    ∃ p : Pvis, thetaEquiv p = f ∧
      ∀ p' : Pvis, thetaEquiv p' = f ↔ p' = p ∨ p' = p * negPair := by
  have hf : IsParityAut f := ⟨hmul, hiso, hcomm⟩
  obtain ⟨g, hA, hu, -⟩ := hf.exists_latticeO
  refine ⟨visPair hf hA hu, thetaEquiv_visPair hf hA hu, fun p' => ?_⟩
  rw [← thetaEquiv_eq_iff, thetaEquiv_visPair hf hA hu]

theorem rational_parity_centralizer_equals_visible :
    (∀ f : SpaceB ≃ₗ[ℚ] SpaceB, ((∀ u v, f (gmul u v) = gmul (f u) (f v)) ∧
        (∀ u v, bform (f u) (f v) = bform u v) ∧ ∀ u, f (xB u) = xB (f u)) ↔ f ∈ Gvis) ∧
    (∀ f : SpaceB ≃ₗ[ℚ] SpaceB, (∀ u v, f (gmul u v) = gmul (f u) (f v)) →
      (∀ u v, bform (f u) (f v) = bform u v) → (∀ u, f (xB u) = xB (f u)) →
      ∃ p : Pvis, thetaEquiv p = f ∧
        ∀ p' : Pvis, thetaEquiv p' = f ↔ p' = p ∨ p' = p * negPair) ∧
    ∀ p : Pvis, (((p * negPair : Pvis).1.1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
        -((p.1.1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) ∧
      mat (p * negPair : Pvis).1.2 = -mat p.1.2 := by
  refine ⟨fun f => ⟨fun ⟨hmul, hiso, hcomm⟩ => ?_, fun hf => ?_⟩, exists_pair_of_parity,
    mul_negPair_eq⟩
  · obtain ⟨p, hp, -⟩ := exists_pair_of_parity f hmul hiso hcomm
    exact ⟨p, hp⟩
  · refine ⟨fun u v => (mem_Gvis_gmul hf u v).1, fun u v => (mem_Gvis_gmul hf u v).2, fun u => ?_⟩
    obtain ⟨p, rfl⟩ := hf
    rw [thetaEquiv_apply, thetaEquiv_apply, theta_xB]

end CFSG.Monster.Parity
