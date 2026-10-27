module

public import CFSG.Monster.Visible.Pair
public import CFSG.Monster.Griess.Parity
import CFSG.Monster.Spin.DyadicNormalizer

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.ScalarKernel Matrix

theorem trace_conj_mul_conj {g M M' : Matrix (Fin 24) (Fin 24) ℚ} (hg : g * gᵀ = 1) :
    trace (gᵀ * M * g * (gᵀ * M' * g)) = trace (M * M') := by
  have e : gᵀ * M * g * (gᵀ * M' * g) = gᵀ * (M * M' * g) := by
    have h1 : g * (gᵀ * (M' * g)) = M' * g := by rw [← Matrix.mul_assoc, hg, Matrix.one_mul]
    simp only [Matrix.mul_assoc, h1]
  rw [e, trace_mul_comm, Matrix.mul_assoc (M * M') g gᵀ, hg, Matrix.mul_one]

theorem trace_thetaA_mul {g : Matrix (Fin 24) (Fin 24) ℚ} (hg : g * gᵀ = 1) (A A' : symMat) :
    trace ((thetaA g A : Matrix (Fin 24) (Fin 24) ℚ) * (thetaA g A' : Matrix (Fin 24) (Fin 24) ℚ))
      = trace ((A : Matrix (Fin 24) (Fin 24) ℚ) * (A' : Matrix (Fin 24) (Fin 24) ℚ)) := by
  rw [coe_thetaA, coe_thetaA]
  exact trace_conj_mul_conj hg

theorem sum_sum_mul_eq_trace (M N : SpaceW) :
    ∑ j, ∑ i, M j i * N j i = trace (M * Nᵀ) := by
  simp only [trace, diag, Matrix.mul_apply, transpose_apply]

theorem sum_sum_thetaW {s : Matrix SpinIdx SpinIdx ℚ} {g : Matrix (Fin 24) (Fin 24) ℚ}
    (hs : s * sᵀ = 1) (hg : g * gᵀ = 1) (N N' : SpaceW) :
    ∑ j, ∑ i, thetaW s g N j i * thetaW s g N' j i = ∑ j, ∑ i, N j i * N' j i := by
  rw [sum_sum_mul_eq_trace, sum_sum_mul_eq_trace, thetaW_apply, thetaW_apply]
  have e : sᵀ * N * g * (sᵀ * N' * g)ᵀ = sᵀ * (N * N'ᵀ * s) := by
    have h1 : g * (gᵀ * (N'ᵀ * s)) = N'ᵀ * s := by rw [← Matrix.mul_assoc, hg, Matrix.one_mul]
    simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc, h1]
  rw [e, trace_mul_comm, Matrix.mul_assoc (N * N'ᵀ) s sᵀ, hs, Matrix.mul_one]

theorem Xlift_dotProduct_Xlift {r r' : Q} (h : IsShortCoord (coordOf r))
    (h' : IsShortCoord (coordOf r')) :
    Xlift r ⬝ᵥ Xlift r' =
      if coordOf r = coordOf r' then sgn (centralCoord r) * sgn (centralCoord r') else 0 := by
  rw [Xlift_eq h, Xlift_eq h', smul_dotProduct, dotProduct_smul, single_dotProduct_single]
  by_cases hc : coordOf r = coordOf r'
  · rw [ite_eq_left (Subtype.ext hc), ite_eq_left hc, smul_eq_mul, smul_eq_mul, mul_one]
  · rw [ite_eq_right (fun h'' => hc (congrArg Subtype.val h'')), ite_eq_right hc, smul_zero,
      smul_zero]

theorem coordOf_eq_iff_projQ (x y : Q) : coordOf x = coordOf y ↔ projQ x = projQ y :=
  Multiplicative.toAdd.apply_eq_iff_eq

theorem coordOf_eq_iff (x y : Q) : coordOf x = coordOf y ↔ y⁻¹ * x ∈ Subgroup.zpowers zQ :=
  (coordOf_eq_iff_projQ x y).trans ((MonoidHom.eq_iff projQ).trans (by rw [ker_projQ, center_Q]))

theorem conjQ_mem_zpowers_iff (p : Pvis) (w : Q) :
    conjQ p w ∈ Subgroup.zpowers zQ ↔ w ∈ Subgroup.zpowers zQ := by
  constructor
  · intro hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hw
    have e : conjQ p (zQ ^ k) = conjQ p w := by rw [map_zpow, conjQ_zQ, hk]
    rw [← (conjQ p).injective e]
    exact Subgroup.zpow_mem_zpowers zQ k
  · intro hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    rw [map_zpow, conjQ_zQ]
    exact Subgroup.zpow_mem_zpowers zQ k

theorem coordOf_conjQ_inj (p : Pvis) {x y : Q} (h : coordOf (conjQ p x) = coordOf (conjQ p y)) :
    coordOf x = coordOf y := by
  rw [coordOf_eq_iff] at h ⊢
  rw [← map_inv (conjQ p) y, ← map_mul (conjQ p) y⁻¹ x, conjQ_mem_zpowers_iff] at h
  exact h

theorem thetaX_single_dotProduct (p : Pvis) (c d : ShortIdx) :
    thetaX p (Pi.single c 1) ⬝ᵥ thetaX p (Pi.single d 1) =
      (Pi.single c 1 : SpaceX) ⬝ᵥ Pi.single d 1 := by
  have hc : IsShortCoord (coordOf (conjQ p (rep c.1))) :=
    isShortCoord_conjQ p ((coordOf_rep c.1).symm ▸ c.2)
  have hd : IsShortCoord (coordOf (conjQ p (rep d.1))) :=
    isShortCoord_conjQ p ((coordOf_rep d.1).symm ▸ d.2)
  rw [thetaX_single, thetaX_single, single_dotProduct_single, Xlift_dotProduct_Xlift hc hd]
  by_cases hcd : c = d
  · subst hcd
    rw [ite_eq_left rfl, ite_eq_left rfl, sgn_mul_self]
  · have hne : coordOf (conjQ p (rep c.1)) ≠ coordOf (conjQ p (rep d.1)) := fun h =>
      hcd (Subtype.ext ((coordOf_rep c.1).symm.trans
        ((coordOf_conjQ_inj p h).trans (coordOf_rep d.1))))
    rw [ite_eq_right hne]
    exact (ite_eq_right hcd).symm

private def dotX : LinearMap.BilinForm ℚ SpaceX :=
  LinearMap.mk₂ ℚ (fun x y => x ⬝ᵥ y) (fun _ _ _ => add_dotProduct _ _ _)
    (fun _ _ _ => smul_dotProduct _ _ _) (fun _ _ _ => dotProduct_add _ _ _)
    (fun _ _ _ => dotProduct_smul _ _ _)

theorem dotProduct_thetaX (p : Pvis) (x y : SpaceX) : thetaX p x ⬝ᵥ thetaX p y = x ⬝ᵥ y := by
  have h : dotX.compl₁₂ (thetaX p) (thetaX p) = dotX :=
    LinearMap.ext_basis (Pi.basisFun ℚ ShortIdx) (Pi.basisFun ℚ ShortIdx) fun c d => by
      simp only [LinearMap.compl₁₂_apply, Pi.basisFun_apply, dotX, LinearMap.mk₂_apply]
      exact thetaX_single_dotProduct p c d
  have h' := LinearMap.congr_fun₂ h x y
  simpa only [LinearMap.compl₁₂_apply, dotX, LinearMap.mk₂_apply] using h'

theorem bform_theta (p : Pvis) (u v : SpaceB) : bform (theta p u) (theta p v) = bform u v := by
  rw [bform_apply, bform_apply, theta_apply, theta_apply]
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (trace_thetaA_mul (mat_mul_transpose p.1.2) u.1 v.1)
    (dotProduct_thetaX p u.2.1 v.2.1))
    (sum_sum_thetaW (isDyadicSpinNormalizer p).mul_transpose (mat_mul_transpose p.1.2) u.2.2 v.2.2)

theorem mat_mem_dyadic (g : latticeO) (i j : Fin 24) : mat g i j ∈ dyadic := by
  have hu := smul_eight_mem_codeLattice (C := Code.C) (Pi.single i (1 : ℤ))
  have h := congrFun (latVec_spec g hu).2 j
  have hr : ratVec ((8 : ℤ) • Pi.single i (1 : ℤ)) = (8 : ℚ) • Pi.single i 1 := by
    funext k
    simp only [ratVec, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  have e : (ratVec ((8 : ℤ) • Pi.single i (1 : ℤ)) ᵥ* mat g) j = 8 * mat g i j := by
    rw [hr, smul_vecMul, single_one_vecMul]
    rfl
  rw [e, ratVec_apply] at h
  have h' : mat g i j = ((latVec (mat g) ((8 : ℤ) • Pi.single i 1) j : ℤ) : ℚ) * ((2 : ℚ) ^ 3)⁻¹ := by
    rw [h]
    ring
  rw [h']
  exact dyadic.mul_mem (intCast_mem dyadic _) (inv_two_pow_mem_dyadic 3)

theorem mul_apply_mem_dyadic {l m n : Type*} [Fintype m] {M : Matrix l m ℚ} {N : Matrix m n ℚ}
    (hM : ∀ i j, M i j ∈ dyadic) (hN : ∀ i j, N i j ∈ dyadic) (i : l) (k : n) :
    (M * N) i k ∈ dyadic := by
  rw [Matrix.mul_apply]
  exact dyadic.sum_mem fun j _ => dyadic.mul_mem (hM i j) (hN j k)

theorem Xlift_apply_mem_dyadic (r : Q) (c : ShortIdx) : Xlift r c ∈ dyadic := by
  by_cases h : IsShortCoord (coordOf r)
  · rw [Xlift_eq h, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs
    · rw [mul_one]
      exact sgn_mem_dyadic _
    · rw [mul_zero]
      exact dyadic.zero_mem
  · rw [Xlift_eq_zero h]
    exact dyadic.zero_mem

theorem thetaX_eq_sum (p : Pvis) (x : SpaceX) :
    thetaX p x = ∑ c, x c • Xlift (conjQ p (rep c.1)) := by
  conv_lhs => rw [← (Pi.basisFun ℚ ShortIdx).sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, Pi.basisFun_apply, Pi.basisFun_repr, thetaX_single]

theorem thetaX_apply_mem_dyadic (p : Pvis) {x : SpaceX} (hx : ∀ c, x c ∈ dyadic) (d : ShortIdx) :
    thetaX p x d ∈ dyadic := by
  rw [thetaX_eq_sum, Finset.sum_apply]
  exact dyadic.sum_mem fun c _ => dyadic.mul_mem (hx c) (Xlift_apply_mem_dyadic _ d)

theorem isDyadicVec_theta (p : Pvis) {u : SpaceB} (hu : IsDyadicVec u) :
    IsDyadicVec (theta p u) := by
  have hg := mat_mem_dyadic p.1.2
  have hgT : ∀ i j, (mat p.1.2)ᵀ i j ∈ dyadic := fun i j => hg j i
  have hs := (isDyadicSpinNormalizer p).2.1
  have hsT : ∀ i j, ((p.1.1 : Matrix SpinIdx SpinIdx ℚ))ᵀ i j ∈ dyadic := fun i j => hs j i
  refine ⟨fun i j => ?_, fun c => ?_, fun j i => ?_⟩
  · show ((mat p.1.2)ᵀ * (u.1 : Matrix (Fin 24) (Fin 24) ℚ) * mat p.1.2) i j ∈ dyadic
    exact mul_apply_mem_dyadic (mul_apply_mem_dyadic hgT hu.1) hg i j
  · exact thetaX_apply_mem_dyadic p hu.2.1 c
  · show ((p.1.1 : Matrix SpinIdx SpinIdx ℚ)ᵀ * u.2.2 * mat p.1.2) j i ∈ dyadic
    exact mul_apply_mem_dyadic (mul_apply_mem_dyadic hsT hu.2.2) hg j i

theorem theta_mem_BR_iff (p : Pvis) {u : SpaceB} : theta p u ∈ BR ↔ u ∈ BR := by
  refine ⟨fun h => ?_, fun h => mem_BR_iff.2 (isDyadicVec_theta p (mem_BR_iff.1 h))⟩
  have h' := mem_BR_iff.2 (isDyadicVec_theta p⁻¹ (mem_BR_iff.1 h))
  rwa [← theta_mul_apply, mul_inv_cancel, theta_one_apply] at h'

theorem map_theta_BR (p : Pvis) : BR.map ((theta p).restrictScalars dyadic) = BR := by
  ext u
  refine ⟨?_, fun h => ⟨theta p⁻¹ u, (theta_mem_BR_iff p⁻¹).2 h, ?_⟩⟩
  · rintro ⟨v, hv, rfl⟩
    exact (theta_mem_BR_iff p).2 hv
  · show theta p (theta p⁻¹ u) = u
    rw [← theta_mul_apply, inv_mul_cancel, theta_one_apply]

theorem zU_conj (r : GL SpinIdx ℚ) : zU⁻¹ * r * zU = r := by
  rw [mul_assoc, inv_mul_eq_iff_eq_mul, zU, mul_neg_one, neg_one_mul]

theorem zU_mul_self : zU * zU = 1 := by
  rw [zU, neg_one_mul, neg_neg]

theorem isDyadicSpinNormalizer_zU : IsDyadicSpinNormalizer zU := by
  refine ⟨?_, fun i j => ?_, (image_conj_eq_Q_iff zU).2 fun r => by rw [zU_conj]⟩
  · rw [mem_orthogonalGroup_iff, coe_zU, zmat, transpose_neg, transpose_one, neg_mul_neg,
      Matrix.one_mul]
  · rw [coe_zU, zmat, Matrix.neg_apply, one_apply]
    split_ifs
    · exact dyadic.neg_mem dyadic.one_mem
    · rw [neg_zero]
      exact dyadic.zero_mem

theorem isCompatible_zU_negOneO : IsCompatible zU negOneO := by
  intro r r' h
  have hr : r' = r := Subtype.ext (h.trans (zU_conj r))
  exact (congrArg (fun x : Q => Multiplicative.toAdd (phi (QuotientGroup.mk x))) hr).trans
    (LinearMap.congr_fun (modTwoEnd_eq_one_of_mat (Or.inr mat_negOneO)) _).symm

@[expose] def negPair : Pvis := ⟨(zU, negOneO), isDyadicSpinNormalizer_zU, isCompatible_zU_negOneO⟩

theorem coe_negPair : (negPair : GL SpinIdx ℚ × latticeO) = (zU, negOneO) := rfl

theorem negOneO_ne_one : negOneO ≠ 1 := by
  intro h
  have h1 := congrArg (fun g => mat g 0 0) h
  simp only [mat_negOneO, mat_one, Matrix.neg_apply, one_apply_eq] at h1
  norm_num at h1

theorem negOneO_mul_self : negOneO * negOneO = 1 :=
  mat_injective (by rw [mat_mul, mat_negOneO, mat_one, neg_one_mul, neg_neg])

theorem negPair_ne_one : negPair ≠ 1 := fun h =>
  negOneO_ne_one (congrArg (fun p : Pvis => p.1.2) h)

theorem negPair_mul_self : negPair * negPair = 1 :=
  Subtype.ext (Prod.ext zU_mul_self negOneO_mul_self)

theorem orderOf_negPair : orderOf negPair = 2 :=
  orderOf_eq_prime (by rw [pow_two, negPair_mul_self]) negPair_ne_one

theorem negPair_mem_center : negPair ∈ Subgroup.center Pvis := by
  rw [Subgroup.mem_center_iff]
  intro p
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show p.1.1 * zU = zU * p.1.1
    rw [zU, mul_neg_one, neg_one_mul]
  · show p.1.2 * negOneO = negOneO * p.1.2
    exact mat_injective (by rw [mat_mul, mat_mul, mat_negOneO, mul_neg_one, neg_one_mul])

theorem thetaA_one (A : symMat) : thetaA 1 A = A :=
  Subtype.ext (by rw [coe_thetaA, transpose_one, Matrix.one_mul, Matrix.mul_one])

theorem thetaX_apply_of_conjQ_eq (p : Pvis) (hp : ∀ t, conjQ p t = t) (x : SpaceX) :
    thetaX p x = x := by
  have h : thetaX p = LinearMap.id := by
    refine (Pi.basisFun ℚ ShortIdx).ext fun c => ?_
    rw [Pi.basisFun_apply, LinearMap.id_apply]
    exact (thetaX_single p c).trans ((congrArg Xlift (hp _)).trans (Xlift_rep c))
  exact LinearMap.congr_fun h x

theorem conjQ_negPair (r : Q) : conjQ negPair r = r := Subtype.ext (zU_conj r)

theorem theta_negPair_apply (x : SpaceB) : theta negPair x = x := by
  rw [theta_apply]
  refine Prod.ext ?_ (Prod.ext (thetaX_apply_of_conjQ_eq _ conjQ_negPair _) ?_)
  · exact Subtype.ext (by
      show (mat negOneO)ᵀ * (x.1 : Matrix (Fin 24) (Fin 24) ℚ) * mat negOneO = x.1
      rw [mat_negOneO, transpose_neg, transpose_one, Matrix.neg_mul, Matrix.one_mul,
        Matrix.mul_neg, Matrix.mul_one, neg_neg])
  · show (zU : Matrix SpinIdx SpinIdx ℚ)ᵀ * x.2.2 * mat negOneO = x.2.2
    rw [mat_negOneO, coe_zU, zmat, transpose_neg, transpose_one, Matrix.neg_mul, Matrix.one_mul,
      Matrix.mul_neg, Matrix.mul_one, neg_neg]

theorem thetaEquiv_negPair : thetaEquiv negPair = 1 := LinearEquiv.ext theta_negPair_apply

theorem thetaEquiv_mul_negPair (p : Pvis) : thetaEquiv (p * negPair) = thetaEquiv p :=
  (thetaEquiv_mul p negPair).trans ((congrArg (· * thetaEquiv p) thetaEquiv_negPair).trans
    (one_mul _))

theorem entry_eq_of_theta_eq (p : Pvis) (h : ∀ x, theta p x = x) (i k : SpinIdx)
    (j l : Fin 24) : (p.1.1 : Matrix SpinIdx SpinIdx ℚ) i k * mat p.1.2 j l =
      (if k = i then 1 else 0) * (if l = j then 1 else 0) := by
  have h1 := congrArg (fun x : SpaceB => x.2.2 k l)
    ((theta_tensor p (Pi.single i 1) (Pi.single j 1)).symm.trans (h _))
  simp only [tensor, vecMulVec_apply, single_one_vecMul, Matrix.row_apply, Pi.single_apply] at h1
  exact h1

theorem eq_smul_one_of_entries {s : Matrix SpinIdx SpinIdx ℚ} {g : Matrix (Fin 24) (Fin 24) ℚ}
    (he : ∀ i k j l, s i k * g j l = (if k = i then 1 else 0) * (if l = j then 1 else 0)) :
    s = s 0 0 • (1 : Matrix SpinIdx SpinIdx ℚ) ∧
      g = (s 0 0)⁻¹ • (1 : Matrix (Fin 24) (Fin 24) ℚ) := by
  have hd : ∀ i j, s i i * g j j = 1 := fun i j => by
    rw [he, ite_eq_left rfl, ite_eq_left rfl, mul_one]
  have hs0 : ∀ i k, i ≠ k → s i k = 0 := fun i k hik => by
    have h1 := he i k 0 0
    rw [ite_eq_right (Ne.symm hik), zero_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_right (right_ne_zero_of_mul_eq_one (hd 0 0))
  have hg0 : ∀ j l, j ≠ l → g j l = 0 := fun j l hjl => by
    have h1 := he 0 0 j l
    rw [ite_eq_right (Ne.symm hjl), mul_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_left (left_ne_zero_of_mul_eq_one (hd 0 0))
  have hsi : ∀ i, s i i = s 0 0 := fun i =>
    mul_right_cancel₀ (right_ne_zero_of_mul_eq_one (hd 0 0)) ((hd i 0).trans (hd 0 0).symm)
  have hgj : ∀ j, g j j = (s 0 0)⁻¹ := fun j => eq_inv_of_mul_eq_one_right (hd 0 j)
  refine ⟨?_, ?_⟩
  · ext i k
    rw [Matrix.smul_apply, one_apply, smul_eq_mul]
    by_cases hik : i = k
    · subst hik
      rw [ite_eq_left rfl, mul_one, hsi]
    · rw [ite_eq_right hik, mul_zero, hs0 i k hik]
  · ext j l
    rw [Matrix.smul_apply, one_apply, smul_eq_mul]
    by_cases hjl : j = l
    · subst hjl
      rw [ite_eq_left rfl, mul_one, hgj]
    · rw [ite_eq_right hjl, mul_zero, hg0 j l hjl]

theorem eq_one_or_eq_negPair (p : Pvis) (h : ∀ x, theta p x = x) : p = 1 ∨ p = negPair := by
  obtain ⟨hs, hg⟩ := eq_smul_one_of_entries (entry_eq_of_theta_eq p h)
  set c := (p.1.1 : Matrix SpinIdx SpinIdx ℚ) 0 0 with hc
  have horth := (isDyadicSpinNormalizer p).mul_transpose
  rw [hs, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    smul_smul] at horth
  have hcc : c * c = 1 := by
    have h1 := congrFun (congrFun horth 0) 0
    rw [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at h1
    exact h1
  rcases mul_self_eq_one_iff.1 hcc with h1 | h1
  · left
    refine Subtype.ext (Prod.ext (Units.ext ?_) (mat_injective ?_))
    · rw [hs, h1, one_smul]
      rfl
    · rw [hg, h1, inv_one, one_smul]
      rfl
  · right
    refine Subtype.ext (Prod.ext (Units.ext ?_) (mat_injective ?_))
    · rw [hs, h1, neg_one_smul]
      exact coe_zU.symm
    · rw [hg, h1, inv_neg, inv_one, neg_one_smul]
      exact mat_negOneO.symm

theorem mem_ker_thetaHom_iff (p : Pvis) : p ∈ thetaHom.ker ↔ p = 1 ∨ p = negPair := by
  rw [MonoidHom.mem_ker, thetaHom_apply, ← MulOpposite.op_one, MulOpposite.op_inj]
  constructor
  · intro h
    exact eq_one_or_eq_negPair p fun x =>
      (thetaEquiv_apply p x).symm.trans (LinearEquiv.congr_fun h x)
  · rintro (rfl | rfl)
    · exact thetaEquiv_one
    · exact thetaEquiv_negPair

theorem coe_ker_thetaHom : (thetaHom.ker : Set Pvis) = {1, negPair} := by
  ext p
  rw [SetLike.mem_coe, mem_ker_thetaHom_iff, Set.mem_insert_iff, Set.mem_singleton_iff]

theorem ker_thetaHom_eq_zpowers : thetaHom.ker = Subgroup.zpowers negPair := by
  refine le_antisymm (fun p hp => ?_)
    (Subgroup.zpowers_le.2 ((mem_ker_thetaHom_iff _).2 (Or.inr rfl)))
  rcases (mem_ker_thetaHom_iff p).1 hp with rfl | rfl
  · exact one_mem _
  · exact Subgroup.mem_zpowers _

instance : (Subgroup.zpowers negPair).Normal :=
  ker_thetaHom_eq_zpowers ▸ thetaHom.normal_ker

theorem natCard_ker_thetaHom : Nat.card thetaHom.ker = 2 := by
  rw [ker_thetaHom_eq_zpowers, Nat.card_zpowers, orderOf_negPair]

theorem ker_thetaHom_le_center : thetaHom.ker ≤ Subgroup.center Pvis := by
  intro p hp
  rcases (mem_ker_thetaHom_iff p).1 hp with rfl | rfl
  · exact one_mem _
  · exact negPair_mem_center

theorem thetaEquiv_mem_Gvis (p : Pvis) : thetaEquiv p ∈ Gvis := ⟨p, rfl⟩

@[expose] def thetaGvis : Pvis →* (Gvis)ᵐᵒᵖ where
  toFun p := MulOpposite.op ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩
  map_one' := congrArg MulOpposite.op
    (Subtype.ext thetaEquiv_one : (⟨thetaEquiv 1, thetaEquiv_mem_Gvis 1⟩ : Gvis) = 1)
  map_mul' p q := congrArg MulOpposite.op
    (Subtype.ext (thetaEquiv_mul p q) : (⟨thetaEquiv (p * q), thetaEquiv_mem_Gvis _⟩ : Gvis) =
      ⟨thetaEquiv q, thetaEquiv_mem_Gvis q⟩ * ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩)

theorem thetaGvis_apply (p : Pvis) :
    thetaGvis p = MulOpposite.op ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ := rfl

theorem thetaGvis_surjective : Function.Surjective thetaGvis := by
  intro f
  obtain ⟨p, hp⟩ := mem_Gvis.1 f.unop.2
  exact ⟨p, MulOpposite.unop_injective (Subtype.ext hp)⟩

theorem ker_thetaGvis : thetaGvis.ker = Subgroup.zpowers negPair := by
  rw [← ker_thetaHom_eq_zpowers]
  ext p
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, thetaGvis_apply, thetaHom_apply]
  constructor
  · intro h
    have h1 : thetaEquiv p = 1 :=
      congrArg (fun x : (Gvis)ᵐᵒᵖ => (x.unop : SpaceB ≃ₗ[ℚ] SpaceB)) h
    exact congrArg MulOpposite.op h1
  · intro h
    have h1 : thetaEquiv p = 1 := MulOpposite.op_injective h
    exact congrArg MulOpposite.op
      (Subtype.ext h1 : (⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ : Gvis) = 1)

@[expose] def quotEquivGvis : Pvis ⧸ Subgroup.zpowers negPair ≃* (Gvis)ᵐᵒᵖ :=
  (QuotientGroup.quotientMulEquivOfEq ker_thetaGvis.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective thetaGvis thetaGvis_surjective)

theorem quotEquivGvis_mk (p : Pvis) :
    quotEquivGvis (QuotientGroup.mk p) = MulOpposite.op ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ :=
  rfl

theorem isDyadicSpinNormalizer_of_mem_Q {r : GL SpinIdx ℚ} (hr : r ∈ Q) :
    IsDyadicSpinNormalizer r := by
  have hr' := hr
  rw [← range_toGL] at hr'
  obtain ⟨x, rfl⟩ := hr'
  refine ⟨?_, fun i j => ?_, (image_conj_eq_Q_iff _).2 fun t => ?_⟩
  · rw [mem_orthogonalGroup_iff, coe_toGL]
    exact qmatR_mul_transpose_self _ _ _
  · rw [coe_toGL]
    exact qmatR_mem_dyadic _ _ _ i j
  · rw [Q.mul_mem_cancel_right hr, Q.mul_mem_cancel_left (Q.inv_mem hr)]

private theorem comm_conj {G : Type*} [CommGroup G] (a b : G) : a⁻¹ * b * a = b := by
  rw [mul_comm a⁻¹ b, mul_assoc, inv_mul_cancel, mul_one]

theorem projQ_conj (r t : Q) : projQ (r⁻¹ * t * r) = projQ t :=
  ((map_mul projQ (r⁻¹ * t) r).trans (congrArg (· * projQ r)
    ((map_mul projQ r⁻¹ t).trans (congrArg (· * projQ t) (map_inv projQ r))))).trans
    (comm_conj (projQ r) (projQ t))

theorem phi_mk_conj (r t : Q) :
    phi (QuotientGroup.mk (r⁻¹ * t * r)) = phi (QuotientGroup.mk t) :=
  congrArg (fun x => Multiplicative.ofAdd (phi0 (Multiplicative.toAdd x))) (projQ_conj r t)

theorem isCompatible_of_mem_Q (r : Q) : IsCompatible (r : GL SpinIdx ℚ) 1 := by
  intro t t' h
  have ht : t' = r⁻¹ * t * r := Subtype.ext h
  exact (congrArg (fun x : Q => Multiplicative.toAdd (phi (QuotientGroup.mk x))) ht).trans
    ((congrArg Multiplicative.toAdd (phi_mk_conj r t)).trans
      (LinearMap.congr_fun modTwoEnd_one _).symm)

theorem mem_Pvis_of_mem_Q (r : Q) : ((r : GL SpinIdx ℚ), (1 : latticeO)) ∈ Pvis :=
  ⟨isDyadicSpinNormalizer_of_mem_Q r.2, isCompatible_of_mem_Q r⟩

@[expose] def rhoPair : Q →* Pvis where
  toFun r := ⟨((r : GL SpinIdx ℚ), 1), mem_Pvis_of_mem_Q r⟩
  map_one' := rfl
  map_mul' _ _ := Subtype.ext (Prod.ext rfl (mul_one 1).symm)

theorem coe_rhoPair (r : Q) : (rhoPair r : GL SpinIdx ℚ × latticeO) = ((r : GL SpinIdx ℚ), 1) :=
  rfl

@[expose] def rhoEquiv (r : Q) : SpaceB ≃ₗ[ℚ] SpaceB := thetaEquiv (rhoPair r)

@[expose] def rho : Q →* (SpaceB ≃ₗ[ℚ] SpaceB)ᵐᵒᵖ := thetaHom.comp rhoPair

theorem rho_apply (r : Q) : rho r = MulOpposite.op (rhoEquiv r) := rfl

theorem rhoEquiv_mul (r r' : Q) : rhoEquiv (r * r') = rhoEquiv r' * rhoEquiv r :=
  (congrArg thetaEquiv (map_mul rhoPair r r')).trans (thetaEquiv_mul _ _)

theorem rhoEquiv_mem_Gvis (r : Q) : rhoEquiv r ∈ Gvis := ⟨rhoPair r, rfl⟩

theorem rhoPair_injective : Function.Injective rhoPair := fun _ _ h =>
  Subtype.ext (congrArg (fun p : Pvis => p.1.1) h)

theorem rho_injective : Function.Injective rho := by
  rw [injective_iff_map_eq_one]
  intro r hr
  have hk : rhoPair r ∈ thetaHom.ker := MonoidHom.mem_ker.2 hr
  rcases (mem_ker_thetaHom_iff _).1 hk with h | h
  · exact rhoPair_injective (h.trans (map_one rhoPair).symm)
  · exact absurd (congrArg (fun p : Pvis => p.1.2) h) (Ne.symm negOneO_ne_one)

theorem rhoEquiv_injective : Function.Injective rhoEquiv := fun _ _ h =>
  rho_injective (congrArg MulOpposite.op h)

@[expose] def rhoQ : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) := rho.range.unop

theorem mem_rhoQ {f : SpaceB ≃ₗ[ℚ] SpaceB} : f ∈ rhoQ ↔ ∃ r : Q, rhoEquiv r = f := by
  rw [rhoQ, Subgroup.mem_unop, MonoidHom.mem_range]
  simp only [rho_apply, MulOpposite.op_inj]

theorem rhoEquiv_mem_rhoQ (r : Q) : rhoEquiv r ∈ rhoQ := mem_rhoQ.2 ⟨r, rfl⟩

theorem rhoQ_le_Gvis : rhoQ ≤ Gvis := fun f hf => by
  obtain ⟨r, rfl⟩ := mem_rhoQ.1 hf
  exact rhoEquiv_mem_Gvis r

theorem rhoEquiv_symMat (r : Q) (A : symMat) : rhoEquiv r (A, 0, 0) = (A, 0, 0) :=
  (theta_symMat (rhoPair r) A).trans (congrArg (fun B => ((B, 0, 0) : SpaceB)) (thetaA_one A))

theorem conjQ_rhoPair (r t : Q) : conjQ (rhoPair r) t = r⁻¹ * t * r := Subtype.ext rfl

theorem rhoEquiv_Xlift (r t : Q) : rhoEquiv r (0, Xlift t, 0) = (0, Xlift (r⁻¹ * t * r), 0) :=
  (theta_Xlift (rhoPair r) t).trans
    (congrArg (fun x => ((0 : symMat), Xlift x, (0 : SpaceW))) (conjQ_rhoPair r t))

theorem rhoEquiv_tensor (r : Q) (q : SpinIdx → ℚ) (v : Fin 24 → ℚ) :
    rhoEquiv r (0, 0, tensor q v) =
      (0, 0, tensor (q ᵥ* ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)) v) :=
  (theta_tensor (rhoPair r) q v).trans (congrArg (fun w => ((0 : symMat), (0 : SpaceX),
    tensor (q ᵥ* ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)) w)) (vecMul_one v))

theorem conjQ_rhoPair_zQ (t : Q) : conjQ (rhoPair zQ) t = t :=
  Subtype.ext ((congrArg (fun s : GL SpinIdx ℚ => s⁻¹ * (t : GL SpinIdx ℚ) * s) coe_zQ).trans
    (zU_conj t))

theorem coe_coe_zQ : (((zQ : GL SpinIdx ℚ)) : Matrix SpinIdx SpinIdx ℚ) = -1 :=
  (congrArg Units.val coe_zQ).trans coe_zU

theorem rhoEquiv_zQ : rhoEquiv zQ = xB := by
  refine LinearEquiv.ext fun x => ?_
  rw [xB_apply]
  show theta (rhoPair zQ) x = _
  rw [theta_apply]
  refine Prod.ext (thetaA_one x.1) (Prod.ext (thetaX_apply_of_conjQ_eq _ conjQ_rhoPair_zQ _) ?_)
  show (((zQ : GL SpinIdx ℚ)) : Matrix SpinIdx SpinIdx ℚ)ᵀ * x.2.2 * mat 1 = -x.2.2
  rw [coe_coe_zQ, mat_one, Matrix.mul_one, transpose_neg, transpose_one, Matrix.neg_mul,
    Matrix.one_mul]

theorem compatible_pair_algebra_action_data :
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
  ⟨bform_theta, map_theta_BR, fun p _ => theta_mem_BR_iff p, coe_negPair, coe_zU,
    mat_negOneO, coe_ker_thetaHom, ker_thetaHom_eq_zpowers, natCard_ker_thetaHom,
    ker_thetaHom_le_center, quotEquivGvis_mk, mem_Pvis_of_mem_Q,
    fun r => ⟨coe_rhoPair r, rfl, rho_apply r, rhoEquiv_mem_Gvis r⟩, rhoEquiv_mul,
    rhoEquiv_injective, rho_injective, rhoEquiv_symMat, rhoEquiv_Xlift, rhoEquiv_tensor,
    fun _ => mem_rhoQ, rhoQ_le_Gvis, rhoEquiv_zQ⟩

end CFSG.Monster.Visible
