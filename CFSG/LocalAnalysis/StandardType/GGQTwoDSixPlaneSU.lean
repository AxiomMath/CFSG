module

public import CFSG.ClassicalGroups.Orthogonal.SixPlane.Basic
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthCentr
public import CFSG.LargeExtraspecial.OrthoF2SpRadical
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalGroups.Orthogonal.SixPlane (V Q Om rot planeOf rot_apply_inl rot_apply_inr
  rot_apply_of_ne Q_apply supp_le_Om rot_mem_supp planePerm planePerm_mem_Om planePerm_conj_rot)
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary (coordBlockSU)
open CFSG.LieType.Steinberg (normOne mem_normOne)
open CFSG.ClassicalInvolution.Models.OrthogonalPairs (QuadExt)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance] ZMod.algebra

noncomputable section

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

section Roots

omit [Finite K] [CharP K 2] in
theorem sixW_sq_add {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {a : ZMod 3} (ha : a = 1 ∨ a = -1) :
    (ω ^ a.val) ^ 2 + ω ^ a.val + 1 = 0 := by
  rcases ha with rfl | rfl
  · have h : (1 : ZMod 3).val = 1 := rfl
    rw [h, pow_one]
    exact hω
  · have h : (-1 : ZMod 3).val = 2 := rfl
    rw [h]
    linear_combination (ω ^ 2 - ω + 1) * hω

omit [Finite K] [CharP K 2] in
theorem sixW_pow_self {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {a : ZMod 3} (ha : a = 1 ∨ a = -1) :
    (ω ^ a.val) ^ a.val = ω := by
  rcases ha with rfl | rfl
  · have h : (1 : ZMod 3).val = 1 := rfl
    rw [h, pow_one, pow_one]
  · have h : (-1 : ZMod 3).val = 2 := rfl
    rw [h]
    linear_combination (ω * (ω - 1)) * hω

omit [Finite K] [CharP K 2] in
theorem sixW_ne_zero {w : K} (hw : w ^ 2 + w + 1 = 0) : w ≠ 0 := by
  rintro rfl
  simp at hw

omit [Finite K] in
theorem sixW_ne_one {w : K} (hw : w ^ 2 + w + 1 = 0) : w ≠ 1 := by
  rintro rfl
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  exact one_ne_zero (by linear_combination hw - h2 : (1 : K) = 0)

theorem sixW_mem_normOne {w : K} (hw : w ^ 2 + w + 1 = 0) :
    Units.mk0 w (sixW_ne_zero hw) ∈ normOne (unitaryInvolution K 2 1) := by
  rw [mem_normOne, Units.val_mk0, unitaryInvolution_apply]
  linear_combination (w - 1) * hw

@[expose] def sixZeta {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : normOne (unitaryInvolution K 2 1) :=
  ⟨Units.mk0 ω (sixW_ne_zero hω), sixW_mem_normOne hω⟩

theorem coe_sixZeta {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    (((sixZeta hω : normOne (unitaryInvolution K 2 1)) : Kˣ) : K) = ω := rfl

end Roots

section Plane

variable (ω : K) (c : Fin n → ZMod 3)

@[expose] def sixPlaneK : V n →ₗ[ZMod 2] (Fin n → K) where
  toFun v i := algebraMap (ZMod 2) K (v (Sum.inl i)) +
    algebraMap (ZMod 2) K (v (Sum.inr i)) * ω ^ (c i).val
  map_add' v v' := by
    funext i
    simp only [Pi.add_apply, map_add]
    ring
  map_smul' a v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def]
    ring

omit [Finite K] in
theorem sixPlaneK_apply (v : V n) (i : Fin n) :
    sixPlaneK ω c v i = algebraMap (ZMod 2) K (v (Sum.inl i)) +
      algebraMap (ZMod 2) K (v (Sum.inr i)) * ω ^ (c i).val :=
  rfl

variable {ω c}

omit [Finite K] in
theorem sixPlaneK_injective (hω : ω ^ 2 + ω + 1 = 0) (hc : ∀ i, c i = 1 ∨ c i = -1) :
    Function.Injective (sixPlaneK ω c) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have key : ∀ i, v (Sum.inl i) = 0 ∧ v (Sum.inr i) = 0 := by
    intro i
    have h := congrFun hv i
    rw [sixPlaneK_apply, Pi.zero_apply] at h
    have hw := sixW_sq_add hω (hc i)
    have hw0 := sixW_ne_zero hw
    have hw1 := sixW_ne_one hw
    generalize ω ^ (c i).val = w at h hw0 hw1
    generalize v (Sum.inl i) = x at h ⊢
    generalize v (Sum.inr i) = y at h ⊢
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h01 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
    rcases h01 x with rfl | rfl <;> rcases h01 y with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exact absurd (by simpa using h) hw0
    · simp at h
    · exact absurd (by simp at h; linear_combination h - h2) hw1
  funext k
  rcases k with i | i
  · exact (key i).1
  · exact (key i).2

theorem sixPlaneK_bijective (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1) : Function.Bijective (sixPlaneK ω c) := by
  refine (sixPlaneK_injective hω hc).bijective_of_nat_card_le ?_
  simp only [Nat.card_fun, Nat.card_sum, Nat.card_fin, Nat.card_zmod, hK]
  rw [← two_mul, pow_mul]
  norm_num

variable (ω c) in
@[expose] def sixPlaneEquiv (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1) : V n ≃ₗ[ZMod 2] (Fin n → K) :=
  LinearEquiv.ofBijective (sixPlaneK ω c) (sixPlaneK_bijective hK hω hc)

theorem sixPlaneEquiv_apply (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (v : V n) :
    sixPlaneEquiv ω c hK hω hc v = sixPlaneK ω c v :=
  rfl

theorem Qn_sixPlaneK (E : QuadExt (ZMod 2) K (unitaryInvolution K 2 1)) (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (v : V n) : Qn E n (sixPlaneK ω c v) = Q n v := by
  apply (algebraMap (ZMod 2) K).injective
  rw [algebraMap_Qn, Q_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sixPlaneK_apply, unitaryInvolution_apply]
  have hw := sixW_sq_add hω (hc i)
  generalize ω ^ (c i).val = w at hw ⊢
  have hA : algebraMap (ZMod 2) K (v (Sum.inl i)) ^ 2 = algebraMap (ZMod 2) K (v (Sum.inl i)) := by
    rw [← map_pow, ZMod.pow_card]
  have hB : algebraMap (ZMod 2) K (v (Sum.inr i)) ^ 2 = algebraMap (ZMod 2) K (v (Sum.inr i)) := by
    rw [← map_pow, ZMod.pow_card]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [map_add, map_mul]
  generalize algebraMap (ZMod 2) K (v (Sum.inl i)) = a at hA ⊢
  generalize algebraMap (ZMod 2) K (v (Sum.inr i)) = b at hB ⊢
  linear_combination (a + 3 * b * w) * hA + (3 * a * w ^ 2 + (b + 1) * w ^ 3 - 1) * hB +
    (3 * a * b + b * (w - 1)) * hw - 2 * a * b * h2

omit [Finite K] in
theorem sixPlaneK_rot (hω : ω ^ 2 + ω + 1 = 0) (hc : ∀ i, c i = 1 ∨ c i = -1) (i : Fin n)
    (v : V n) :
    sixPlaneK ω c (rot n i v) =
      fun j => (if j = i then ω ^ (c i).val else 1) * sixPlaneK ω c v j := by
  funext j
  rw [sixPlaneK_apply, sixPlaneK_apply]
  by_cases hj : j = i
  · subst hj
    rw [if_pos rfl, rot_apply_inl, rot_apply_inr, map_add]
    have hw := sixW_sq_add hω (hc j)
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination (-algebraMap (ZMod 2) K (v (Sum.inr j))) * hw +
      (algebraMap (ZMod 2) K (v (Sum.inr j)) * (1 + ω ^ (c j).val)) * h2
  · rw [if_neg hj, one_mul, rot_apply_of_ne i v (show planeOf (Sum.inl j) ≠ i from hj),
      rot_apply_of_ne i v (show planeOf (Sum.inr j) ≠ i from hj)]

omit [Finite K] in
theorem sixPlaneK_rot_pow (hω : ω ^ 2 + ω + 1 = 0) (hc : ∀ i, c i = 1 ∨ c i = -1) (i : Fin n)
    (k : ℕ) (v : V n) :
    sixPlaneK ω c ((rot n i ^ k) v) =
      fun j => (if j = i then (ω ^ (c i).val) ^ k else 1) * sixPlaneK ω c v j := by
  induction k with
  | zero =>
      funext j
      simp
  | succ k ih =>
      rw [pow_succ', LinearEquiv.mul_apply, sixPlaneK_rot hω hc i, ih]
      funext j
      beta_reduce
      split_ifs <;> ring

end Plane

section Unitary

variable {ω : K} {c : Fin n → ZMod 3}

variable (ω c) in
@[expose] def sixConj (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1) :
    (V n ≃ₗ[ZMod 2] V n) ≃* ((Fin n → K) ≃ₗ[ZMod 2] (Fin n → K)) where
  toFun g := ((sixPlaneEquiv ω c hK hω hc).symm.trans g).trans (sixPlaneEquiv ω c hK hω hc)
  invFun h := ((sixPlaneEquiv ω c hK hω hc).trans h).trans (sixPlaneEquiv ω c hK hω hc).symm
  left_inv g := by
    ext v
    simp
  right_inv h := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

theorem sixConj_apply (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (g : V n ≃ₗ[ZMod 2] V n) (v : V n) :
    sixConj ω c hK hω hc g (sixPlaneEquiv ω c hK hω hc v) = sixPlaneEquiv ω c hK hω hc (g v) := by
  simp [sixConj]

theorem sixConj_rot_pow (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (i : Fin n) :
    sixConj ω c hK hω hc (rot n i ^ (c i).val) =
      diagHom (ZMod 2) (unitaryInvolution K 2 1) n (Pi.mulSingle i (sixZeta hω)) := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨v, rfl⟩ := (sixPlaneEquiv ω c hK hω hc).surjective x
  rw [sixConj_apply, sixPlaneEquiv_apply, sixPlaneEquiv_apply, sixPlaneK_rot_pow hω hc,
    sixW_pow_self hω (hc i)]
  funext j
  rw [diagHom_apply, Pi.mulSingle_apply]
  split_ifs <;> simp [coe_sixZeta]

variable (ω c) in
@[expose] def sixSU (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1) : Su K 2 1 n →* (V n ≃ₗ[ZMod 2] V n) :=
  (sixConj ω c hK hω hc).symm.toMonoidHom.comp
    (suEndN (F := ZMod 2) (unitaryInvolution K 2 1) n)

theorem sixSU_apply (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (s : Su K 2 1 n) :
    sixSU ω c hK hω hc s =
      (sixConj ω c hK hω hc).symm (suEndN (F := ZMod 2) (unitaryInvolution K 2 1) n s) :=
  rfl

end Unitary

end

end CFSG.StandardType.QTwo

end
