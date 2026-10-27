module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticSupport
public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticPlaneActions
public import Mathlib.LinearAlgebra.Pi
public import CFSG.LinearAlgebra.SL2CharTwoFixedVector

public section

namespace CFSG.StandardType.QTwoSymplecticCav

open Matrix Module Polynomial CFSG.Open
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.StandardType.WitSpNs
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCSpFull (spEnd_mul spEnd_one)

variable {K : Type} [Field K] {n : ℕ}

theorem finrank_le_two_mul_card_of_plane_support
    (W : Submodule K (Fin n ⊕ Fin n → K)) (I : Finset (Fin n))
    (hW : ∀ v ∈ W, ∀ a, a ∉ planeCoords I → v a = 0) :
    finrank K W ≤ 2 * I.card := by
  have hle : W ≤ Pi.spanSubset K (planeCoords I) := by
    intro v hv
    exact Pi.mem_spanSubset_iff.mpr (hW v hv)
  have hS : planeCoords I =
      ((I.disjSum I : Finset (Fin n ⊕ Fin n)) : Set (Fin n ⊕ Fin n)) := by
    ext a
    rcases a with a | a <;> simp [planeCoords, planeOf]
  calc finrank K W ≤ finrank K (Pi.spanSubset K (planeCoords I)) :=
        Submodule.finrank_mono hle
    _ = (planeCoords I).ncard := Pi.dim_spanSubset
    _ = 2 * I.card := by rw [hS]; simp [Finset.card_disjSum, two_mul]

theorem planeMat_mulVec_coord (P : Fin n → Matrix (Fin 2) (Fin 2) K)
    (v : Fin n ⊕ Fin n → K) (i : Fin n) (a : Fin 2) :
    (planeMat P *ᵥ v) (coord a i) = (P i *ᵥ (fun b => v (coord b i))) a := by
  fin_cases a
  all_goals
    simp only [planeMat, Matrix.of_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two]
    dsimp only [coord, plane, side]
    simp [ite_mul]


theorem pow_val_ne_one_of_quad [Finite K] (hK : Nat.card K = 2)
    {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1) (hM : M * M + M + 1 = 0)
    {a : ZMod 3} (ha : a ≠ 0) : M ^ a.val ≠ 1 := by
  let T : Matrix.SpecialLinearGroup (Fin 2) K := ⟨M, hdet⟩
  have h3 : T ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    exact SymplecticPlaneActions.pow_three_eq_one_of_sq_add_self_add_one hM
  have h1 : T ≠ 1 := by
    intro h
    have hm := congrArg (fun t : Matrix.SpecialLinearGroup (Fin 2) K =>
      (t : Matrix (Fin 2) (Fin 2) K)) h
    exact SymplecticPlaneActions.ne_one_of_sq_add_self_add_one hK hM hm
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf T = 3 := orderOf_eq_prime h3 h1
  intro h
  have ht : T ^ a.val = 1 := by
    apply Subtype.ext
    simpa only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] using h
  have hd : 3 ∣ a.val := by simpa only [ho] using orderOf_dvd_of_pow_eq_one ht
  have hz := Nat.dvd_iff_mod_eq_zero.mp hd
  rw [Nat.mod_eq_of_lt (ZMod.val_lt a)] at hz
  exact ha ((ZMod.val_eq_zero a).mp hz)

theorem eq_zero_of_fix_nonzero_plane_power [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {M : Matrix (Fin 2) (Fin 2) K}
    (hdet : M.det = 1) (hM : M * M + M + 1 = 0)
    {a : ZMod 3} (ha : a ≠ 0) {v : Fin 2 → K} (hv : M ^ a.val *ᵥ v = v) : v = 0 := by
  by_contra hne
  have hd : (M ^ a.val).det = 1 := by rw [Matrix.det_pow, hdet, one_pow]
  have hs := CFSG.LinearAlgebra.mul_self_eq_one_of_mulVec_eq_self (M ^ a.val) hd hne hv
  have hc : (M ^ a.val) ^ 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm a.val 3, pow_mul,
      SymplecticPlaneActions.pow_three_eq_one_of_sq_add_self_add_one hM, one_pow]
  have hp : M ^ a.val = 1 := by
    calc M ^ a.val = (M ^ a.val * M ^ a.val) * M ^ a.val := by rw [hs, one_mul]
      _ = 1 := by simpa only [pow_succ, pow_two, pow_one, pow_zero, one_mul] using hc
  exact pow_val_ne_one_of_quad hK hdet hM ha hp


theorem plane_zero_of_mem_fixed [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {M : Matrix (Fin 2) (Fin 2) K}
    (hdet : M.det = 1) (hM : M * M + M + 1 = 0)
    {c : Fin n → Multiplicative (ZMod 3)} {t : StatedSp n K}
    (ht : CFSG.LieType.Universal.Symplectic.SpExtras.mat n K t =
      planeMat (fun j => M ^ (Multiplicative.toAdd (c j)).val))
    {w : Fin n ⊕ Fin n → K} (hw : w ∈ LinearMap.ker (spEnd t - 1))
    {i : Fin n} (hc : c i ≠ 1) (b : Fin 2) : w (coord b i) = 0 := by
  have hca : Multiplicative.toAdd (c i) ≠ 0 := by
    intro hz
    apply hc
    change Multiplicative.ofAdd (Multiplicative.toAdd (c i)) = Multiplicative.ofAdd (0 : ZMod 3)
    exact congrArg Multiplicative.ofAdd hz
  have hfix : spEnd t w = w := sub_eq_zero.mp (LinearMap.mem_ker.mp hw)
  have hplane : M ^ (Multiplicative.toAdd (c i)).val *ᵥ (fun b => w (coord b i)) =
      (fun b => w (coord b i)) := by
    funext b
    have h := congrFun hfix (coord b i)
    change (CFSG.LieType.Universal.Symplectic.SpExtras.mat n K t *ᵥ w) (coord b i) = w (coord b i) at h
    rw [ht, planeMat_mulVec_coord] at h
    exact h
  exact congrFun (eq_zero_of_fix_nonzero_plane_power hK hdet hM hca hplane) b

theorem finrank_fixed_le_two_mul_zero_card [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {M : Matrix (Fin 2) (Fin 2) K}
    (hdet : M.det = 1) (hM : M * M + M + 1 = 0)
    {c : Fin n → Multiplicative (ZMod 3)} {t : StatedSp n K}
    (ht : CFSG.LieType.Universal.Symplectic.SpExtras.mat n K t =
      planeMat (fun j => M ^ (Multiplicative.toAdd (c j)).val)) :
    finrank K (LinearMap.ker (spEnd t - 1)) ≤
      2 * (Finset.univ.filter (fun j => c j = 1)).card := by
  classical
  apply finrank_le_two_mul_card_of_plane_support
  intro w hw a ha
  have hc : c (plane a) ≠ 1 := by
    intro hz
    apply ha
    change plane a ∈ Finset.univ.filter (fun j => c j = 1)
    simp [hz]
  have hcoord : coord (side a) (plane a) = a := by rcases a with a | a <;> simp [coord, side, plane]
  simpa only [hcoord] using plane_zero_of_mem_fixed hK hdet hM ht hw hc (side a)

theorem finrank_quad_le_two_mul_moving_card [CharP K 2]
    {M : Matrix (Fin 2) (Fin 2) K} {c : Fin n → Multiplicative (ZMod 3)}
    {t : StatedSp n K}
    (ht : CFSG.LieType.Universal.Symplectic.SpExtras.mat n K t =
      planeMat (fun j => M ^ (Multiplicative.toAdd (c j)).val)) :
    finrank K (primaryComponent (spEnd t) (X ^ 2 + X + 1)) ≤
      2 * (Finset.univ.filter (fun j => c j ≠ 1)).card := by
  classical
  apply finrank_le_two_mul_card_of_plane_support
  intro w hw a ha
  have hc : c (plane a) = 1 := by
    by_contra hz
    apply ha
    change plane a ∈ Finset.univ.filter (fun j => c j ≠ 1)
    simp [hz]
  have hcoord : coord (side a) (plane a) = a := by rcases a with a | a <;> simp [coord, side, plane]
  have hAt : ∀ v : Fin n ⊕ Fin n → K, (spEnd t v) a = v a := by
    intro v
    change (CFSG.LieType.Universal.Symplectic.SpExtras.mat n K t *ᵥ v) a = v a
    rw [ht]
    have h := planeMat_mulVec_coord
      (fun j => M ^ (Multiplicative.toAdd (c j)).val) v (plane a) (side a)
    have hp0 : M ^ (Multiplicative.toAdd (c (plane a))).val = 1 := by
      rw [hc]
      rfl
    rw [hcoord, hp0, Matrix.one_mulVec] at h
    simpa only [hcoord] using h
  have h := mem_primaryComponent.mp hw
  simp only [map_add, map_pow, map_mul, aeval_X, map_one, LinearMap.add_apply, pow_two,
    Module.End.mul_apply, Module.End.one_apply] at h
  have he := congrArg (fun v : Fin n ⊕ Fin n → K => v a) h
  simp only [Pi.add_apply, Pi.zero_apply] at he
  rw [hAt (spEnd t w), hAt w] at he
  have h2 : w a + w a = 0 := CharTwo.add_self_eq_zero (w a)
  simpa only [h2, zero_add] using he


theorem finrank_ker_aeval_conj (a t : StatedSp n K) (p : K[X]) :
    finrank K (LinearMap.ker (aeval (spEnd (a * t * a⁻¹)) p)) =
      finrank K (LinearMap.ker (aeval (spEnd t) p)) := by
  let Φ : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) :=
    { toFun := spEnd a
      invFun := spEnd a⁻¹
      map_add' := map_add (spEnd a)
      map_smul' := map_smul (spEnd a)
      left_inv := fun v => by
        rw [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one, Module.End.one_apply]
      right_inv := fun v => by
        rw [← Module.End.mul_apply, ← spEnd_mul, mul_inv_cancel, spEnd_one, Module.End.one_apply] }
  have hconj : spEnd (a * t * a⁻¹) = Φ.conjAlgEquiv K (spEnd t) := by
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.conjAlgEquiv_apply_apply]
    change spEnd (a * t * a⁻¹) v = spEnd a (spEnd t (spEnd a⁻¹ v))
    rw [spEnd_mul, spEnd_mul, Module.End.mul_apply, Module.End.mul_apply]
  have heval : aeval (spEnd (a * t * a⁻¹)) p = Φ.conjAlgEquiv K (aeval (spEnd t) p) := by
    rw [hconj]
    exact aeval_algHom_apply (Φ.conjAlgEquiv K) (spEnd t) p
  have hker : LinearMap.ker (aeval (spEnd (a * t * a⁻¹)) p) =
      (LinearMap.ker (aeval (spEnd t) p)).comap Φ.symm.toLinearMap := by
    ext v
    rw [LinearMap.mem_ker, Submodule.mem_comap, LinearMap.mem_ker, heval,
      LinearEquiv.conjAlgEquiv_apply_apply]
    simp only [LinearEquiv.coe_coe]
    constructor
    · intro h
      apply Φ.injective
      simpa only [map_zero] using h
    · intro h
      rw [h, map_zero]
  rw [hker, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

end CFSG.StandardType.QTwoSymplecticCav

end
