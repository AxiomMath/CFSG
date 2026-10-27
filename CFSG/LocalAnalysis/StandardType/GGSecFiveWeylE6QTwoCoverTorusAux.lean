module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTransvection
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModuleTorus
public import Mathlib.Algebra.Group.Subgroup.Map

public section

open CFSG.Assembly Matrix CFSG.SeitzReduction.UnitaryPilot

namespace CFSG.StandardType.USixTwo

variable {K : Type} [Field K] [Finite K]

@[expose]
noncomputable def genT (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (i : Fin 5) : torSU K :=
  USixTwo.diagTwoTor hω (show (0 : Fin 6) ≠ Fin.succ i from (Fin.succ_ne_zero i).symm)

private def genIdx : List (Fin 5) := [0, 1, 2, 3, 4]

private theorem genT_param (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (i : Fin 5) (j : Fin 6) (hj : j ≠ 0) :
    USixTwo.torParamHom (K := K) (genT hK hω i) j =
      if j = Fin.succ i then (USixTwo.unitOmega hω) ^ 2 else 1 := by
  have hmat := congrArg (fun G : GL (Fin 6) K =>
    ((G : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) j j)
    (USixTwo.diagGL_torParamHom (K := K) (genT hK hω i))
  rw [TauCeti.diagGL_coe, Matrix.diagonal_apply_eq] at hmat
  have hval : ((USixTwo.torParamHom (K := K) (genT hK hω i) j : Kˣ) : K) =
      (if j = Fin.succ i then (USixTwo.unitOmega hω) ^ 2 else 1 : Kˣ) := by
    rw [hmat]
    simp only [genT, USixTwo.diagTwoTor_matrix, USixTwo.diagTwo, Matrix.diagonal_apply]
    by_cases h : j = Fin.succ i
    · subst h
      simp [USixTwo.diagVec_other (show (0 : Fin 6) ≠ i.succ from (Fin.succ_ne_zero i).symm),
        USixTwo.unitOmega]
    · have hkj : j ≠ i.succ := h
      simp [USixTwo.diagVec_of_ne (i := 0) (j := i.succ) hj hkj, h]
  exact Units.ext hval

private noncomputable def genMap (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (c : Fin 5 → ZMod 3) : torSU K :=
  (genIdx.map (fun i => genT hK hω i ^ (c i).val)).prod

private theorem genMap_param_succ (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (c : Fin 5 → ZMod 3) (k : Fin 5) :
    USixTwo.torParamHom (K := K) (genMap hK hω c) (Fin.succ k) =
      ((USixTwo.unitOmega hω) ^ 2) ^ (c k).val := by
  fin_cases k <;>
    simp [genMap, genIdx, genT_param hK hω, USixTwo.unitOmega]

private theorem genMap_injective (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) : Function.Injective (genMap (K := K) hK hω) := by
  intro c d hcd
  funext k
  have h := congrArg (fun D : torSU K =>
    USixTwo.torParamHom (K := K) D (Fin.succ k)) hcd
  rw [genMap_param_succ hK hω, genMap_param_succ hK hω] at h
  have hord : orderOf ((USixTwo.unitOmega hω) ^ 2) = 3 := by
    rw [orderOf_pow, USixTwo.orderOf_unitOmega hK hω]
    norm_num
  have hmodeq : (c k).val ≡ (d k).val [MOD 3] := by
    have hm : (c k).val ≡ (d k).val [MOD orderOf ((USixTwo.unitOmega hω) ^ 2)] :=
      pow_eq_pow_iff_modEq.mp h
    rwa [hord] at hm
  have hvaleq : (c k).val = (d k).val :=
    hmodeq.eq_of_lt_of_lt (ZMod.val_lt _) (ZMod.val_lt _)
  exact ZMod.val_injective 3 hvaleq

private theorem closure_genT_eq_top (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) :
    Subgroup.closure (Set.range (genT (K := K) hK hω)) = ⊤ := by
  let H : Subgroup ↥(torSU K) := Subgroup.closure (Set.range (genT (K := K) hK hω))
  have hmem : ∀ c : Fin 5 → ZMod 3, genMap (K := K) hK hω c ∈ H := by
    intro c
    rw [genMap]
    refine Subgroup.list_prod_mem H ?_
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact Subgroup.pow_mem (K := H) (Subgroup.subset_closure (Set.mem_range_self i)) _
  have hcard_range : Nat.card (Set.range (genMap (K := K) hK hω)) = 3 ^ 5 := by
    have hcard : Nat.card (Fin 5 → ZMod 3) = 3 ^ 5 := by
      rw [Nat.card_fun]
      norm_num [ZMod.card]
    rw [← hcard]
    exact (Nat.card_congr (Equiv.ofInjective _ (genMap_injective hK hω))).symm
  have hge : 3 ^ 5 ≤ Nat.card H := by
    rw [← hcard_range]
    refine Nat.card_le_card_of_injective
      (fun x : Set.range (genMap (K := K) hK hω) => (⟨x.1, ?_⟩ : H)) ?_
    · obtain ⟨c, hc⟩ := x.2
      rw [← hc]
      exact hmem c
    · intro a b hab
      apply Subtype.ext
      exact congrArg (fun x : H => x.1) hab
  have hle : Nat.card H ≤ 3 ^ 5 := by
    have := H.card_le_card_group
    rwa [card_torSU hK] at this
  have hcardH : Nat.card H = Nat.card (torSU K) := by
    rw [le_antisymm hle hge, card_torSU hK]
  exact Subgroup.eq_top_of_card_eq (H := H) hcardH

theorem closure_genT_eq_torSU (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) :
    Subgroup.closure (Set.range (fun i : Fin 5 =>
      (genT (K := K) hK hω i : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))))) = USixTwo.torSU K := by
  have hmap := congrArg (fun H : Subgroup ↥(USixTwo.torSU K) =>
    H.map (USixTwo.torSU K).subtype) (closure_genT_eq_top hK hω)
  rw [MonoidHom.map_closure] at hmap
  have htop : (⊤ : Subgroup ↥(USixTwo.torSU K)).map (USixTwo.torSU K).subtype =
      USixTwo.torSU K := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  rw [htop, ← Set.range_comp] at hmap
  simpa [Function.comp_def] using hmap

private noncomputable def diagTwoUnit {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (i j : Fin 6) :
    Fin 6 → Kˣ :=
  fun k => if k = j then (USixTwo.unitOmega hω) ^ 2 else if k = i then USixTwo.unitOmega hω else 1

private theorem diagTwoUnit_coe {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {i j : Fin 6}
    (hij : i ≠ j) (k : Fin 6) :
    ((diagTwoUnit hω i j k : Kˣ) : K) = USixTwo.diagVec ω i j k := by
  by_cases hkj : k = j
  · subst hkj
    simp [diagTwoUnit, USixTwo.diagVec_other hij, USixTwo.unitOmega, Units.val_mk0]
  · by_cases hki : k = i
    · subst hki
      simp [diagTwoUnit, USixTwo.diagVec_self hij, USixTwo.unitOmega, Units.val_mk0, hkj]
    · simp [diagTwoUnit, USixTwo.diagVec_of_ne hki hkj, hki, hkj]

private theorem unitOmega_inv {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    (USixTwo.unitOmega hω)⁻¹ = (USixTwo.unitOmega hω) ^ 2 := by
  have h3 := USixTwo.unitOmega_cube hω
  have h2 : (USixTwo.unitOmega hω) ^ 2 * USixTwo.unitOmega hω = 1 := by
    rw [← pow_succ, show 2 + 1 = 3 by norm_num, h3]
  exact inv_eq_of_mul_eq_one_left h2

private theorem unitOmega_sq_inv {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    ((USixTwo.unitOmega hω) ^ 2)⁻¹ = USixTwo.unitOmega hω := by
  have h3 := USixTwo.unitOmega_cube hω
  have h2 : USixTwo.unitOmega hω * (USixTwo.unitOmega hω) ^ 2 = 1 := by
    rw [← pow_succ' (USixTwo.unitOmega hω) 2, show 2 + 1 = 3 by norm_num, h3]
  exact (eq_inv_of_mul_eq_one_left h2).symm

private theorem diagTwoUnit_swap {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {i j : Fin 6} (hij : i ≠ j) :
    (fun k => diagTwoUnit hω i j ((Equiv.swap i j)⁻¹ k)) =
      fun k => (diagTwoUnit hω i j k)⁻¹ := by
  funext k
  by_cases hkj : k = j
  · subst hkj
    simp [diagTwoUnit, Equiv.swap_apply_right, hij, unitOmega_sq_inv hω]
  · by_cases hki : k = i
    · subst hki
      simp [diagTwoUnit, Equiv.swap_apply_left, hij, hkj, unitOmega_inv hω]
    · have hki' : (Equiv.swap i j)⁻¹ k ≠ i := by
        intro h
        exact hkj (by simpa using congrArg (Equiv.swap i j) h)
      have hkj' : (Equiv.swap i j)⁻¹ k ≠ j := by
        intro h
        exact hki (by simpa using congrArg (Equiv.swap i j) h)
      have hki'' : (Equiv.swap i j) k ≠ i := by simpa using hki'
      have hkj'' : (Equiv.swap i j) k ≠ j := by simpa using hkj'
      simp [diagTwoUnit, hki, hkj, hki'', hkj'']

private theorem diagTwoGL_eq_diagGL {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {i j : Fin 6} (hij : i ≠ j) :
    USixTwo.diagTwoGL hω hij = TauCeti.diagGL (diagTwoUnit hω i j) := by
  apply Units.ext
  rw [TauCeti.diagGL_coe]
  change diagonal (USixTwo.diagVec ω i j) = diagonal (fun k => (diagTwoUnit hω i j k : K))
  congr 1
  funext k
  exact (diagTwoUnit_coe hω hij k).symm

private theorem permGLSU_conj_diagTwoGL (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {i j : Fin 6} (hij : i ≠ j) :
    permGLSU hK (Equiv.swap i j) * USixTwo.diagTwoGL hω hij *
      (permGLSU hK (Equiv.swap i j))⁻¹ = (USixTwo.diagTwoGL hω hij)⁻¹ := by
  rw [diagTwoGL_eq_diagGL hω hij]
  have h := TauCeti.permutationGL_mul_diagGL_mul_inv (Equiv.swap i j) (diagTwoUnit hω i j)
  rw [diagTwoUnit_swap hω hij] at h
  have hP : (permGLSU hK (Equiv.swap i j) : GL (Fin 6) K) =
      TauCeti.permutationGL (Equiv.swap i j) := coe_permGLSU hK _
  have hPinv : (↑((permGLSU hK (Equiv.swap i j))⁻¹) : GL (Fin 6) K) =
      (TauCeti.permutationGL (Equiv.swap i j))⁻¹ := by
    change ((permGLSU hK (Equiv.swap i j) : GL (Fin 6) K))⁻¹ =
      (TauCeti.permutationGL (Equiv.swap i j))⁻¹
    rw [hP]
  rw [hP, hPinv]
  rw [h]
  rw [← map_inv]
  rfl

theorem permSU_conj_image_diagTwoSU (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {i j : Fin 6} (hij : i ≠ j)
    (e : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) ≃*
      ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K 6))
    (he : ∀ x, (e x : GL (Fin 6) K) = (x : GL (Fin 6) K)) :
    permSU (fieldDataFour hK) (Equiv.swap i j) * e (USixTwo.diagTwoSU hω hij) *
      (permSU (fieldDataFour hK) (Equiv.swap i j))⁻¹ =
      (e (USixTwo.diagTwoSU hω hij))⁻¹ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [he (USixTwo.diagTwoSU hω hij), USixTwo.coe_diagTwoSU hω hij]
  have hp : (permSU (fieldDataFour hK) (Equiv.swap i j) : GL (Fin 6) K) =
      USixTwo.permGLSU hK (Equiv.swap i j) := by
    rw [coe_permSU_eq_permutationGL, USixTwo.coe_permGLSU, Equiv.swap_inv]
  rw [hp]
  exact permGLSU_conj_diagTwoGL hK hω hij

end CFSG.StandardType.USixTwo
