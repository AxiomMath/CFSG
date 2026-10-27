module

public import CFSG.LocalAnalysis.SteinbergSFFullCenterTorusComplement

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace FullCenterWeyl

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

section General

variable {G : Type*} [Group G]

theorem mem_or_mul_mem {N : Subgroup G} {t : G} (htt : t * t = 1)
    (htN : t ∈ normalizer (N : Set G)) {x : G} (hx : x ∈ N ⊔ zpowers t) :
    x ∈ N ∨ t * x ∈ N := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ (zpowers_le.mpr htN)] at hx
  obtain ⟨y, hy, c, hc, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hc
  rcases zpow_eq_one_or_eq htt j with h1 | h1
  · left
    simp only at h1 ⊢
    rw [h1, mul_one]
    exact hy
  · right
    simp only at h1 ⊢
    rw [h1, show t * (y * t) = t * y * t⁻¹ by rw [inv_eq_of_mul_eq_one_right htt, mul_assoc]]
    exact (mem_normalizer_iff.mp htN y).mp hy

theorem mul_mem_iff_of {N : Subgroup G} {t : G} (htt : t * t = 1)
    (htN : t ∈ normalizer (N : Set G)) {x y : G} (hx : x ∈ N ∨ t * x ∈ N)
    (hy : y ∈ N ∨ t * y ∈ N) : x * y ∈ N ↔ (x ∈ N ↔ y ∈ N) := by
  by_cases hxN : x ∈ N <;> by_cases hyN : y ∈ N
  · exact iff_of_true (mul_mem hxN hyN) (iff_of_true hxN hyN)
  · refine iff_of_false (fun hxy => hyN (by simpa using mul_mem (inv_mem hxN) hxy)) ?_
    exact fun h1 => hyN (h1.mp hxN)
  · refine iff_of_false (fun hxy => hxN (by simpa using mul_mem hxy (inv_mem hyN))) ?_
    exact fun h1 => hxN (h1.mpr hyN)
  · have htx' := hx.resolve_left hxN
    have hty' := hy.resolve_left hyN
    refine iff_of_true ?_ (iff_of_false hxN hyN)
    have e : x * y = (t * (t * x) * t⁻¹) * (t * y) := by
      rw [inv_eq_of_mul_eq_one_right htt]
      calc x * y = (t * t) * x * (t * t) * y := by rw [htt]; group
        _ = t * (t * x) * t * (t * y) := by group
    rw [e]
    exact mul_mem ((mem_normalizer_iff.mp htN _).mp htx') hty'

end General

section Model

variable {K : Type} [Field K]

variable (K) in
@[expose] def weylMat : Axis → Matrix (Fin 4) (Fin 4) K
  | .one => !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  | .two => !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

theorem weylMat_mul_self (i : Axis) : weylMat K i * weylMat K i = 1 := by
  cases i <;>
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [weylMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem weylMat_mem (i : Axis) : (weylMat K i)ᵀ * minorJ K * weylMat K i = minorJ K := by
  cases i <;>
  · ext k l
    rw [transpose_mul_minorJ_mul_apply, minorJ_apply]
    fin_cases k <;> fin_cases l <;> simp [weylMat]

variable (K) in
@[expose] def weylElt (i : Axis) : antiSp K :=
  ⟨⟨weylMat K i, weylMat K i, weylMat_mul_self i, weylMat_mul_self i⟩, weylMat_mem i⟩

theorem glMat_weylElt (i : Axis) : glMat (weylElt K i : GL (Fin 4) K) = weylMat K i := rfl

theorem weylElt_mul_self (i : Axis) : weylElt K i * weylElt K i = 1 :=
  antiSp_ext (weylMat_mul_self i)

theorem weylElt_inv (i : Axis) : (weylElt K i)⁻¹ = weylElt K i :=
  inv_eq_of_mul_eq_one_right (weylElt_mul_self i)

@[expose] def upperSL (x : K) : SL₂ K := ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def diagSL (c : Kˣ) : SL₂ K :=
  ⟨!![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

variable [CharP K 2]

@[expose] def swapSL : SL₂ K := ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

omit [CharP K 2] in
theorem coe_upperSL (x : K) :
    ((upperSL x : SL₂ K) : Matrix (Fin 2) (Fin 2) K) = !![1, x; 0, 1] := rfl

omit [CharP K 2] in
theorem coe_diagSL (c : Kˣ) :
    ((diagSL c : SL₂ K) : Matrix (Fin 2) (Fin 2) K) = !![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)] := rfl

theorem coe_swapSL : ((swapSL : SL₂ K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := rfl

theorem sl2_mem (S : Subgroup (SL₂ K)) (hu : ∀ x, upperSL x ∈ S) (hd : ∀ c : Kˣ, diagSL c ∈ S)
    (hw : swapSL ∈ S) (M : SL₂ K) : M ∈ S := by
  have hdet : (M : Matrix (Fin 2) (Fin 2) K) 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact M.2
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  by_cases hc : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · have ha : (M : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
      intro h0; rw [h0, hc] at hdet; simp at hdet
    have e : M = diagSL (Units.mk0 _ ha) * upperSL ((M : Matrix (Fin 2) (Fin 2) K) 0 1 *
        ((M : Matrix (Fin 2) (Fin 2) K) 0 0)⁻¹) := by
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_upperSL, coe_diagSL]
      rw [hc, mul_zero, sub_zero] at hdet
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc]
      · field_simp
      · field_simp
        linear_combination hdet
    rw [e]
    exact mul_mem (hd _) (hu _)
  · have e : M = upperSL ((M : Matrix (Fin 2) (Fin 2) K) 0 0 / M 1 0) * swapSL *
        diagSL (Units.mk0 _ hc) * upperSL ((M : Matrix (Fin 2) (Fin 2) K) 1 1 / M 1 0) := by
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, coe_upperSL, coe_upperSL, coe_diagSL, coe_swapSL]
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · field_simp
      · field_simp
        linear_combination (-1 : K) * hdet - h2
      · field_simp
    rw [e]
    exact mul_mem (mul_mem (mul_mem (hu _) hw) (hd _)) (hu _)

variable [Finite K]

omit [CharP K 2] [Finite K] in
theorem diagMat_eq (r s : K) :
    diagMat r s = !![r⁻¹, 0, 0, 0; 0, s⁻¹, 0, 0; 0, 0, s, 0; 0, 0, 0, r] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [diagMat]

theorem glMat_sHom_one (M : SL₂ K) :
    glMat (sHom K Axis.one M : GL (Fin 4) K) =
      !![(M : Matrix (Fin 2) (Fin 2) K) 0 0, M 0 1, 0, 0; M 1 0, M 1 1, 0, 0;
        0, 0, M 0 0, M 0 1; 0, 0, M 1 0, M 1 1] := by
  show minorMap (sMat (M : Matrix (Fin 2) (Fin 2) K)) = _
  ext A B
  fin_cases A <;> fin_cases B <;> simp [minorMap_apply, minorIdx_zero, minorIdx_one,
    minorIdx_two, minorIdx_three, sMat]

theorem glMat_sHom_two (M : SL₂ K) :
    glMat (sHom K Axis.two M : GL (Fin 4) K) = sMat (M : Matrix (Fin 2) (Fin 2) K) := rfl

theorem sHom_swapSL (i : Axis) : sHom K i swapSL = weylElt K i := by
  apply antiSp_ext
  cases i
  · rw [glMat_sHom_one, glMat_weylElt, coe_swapSL]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [weylMat]
  · rw [glMat_sHom_two, glMat_weylElt, coe_swapSL]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [weylMat, sMat]

theorem sHom_upperSL_mem (i : Axis) (x : K) : sHom K i (upperSL x) ∈ antiUnipotent K := by
  cases i
  · refine ⟨x, 0, 0, 0, antiSp_ext ?_⟩
    rw [glMat_sHom_one, glMat_uElt, coe_upperSL]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [uMat]
  · refine ⟨0, 0, 0, x, antiSp_ext ?_⟩
    rw [glMat_sHom_two, glMat_uElt, coe_upperSL]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [uMat, sMat]

theorem sHom_diagSL_mem (i : Axis) (c : Kˣ) : sHom K i (diagSL c) ∈ diagTorus K := by
  cases i
  · refine ⟨((c⁻¹ : Kˣ) : K), c, Units.ne_zero _, Units.ne_zero _, ?_⟩
    rw [glMat_sHom_one, coe_diagSL, diagMat_eq]
    ext a b
    fin_cases a <;> fin_cases b <;> simp
  · refine ⟨1, ((c⁻¹ : Kˣ) : K), one_ne_zero, Units.ne_zero _, ?_⟩
    rw [glMat_sHom_two, coe_diagSL, diagMat_eq]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [sMat]

theorem dHom_mem (i : Axis) (l : Kˣ) : dHom K i l ∈ diagTorus K := by
  cases i
  · refine ⟨((l⁻¹ : Kˣ) : K), ((l⁻¹ : Kˣ) : K), Units.ne_zero _, Units.ne_zero _, ?_⟩
    show minorMap (dMat l) = _
    ext a b
    fin_cases a <;> fin_cases b <;> simp [minorMap_apply, minorIdx_zero, minorIdx_one,
      minorIdx_two, minorIdx_three, dMat, diagMat]
  · refine ⟨((l⁻¹ : Kˣ) : K), 1, Units.ne_zero _, one_ne_zero, ?_⟩
    show dMat l = _
    ext a b
    fin_cases a <;> fin_cases b <;> simp [dMat, diagMat]

omit [CharP K 2] [Finite K] in
theorem weylMat_one_conj (r s : K) :
    weylMat K Axis.one * diagMat r s * weylMat K Axis.one = diagMat s r := by
  rw [diagMat_eq, diagMat_eq]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [weylMat, Matrix.mul_apply, Fin.sum_univ_four]

omit [CharP K 2] [Finite K] in
theorem weylMat_two_conj (r s : K) :
    weylMat K Axis.two * diagMat r s * weylMat K Axis.two = diagMat r s⁻¹ := by
  rw [diagMat_eq, diagMat_eq, inv_inv]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [weylMat, Matrix.mul_apply, Fin.sum_univ_four]

omit [CharP K 2] [Finite K] in
theorem weylElt_conj_mem_diagTorus (i : Axis) {δ : antiSp K} (hδ : δ ∈ diagTorus K) :
    weylElt K i * δ * (weylElt K i)⁻¹ ∈ diagTorus K := by
  obtain ⟨r, s, hr, hs, hδm⟩ := hδ
  have e : glMat ((weylElt K i * δ * (weylElt K i)⁻¹ : antiSp K) : GL (Fin 4) K) =
      weylMat K i * diagMat r s * weylMat K i := by
    rw [weylElt_inv]
    change glMat (weylElt K i : GL (Fin 4) K) * glMat (δ : GL (Fin 4) K) *
      glMat (weylElt K i : GL (Fin 4) K) = _
    rw [glMat_weylElt, hδm]
  cases i
  · exact ⟨s, r, hs, hr, by rw [e, weylMat_one_conj]⟩
  · exact ⟨r, s⁻¹, hr, inv_ne_zero hs, by rw [e, weylMat_two_conj]⟩

omit [CharP K 2] [Finite K] in
theorem weylElt_conj_mem_axisTorus (i : Axis) {δ : antiSp K} (hδ : δ ∈ axisTorus K i) :
    weylElt K i * δ * (weylElt K i)⁻¹ ∈ axisTorus K i := by
  cases i
  · obtain ⟨r, hr, hδm⟩ := hδ
    refine ⟨r⁻¹, inv_ne_zero hr, ?_⟩
    rw [weylElt_inv]
    change glMat (weylElt K _ : GL (Fin 4) K) * glMat (δ : GL (Fin 4) K) *
      glMat (weylElt K _ : GL (Fin 4) K) = _
    rw [glMat_weylElt, hδm, weylMat_one_conj, inv_inv]
  · obtain ⟨s, hs, hδm⟩ := hδ
    refine ⟨s⁻¹, inv_ne_zero hs, ?_⟩
    rw [weylElt_inv]
    change glMat (weylElt K _ : GL (Fin 4) K) * glMat (δ : GL (Fin 4) K) *
      glMat (weylElt K _ : GL (Fin 4) K) = _
    rw [glMat_weylElt, hδm, weylMat_two_conj]

omit [Finite K] in
theorem inv_conj_mem_radA1 {δ : antiSp K} {r : K} (hr : r ≠ 0)
    (hδ : glMat (δ : GL (Fin 4) K) = diagMat r r) (a b c d : K) :
    (uElt a b c d)⁻¹ * (δ⁻¹ * uElt a b c d * δ) ∈ radA1 K := by
  rw [diagTorus_conj hr hr hδ, uElt_inv, uElt_mul]
  have e : a + r * r⁻¹ * a = 0 := by rw [mul_inv_cancel₀ hr, one_mul, CharTwo.add_self_eq_zero]
  rw [e]
  exact ⟨_, _, _, rfl⟩

omit [Finite K] in
theorem inv_conj_mem_radA2 {δ : antiSp K} {r : K} (hr : r ≠ 0)
    (hδ : glMat (δ : GL (Fin 4) K) = diagMat r 1) (a b c d : K) :
    (uElt a b c d)⁻¹ * (δ⁻¹ * uElt a b c d * δ) ∈ radA2 K := by
  rw [diagTorus_conj hr one_ne_zero hδ, uElt_inv, uElt_mul]
  have e : d + 1 ^ 2 * d = 0 := by rw [one_pow, one_mul, CharTwo.add_self_eq_zero]
  rw [e]
  exact ⟨_, _, _, rfl⟩

@[expose] def radChar : Axis → K → K → K
  | .one => fun _ s => s
  | .two => fun r s => r * s⁻¹

end Model

section Weyl

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
local notation "𝐍[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) :
  Subgroup G) : Set G)
local notation "𝐌[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) :
  Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
local notation "𝐉" => pull φ (diagTorus K)
local notation "𝐉[" i "]" => pull φ (axisTorus K i)
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)

omit [Finite G] [CharP K 2] [Finite K] in
theorem w_mem_L (i : Axis) : 𝐰[i] ∈ L := (φ.symm _).2

omit [Finite G] [CharP K 2] [Finite K] in
theorem w_mul_self (i : Axis) : 𝐰[i] * 𝐰[i] = 1 := by
  rw [← coe_mul, ← map_mul, weylElt_mul_self, map_one]
  rfl

omit [Finite G] [CharP K 2] [Finite K] in
theorem w_inv (i : Axis) : 𝐰[i]⁻¹ = 𝐰[i] := inv_eq_of_mul_eq_one_right (w_mul_self i)

omit [Finite G] in
theorem w_eq (i : Axis) : 𝐰[i] = ((φ.symm (sHom K i swapSL) : L) : G) := by
  rw [sHom_swapSL]

theorem w_facts (h : FCHyp L K n φ t) (i : Axis) :
    𝐰[i] ∈ 𝐂 ∧ 𝐰[i] ∈ normalizer (𝐀[i] : Set G) ∧ 𝐰[i] ∈ normalizer (𝐔[i] : Set G) ∧
      𝐰[i] ∈ 𝐍[i] ∧ 𝐰[i] ∈ 𝐌[i] ∧ ∀ u ∈ 𝐔[i], u * 𝐰[i] = 𝐰[i] * u := by
  rw [w_eq]
  obtain ⟨h1, h2, h3, h4⟩ := h.symm_s_mem i swapSL
  exact ⟨h1, h2, h3, h4, h.symm_s_mem_M i swapSL,
    ((TwoCoreSetup.mem_pull_rootC_iff φ i).mp (symm_s_mem_rootC h.twoCore φ i swapSL)).2⟩

theorem conj_w_mem_A (h : FCHyp L K n φ t) (i : Axis) {a : G} (ha : a ∈ 𝐀[i]) :
    𝐰[i] * a * 𝐰[i]⁻¹ ∈ 𝐀[i] :=
  (mem_normalizer_iff.mp (w_facts h i).2.1 a).mp ha

theorem conj_w_mem_D (h : FCHyp L K n φ t) (i : Axis) {d : G} (hd : d ∈ 𝐃[i]) :
    𝐰[i] * d * 𝐰[i]⁻¹ ∈ 𝐃[i] :=
  conj_mem_pCore_map (w_facts h i).2.2.2.2.1 hd

theorem conj_w_mem_E (h : FCHyp L K n φ t) (i : Axis) {e : G} (he : e ∈ 𝐄[i]) :
    𝐰[i] * e * 𝐰[i]⁻¹ ∈ 𝐄[i] :=
  conj_mem_pCore_map (w_facts h i).2.2.2.1 he

omit [Finite G] [CharP K 2] [Finite K] in
theorem conj_w_mem_J (i : Axis) {j : G} (hj : j ∈ 𝐉) : 𝐰[i] * j * 𝐰[i]⁻¹ ∈ 𝐉 := by
  obtain ⟨δ, hδ, rfl⟩ := exists_eq_symm_of_mem_pull hj
  rw [symm_conj_eq]
  exact symm_mem_pull.mpr (weylElt_conj_mem_diagTorus i hδ)

omit [Finite G] [CharP K 2] [Finite K] in
theorem conj_w_mem_Ji (i : Axis) {j : G} (hj : j ∈ 𝐉[i]) : 𝐰[i] * j * 𝐰[i]⁻¹ ∈ 𝐉[i] := by
  obtain ⟨δ, hδ, rfl⟩ := exists_eq_symm_of_mem_pull hj
  rw [symm_conj_eq]
  exact symm_mem_pull.mpr (weylElt_conj_mem_axisTorus i hδ)

omit [Finite G] in
theorem psiG_conj_w (h : FCHyp L K n φ t) (i : Axis) {a : G} (ha : a ∈ 𝐀[i]) :
    psiG φ i (𝐰[i] * a * 𝐰[i]⁻¹) = ![psiG φ i a 1, psiG φ i a 0] := by
  rw [w_eq, (psiG_conj_s h.twoCore φ i swapSL ha).2, coe_swapSL]
  refine vec2_ext ?_ ?_ <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

omit [Finite G] in
theorem mem_U_of_conj_w (h : FCHyp L K n φ t) (i : Axis) {z : G} (hz : z ∈ 𝐙)
    (hwz : 𝐰[i] * z * 𝐰[i]⁻¹ ∈ 𝐙) : z ∈ 𝐔[i] := by
  have hzA : z ∈ 𝐀[i] := pull_mono φ (center_le_rootA i) hz
  have h1 := psiG_ZP_one h i hwz
  rw [psiG_conj_w h i hzA] at h1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
  refine (psiG_eq_zero_iff h.twoCore φ i hzA).mp (vec2_ext ?_ ?_)
  · simpa using h1
  · simpa using psiG_ZP_one h i hz

theorem exists_A_eq (h : FCHyp L K n φ t) (i : Axis) {a : G} (ha : a ∈ 𝐀[i]) :
    ∃ z ∈ 𝐙, ∃ u ∈ 𝐔[i.swap], a = z * (𝐰[i] * u * 𝐰[i]⁻¹) := by
  obtain ⟨u, hu, hψu⟩ := exists_psiG_U_swap h i (psiG φ i a 1)
  have huA : u ∈ 𝐀[i] := pull_mono φ ((rootU_le_center _).trans (center_le_rootA i)) hu
  have hwu := conj_w_mem_A h i huA
  refine ⟨a * (𝐰[i] * u * 𝐰[i]⁻¹)⁻¹, ?_, u, hu, by group⟩
  have hm : a * (𝐰[i] * u * 𝐰[i]⁻¹)⁻¹ ∈ 𝐀[i] := mul_mem ha (inv_mem hwu)
  refine (psiG_one_eq_zero_iff h i hm).mp ?_
  rw [psiG_mul h.twoCore φ i ha (inv_mem hwu), psiG_inv h.twoCore φ i hwu, psiG_conj_w h i huA,
    hψu]
  simp

omit [Finite G] in
theorem psiG_conj_torus (h : FCHyp L K n φ t) (i : Axis) {δ : antiSp K} {r s : K} (hr : r ≠ 0)
    (hs : s ≠ 0) (hδ : glMat (δ : GL (Fin 4) K) = diagMat r s) {a : G} (ha : a ∈ 𝐀[i]) :
    psiG φ i (((φ.symm δ : L) : G)⁻¹ * a * ((φ.symm δ : L) : G)) 1 =
      radChar i r s * psiG φ i a 1 := by
  obtain ⟨z, hz, rfl⟩ := exists_eq_symm_of_mem_pull ha
  have hn : 1 ≤ n := by have := h.setup.two_le; omega
  cases i
  · obtain ⟨b, c, d, rfl⟩ := hz
    rw [Setup.symm_conj (diagTorus_conj hr hs hδ 0 b c d), mul_zero,
      psiG_one_uElt h.setup.card_K hn, psiG_one_uElt h.setup.card_K hn]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, radChar]
    rw [mul_pow, sq_pow_pred h s]
  · obtain ⟨a', b, c, rfl⟩ := hz
    rw [Setup.symm_conj (diagTorus_conj hr hs hδ a' b c 0), mul_zero, psiG_two_uElt,
      psiG_two_uElt]
    simp [radChar]

theorem psiG_inv_conj_torus (h : FCHyp L K n φ t) (i : Axis) {δ : antiSp K} {r s : K}
    (hr : r ≠ 0) (hs : s ≠ 0) (hδ : glMat (δ : GL (Fin 4) K) = diagMat r s) {a : G}
    (ha : a ∈ 𝐀[i]) :
    a⁻¹ * (((φ.symm δ : L) : G)⁻¹ * a * ((φ.symm δ : L) : G)) ∈ 𝐀[i] ∧
      psiG φ i (a⁻¹ * (((φ.symm δ : L) : G)⁻¹ * a * ((φ.symm δ : L) : G))) 1 =
        (radChar i r s - 1) * psiG φ i a 1 := by
  have hτ : ((φ.symm δ : L) : G) ∈ 𝐉 := symm_mem_pull.mpr ⟨r, s, hr, hs, hδ⟩
  have hτa : ((φ.symm δ : L) : G)⁻¹ * a * ((φ.symm δ : L) : G) ∈ 𝐀[i] := by
    have := (mem_normalizer_iff.mp (FCHyp.torus_le_normalizer_A i (inv_mem hτ)) a).mp ha
    rwa [inv_inv] at this
  refine ⟨mul_mem (inv_mem ha) hτa, ?_⟩
  rw [psiG_mul h.twoCore φ i (inv_mem ha) hτa, psiG_inv h.twoCore φ i ha, Pi.add_apply,
    Pi.neg_apply, psiG_conj_torus h i hr hs hδ ha]
  ring

omit [Finite G] [Finite K] in
theorem pairTorus_of {δ : antiSp K} {r s : K} (hr : r ≠ 0)
    (hs : s ≠ 0) (hδ : glMat (δ : GL (Fin 4) K) = diagMat r s) (i : Axis)
    (h1 : ∀ u ∈ antiUnipotent K, u⁻¹ * (δ⁻¹ * u * δ) ∈ rootA K i)
    (h2 : ∀ u ∈ antiUnipotent K, u⁻¹ * (δ * u * δ⁻¹) ∈ rootA K i) :
    ((φ.symm δ : L) : G) ∈ 𝐉 ∧
      (∀ p ∈ 𝐏, p⁻¹ * (((φ.symm δ : L) : G)⁻¹ * p * ((φ.symm δ : L) : G)) ∈ 𝐀[i]) ∧
      (∀ p ∈ 𝐏, p⁻¹ * (((φ.symm δ : L) : G) * p * ((φ.symm δ : L) : G)⁻¹) ∈ 𝐀[i]) := by
  refine ⟨symm_mem_pull.mpr ⟨r, s, hr, hs, hδ⟩, fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := exists_eq_symm_of_mem_pull hp
    have e : ((φ.symm u : L) : G)⁻¹ * (((φ.symm δ : L) : G)⁻¹ * ((φ.symm u : L) : G) *
        ((φ.symm δ : L) : G)) = ((φ.symm (u⁻¹ * (δ⁻¹ * u * δ)) : L) : G) := by
      simp [map_mul, map_inv]
    rw [e]
    exact symm_mem_pull.mpr (h1 u hu)
  · obtain ⟨u, hu, rfl⟩ := exists_eq_symm_of_mem_pull hp
    have e : ((φ.symm u : L) : G)⁻¹ * (((φ.symm δ : L) : G) * ((φ.symm u : L) : G) *
        ((φ.symm δ : L) : G)⁻¹) = ((φ.symm (u⁻¹ * (δ * u * δ⁻¹)) : L) : G) := by
      simp [map_mul, map_inv]
    rw [e]
    exact symm_mem_pull.mpr (h2 u hu)

omit [Finite G] in
theorem exists_pairTorus (h : FCHyp L K n φ t) (i : Axis) :
    ∃ τ ∈ 𝐉, (∀ p ∈ 𝐏, p⁻¹ * (τ⁻¹ * p * τ) ∈ 𝐀[i]) ∧ (∀ p ∈ 𝐏, p⁻¹ * (τ * p * τ⁻¹) ∈ 𝐀[i]) ∧
      ∃ μ : K, μ ≠ 1 ∧ ∀ a ∈ 𝐀[i], psiG φ i (τ⁻¹ * a * τ) 1 = μ * psiG φ i a 1 := by
  have hK2 : 2 < Nat.card K := by have := h.four_le_card; omega
  obtain ⟨r, hr0, hr1⟩ := exists_ne_zero_ne hK2 (1 : K)
  cases i
  · obtain ⟨δ, -, hδ⟩ := exists_diagTorus (K := K) hr0 hr0
    have hδ' := glMat_inv_eq hr0 hr0 hδ
    obtain ⟨hτ, h1, h2⟩ := pairTorus_of (φ := φ) hr0 hr0 hδ Axis.one
      (fun u hu => by
        obtain ⟨a, b, c, d, rfl⟩ := hu
        exact inv_conj_mem_radA1 hr0 hδ a b c d)
      (fun u hu => by
        obtain ⟨a, b, c, d, rfl⟩ := hu
        have := inv_conj_mem_radA1 (inv_ne_zero hr0) hδ' a b c d
        rwa [inv_inv] at this)
    exact ⟨_, hτ, h1, h2, r, Ne.symm hr1, fun a ha => psiG_conj_torus h _ hr0 hr0 hδ ha⟩
  · obtain ⟨δ, -, hδ⟩ := exists_diagTorus (K := K) hr0 one_ne_zero
    have hδ' := glMat_inv_eq hr0 one_ne_zero hδ
    rw [inv_one] at hδ'
    obtain ⟨hτ, h1, h2⟩ := pairTorus_of (φ := φ) hr0 one_ne_zero hδ Axis.two
      (fun u hu => by
        obtain ⟨a, b, c, d, rfl⟩ := hu
        exact inv_conj_mem_radA2 hr0 hδ a b c d)
      (fun u hu => by
        obtain ⟨a, b, c, d, rfl⟩ := hu
        have := inv_conj_mem_radA2 (inv_ne_zero hr0) hδ' a b c d
        rwa [inv_inv] at this)
    refine ⟨_, hτ, h1, h2, r, Ne.symm hr1, fun a ha => ?_⟩
    rw [psiG_conj_torus h _ hr0 one_ne_zero hδ ha]
    simp [radChar]

theorem exists_good_Ji (h : FCHyp L K n φ t) (i : Axis) :
    ∃ g ∈ 𝐉[i], ∀ a ∈ 𝐀[i], a⁻¹ * (g⁻¹ * a * g) ∈ 𝐙 → a ∈ 𝐙 := by
  have hK2 : 2 < Nat.card K := by have := h.four_le_card; omega
  obtain ⟨r, hr0, hr1⟩ := exists_ne_zero_ne hK2 (1 : K)
  have key : ∀ {δ : antiSp K} {r' s' : K}, r' ≠ 0 → s' ≠ 0 →
      glMat (δ : GL (Fin 4) K) = diagMat r' s' → radChar i r' s' ≠ 1 →
      ∀ a ∈ 𝐀[i], a⁻¹ * (((φ.symm δ : L) : G)⁻¹ * a * ((φ.symm δ : L) : G)) ∈ 𝐙 → a ∈ 𝐙 := by
    intro δ r' s' hr' hs' hδ hμ a ha haZ
    obtain ⟨hm, hψ⟩ := psiG_inv_conj_torus h i hr' hs' hδ ha
    rw [(psiG_one_eq_zero_iff h i hm).mpr haZ] at hψ
    refine (psiG_one_eq_zero_iff h i ha).mp ?_
    exact (mul_eq_zero.mp hψ.symm).resolve_left (sub_ne_zero.mpr hμ)
  cases i
  · obtain ⟨δ, -, hδ⟩ := exists_diagTorus (K := K) hr0 (inv_ne_zero hr0)
    refine ⟨_, symm_mem_pull.mpr ⟨r, hr0, hδ⟩, key hr0 (inv_ne_zero hr0) hδ ?_⟩
    simp only [radChar]
    intro h1
    exact hr1 (by rw [← inv_inv r, h1, inv_one])
  · obtain ⟨δ, -, hδ⟩ := exists_diagTorus (K := K) one_ne_zero hr0
    refine ⟨_, symm_mem_pull.mpr ⟨r, hr0, hδ⟩, key one_ne_zero hr0 hδ ?_⟩
    simp only [radChar, one_mul]
    intro h1
    exact hr1 (by rw [← inv_inv r, h1, inv_one])

theorem exists_Jswap_conj (h : FCHyp L K n φ t) (i : Axis) {a a' : G} (ha : a ∈ 𝐀[i])
    (ha' : a' ∈ 𝐀[i]) (haZ : a ∉ 𝐙) (ha'Z : a' ∉ 𝐙) :
    ∃ g ∈ 𝐉[i.swap], (g⁻¹ * a * g)⁻¹ * a' ∈ 𝐙 := by
  have hx : psiG φ i a 1 ≠ 0 := fun h0 => haZ ((psiG_one_eq_zero_iff h i ha).mp h0)
  have hx' : psiG φ i a' 1 ≠ 0 := fun h0 => ha'Z ((psiG_one_eq_zero_iff h i ha').mp h0)
  have key : ∀ {δ : antiSp K} {r' s' : K}, r' ≠ 0 → s' ≠ 0 →
      glMat (δ : GL (Fin 4) K) = diagMat r' s' →
      radChar i r' s' = psiG φ i a' 1 / psiG φ i a 1 →
      (((φ.symm δ : L) : G)⁻¹ * a * ((φ.symm δ : L) : G))⁻¹ * a' ∈ 𝐙 := by
    intro δ r' s' hr' hs' hδ hμ
    have hτ : ((φ.symm δ : L) : G) ∈ 𝐉 := symm_mem_pull.mpr ⟨r', s', hr', hs', hδ⟩
    have hτa : ((φ.symm δ : L) : G)⁻¹ * a * ((φ.symm δ : L) : G) ∈ 𝐀[i] := by
      have := (mem_normalizer_iff.mp (FCHyp.torus_le_normalizer_A i (inv_mem hτ)) a).mp ha
      rwa [inv_inv] at this
    refine (psiG_one_eq_zero_iff h i (mul_mem (inv_mem hτa) ha')).mp ?_
    rw [psiG_mul h.twoCore φ i (inv_mem hτa) ha', psiG_inv h.twoCore φ i hτa, Pi.add_apply,
      Pi.neg_apply, psiG_conj_torus h i hr' hs' hδ ha, hμ]
    field_simp
    ring
  have hq : psiG φ i a' 1 / psiG φ i a 1 ≠ 0 := div_ne_zero hx' hx
  cases i
  · obtain ⟨δ, -, hδ⟩ := exists_diagTorus (K := K) one_ne_zero hq
    exact ⟨_, symm_mem_pull.mpr ⟨_, hq, hδ⟩, key one_ne_zero hq hδ rfl⟩
  · obtain ⟨r, hr⟩ := exists_sq_eq (psiG φ Axis.two a' 1 / psiG φ Axis.two a 1)
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hq (by rw [← hr]; ring)
    obtain ⟨δ, -, hδ⟩ := exists_diagTorus (K := K) hr0 (inv_ne_zero hr0)
    refine ⟨_, symm_mem_pull.mpr ⟨r, hr0, hδ⟩, key hr0 (inv_ne_zero hr0) hδ ?_⟩
    rw [← hr]
    simp only [radChar, inv_inv]
    ring

end Weyl

section Products

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
local notation "𝐍[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) :
  Subgroup G) : Set G)
local notation "𝐌[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) :
  Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐐[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐃[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐑[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐄[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐇" => (𝐐[Axis.one] ⊔ 𝐐[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
local notation "𝐉" => pull φ (diagTorus K)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐉[" i "]" => pull φ (axisTorus K i)
set_option quotPrecheck false in
local notation "𝐖[" i "]" => (𝐅 ⊓ centralizer (𝐉[i] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊[" i "]" => (𝐀[i] ⊔ (𝐅 ⊓ 𝐃[i]) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊⋆" => (𝐊[Axis.one] ⊔ 𝐊[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐋[" i "]" => (𝐅 ⊔ 𝐀[i] : Subgroup G)

theorem A_le_D (h : FCHyp L K n φ t) (i : Axis) : 𝐀[i] ≤ 𝐃[i] :=
  le_sup_right.trans (h.B_le_D i)

theorem A_le_H (h : FCHyp L K n φ t) (i : Axis) : 𝐀[i] ≤ 𝐇 := (A_le_D h i).trans (D_le_H i)

omit [Finite G] [Finite K] in
theorem P_le_H : 𝐏 ≤ 𝐇 := fun _ hp => Q_le_H (mem_sup_left hp)

theorem conj_H_mem_A (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ 𝐇) {a : G}
    (ha : a ∈ 𝐀[i]) : x * a * x⁻¹ ∈ 𝐀[i] :=
  (mem_normalizer_iff.mp (h.N_le_normalizer_A i (R_le_N h i (H_le_R h i hx))) a).mp ha

theorem conj_H_mem_D (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ 𝐇) {d : G}
    (hd : d ∈ 𝐃[i]) : x * d * x⁻¹ ∈ 𝐃[i] :=
  h.conj_mem_D i (R_le_N h i (H_le_R h i hx)) hd

theorem A_comm_D (h : FCHyp L K n φ t) (i : Axis) {a : G} (ha : a ∈ 𝐀[i]) {d : G}
    (hd : d ∈ 𝐃[i]) : a * d = d * a :=
  (D_comm_A h i hd ha).symm

omit [Finite G] [Finite K] in
theorem A_le_C (h : FCHyp L K n φ t) (i : Axis) : 𝐀[i] ≤ 𝐂 := fun _ ha =>
  h.setup.L_le (pull_le φ _ ha)

theorem A_inf_F (h : FCHyp L K n φ t) (i : Axis) : 𝐀[i] ⊓ 𝐅 = 𝐙 :=
  le_antisymm (fun _ hx => mem_ZP_of_mem_F h hx.2 (A_le_C h i hx.1))
    (le_inf (pull_mono φ (center_le_rootA i)) (ZP_le_F h))

theorem A_inf_Fi (h : FCHyp L K n φ t) (i : Axis) : 𝐀[i] ⊓ (𝐅 ⊓ 𝐃[i]) = 𝐙 :=
  le_antisymm ((inf_le_inf_left _ inf_le_left).trans (A_inf_F h i).le)
    (le_inf (pull_mono φ (center_le_rootA i)) (ZP_le_Fi h i))

theorem conj_H_mem_Fi (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ 𝐇) {f : G}
    (hf : f ∈ 𝐅 ⊓ 𝐃[i]) : x * f * x⁻¹ ∈ 𝐅 ⊓ 𝐃[i] :=
  ⟨conj_H_mem_F h hx hf.1, conj_H_mem_D h i hx hf.2⟩

theorem Fi_le_normalizer_A (h : FCHyp L K n φ t) (i : Axis) :
    𝐅 ⊓ 𝐃[i] ≤ normalizer (𝐀[i] : Set G) := fun _ hx =>
  mem_normalizer_of_conj_le fun _ ha => conj_H_mem_A h i (F_le_H h hx.1) ha

theorem K_mul (h : FCHyp L K n φ t) (i : Axis) :
    (𝐀[i] : Set G) * ((𝐅 ⊓ 𝐃[i] : Subgroup G) : Set G) = 𝐊[i] :=
  (coe_mul_of_right_le_normalizer_left _ _ (Fi_le_normalizer_A h i)).symm

theorem card_K (h : FCHyp L K n φ t) (i : Axis) : Nat.card 𝐊[i] = Nat.card K ^ 4 := by
  have h1 := card_sup_mul_card_inf 𝐀[i] (𝐅 ⊓ 𝐃[i]) (Fi_le_normalizer_A h i)
  rw [A_inf_Fi h i, FCHyp.card_ZP, card_Fi h, card_pull, card_rootA] at h1
  have hq : 0 < Nat.card K ^ 2 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)

theorem K_le_D (h : FCHyp L K n φ t) (i : Axis) : 𝐊[i] ≤ 𝐃[i] := sup_le (A_le_D h i) inf_le_right

theorem K_le_H (h : FCHyp L K n φ t) (i : Axis) : 𝐊[i] ≤ 𝐇 := (K_le_D h i).trans (D_le_H i)

theorem K_comm (h : FCHyp L K n φ t) (i : Axis) {x y : G} (hx : x ∈ 𝐊[i]) (hy : y ∈ 𝐊[i]) :
    x * y = y * x := by
  rw [← SetLike.mem_coe, ← K_mul h i] at hx hy
  obtain ⟨a, ha, f, hf, rfl⟩ := hx
  obtain ⟨b, hb, g, hg, rfl⟩ := hy
  have hab : Commute a b := A_mul_comm h i ha hb
  have hag : Commute a g := A_comm_D h i ha hg.2
  have hfb : Commute f b := (A_comm_D h i hb hf.2).symm
  have hfg : Commute f g := F_comm h hf.1 hg.1
  exact (Commute.mul_left (Commute.mul_right hab hag) (Commute.mul_right hfb hfg)).eq

theorem conj_H_mem_K (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ 𝐇) {k : G}
    (hk : k ∈ 𝐊[i]) : x * k * x⁻¹ ∈ 𝐊[i] :=
  conj_mem_sup (fun _ ha => conj_H_mem_A h i hx ha) (fun _ hf => conj_H_mem_Fi h i hx hf) hk

theorem H_le_normalizer_K (h : FCHyp L K n φ t) (i : Axis) :
    𝐇 ≤ normalizer (𝐊[i] : Set G) := fun _ hx =>
  mem_normalizer_of_conj_le fun _ hk => conj_H_mem_K h i hx hk

theorem K_inf_C (h : FCHyp L K n φ t) (i : Axis) : 𝐊[i] ⊓ 𝐂 = 𝐀[i] := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left (A_le_C h i))
  obtain ⟨hxK, hxC⟩ := mem_inf.mp hx
  rw [← SetLike.mem_coe, ← K_mul h i] at hxK
  obtain ⟨a, ha, f, hf, rfl⟩ := hxK
  have hfC : f ∈ 𝐂 := by simpa using mul_mem (inv_mem (A_le_C h i ha)) hxC
  exact mul_mem ha (pull_mono φ (center_le_rootA i) (mem_ZP_of_mem_F h hf.1 hfC))

theorem t_not_mem_K (h : FCHyp L K n φ t) (i : Axis) : t ∉ 𝐊[i] := fun ht => by
  have h1 : t ∈ 𝐊[i] ⊓ 𝐂 := ⟨ht, mem_centralizer_singleton_iff.mpr rfl⟩
  rw [K_inf_C h i] at h1
  exact h.twoCore.t_not_mem (pull_le φ _ h1)

theorem K_sup_t (h : FCHyp L K n φ t) (i : Axis) :
    𝐊[i] ⊓ zpowers t = ⊥ ∧ 𝐊[i] ⊔ zpowers t = 𝐃[i] := by
  have hinf : 𝐊[i] ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxK, hxt⟩ := mem_inf.mp hx
    have hx' : x = 1 ∨ x = t := by
      obtain ⟨j, rfl⟩ := hxt
      exact zpow_eq_one_or_eq h.setup.t_mul_t j
    rcases hx' with rfl | rfl
    · exact one_mem _
    · exact absurd hxK (t_not_mem_K h i)
  refine ⟨hinf, ?_⟩
  have hnorm : zpowers t ≤ normalizer (𝐊[i] : Set G) :=
    zpowers_le.mpr (H_le_normalizer_K h i t_mem_H)
  have h1 := card_sup_mul_card_inf 𝐊[i] (zpowers t) hnorm
  rw [hinf, card_bot, mul_one, card_K h i, Nat.card_zpowers, h.setup.order_t] at h1
  refine eq_of_le_of_card_ge (sup_le (K_le_D h i) (zpowers_le.mpr (t_mem_D h i))) ?_
  rw [h.card_D i, h1, mul_comm]

theorem K_unique (h : FCHyp L K n φ t) (i : Axis) {S : Subgroup G} (hSD : S ≤ 𝐃[i])
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    Nat.card S ≤ Nat.card 𝐊[i] ∧ (Nat.card S = Nat.card 𝐊[i] → S = 𝐊[i]) := by
  by_cases hSK : S ≤ 𝐊[i]
  · exact ⟨card_le_of_le hSK, fun he => eq_of_le_of_card_ge hSK he.ge⟩
  obtain ⟨g, hgS, hgK⟩ := IsConcreteLE.not_le_iff_exists.mp hSK
  have htK : t ∈ normalizer (𝐊[i] : Set G) := H_le_normalizer_K h i t_mem_H
  have hgD : g ∈ 𝐊[i] ⊔ zpowers t := by rw [(K_sup_t h i).2]; exact hSD hgS
  have htg : t * g ∈ 𝐊[i] := (mem_or_mul_mem h.setup.t_mul_t htK hgD).resolve_left hgK
  have hinf : 𝐊[i] ⊓ S ≤ 𝐀[i] := by
    intro y hy
    rw [← K_inf_C h i]
    refine ⟨hy.1, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : y * g = g * y := hS y hy.2 g hgS
    have h2 : y * (t * g) = (t * g) * y := K_comm h i hy.1 htg
    calc y * t = y * (t * g) * g⁻¹ := by group
      _ = t * g * y * g⁻¹ := by rw [h2]
      _ = t * (g * y * g⁻¹) := by group
      _ = t * y := by rw [← h1, mul_inv_cancel_right]
  have hSN : S ≤ normalizer (𝐊[i] : Set G) := hSD.trans ((D_le_H i).trans (H_le_normalizer_K h i))
  have h1 := card_sup_mul_card_inf 𝐊[i] S hSN
  have h2 : Nat.card (𝐊[i] ⊔ S : Subgroup G) ≤ 2 * Nat.card K ^ 4 := by
    rw [← h.card_D i]
    exact card_le_of_le (sup_le (K_le_D h i) hSD)
  have h3 : Nat.card (𝐊[i] ⊓ S : Subgroup G) ≤ Nat.card K ^ 3 := by
    rw [← card_rootA (K := K) i, ← card_pull φ]
    exact card_le_of_le hinf
  rw [card_K h i] at h1
  have h4 : Nat.card K ^ 4 * Nat.card S ≤ Nat.card K ^ 4 * (2 * Nat.card K ^ 3) := by
    rw [← h1]
    calc Nat.card (𝐊[i] ⊔ S : Subgroup G) * Nat.card (𝐊[i] ⊓ S : Subgroup G)
        ≤ (2 * Nat.card K ^ 4) * Nat.card K ^ 3 := Nat.mul_le_mul h2 h3
      _ = Nat.card K ^ 4 * (2 * Nat.card K ^ 3) := by ring
  have hq4 : 0 < Nat.card K ^ 4 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  have h5 := Nat.le_of_mul_le_mul_left h4 hq4
  have h6 : 2 * Nat.card K ^ 3 < Nat.card K ^ 4 := by
    have := h.four_le_card
    have h7 : 0 < Nat.card K ^ 3 := by positivity
    calc 2 * Nat.card K ^ 3 < Nat.card K * Nat.card K ^ 3 := by
          exact Nat.mul_lt_mul_of_pos_right (by omega) h7
      _ = Nat.card K ^ 4 := by ring
  rw [card_K h i]
  exact ⟨by omega, fun he => absurd he (by omega)⟩

theorem F_inf_P (h : FCHyp L K n φ t) : 𝐅 ⊓ 𝐏 = 𝐙 :=
  le_antisymm (fun _ hx => mem_ZP_of_mem_F h hx.1 (h.setup.L_le (pull_le φ _ hx.2)))
    (le_inf (ZP_le_F h) Setup.ZP_le_PG)

theorem conj_H_mem_P (h : FCHyp L K n φ t) {x : G} (hx : x ∈ 𝐇) {p : G} (hp : p ∈ 𝐏) :
    x * p * x⁻¹ ∈ 𝐏 := by
  rw [P_eq_A_sup_A] at hp ⊢
  exact conj_mem_sup (fun _ ha => conj_H_mem_A h _ hx ha) (fun _ ha => conj_H_mem_A h _ hx ha) hp

theorem Ks_eq (h : FCHyp L K n φ t) : 𝐊⋆ = 𝐅 ⊔ 𝐏 := by
  apply le_antisymm
  · have hA : ∀ i : Axis, 𝐀[i] ≤ 𝐅 ⊔ 𝐏 := fun i =>
      (pull_mono φ (rootA_le_antiUnipotent i)).trans le_sup_right
    exact sup_le (sup_le (hA _) (inf_le_left.trans le_sup_left))
      (sup_le (hA _) (inf_le_left.trans le_sup_left))
  · refine sup_le (fun f hf => ?_) ?_
    · rw [← SetLike.mem_coe, ← W_mul_W h] at hf
      obtain ⟨x, hx, y, hy, rfl⟩ := hf
      exact mul_mem (mem_sup_left (mem_sup_right (W_le_Fi h _ hx)))
        (mem_sup_right (mem_sup_right (W_le_Fi h _ hy)))
    · rw [P_eq_A_sup_A]
      exact sup_le_sup le_sup_left le_sup_left

theorem F_mul_P (h : FCHyp L K n φ t) : (𝐅 : Set G) * (𝐏 : Set G) = 𝐊⋆ := by
  rw [Ks_eq h]
  exact (coe_mul_of_right_le_normalizer_left _ _ (P_le_H.trans (H_le_normalizer_F h))).symm

theorem K_mul_K (h : FCHyp L K n φ t) :
    (𝐊[Axis.one] : Set G) * (𝐊[Axis.two] : Set G) = 𝐊⋆ :=
  (coe_mul_of_right_le_normalizer_left _ _
    ((K_le_H h Axis.two).trans (H_le_normalizer_K h Axis.one))).symm

theorem card_Ks (h : FCHyp L K n φ t) : Nat.card 𝐊⋆ = Nat.card K ^ 6 := by
  have h1 := card_sup_mul_card_inf 𝐅 𝐏 (P_le_H.trans (H_le_normalizer_F h))
  rw [F_inf_P h, FCHyp.card_ZP, card_F h, card_pull, (card_radicals (K := K)).1, ← Ks_eq h] at h1
  have hq : 0 < Nat.card K ^ 2 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)

theorem Ks_inf_Q (h : FCHyp L K n φ t) : 𝐊⋆ ⊓ 𝐐 = 𝐏 := by
  refine le_antisymm (fun x hx => ?_) (le_inf ((Ks_eq h).symm ▸ le_sup_right) le_sup_left)
  obtain ⟨hxK, hxQ⟩ := mem_inf.mp hx
  rw [← SetLike.mem_coe, ← F_mul_P h] at hxK
  obtain ⟨f, hf, p, hp, rfl⟩ := hxK
  have hfQ : f ∈ 𝐐 := by simpa using mul_mem hxQ (inv_mem (mem_sup_left hp : p ∈ 𝐐))
  exact mul_mem (Setup.ZP_le_PG (mem_ZP_of_mem_F h hf (h.setup.Q_le_C hfQ))) hp

theorem Ks_le_H (h : FCHyp L K n φ t) : 𝐊⋆ ≤ 𝐇 := by
  rw [Ks_eq h]
  exact sup_le (F_le_H h) P_le_H

theorem conj_H_mem_Ks (h : FCHyp L K n φ t) {x : G} (hx : x ∈ 𝐇) {k : G} (hk : k ∈ 𝐊⋆) :
    x * k * x⁻¹ ∈ 𝐊⋆ := by
  rw [Ks_eq h] at hk ⊢
  exact conj_mem_sup (fun _ hf => conj_H_mem_F h hx hf) (fun _ hp => conj_H_mem_P h hx hp) hk

theorem t_not_mem_Ks (h : FCHyp L K n φ t) : t ∉ 𝐊⋆ := fun ht => by
  have h1 : t ∈ 𝐊⋆ ⊓ 𝐐 := ⟨ht, mem_sup_right (mem_zpowers t)⟩
  rw [Ks_inf_Q h] at h1
  exact h.twoCore.t_not_mem (pull_le φ _ h1)

theorem Ks_sup_t (h : FCHyp L K n φ t) : 𝐊⋆ ⊓ zpowers t = ⊥ ∧ 𝐊⋆ ⊔ zpowers t = 𝐇 := by
  have hinf : 𝐊⋆ ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxK, hxt⟩ := mem_inf.mp hx
    have hx' : x = 1 ∨ x = t := by
      obtain ⟨j, rfl⟩ := hxt
      exact zpow_eq_one_or_eq h.setup.t_mul_t j
    rcases hx' with rfl | rfl
    · exact one_mem _
    · exact absurd hxK (t_not_mem_Ks h)
  refine ⟨hinf, ?_⟩
  have hnorm : zpowers t ≤ normalizer (𝐊⋆ : Set G) := zpowers_le.mpr
    (mem_normalizer_of_conj_le fun _ hk => conj_H_mem_Ks h t_mem_H hk)
  have h1 := card_sup_mul_card_inf 𝐊⋆ (zpowers t) hnorm
  rw [hinf, card_bot, mul_one, card_Ks h, Nat.card_zpowers, h.setup.order_t] at h1
  refine eq_of_le_of_card_ge (sup_le (Ks_le_H h) (zpowers_le.mpr t_mem_H)) ?_
  rw [h.H_facts.2.2, h1, mul_comm]

omit [Finite G] [Finite K] in
theorem E0_le_E (i : Axis) : 𝐄₀ ≤ 𝐄[i] := by
  cases i
  · exact inf_le_left
  · exact inf_le_right

omit [Finite K] in
theorem F_le_E (h : FCHyp L K n φ t) (i : Axis) : 𝐅 ≤ 𝐄[i] := (F_le_E0 h).trans (E0_le_E i)

theorem L_mul (h : FCHyp L K n φ t) (i : Axis) : (𝐅 : Set G) * (𝐀[i] : Set G) = 𝐋[i] :=
  (coe_mul_of_right_le_normalizer_left _ _ ((A_le_H h i).trans (H_le_normalizer_F h))).symm

theorem card_L (h : FCHyp L K n φ t) (i : Axis) : Nat.card 𝐋[i] = Nat.card K ^ 5 := by
  have h1 := card_sup_mul_card_inf 𝐅 𝐀[i] ((A_le_H h i).trans (H_le_normalizer_F h))
  rw [inf_comm 𝐅 𝐀[i], A_inf_F h i, FCHyp.card_ZP, card_F h, card_pull, card_rootA] at h1
  have hq : 0 < Nat.card K ^ 2 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)

theorem L_le_Hi (h : FCHyp L K n φ t) (i : Axis) : 𝐋[i] ≤ 𝐇 ⊓ 𝐄[i] :=
  sup_le (le_inf (F_le_H h) (F_le_E h i)) ((A_le_D h i).trans (D_le_Hi h i))

theorem conj_H_mem_L (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ 𝐇) {l : G}
    (hl : l ∈ 𝐋[i]) : x * l * x⁻¹ ∈ 𝐋[i] :=
  conj_mem_sup (fun _ hf => conj_H_mem_F h hx hf) (fun _ ha => conj_H_mem_A h i hx ha) hl

theorem conj_E_mem_L (h : FCHyp L K n φ t) (i : Axis) {e : G} (he : e ∈ 𝐄[i]) {l : G}
    (hl : l ∈ 𝐋[i]) : e * l * e⁻¹ ∈ 𝐋[i] := by
  have hlE : l ∈ 𝐄[i] := ((L_le_Hi h i).trans inf_le_right) hl
  have h1 := commutator_mem_closure_sq hlE (inv_mem he)
  rw [inv_inv, closure_sq_E h i] at h1
  rw [show e * l * e⁻¹ = l * (l⁻¹ * (e * l * e⁻¹)) by group]
  exact mul_mem hl (mem_sup_right h1)

theorem R_le_normalizer_L (h : FCHyp L K n φ t) (i : Axis) :
    𝐑[i] ≤ normalizer (𝐋[i] : Set G) :=
  sup_le (fun _ hq => mem_normalizer_of_conj_le fun _ hl => conj_H_mem_L h i (Q_le_H hq) hl)
    fun _ he => mem_normalizer_of_conj_le fun _ hl => conj_E_mem_L h i he hl

theorem conj_R_mem_L (h : FCHyp L K n φ t) (i : Axis) {r : G} (hr : r ∈ 𝐑[i]) {l : G}
    (hl : l ∈ 𝐋[i]) : r * l * r⁻¹ ∈ 𝐋[i] :=
  (mem_normalizer_iff.mp (R_le_normalizer_L h i hr) l).mp hl

theorem t_not_mem_L (h : FCHyp L K n φ t) (i : Axis) : t ∉ 𝐋[i] := fun ht => by
  rw [← SetLike.mem_coe, ← L_mul h i] at ht
  obtain ⟨f, hf, a, ha, hfa⟩ := ht
  have hfC : f ∈ 𝐂 := by
    have e : f = t * a⁻¹ := by rw [← hfa]; group
    rw [e]
    exact mul_mem (mem_centralizer_singleton_iff.mpr rfl) (inv_mem (A_le_C h i ha))
  have hfL : f ∈ L := pull_le φ _ (mem_ZP_of_mem_F h hf hfC)
  exact h.twoCore.t_not_mem (by rw [← hfa]; exact mul_mem hfL (pull_le φ _ ha))

theorem L_sup_t (h : FCHyp L K n φ t) (i : Axis) : 𝐋[i] ⊔ zpowers t = 𝐇 ⊓ 𝐄[i] := by
  have hinf : 𝐋[i] ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxL, hxt⟩ := mem_inf.mp hx
    have hx' : x = 1 ∨ x = t := by
      obtain ⟨j, rfl⟩ := hxt
      exact zpow_eq_one_or_eq h.setup.t_mul_t j
    rcases hx' with rfl | rfl
    · exact one_mem _
    · exact absurd hxL (t_not_mem_L h i)
  have hnorm : zpowers t ≤ normalizer (𝐋[i] : Set G) := zpowers_le.mpr
    (mem_normalizer_of_conj_le fun _ hl => conj_H_mem_L h i t_mem_H hl)
  have h1 := card_sup_mul_card_inf 𝐋[i] (zpowers t) hnorm
  rw [hinf, card_bot, mul_one, card_L h i, Nat.card_zpowers, h.setup.order_t] at h1
  refine eq_of_le_of_card_ge (sup_le (L_le_Hi h i)
    (zpowers_le.mpr (mem_inf.mpr ⟨t_mem_H, t_mem_E h i⟩))) ?_
  rw [card_Hi h i, h1, mul_comm]

omit [Finite G] [Finite K] in
theorem A_le_L (i : Axis) : 𝐀[i] ≤ 𝐋[i] := le_sup_right

omit [Finite G] [Finite K] in
theorem F_le_L (i : Axis) : 𝐅 ≤ 𝐋[i] := le_sup_left

theorem J_le_normalizer_L (h : FCHyp L K n φ t) (i : Axis) :
    𝐉 ≤ normalizer (𝐋[i] : Set G) := fun j hj =>
  mem_normalizer_of_conj_le fun _ hl => conj_mem_sup
    (fun f hf => by simpa using conj_torus_mem_F h (inv_mem hj) hf)
    (fun a ha => (mem_normalizer_iff.mp (FCHyp.torus_le_normalizer_A i hj) a).mp ha) hl

theorem psiG_y_mul (h : FCHyp L K n φ t) (i : Axis) {r s : G} (hr : r ∈ 𝐑[i]) (hs : s ∈ 𝐑[i]) :
    psiG φ i (t⁻¹ * ((r * s) * t * (r * s)⁻¹)) 1 =
      psiG φ i (t⁻¹ * (r * t * r⁻¹)) 1 + psiG φ i (t⁻¹ * (s * t * s⁻¹)) 1 := by
  have := congrArg Heis.y (map_mul (parabolicHom h i) ⟨r, hr⟩ ⟨s, hs⟩)
  rw [Heis.mul_y] at this
  exact this

theorem mem_H_iff_y (h : FCHyp L K n φ t) (i : Axis) {r : G} (hr : r ∈ 𝐑[i]) :
    r ∈ 𝐇 ↔ psiG φ i (t⁻¹ * (r * t * r⁻¹)) 1 = 0 :=
  mem_H_iff h i ⟨r, hr⟩

theorem exists_E_decomp (h : FCHyp L K n φ t) (i : Axis) {τ : G} (hτ : τ ∈ 𝐉) {μ : K}
    (hμ : μ ≠ 1) (hτψ : ∀ a ∈ 𝐀[i], psiG φ i (τ⁻¹ * a * τ) 1 = μ * psiG φ i a 1) {e : G}
    (he : e ∈ 𝐄[i]) : ∃ e' ∈ 𝐄[i], (e'⁻¹ * (τ⁻¹ * e' * τ))⁻¹ * e ∈ 𝐇 := by
  have hμ' : μ - 1 ≠ 0 := sub_ne_zero.mpr hμ
  have hER : ∀ {x : G}, x ∈ 𝐄[i] → x ∈ 𝐑[i] := fun hx => mem_sup_right hx
  set Y : G → K := fun r => psiG φ i (t⁻¹ * (r * t * r⁻¹)) 1 with hY
  have hY1 : Y 1 = 0 := by
    have := psiG_y_mul h i (one_mem 𝐑[i]) (one_mem 𝐑[i])
    simp only [mul_one] at this
    change Y 1 = Y 1 + Y 1 at this
    linear_combination (-1 : K) * this
  have hYinv : ∀ {r : G}, r ∈ 𝐑[i] → Y r⁻¹ = -Y r := fun {r} hr => by
    have := psiG_y_mul h i hr (inv_mem hr)
    rw [mul_inv_cancel] at this
    change Y 1 = Y r + Y r⁻¹ at this
    rw [hY1] at this
    linear_combination -this
  have hYτ : ∀ {r : G}, r ∈ 𝐑[i] → Y (τ⁻¹ * r * τ) = μ * Y r := fun {r} hr => by
    have hτt : τ⁻¹ * t * τ = t := by
      rw [mul_assoc, ← torus_comm_t h hτ, inv_mul_cancel_left]
    have e1 : t⁻¹ * ((τ⁻¹ * r * τ) * t * (τ⁻¹ * r * τ)⁻¹) = τ⁻¹ * (t⁻¹ * (r * t * r⁻¹)) * τ := by
      calc t⁻¹ * ((τ⁻¹ * r * τ) * t * (τ⁻¹ * r * τ)⁻¹)
          = (τ⁻¹ * t * τ)⁻¹ * ((τ⁻¹ * r * τ) * (τ⁻¹ * t * τ) * (τ⁻¹ * r * τ)⁻¹) := by rw [hτt]
        _ = τ⁻¹ * (t⁻¹ * (r * t * r⁻¹)) * τ := by group
    change psiG φ i _ 1 = μ * psiG φ i _ 1
    rw [e1]
    exact hτψ _ (conj_t_mem_A h i hr)
  obtain ⟨e₀, he', htr⟩ := translations_mem_E h i ![0, Y e / (μ - 1)]
  set e' : G := (e₀ : G) with he'_def
  have hψe' : psiG φ i (t⁻¹ * (e' * t * e'⁻¹)) = ![0, Y e / (μ - 1)] := by
    have h1 := (h.actHyp i).aff_zero e₀
    rw [htr, zero_add] at h1
    exact h1.symm
  have hYe' : Y e' = Y e / (μ - 1) := by
    change psiG φ i _ 1 = _
    rw [hψe']
    simp
  refine ⟨e', he', ?_⟩
  have hτe' : τ⁻¹ * e' * τ ∈ 𝐄[i] := conj_torus_mem_E h i hτ he'
  have hx : e'⁻¹ * (τ⁻¹ * e' * τ) ∈ 𝐄[i] := mul_mem (inv_mem he') hτe'
  refine (mem_H_iff_y h i (mul_mem (inv_mem (hER hx)) (hER he))).mpr ?_
  change Y _ = 0
  rw [show Y ((e'⁻¹ * (τ⁻¹ * e' * τ))⁻¹ * e) = Y (e'⁻¹ * (τ⁻¹ * e' * τ))⁻¹ + Y e from
      psiG_y_mul h i (inv_mem (hER hx)) (hER he), hYinv (hER hx),
    show Y (e'⁻¹ * (τ⁻¹ * e' * τ)) = Y e'⁻¹ + Y (τ⁻¹ * e' * τ) from
      psiG_y_mul h i (inv_mem (hER he')) (hER hτe'), hYinv (hER he'), hYτ (hER he'), hYe']
  field_simp
  ring

theorem comm_P_E (h : FCHyp L K n φ t) (i : Axis) {p : G} (hp : p ∈ 𝐏) {e : G}
    (he : e ∈ 𝐄[i]) : p⁻¹ * (e⁻¹ * p * e) ∈ 𝐋[i] := by
  have hpH : p ∈ 𝐇 := P_le_H hp
  have hpR : p ∈ 𝐑[i] := H_le_R h i hpH
  have htt := h.setup.t_mul_t
  have htN : t ∈ normalizer (𝐋[i] : Set G) :=
    mem_normalizer_of_conj_le fun _ hl => conj_H_mem_L h i t_mem_H hl
  have hcos : ∀ x ∈ 𝐄[i], p⁻¹ * (x⁻¹ * p * x) ∈ 𝐋[i] ∨ t * (p⁻¹ * (x⁻¹ * p * x)) ∈ 𝐋[i] := by
    intro x hx
    refine mem_or_mul_mem htt htN ?_
    rw [L_sup_t h i]
    refine mem_inf.mpr ⟨mul_mem (inv_mem hpH) ?_, ?_⟩
    · have := conj_mem_H h i (inv_mem (mem_sup_right hx : x ∈ 𝐑[i])) hpH
      rwa [inv_inv] at this
    · rw [show p⁻¹ * (x⁻¹ * p * x) = (p⁻¹ * x⁻¹ * p⁻¹⁻¹) * x by group]
      exact mul_mem (conj_mem_E h i (inv_mem hpR) (inv_mem hx)) hx
  have hconj : ∀ y ∈ 𝐄[i], ∀ w : G, (w ∈ 𝐋[i] ∨ t * w ∈ 𝐋[i]) →
      (y⁻¹ * w * y ∈ 𝐋[i] ↔ w ∈ 𝐋[i]) ∧ (y⁻¹ * w * y ∈ 𝐋[i] ∨ t * (y⁻¹ * w * y) ∈ 𝐋[i]) := by
    intro y hy w hw
    have hyR : y⁻¹ ∈ 𝐑[i] := inv_mem (mem_sup_right hy)
    have hiff : y⁻¹ * w * y ∈ 𝐋[i] ↔ w ∈ 𝐋[i] := by
      have := mem_normalizer_iff.mp (R_le_normalizer_L h i hyR) w
      rw [inv_inv] at this
      exact this.symm
    refine ⟨hiff, ?_⟩
    rcases hw with hw | hw
    · exact Or.inl (hiff.mpr hw)
    · right
      have ha : t⁻¹ * (y * t * y⁻¹) ∈ 𝐀[i] := conj_t_mem_A h i (mem_sup_right hy)
      have hat : (t⁻¹ * (y * t * y⁻¹)) * t = t * (t⁻¹ * (y * t * y⁻¹)) :=
        (h.twoCore.comm (pull_le φ _ ha)).symm
      have e1 : t * (y⁻¹ * w * y) = y⁻¹ * ((t⁻¹ * (y * t * y⁻¹)) * (t * w)) * y := by
        calc t * (y⁻¹ * w * y) = y⁻¹ * (t * (t⁻¹ * (y * t * y⁻¹))) * w * y := by group
          _ = y⁻¹ * ((t⁻¹ * (y * t * y⁻¹)) * t) * w * y := by rw [hat]
          _ = y⁻¹ * ((t⁻¹ * (y * t * y⁻¹)) * (t * w)) * y := by group
      rw [e1]
      have := mem_normalizer_iff.mp (R_le_normalizer_L h i hyR)
        (t⁻¹ * (y * t * y⁻¹) * (t * w))
      rw [inv_inv] at this
      exact this.mp (mul_mem (A_le_L i ha) hw)
  have hmul : ∀ x ∈ 𝐄[i], ∀ y ∈ 𝐄[i], (p⁻¹ * ((x * y)⁻¹ * p * (x * y)) ∈ 𝐋[i] ↔
      (p⁻¹ * (x⁻¹ * p * x) ∈ 𝐋[i] ↔ p⁻¹ * (y⁻¹ * p * y) ∈ 𝐋[i])) := by
    intro x hx y hy
    have e1 : p⁻¹ * ((x * y)⁻¹ * p * (x * y)) =
        (p⁻¹ * (y⁻¹ * p * y)) * (y⁻¹ * (p⁻¹ * (x⁻¹ * p * x)) * y) := by group
    obtain ⟨hiff, hc⟩ := hconj y hy _ (hcos x hx)
    rw [e1, mul_mem_iff_of htt htN (hcos y hy) hc, hiff]
    exact iff_comm
  obtain ⟨τ, hτ, -, hτ2, μ, hμ, hτψ⟩ := exists_pairTorus h i
  have hτN := J_le_normalizer_L h i hτ
  have htor : ∀ x ∈ 𝐄[i], (p⁻¹ * ((τ⁻¹ * x * τ)⁻¹ * p * (τ⁻¹ * x * τ)) ∈ 𝐋[i] ↔
      p⁻¹ * (x⁻¹ * p * x) ∈ 𝐋[i]) := by
    intro x hx
    have ha : p⁻¹ * (τ * p * τ⁻¹) ∈ 𝐀[i] := hτ2 p hp
    have hxa : x⁻¹ * (p⁻¹ * (τ * p * τ⁻¹)) * x ∈ 𝐀[i] := by
      have := (h.actHyp i).conj_A x⁻¹ (inv_mem (map_subtype_le _ hx)) _ ha
      rwa [inv_inv] at this
    have e1 : p⁻¹ * ((τ⁻¹ * x * τ)⁻¹ * p * (τ⁻¹ * x * τ)) = τ⁻¹ * ((p⁻¹ * (τ * p * τ⁻¹))⁻¹ *
        (p⁻¹ * (x⁻¹ * p * x)) * (x⁻¹ * (p⁻¹ * (τ * p * τ⁻¹)) * x)) * τ := by group
    rw [e1, ← mem_normalizer_iff''.mp hτN]
    constructor
    · intro h1
      have := mul_mem (mul_mem (A_le_L i ha) h1) (inv_mem (A_le_L i hxa))
      rwa [show p⁻¹ * (τ * p * τ⁻¹) * ((p⁻¹ * (τ * p * τ⁻¹))⁻¹ * (p⁻¹ * (x⁻¹ * p * x)) *
        (x⁻¹ * (p⁻¹ * (τ * p * τ⁻¹)) * x)) * (x⁻¹ * (p⁻¹ * (τ * p * τ⁻¹)) * x)⁻¹ =
        p⁻¹ * (x⁻¹ * p * x) by group] at this
    · intro h1
      exact mul_mem (mul_mem (inv_mem (A_le_L i ha)) h1) (A_le_L i hxa)
  obtain ⟨e', he', hdec⟩ := exists_E_decomp h i hτ hμ hτψ he
  have hτe' : τ⁻¹ * e' * τ ∈ 𝐄[i] := conj_torus_mem_E h i hτ he'
  have hx : e'⁻¹ * (τ⁻¹ * e' * τ) ∈ 𝐄[i] := mul_mem (inv_mem he') hτe'
  have hk : (e'⁻¹ * (τ⁻¹ * e' * τ))⁻¹ * e ∈ 𝐄[i] := mul_mem (inv_mem hx) he
  have hHi : p⁻¹ * (((e'⁻¹ * (τ⁻¹ * e' * τ))⁻¹ * e)⁻¹ * p * ((e'⁻¹ * (τ⁻¹ * e' * τ))⁻¹ * e)) ∈
      𝐋[i] := F_le_L i (ZP_le_F h (commutator_mem_ZP h hpH hdec))
  have h1 : p⁻¹ * ((e'⁻¹ * e')⁻¹ * p * (e'⁻¹ * e')) ∈ 𝐋[i] := by
    rw [inv_mul_cancel, inv_one, one_mul, mul_one, inv_mul_cancel]
    exact one_mem _
  have h2 := (hmul _ (inv_mem he') _ he').mp h1
  have hxχ : p⁻¹ * ((e'⁻¹ * (τ⁻¹ * e' * τ))⁻¹ * p * (e'⁻¹ * (τ⁻¹ * e' * τ))) ∈ 𝐋[i] := by
    rw [hmul _ (inv_mem he') _ hτe', htor _ he']
    exact h2
  have h3 := hmul _ hx _ hk
  rw [show e'⁻¹ * (τ⁻¹ * e' * τ) * ((e'⁻¹ * (τ⁻¹ * e' * τ))⁻¹ * e) = e by group] at h3
  exact h3.mpr (iff_of_true hxχ hHi)

theorem comm_H_E (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ 𝐇) {e : G}
    (he : e ∈ 𝐄[i]) : x⁻¹ * (e⁻¹ * x * e) ∈ 𝐋[i] := by
  let S : Subgroup G :=
    { carrier := {x | x ∈ 𝐑[i] ∧ ∀ e ∈ 𝐄[i], x⁻¹ * (e⁻¹ * x * e) ∈ 𝐋[i]}
      mul_mem' := by
        rintro x y ⟨hxR, hx⟩ ⟨hyR, hy⟩
        refine ⟨mul_mem hxR hyR, fun e he => ?_⟩
        have h1 : y⁻¹ * (x⁻¹ * (e⁻¹ * x * e)) * y ∈ 𝐋[i] := by
          have := conj_R_mem_L h i (inv_mem hyR) (hx e he)
          rwa [inv_inv] at this
        rw [show (x * y)⁻¹ * (e⁻¹ * (x * y) * e) =
          y⁻¹ * (x⁻¹ * (e⁻¹ * x * e)) * y * (y⁻¹ * (e⁻¹ * y * e)) by group]
        exact mul_mem h1 (hy e he)
      one_mem' := ⟨one_mem _, fun e _ => by
        rw [inv_one, one_mul, mul_one, inv_mul_cancel]
        exact one_mem _⟩
      inv_mem' := by
        rintro x ⟨hxR, hx⟩
        refine ⟨inv_mem hxR, fun e he => ?_⟩
        rw [show x⁻¹⁻¹ * (e⁻¹ * x⁻¹ * e) = x * (x⁻¹ * (e⁻¹ * x * e))⁻¹ * x⁻¹ by group]
        exact conj_R_mem_L h i hxR (inv_mem (hx e he)) }
  have hFS : 𝐅 ≤ S := fun f hf => ⟨H_le_R h i (F_le_H h hf), fun e he => by
    have := conj_R_mem_L h i (inv_mem (mem_sup_right he : e ∈ 𝐑[i])) (F_le_L i hf)
    rw [inv_inv] at this
    exact mul_mem (inv_mem (F_le_L i hf)) this⟩
  have hPS : 𝐏 ≤ S := fun p hp => ⟨H_le_R h i (P_le_H hp), fun e he => comm_P_E h i hp he⟩
  have htS : t ∈ S := ⟨H_le_R h i t_mem_H, fun e he => by
    have := conj_t_mem_A h i (inv_mem (mem_sup_right he : e ∈ 𝐑[i]))
    rw [inv_inv] at this
    exact A_le_L i this⟩
  have hHS : 𝐇 ≤ S := by
    rw [← (Ks_sup_t h).2, Ks_eq h]
    exact sup_le (sup_le hFS hPS) (zpowers_le.mpr htS)
  exact (hHS hx).2 e he

theorem sq_R_le_L (h : FCHyp L K n φ t) (i : Axis) :
    closure {x : G | ∃ y ∈ 𝐑[i], x = y * y} ≤ 𝐋[i] := by
  rw [closure_le]
  rintro _ ⟨y, hy, rfl⟩
  rw [← SetLike.mem_coe, ← R_mul h i] at hy
  obtain ⟨q, hq, e, he, rfl⟩ := hy
  have hqH : q ∈ 𝐇 := Q_le_H hq
  have h1 : q * q ∈ 𝐋[i] := F_le_L i (ZP_le_F h (mul_self_mem_ZP h hqH))
  have h2 : q⁻¹ * (e⁻¹⁻¹ * q * e⁻¹) ∈ 𝐋[i] := comm_H_E h i hqH (inv_mem he)
  have h3 : e * e ∈ 𝐋[i] := A_le_L i (by
    rw [← closure_sq_E h i]
    exact subset_closure ⟨e, he, rfl⟩)
  rw [inv_inv] at h2
  rw [show q * e * (q * e) = (q * q) * (q⁻¹ * (e * q * e⁻¹)) * (e * e) by group]
  exact mul_mem (mul_mem h1 h2) h3

theorem Ks_normal_R (h : FCHyp L K n φ t) (i : Axis) :
    𝐊⋆ ≤ 𝐑[i] ∧ (𝐊⋆.subgroupOf 𝐑[i]).Normal := by
  have hLK : 𝐋[i] ≤ 𝐊⋆ := by
    rw [Ks_eq h]
    exact sup_le le_sup_left ((pull_mono φ (rootA_le_antiUnipotent i)).trans le_sup_right)
  have hKR : 𝐊⋆ ≤ 𝐑[i] := (Ks_le_H h).trans (H_le_R h i)
  refine ⟨hKR, ⟨fun k hk r => mem_subgroupOf.mpr ?_⟩⟩
  have hk' : (k : G) ∈ 𝐊⋆ := mem_subgroupOf.mp hk
  have h1 := commutator_mem_closure_sq (hKR hk') (inv_mem r.2)
  rw [inv_inv] at h1
  have h2 := hLK (sq_R_le_L h i h1)
  rw [coe_mul, coe_mul, coe_inv, show (r : G) * k * (r : G)⁻¹ =
    k * ((k : G)⁻¹ * ((r : G) * k * (r : G)⁻¹)) by group]
  exact mul_mem hk' h2

end Products

end FullCenterWeyl

end CFSG.LocalAnalysis.SymplecticFourStandard
