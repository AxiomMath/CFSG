module

import CFSG.Quasithin.Recognition.St84.G24Tools
import CFSG.Quasithin.Background.SpecialPGroupCenter
public import CFSG.Quasithin.Recognition.St84.G24Vertex2Action

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.Quasithin.F7 CFSG.Quasithin.St84
open CFSG.Quasithin.KGC31 (eElt eElt_zero eElt_single eElt_add eElt_injective
  conj_eElt map_eElt)
open CFSG.GroupTheory (eElt_mem_of_forall_mem eElt_add_mul_inv_mem conj_eElt_mul_inv_mem
  eElt_eq_castAdd_mul_natAdd eElt_ofAdd_cols eElt_mul_inv_mem_of_cols eEltQuotEquiv
  eEltQuotEquiv_ofAdd)
open Certificates.A5GL42 (aN bN)
open CFSG.Quasithin.H.Q13 (om)
open scoped commutatorElement Matrix

variable {G : Type} [Group G]
variable {L1 L2 S : Subgroup G}


private theorem omega2_mul_omega2_sq : om * om ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private theorem omega2_col_zero :
    (fun i : Fin 2 => om i 0) = (fun i : Fin 2 =>
      (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) i 1) := by
  funext i
  fin_cases i <;> decide

private theorem v2Block_mul (U1 : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (X1 : Matrix (Fin 2) (Fin 4) (ZMod 2)) (N1 : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (U2 : Matrix (Fin 2) (Fin 2) (ZMod 2)) (X2 : Matrix (Fin 2) (Fin 4) (ZMod 2))
    (N2 : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    v2Block U1 X1 N1 * v2Block U2 X2 N2 =
      v2Block (U1 * U2) (U1 * X2 + X1 * N2) (N1 * N2) := by
  ext i j
  refine Fin.addCases (m := 2) (n := 4) (fun a => ?_) (fun c => ?_) i
  · refine Fin.addCases (m := 2) (n := 4) (fun b => ?_) (fun d => ?_) j
    · rw [v2Block_castAdd_castAdd, Matrix.mul_apply, Fin.sum_univ_add (a := 2) (b := 4),
        Matrix.mul_apply]
      simp only [v2Block_castAdd_castAdd, v2Block_castAdd_natAdd, v2Block_natAdd_castAdd,
        mul_zero, Finset.sum_const_zero, add_zero]
    · rw [v2Block_castAdd_natAdd, Matrix.mul_apply, Fin.sum_univ_add (a := 2) (b := 4),
        Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
      simp only [v2Block_castAdd_castAdd, v2Block_castAdd_natAdd, v2Block_natAdd_castAdd,
        v2Block_natAdd_natAdd, mul_zero, Finset.sum_const_zero, add_zero]
  · refine Fin.addCases (m := 2) (n := 4) (fun b => ?_) (fun d => ?_) j
    · rw [v2Block_natAdd_castAdd, Matrix.mul_apply, Fin.sum_univ_add (a := 2) (b := 4)]
      simp only [v2Block_castAdd_castAdd, v2Block_castAdd_natAdd, v2Block_natAdd_castAdd,
        v2Block_natAdd_natAdd, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    · rw [v2Block_natAdd_natAdd, Matrix.mul_apply, Fin.sum_univ_add (a := 2) (b := 4),
        Matrix.mul_apply]
      simp only [v2Block_castAdd_castAdd, v2Block_castAdd_natAdd, v2Block_natAdd_castAdd,
        v2Block_natAdd_natAdd, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      ring

private theorem v2Block_B_col_zero :
    (fun j : Fin 6 => v2Block om (0 : Matrix (Fin 2) (Fin 4) (ZMod 2))
      (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) j 0) =
      fun j : Fin 6 => if h : j.val < 2 then
        (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) ⟨j.val, h⟩ 1 else 0 := by
  have h0 : (fun j : Fin 6 => v2Block om (0 : Matrix (Fin 2) (Fin 4) (ZMod 2))
      (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) j 0) =
      (fun j : Fin 6 => v2Block om (0 : Matrix (Fin 2) (Fin 4) (ZMod 2))
        (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) j (Fin.castAdd 4 (0 : Fin 2))) := by
    funext j
    rfl
  rw [h0, v2Block_col_U]
  funext j
  by_cases hj : j.val < 2
  · rw [dif_pos hj, dif_pos hj]
    exact congrFun omega2_col_zero ⟨j.val, hj⟩
  · rw [dif_neg hj, dif_neg hj]

private theorem v2Block_B_col_one :
    (fun j : Fin 6 => v2Block om (0 : Matrix (Fin 2) (Fin 4) (ZMod 2))
      (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) j 1) =
      fun j : Fin 6 => if h : j.val < 2 then om ⟨j.val, h⟩ 1 else 0 := by
  have h1 : (fun j : Fin 6 => v2Block om (0 : Matrix (Fin 2) (Fin 4) (ZMod 2))
      (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) j 1) =
      (fun j : Fin 6 => v2Block om (0 : Matrix (Fin 2) (Fin 4) (ZMod 2))
        (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) j (Fin.castAdd 4 (1 : Fin 2))) := by
    funext j
    rfl
  rw [h1, v2Block_col_U]

private theorem eElt_congr_of_cols [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G} (hu : u ∈ F.W)
    (hn : F.IsNLift n) {f' : Fin 6 → G} {B : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (hframe : ∀ j : Fin 6, f' j *
      (eElt (v2Frame F.k u n) fun i => B i j)⁻¹ ∈ centerOf (dsQ L2 L1 S)) :
    ∀ v : Fin 6 → ZMod 2,
      eElt f' v * (eElt (v2Frame F.k u n) (B *ᵥ v))⁻¹ ∈ centerOf (dsQ L2 L1 S) := by
  obtain ⟨hfQ, -, hfSq, hfCm, -⟩ := F.frame_spec hD hu hn
  exact CFSG.GroupTheory.eElt_mul_inv_mem_of_cols
    (fun y hy i => (F.special_data hD).2.2.2.1 y hy (v2Frame F.k u n i) (hfQ i))
    hfSq hfCm B hframe

private theorem conj_congr_of_matrix [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G} (hu : u ∈ F.W)
    (hn : F.IsNLift n) {f' : Fin 6 → G} {B : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (hframe : ∀ j : Fin 6, f' j *
      (eElt (v2Frame F.k u n) fun i => B i j)⁻¹ ∈ centerOf (dsQ L2 L1 S))
    {g : G} (hgA : g ∈ F.A) {M M' : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (hg : ∀ j : Fin 6, g * v2Frame F.k u n j * g⁻¹ *
      (eElt (v2Frame F.k u n) fun i => M i j)⁻¹ ∈ centerOf (dsQ L2 L1 S))
    (hgZ : ∀ z ∈ centerOf (dsQ L2 L1 S), g * z * g⁻¹ ∈ centerOf (dsQ L2 L1 S))
    (hMB : M * B = B * M') :
    ∀ j : Fin 6, g * f' j * g⁻¹ *
      (eElt f' fun i => M' i j)⁻¹ ∈ centerOf (dsQ L2 L1 S) := by
  classical
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  obtain ⟨hfQ, hfC, hfSq, hfCm, -⟩ := F.frame_spec hD hu hn
  have hspec := F.special_data hD
  have hZQ : Z2 ≤ Q2 := hspec.2.2.1
  have hZcQ : ∀ y ∈ Z2, ∀ x ∈ Q2, y * x = x * y := hspec.2.2.2.1
  haveI : (Z2.subgroupOf Q2).Normal := Subgroup.normal_of_le_center fun z hz =>
    Subgroup.mem_center_iff.mpr fun x => Subtype.ext (hZcQ z hz x x.2).symm
  have hf'Q : ∀ i, f' i ∈ Q2 := by
    intro i
    have hm := hframe i
    have he : eElt (v2Frame F.k u n) (fun j => B j i) ∈ Q2 :=
      eElt_mem_of_forall_mem hfQ _
    rw [show f' i = (f' i * (eElt (v2Frame F.k u n) fun j => B j i)⁻¹) *
        eElt (v2Frame F.k u n) (fun j => B j i) from by group]
    exact Q2.mul_mem (hZQ hm) he
  have hlift := eElt_congr_of_cols F hD hu hn hframe
  intro j
  have hgQ : ∀ x ∈ Q2, g * x * g⁻¹ ∈ Q2 := by
    intro x hx
    exact (Subgroup.mem_normalizer_iff.mp (hspec.1 hgA) x).mp hx
  have hx : (QuotientGroup.mk (⟨f' j, hf'Q j⟩ : ↥Q2) : ↥Q2 ⧸ Z2.subgroupOf Q2) =
      QuotientGroup.mk ⟨eElt (v2Frame F.k u n) (fun i => B i j),
        eElt_mem_of_forall_mem hfQ _⟩ := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [Subgroup.mem_subgroupOf, div_eq_mul_inv]
    exact hframe j
  have hres := CFSG.GroupTheory.mk_conj_eq_mk_mulVec (Q := Q2) (Z := Z2)
    (f := v2Frame F.k u n) (g := g) hfQ hfC hfSq hfCm hgZ M hg
    (x := ⟨f' j, hf'Q j⟩) (w := ⟨g * f' j * g⁻¹, hgQ (f' j) (hf'Q j)⟩)
    (v := fun i => B i j) hx (by simp)
  have hmv : M *ᵥ (fun i => B i j) = B *ᵥ (fun i => M' i j) := by
    rw [← Matrix.col_apply' B j, ← Matrix.mulVec_single_one B,
      ← Matrix.col_apply' M' j, ← Matrix.mulVec_single_one M',
      Matrix.mulVec_mulVec, hMB, ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one,
      Matrix.col_apply']
  have hY : eElt f' (fun i => M' i j) *
      (eElt (v2Frame F.k u n) (B *ᵥ (fun i => M' i j)))⁻¹ ∈ Z2 := hlift _
  have hfin : (QuotientGroup.mk (⟨g * f' j * g⁻¹, hgQ (f' j) (hf'Q j)⟩ : ↥Q2) :
      ↥Q2 ⧸ Z2.subgroupOf Q2) =
      QuotientGroup.mk ⟨eElt f' (fun i => M' i j),
        eElt_mem_of_forall_mem hf'Q _⟩ := by
    rw [hres, hmv]
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [Subgroup.mem_subgroupOf, div_eq_mul_inv]
    have hinv := Z2.inv_mem hY
    rwa [show (eElt f' (fun i => M' i j) *
        (eElt (v2Frame F.k u n) (B *ᵥ (fun i => M' i j)))⁻¹)⁻¹ =
        eElt (v2Frame F.k u n) (B *ᵥ (fun i => M' i j)) *
          (eElt f' (fun i => M' i j))⁻¹ from by group] at hinv
  have h3 := QuotientGroup.eq_iff_div_mem.mp hfin
  rw [Subgroup.mem_subgroupOf, div_eq_mul_inv] at h3
  simpa using h3

private theorem frame_change_k_N (k u : G) (n : Fin 4 → G) :
    ∀ j : Fin 4, eElt (v2Frame k u n) (fun i =>
      v2Block om (0 : Matrix (Fin 2) (Fin 4) (ZMod 2))
        (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) i (Fin.natAdd 2 j)) = n j := by
  intro j
  let fU : Fin 2 → G := show Fin 2 → G from ![u, k * u * k⁻¹]
  have hf_eq : v2Frame k u n = Fin.append fU n := by
    dsimp only [fU]
    exact v2Frame_eq_append k u n
  rw [hf_eq, eElt_eq_castAdd_mul_natAdd]
  simp only [Fin.append_left, Fin.append_right]
  have h1 : (fun i : Fin 2 => (fun i' : Fin 6 =>
      v2Block om (0 : Matrix (Fin 2) (Fin 4) (ZMod 2))
        (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) i' (Fin.natAdd 2 j))
      (Fin.castAdd 4 i)) = 0 := by
    funext i
    show v2Block om (0 : Matrix (Fin 2) (Fin 4) (ZMod 2))
      (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) (Fin.castAdd 4 i) (Fin.natAdd 2 j) = 0
    rw [v2Block_castAdd_natAdd]
    rfl
  have h2 : (fun k : Fin 4 => (fun i' : Fin 6 =>
      v2Block om (0 : Matrix (Fin 2) (Fin 4) (ZMod 2))
        (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) i' (Fin.natAdd 2 j))
      (Fin.natAdd 2 k)) = Pi.single j 1 := by
    funext k
    show v2Block om (0 : Matrix (Fin 2) (Fin 4) (ZMod 2))
      (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) (Fin.natAdd 2 k) (Fin.natAdd 2 j) =
      (Pi.single j (1 : ZMod 2) : Fin 4 → ZMod 2) k
    rw [v2Block_natAdd_natAdd]
    by_cases hkj : k = j
    · subst hkj
      rw [Pi.single_eq_same, Matrix.one_apply, if_pos rfl]
    · rw [Pi.single_eq_of_ne hkj, Matrix.one_apply, if_neg hkj]
  rw [h1, h2, eElt_zero, one_mul, eElt_single]

private theorem frame_change_k [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G} (hu : u ∈ F.W) :
    ∀ i : Fin 6, v2Frame F.k (F.k * u * F.k⁻¹) n i *
      (eElt (v2Frame F.k u n) fun j =>
        v2Block om (0 : Matrix (Fin 2) (Fin 4) (ZMod 2))
          (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) j i)⁻¹ ∈
      centerOf (dsQ L2 L1 S) := by
  classical
  let u1 : G := F.k * u * F.k⁻¹
  let fU : Fin 2 → G := show Fin 2 → G from ![u, u1]
  let f : Fin 6 → G := v2Frame F.k u n
  let B : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
    v2Block om (0 : Matrix (Fin 2) (Fin 4) (ZMod 2))
      (1 : Matrix (Fin 4) (Fin 4) (ZMod 2))
  have hcol0 : eElt f (fun j => B j 0) = u1 := by
    have hB0 : (fun j : Fin 6 => B j 0) = fun j : Fin 6 => if h : j.val < 2 then
        (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) ⟨j.val, h⟩ 1 else 0 := by
      simpa only [B] using v2Block_B_col_zero
    rw [hB0]
    have h := G24Vertex2.eElt_block_one F.k u n 1
    change eElt (v2Frame F.k u n) (fun j : Fin 6 => if h : j.val < 2 then
      (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) ⟨j.val, h⟩ 1 else 0) = u1
    simpa using h
  have hcol1 : eElt f (fun j => B j 1) = u * u1 := by
    have hB1 : (fun j : Fin 6 => B j 1) = fun j : Fin 6 => if h : j.val < 2 then
        om ⟨j.val, h⟩ 1 else 0 := by
      simpa only [B] using v2Block_B_col_one
    rw [hB1]
    have h := G24Vertex2.eElt_block_omega F.k u n
    change eElt (v2Frame F.k u n) (fun j : Fin 6 => if h : j.val < 2 then
      om ⟨j.val, h⟩ 1 else 0) = u * u1
    simpa using h
  have hcolN := frame_change_k_N F.k u n
  intro i
  fin_cases i
  · change u1 * (eElt f (fun j => B j 0))⁻¹ ∈ centerOf (dsQ L2 L1 S)
    rw [hcol0, mul_inv_cancel]
    exact (centerOf (dsQ L2 L1 S)).one_mem
  · change F.k * u1 * F.k⁻¹ * (eElt f (fun j => B j 1))⁻¹ ∈ centerOf (dsQ L2 L1 S)
    rw [hcol1]
    exact F.k_conj_mem_center hD hu
  · change n 0 * (eElt f (fun j => B j 2))⁻¹ ∈ centerOf (dsQ L2 L1 S)
    have hc : eElt f (fun j => B j 2) = n 0 := by simpa using hcolN 0
    rw [hc, mul_inv_cancel]
    exact (centerOf (dsQ L2 L1 S)).one_mem
  · change n 1 * (eElt f (fun j => B j 3))⁻¹ ∈ centerOf (dsQ L2 L1 S)
    have hc : eElt f (fun j => B j 3) = n 1 := by simpa using hcolN 1
    rw [hc, mul_inv_cancel]
    exact (centerOf (dsQ L2 L1 S)).one_mem
  · change n 2 * (eElt f (fun j => B j 4))⁻¹ ∈ centerOf (dsQ L2 L1 S)
    have hc : eElt f (fun j => B j 4) = n 2 := by simpa using hcolN 2
    rw [hc, mul_inv_cancel]
    exact (centerOf (dsQ L2 L1 S)).one_mem
  · change n 3 * (eElt f (fun j => B j 5))⁻¹ ∈ centerOf (dsQ L2 L1 S)
    have hc : eElt f (fun j => B j 5) = n 3 := by simpa using hcolN 3
    rw [hc, mul_inv_cancel]
    exact (centerOf (dsQ L2 L1 S)).one_mem

private theorem isAct_conj_k [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G}
    {X : Fin 3 → Matrix (Fin 2) (Fin 4) (ZMod 2)} (hu : u ∈ F.W)
    (hu' : u ∉ centerOf (dsQ L2 L1 S)) (hn : F.IsNLift n) (hX : F.IsAct u n X) :
    F.k * u * F.k⁻¹ ∈ F.W ∧ F.k * u * F.k⁻¹ ∉ centerOf (dsQ L2 L1 S) ∧
      F.IsAct (F.k * u * F.k⁻¹) n (fun t => om ^ 2 * X t) := by
  classical
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let u1 : G := F.k * u * F.k⁻¹
  let B : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
    v2Block om (0 : Matrix (Fin 2) (Fin 4) (ZMod 2))
      (1 : Matrix (Fin 4) (Fin 4) (ZMod 2))
  have hu1W : u1 ∈ F.W := by
    dsimp only [u1]
    exact (Subgroup.mem_normalizer_iff.mp (F.k_le_normalizer_W) u).mp hu
  have hu1' : u1 ∉ Z2 := by
    intro h
    apply hu'
    have hk : F.k⁻¹ ∈ Subgroup.normalizer (Z2 : Set G) :=
      (Subgroup.normalizer (Z2 : Set G)).inv_mem (F.k_mem_normalizer_Z2)
    have h2 : F.k⁻¹ * u1 * (F.k⁻¹)⁻¹ ∈ Z2 :=
      (Subgroup.mem_normalizer_iff.mp hk u1).mp h
    have heq : F.k⁻¹ * u1 * (F.k⁻¹)⁻¹ = u := by
      dsimp only [u1]; group
    rwa [heq] at h2
  have hframe : ∀ i : Fin 6, v2Frame F.k u1 n i *
      (eElt (v2Frame F.k u n) fun j => B j i)⁻¹ ∈ Z2 :=
    frame_change_k F hD hu
  have hspec := F.special_data hD
  have hgZ_a : ∀ z ∈ Z2, F.a * z * F.a⁻¹ ∈ Z2 :=
    fun z hz => hspec.2.2.2.2.2.2.1 F.a F.a_mem.1 z hz
  have hgZ_b : ∀ z ∈ Z2, F.b * z * F.b⁻¹ ∈ Z2 :=
    fun z hz => hspec.2.2.2.2.2.2.1 F.b F.b_mem.1 z hz
  have hgZ_k : ∀ z ∈ Z2, F.k * z * F.k⁻¹ ∈ Z2 :=
    fun z hz => (Subgroup.mem_normalizer_iff.mp F.k_mem_normalizer_Z2 z).mp hz
  have hRB : ∀ (U : Matrix (Fin 2) (Fin 2) (ZMod 2))
      (Xg : Matrix (Fin 2) (Fin 4) (ZMod 2)) (N : Matrix (Fin 4) (Fin 4) (ZMod 2)),
      U * om = om * U →
      v2Block U Xg N * B = B * v2Block U (om ^ 2 * Xg) N := by
    intro U Xg N hU
    rw [show B = v2Block om (0 : Matrix (Fin 2) (Fin 4) (ZMod 2))
        (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) from rfl, v2Block_mul, v2Block_mul]
    have hX : om * (om ^ 2 * Xg) = Xg := by
      rw [← Matrix.mul_assoc, omega2_mul_omega2_sq, Matrix.one_mul]
    rw [hX, hU]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
      zero_add, add_zero]
  refine ⟨hu1W, hu1', ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact conj_congr_of_matrix F hD hu hn hframe F.a_mem.1 hX.1 hgZ_a
      (hRB 1 (X 0) aN (by rw [Matrix.one_mul, Matrix.mul_one]))
  · exact conj_congr_of_matrix F hD hu hn hframe F.b_mem.1 hX.2.1 hgZ_b
      (hRB 1 (X 1) bN (by rw [Matrix.one_mul, Matrix.mul_one]))
  · exact conj_congr_of_matrix F hD hu hn hframe F.k_mem_A hX.2.2 hgZ_k
      (hRB om (X 2) F.Mk rfl)

theorem G24Frame2.isAct_rescale [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G}
    {X : Fin 3 → Matrix (Fin 2) (Fin 4) (ZMod 2)} (hu : u ∈ F.W)
    (hu' : u ∉ centerOf (dsQ L2 L1 S)) (hn : F.IsNLift n) (hX : F.IsAct u n X) (s : ℕ) :
    F.k ^ s * u * (F.k ^ s)⁻¹ ∈ F.W ∧ F.k ^ s * u * (F.k ^ s)⁻¹ ∉ centerOf (dsQ L2 L1 S) ∧
    F.IsAct (F.k ^ s * u * (F.k ^ s)⁻¹) n fun t => om ^ (2 * s) * X t := by
  induction s with
  | zero =>
    have hY : (fun t : Fin 3 => om ^ (2 * 0) * X t) = X := by
      funext t
      simp
    have hk : F.k ^ 0 * u * (F.k ^ 0)⁻¹ = u := by simp
    rw [hk, hY]
    exact ⟨hu, hu', hX⟩
  | succ s ih =>
    obtain ⟨huW, huZ, huX⟩ := ih
    obtain ⟨h1, h2, h3⟩ := isAct_conj_k F hD huW huZ hn huX
    have hpow : F.k ^ (s + 1) * u * (F.k ^ (s + 1))⁻¹ =
        F.k * (F.k ^ s * u * (F.k ^ s)⁻¹) * F.k⁻¹ := by
      rw [pow_succ']
      group
    have hY : (fun t : Fin 3 => om ^ 2 * (om ^ (2 * s) * X t)) =
        fun t : Fin 3 => om ^ (2 * (s + 1)) * X t := by
      funext t
      rw [← Matrix.mul_assoc, ← pow_add, show 2 + 2 * s = 2 * (s + 1) from by ring]
    refine ⟨?_, ?_, ?_⟩
    · rwa [hpow]
    · rwa [hpow]
    · rwa [← hpow, hY] at h3

private theorem v2Block_shift_mul (U : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (X : Matrix (Fin 2) (Fin 4) (ZMod 2)) (N : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (m : Matrix (Fin 2) (Fin 4) (ZMod 2)) :
    v2Block U X N * v2Block 1 m 1 =
      v2Block 1 m 1 * v2Block U (X + m * N + U * m) N := by
  rw [v2Block_mul, v2Block_mul]
  simp only [Matrix.one_mul, Matrix.mul_one]
  have hmm : (m * N + m * N : Matrix (Fin 2) (Fin 4) (ZMod 2)) = 0 := by
    ext i j
    exact CharTwo.add_self_eq_zero _
  rw [show X + m * N + U * m + m * N = U * m + X from by
    calc X + m * N + U * m + m * N = X + U * m + (m * N + m * N) := by abel
      _ = X + U * m := by rw [hmm, add_zero]
      _ = U * m + X := by abel]

private theorem shift_isNLift [Finite G] (F : G24Frame2 L1 L2 S)
    {u : G} {n : Fin 4 → G} (hu : u ∈ F.W)
    (hn : F.IsNLift n) (m : Matrix (Fin 2) (Fin 4) (ZMod 2)) :
    F.IsNLift (fun j => n j * eElt ![u, F.k * u * F.k⁻¹] fun s => m s j) := by
  classical
  let Q2 : Subgroup G := dsQ L2 L1 S
  let u1 : G := F.k * u * F.k⁻¹
  let fU : Fin 2 → G := show Fin 2 → G from ![u, u1]
  have hu1W : u1 ∈ F.W := by
    dsimp only [u1]
    exact (Subgroup.mem_normalizer_iff.mp (F.k_le_normalizer_W) u).mp hu
  have hfUW : ∀ i, fU i ∈ F.W := by
    intro i
    fin_cases i
    · simpa [fU] using hu
    · simpa [fU] using hu1W
  have hfUQ : ∀ i, fU i ∈ Q2 := fun i => ((F.mem_W (fU i)).mp (hfUW i)).1
  have hnQ : ∀ j, n j ∈ Q2 := fun j => (hn j).choose
  have hnφ : ∀ j, F.FN.φ ⟨n j, hnQ j⟩ =
      Multiplicative.ofAdd (Pi.single j (1 : ZMod 2)) := by
    intro j
    obtain ⟨h, hh⟩ := hn j
    have hsub : (⟨n j, hnQ j⟩ : ↥Q2) = ⟨n j, h⟩ := Subtype.ext rfl
    rw [hsub]
    exact hh
  have hqW : ∀ j : Fin 4, eElt fU (fun s => m s j) ∈ F.W := fun j =>
    eElt_mem_of_forall_mem hfUW _
  have hqQ : ∀ j : Fin 4, eElt fU (fun s => m s j) ∈ Q2 :=
    fun j => ((F.mem_W _).mp (hqW j)).1
  intro j
  have hmem : n j * eElt fU (fun s => m s j) ∈ Q2 := Q2.mul_mem (hnQ j) (hqQ j)
  refine ⟨hmem, ?_⟩
  have hqker : F.FN.φ ⟨eElt fU (fun s => m s j), hqQ j⟩ = 1 :=
    (F.FN.ker _).mpr (hqW j)
  have hsplit : (⟨n j * eElt fU (fun s => m s j), hmem⟩ : ↥Q2) =
      ⟨n j, hnQ j⟩ * ⟨eElt fU (fun s => m s j), hqQ j⟩ := rfl
  rw [hsplit, map_mul, hnφ j, hqker, mul_one]

private theorem frame_change_shift_N [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G} (hu : u ∈ F.W)
    (hn : F.IsNLift n) (m : Matrix (Fin 2) (Fin 4) (ZMod 2)) :
    ∀ d : Fin 4,
      v2Frame F.k u (fun j => n j * eElt ![u, F.k * u * F.k⁻¹] fun s => m s j)
          (Fin.natAdd 2 d) *
      (eElt (v2Frame F.k u n) fun i => v2Block 1 m 1 i (Fin.natAdd 2 d))⁻¹ ∈
        centerOf (dsQ L2 L1 S) := by
  classical
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let u1 : G := F.k * u * F.k⁻¹
  let fU : Fin 2 → G := show Fin 2 → G from ![u, u1]
  let n' : Fin 4 → G := fun j => n j * eElt fU (fun s => m s j)
  let f : Fin 6 → G := v2Frame F.k u n
  let B : Matrix (Fin 6) (Fin 6) (ZMod 2) := v2Block 1 m 1
  have hu1W : u1 ∈ F.W := by
    dsimp only [u1]
    exact (Subgroup.mem_normalizer_iff.mp (F.k_le_normalizer_W) u).mp hu
  have hfUW : ∀ i, fU i ∈ F.W := by
    intro i
    fin_cases i
    · simpa [fU] using hu
    · simpa [fU] using hu1W
  have hnQ : ∀ j, n j ∈ Q2 := fun j => (hn j).choose
  have hqW : ∀ j : Fin 4, eElt fU (fun s => m s j) ∈ F.W := fun j =>
    eElt_mem_of_forall_mem hfUW _
  have hqQ : ∀ j : Fin 4, eElt fU (fun s => m s j) ∈ Q2 :=
    fun j => ((F.mem_W _).mp (hqW j)).1
  intro d
  change v2Frame F.k u n' (Fin.natAdd 2 d) *
    (eElt f (fun i => B i (Fin.natAdd 2 d)))⁻¹ ∈ Z2
  let q : Fin 4 → ZMod 2 := Pi.single d (1 : ZMod 2)
  have hb : (fun i : Fin 6 => B i (Fin.natAdd 2 d)) =
      Fin.append (fun a : Fin 2 => m a d) q := by
    rw [show B = v2Block 1 m 1 from rfl, v2Block_col_N]
    congr 1
    funext t
    simp only [Matrix.one_apply]
    by_cases h : d = t
    · subst h
      simp [q]
    · simp [q, Ne.symm h]
  have hBcol : eElt f (fun i => B i (Fin.natAdd 2 d)) =
      eElt fU (fun s => m s d) * n d := by
    rw [show f = Fin.append fU n from v2Frame_eq_append F.k u n, hb,
      eElt_eq_castAdd_mul_natAdd]
    simp only [Fin.append_left, Fin.append_right]
    rw [show q = Pi.single d (1 : ZMod 2) from rfl, eElt_single]
  rw [v2Frame_natAdd F.k u n' d, hBcol]
  change n d * eElt fU (fun s => m s d) *
    (eElt fU (fun s => m s d) * n d)⁻¹ ∈ Z2
  rw [show n d * eElt fU (fun s => m s d) *
      (eElt fU (fun s => m s d) * n d)⁻¹ =
      ⁅n d, eElt fU (fun s => m s d)⁆ from by
    rw [commutatorElement_def]
    group]
  exact CFSG.Quasithin.IsSpecialPGroup.commutator_le_centerOf hD.special_right
    (Subgroup.commutator_mem_commutator (hnQ d) (hqQ d))

private theorem frame_change_shift [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G} (hu : u ∈ F.W)
    (hn : F.IsNLift n) (m : Matrix (Fin 2) (Fin 4) (ZMod 2)) :
    ∀ i : Fin 6,
      v2Frame F.k u (fun j => n j * eElt ![u, F.k * u * F.k⁻¹] fun s => m s j) i *
      (eElt (v2Frame F.k u n) fun j => v2Block 1 m 1 j i)⁻¹ ∈
        centerOf (dsQ L2 L1 S) := by
  classical
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let u1 : G := F.k * u * F.k⁻¹
  let fU : Fin 2 → G := show Fin 2 → G from ![u, u1]
  let n' : Fin 4 → G := fun j => n j * eElt fU (fun s => m s j)
  let f : Fin 6 → G := v2Frame F.k u n
  let f' : Fin 6 → G := v2Frame F.k u n'
  let B : Matrix (Fin 6) (Fin 6) (ZMod 2) := v2Block 1 m 1
  have hu1W : u1 ∈ F.W := by
    dsimp only [u1]
    exact (Subgroup.mem_normalizer_iff.mp (F.k_le_normalizer_W) u).mp hu
  have hfUW : ∀ i, fU i ∈ F.W := by
    intro i
    fin_cases i
    · simpa [fU] using hu
    · simpa [fU] using hu1W
  have hfUQ : ∀ i, fU i ∈ Q2 := fun i => ((F.mem_W (fU i)).mp (hfUW i)).1
  have hnQ : ∀ j, n j ∈ Q2 := fun j => (hn j).choose
  have hqW : ∀ j : Fin 4, eElt fU (fun s => m s j) ∈ F.W := fun j =>
    eElt_mem_of_forall_mem hfUW _
  have hqQ : ∀ j : Fin 4, eElt fU (fun s => m s j) ∈ Q2 :=
    fun j => ((F.mem_W _).mp (hqW j)).1
  have hframe0 : ∀ a : Fin 2, f' (Fin.castAdd 4 a) *
      (eElt f (fun i => B i (Fin.castAdd 4 a)))⁻¹ ∈ Z2 := by
    intro a
    dsimp only [f, f']
    have hb : (fun i : Fin 6 => B i (Fin.castAdd 4 a)) =
        fun i : Fin 6 => if h : i.val < 2 then
          (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) ⟨i.val, h⟩ a else 0 := by
      simpa only [B] using
        (v2Block_col_U (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) m 1 a)
    rw [v2Frame_castAdd F.k u n' a, hb, G24Vertex2.eElt_block_one F.k u n a, mul_inv_cancel]
    exact Z2.one_mem
  have hframeN := frame_change_shift_N F hD hu hn m
  intro i
  refine Fin.addCases (m := 2) (n := 4) (fun a => ?_) (fun d => ?_) i
  · exact hframe0 a
  · exact hframeN d

theorem G24Frame2.isAct_shift [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G}
    {X : Fin 3 → Matrix (Fin 2) (Fin 4) (ZMod 2)} (hu : u ∈ F.W)
    (hu' : u ∉ centerOf (dsQ L2 L1 S)) (hn : F.IsNLift n) (hX : F.IsAct u n X)
    (m : Matrix (Fin 2) (Fin 4) (ZMod 2)) :
    F.IsNLift (fun j => n j * eElt ![u, F.k * u * F.k⁻¹] fun s => m s j) ∧
    F.IsAct u (fun j => n j * eElt ![u, F.k * u * F.k⁻¹] fun s => m s j)
      ![X 0 + m * aN + m, X 1 + m * bN + m, X 2 + m * F.Mk + om * m] := by
  classical
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let n' : Fin 4 → G := fun j => n j * eElt ![u, F.k * u * F.k⁻¹] fun s => m s j
  let B : Matrix (Fin 6) (Fin 6) (ZMod 2) := v2Block 1 m 1
  have hn' : F.IsNLift n' := shift_isNLift F hu hn m
  have hframe : ∀ i : Fin 6, v2Frame F.k u n' i *
      (eElt (v2Frame F.k u n) fun j => B j i)⁻¹ ∈ Z2 :=
    frame_change_shift F hD hu hn m
  have hspec := F.special_data hD
  have hgZ_a : ∀ z ∈ Z2, F.a * z * F.a⁻¹ ∈ Z2 :=
    fun z hz => hspec.2.2.2.2.2.2.1 F.a F.a_mem.1 z hz
  have hgZ_b : ∀ z ∈ Z2, F.b * z * F.b⁻¹ ∈ Z2 :=
    fun z hz => hspec.2.2.2.2.2.2.1 F.b F.b_mem.1 z hz
  have hgZ_k : ∀ z ∈ Z2, F.k * z * F.k⁻¹ ∈ Z2 :=
    fun z hz => (Subgroup.mem_normalizer_iff.mp F.k_mem_normalizer_Z2 z).mp hz
  have hRB : ∀ (U : Matrix (Fin 2) (Fin 2) (ZMod 2))
      (Xg : Matrix (Fin 2) (Fin 4) (ZMod 2)) (N : Matrix (Fin 4) (Fin 4) (ZMod 2)),
      v2Block U Xg N * B = B * v2Block U (Xg + m * N + U * m) N := by
    intro U Xg N
    rw [show B = v2Block 1 m 1 from rfl]
    exact v2Block_shift_mul U Xg N m
  have hRB_a : v2Block 1 (X 0) aN * B =
      B * v2Block 1 (X 0 + m * aN + m) aN := by
    have h := hRB 1 (X 0) aN
    simpa only [Matrix.one_mul] using h
  have hRB_b : v2Block 1 (X 1) bN * B =
      B * v2Block 1 (X 1 + m * bN + m) bN := by
    have h := hRB 1 (X 1) bN
    simpa only [Matrix.one_mul] using h
  have hRB_k : v2Block om (X 2) F.Mk * B =
      B * v2Block om (X 2 + m * F.Mk + om * m) F.Mk :=
    hRB om (X 2) F.Mk
  refine ⟨hn', ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro j
    simpa only [Matrix.cons_val_zero] using
      conj_congr_of_matrix F hD hu hn hframe F.a_mem.1 hX.1 hgZ_a hRB_a j
  · intro j
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using
      conj_congr_of_matrix F hD hu hn hframe F.b_mem.1 hX.2.1 hgZ_b hRB_b j
  · intro j
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] using
      conj_congr_of_matrix F hD hu hn hframe F.k_mem_A hX.2.2 hgZ_k hRB_k j

end CFSG.Quasithin.F112R.St84
