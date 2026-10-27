module

public import CFSG.Quasithin.Recognition.St84.G24Vertex2Indep
import CFSG.GroupTheory.FixedPointFreeModCentral
import CFSG.Quasithin.Background.SpecialPGroupCenter
import CFSG.Quasithin.Recognition.St84.G24Tools

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.Quasithin.F7 CFSG.Quasithin.St84
open CFSG.Quasithin.KGC31 (eElt eElt_zero eElt_single eElt_add eElt_injective
  conj_eElt map_eElt)
open CFSG.GroupTheory (eElt_mem_of_forall_mem eElt_add_mul_inv_mem conj_eElt_mul_inv_mem
  eElt_eq_castAdd_mul_natAdd eEltQuotEquiv eEltQuotEquiv_ofAdd)
open Certificates.A5GL42 (aN bN)
open CFSG.Quasithin.H.Q13 (om)
open scoped commutatorElement Matrix

variable {G : Type} [Group G]
variable {L1 L2 S : Subgroup G}

theorem G24Frame2.k_conj_mem_center [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} (hu : u ∈ F.W) :
    F.k * (F.k * u * F.k⁻¹) * F.k⁻¹ *
      (u * (F.k * u * F.k⁻¹))⁻¹ ∈ centerOf (dsQ L2 L1 S) := by
  refine CFSG.GroupTheory.conj_conj_mul_inv_mem_of_pow_three_eq_one
    (Q := F.W) (Z := centerOf (dsQ L2 L1 S)) (k := F.k) (x := u) ?_ ?_ ?_ ?_ ?_ ?_ hu
  · rw [← F.orderOf_k]; exact pow_orderOf_eq_one F.k
  · intro q hq
    exact (Subgroup.mem_normalizer_iff.mp F.k_le_normalizer_W q).mp hq
  · intro z hz q hq
    exact (F.special_data hD).2.2.2.1 z hz q (((F.mem_W q).mp hq).1)
  · intro q hq
    exact (F.special_data hD).2.2.2.2.2.1 q (((F.mem_W q).mp hq).1)
  · intro q hq r hr
    exact CFSG.Quasithin.IsSpecialPGroup.commutator_le_centerOf hD.special_right
      (Subgroup.commutator_mem_commutator (((F.mem_W q).mp hq).1)
        (((F.mem_W r).mp hr).1))
  · intro q hq hfix
    exact F.mem_Z2_of_fixed_on_W hD hq hfix

private theorem FN_coord [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} (hu : u ∈ F.W)
    (hu' : u ∉ centerOf (dsQ L2 L1 S)) {n : Fin 4 → G} (hn : F.IsNLift n)
    {x : G} (hx : x ∈ dsQ L2 L1 S) :
    ∃ v : Fin 6 → ZMod 2, ∃ y ∈ centerOf (dsQ L2 L1 S),
      x = eElt (v2Frame F.k u n) v * y ∧
      Multiplicative.toAdd (F.FN.φ ⟨x, hx⟩) = fun j : Fin 4 => v (Fin.natAdd 2 j) := by
  classical
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  obtain ⟨hfQ, hfC, hfSq, hfCm, -⟩ := F.frame_spec hD hu hn
  have hnQ : ∀ j, n j ∈ Q2 := fun j => (hn j).choose
  obtain ⟨v, y, hy, hxy⟩ := F.exists_eElt_mul hD hu hu' hn x hx
  let w : Fin 6 → Fin 4 → ZMod 2 := fun i =>
    if h : 2 ≤ i.val then Pi.single ⟨i.val - 2, by omega⟩ (1 : ZMod 2) else 0
  have hv2W : F.k * u * F.k⁻¹ ∈ F.W :=
    (Subgroup.mem_normalizer_iff.mp (F.k_le_normalizer_W) u).mp hu
  have hφw : ∀ i, Multiplicative.toAdd (F.FN.φ ⟨v2Frame F.k u n i, hfQ i⟩) = w i := by
    intro i
    fin_cases i
    · simp [v2Frame, w]
      have h : F.FN.φ ⟨u, hfQ 0⟩ = 1 := (F.FN.ker _).mpr (by simpa using hu)
      rw [h]
    · simp [v2Frame, w]
      have h : F.FN.φ ⟨F.k * u * F.k⁻¹, hfQ 1⟩ = 1 :=
        (F.FN.ker _).mpr (by simpa using hv2W)
      rw [h]
    · simp [v2Frame, w, (hn 0).choose_spec]
    · simp [v2Frame, w, (hn 1).choose_spec]
    · simp [v2Frame, w, (hn 2).choose_spec]
    · simp [v2Frame, w, (hn 3).choose_spec]
  have hsum := G24Vertex2.toAdd_phi_eElt_gen F.FN.φ (v2Frame F.k u n) hfQ w hφw v
  have hZ2W : Z2 ≤ F.W := F.Z2_le_W
  have hyW : y ∈ F.W := hZ2W hy
  have hφy : F.FN.φ ⟨y, hy.1⟩ = 1 := (F.FN.ker _).mpr hyW
  have hφx : F.FN.φ ⟨x, hx⟩ =
      F.FN.φ ⟨eElt (v2Frame F.k u n) v, eElt_mem_of_forall_mem hfQ v⟩ := by
    have hsub : (⟨x, hx⟩ : ↥Q2) =
        ⟨eElt (v2Frame F.k u n) v, eElt_mem_of_forall_mem hfQ v⟩ * ⟨y, hy.1⟩ := by
      apply Subtype.ext
      simpa [Subgroup.coe_mul] using hxy
    rw [hsub, map_mul, hφy, mul_one]
  have hsum_last : (∑ i : Fin 6, (v i).val • w i) = fun j : Fin 4 => v (Fin.natAdd 2 j) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single (Fin.natAdd 2 j)]
    · have hval : ((v (Fin.natAdd 2 j)).val : ZMod 2) = v (Fin.natAdd 2 j) := by
        apply ZMod.val_injective 2
        rw [ZMod.val_natCast_of_lt (ZMod.val_lt (v (Fin.natAdd 2 j)))]
      simp [w, Pi.single, hval, ZMod.val_one]
    · intro b _ hb
      by_cases h2 : 2 ≤ b.val
      · have hne : (⟨b.val - 2, by omega⟩ : Fin 4) ≠ j := by
          intro he
          apply hb
          apply Fin.ext
          have hv := congrArg Fin.val he
          simp at hv
          simp [Fin.natAdd]
          omega
        have hne' : j ≠ (⟨b.val - 2, by omega⟩ : Fin 4) := fun h => hne h.symm
        simp [w, h2, Pi.single_eq_of_ne hne']
      · simp [w, h2]
    · intro hj
      simp at hj
  refine ⟨v, y, hy, hxy, ?_⟩
  rw [hφx, hsum, hsum_last]

private theorem act_for_cols [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G} (hu : u ∈ F.W)
    (hn : F.IsNLift n) {g : G}
    {U : Matrix (Fin 2) (Fin 2) (ZMod 2)} {X : Matrix (Fin 2) (Fin 4) (ZMod 2)}
    {N : Matrix (Fin 4) (Fin 4) (ZMod 2)} {v : Fin 4 → Fin 6 → ZMod 2}
    {y : Fin 4 → G}
    (hU : ∀ j : Fin 2, g * (show Fin 2 → G from ![u, F.k * u * F.k⁻¹]) j * g⁻¹ *
      (eElt (v2Frame F.k u n) fun i => if h : i.val < 2 then U ⟨i.val, h⟩ j else 0)⁻¹ ∈
        centerOf (dsQ L2 L1 S))
    (hx : ∀ j : Fin 4, g * n j * g⁻¹ = eElt (v2Frame F.k u n) (v j) * y j)
    (hy : ∀ j : Fin 4, y j ∈ centerOf (dsQ L2 L1 S))
    (hvj : ∀ j : Fin 4, v j = Fin.append (fun i : Fin 2 => X i j)
      (fun k : Fin 4 => N k j)) :
    ∀ j : Fin 6, g * v2Frame F.k u n j * g⁻¹ *
      (eElt (v2Frame F.k u n) fun i => v2Block U X N i j)⁻¹ ∈
        centerOf (dsQ L2 L1 S) := by
  obtain ⟨hfQ, -, -, -, -⟩ := F.frame_spec hD hu hn
  intro j6
  by_cases hj : j6.val < 2
  · let j2 : Fin 2 := ⟨j6.val, hj⟩
    have hj6 : j6 = Fin.castAdd 4 j2 := Fin.ext (by simp [j2])
    have hbn : (fun i : Fin 6 => v2Block U X N i j6) =
        fun i : Fin 6 => if h : i.val < 2 then U ⟨i.val, h⟩ j2 else 0 := by
      rw [hj6]
      exact v2Block_col_U U X N j2
    rw [hbn]
    have hfj : (show Fin 2 → G from ![u, F.k * u * F.k⁻¹]) j2 = v2Frame F.k u n j6 := by
      rw [hj6]
      exact (v2Frame_castAdd F.k u n j2).symm
    have hspec := hU j2
    rwa [hfj] at hspec
  · let j4 : Fin 4 := ⟨j6.val - 2, by omega⟩
    have hj6 : j6 = Fin.natAdd 2 j4 := Fin.ext (by simp only [j4, Fin.natAdd]; omega)
    have hbn : (fun i : Fin 6 => v2Block U X N i j6) = v j4 := by
      rw [hj6, v2Block_col_N]
      exact (hvj j4).symm
    rw [hbn]
    have hfj : v2Frame F.k u n j6 = n j4 := by
      rw [hj6]
      exact v2Frame_natAdd F.k u n j4
    have hxeq : g * v2Frame F.k u n j6 * g⁻¹ = g * n j4 * g⁻¹ := by rw [hfj]
    rw [hxeq, hx j4]
    have hconj := G24Vertex2.conj_eq_of_mem_centerOf (hy j4)
      (eElt_mem_of_forall_mem hfQ (v j4))
    rw [hconj]
    exact hy j4

private theorem exists_act_for [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G} (hu : u ∈ F.W)
    (hu' : u ∉ centerOf (dsQ L2 L1 S)) (hn : F.IsNLift n)
    (g : G) (gP : ↥(L2 ⊔ bigB L1 L2 S)) (hg : (gP : G) = g)
    (U : Matrix (Fin 2) (Fin 2) (ZMod 2)) (N : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hM : glMat (F.FN.M gP) = N)
    (hU : ∀ j : Fin 2, g * (show Fin 2 → G from ![u, F.k * u * F.k⁻¹]) j * g⁻¹ *
      (eElt (v2Frame F.k u n) fun i => if h : i.val < 2 then U ⟨i.val, h⟩ j else 0)⁻¹ ∈
        centerOf (dsQ L2 L1 S)) :
    ∃ X : Matrix (Fin 2) (Fin 4) (ZMod 2),
      ∀ j : Fin 6, g * v2Frame F.k u n j * g⁻¹ *
        (eElt (v2Frame F.k u n) fun i => v2Block U X N i j)⁻¹ ∈
          centerOf (dsQ L2 L1 S) := by
  classical
  let Q2 : Subgroup G := dsQ L2 L1 S
  let f := v2Frame F.k u n
  obtain ⟨hfQ, hfC, hfSq, hfCm, -⟩ := F.frame_spec hD hu hn
  have hnQ : ∀ j, n j ∈ Q2 := fun j => (hn j).choose
  have hQN : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (Q2 : Set G) :=
    P_le_normalizer_dsQ_right L1 L2 S
  let x : Fin 4 → G := fun j => g * n j * g⁻¹
  have hxQ : ∀ j, x j ∈ Q2 := fun j => by
    have := (Subgroup.mem_normalizer_iff.mp (hQN gP.2) (n j)).mp (hnQ j)
    simpa [x, hg] using this
  choose v y hy hxy hcoord using fun j =>
    FN_coord F hD hu hu' hn (hxQ j)
  have hlast : ∀ (j : Fin 4) (k : Fin 4), v j (Fin.natAdd 2 k) = N k j := by
    intro j k
    let hxP : ↥Q2 := ⟨x j, hxQ j⟩
    let hnP : ↥Q2 := ⟨n j, hnQ j⟩
    have hact := F.FN.act gP hnP hxP (by
      rw [hg])
    have hNcol : Multiplicative.toAdd (F.FN.φ hxP) = fun k : Fin 4 => N k j := by
      rw [← hact, hM]
      have hφ : Multiplicative.toAdd (F.FN.φ hnP) = Pi.single j (1 : ZMod 2) := by
        have h := congrArg Multiplicative.toAdd ((hn j).choose_spec)
        simpa [hnP] using h
      rw [hφ, Matrix.mulVec_single_one]
      rfl
    have h1 := congrFun (hcoord j) k
    have h2 := congrFun hNcol k
    exact h1.symm.trans h2
  let X : Matrix (Fin 2) (Fin 4) (ZMod 2) := fun i j => v j (Fin.castAdd 4 i)
  have hvj : ∀ j : Fin 4, v j = Fin.append (fun i : Fin 2 => X i j)
      (fun k : Fin 4 => N k j) := by
    intro j
    funext i
    refine Fin.addCases (m := 2) (n := 4) (fun l => ?_) (fun r => ?_) i
    · simp [X, Fin.append_left]
    · rw [hlast j r]
      exact (Fin.append_right (fun i : Fin 2 => X i j) (fun k : Fin 4 => N k j) r).symm
  exact ⟨X, act_for_cols F hD hu hn hU hxy hy hvj⟩

theorem G24Vertex2.eElt_block_one (k u : G) (n : Fin 4 → G) (j : Fin 2) :
    eElt (v2Frame k u n)
        (fun i : Fin 6 => if h : i.val < 2 then (1 : Matrix (Fin 2) (Fin 2) (ZMod 2))
          ⟨i.val, h⟩ j else 0) =
      (show Fin 2 → G from ![u, k * u * k⁻¹]) j := by
  let fU : Fin 2 → G := show Fin 2 → G from ![u, k * u * k⁻¹]
  rw [v2Frame_eq_append, eElt_eq_castAdd_mul_natAdd]
  have hval1 : (fun i : Fin 2 => Fin.append fU n (Fin.castAdd 4 i)) = fU := by
    funext i
    exact Fin.append_left fU n i
  have hval2 : (fun j : Fin 4 => Fin.append fU n (Fin.natAdd 2 j)) = n := by
    funext j
    exact Fin.append_right fU n j
  have h1 : (fun i : Fin 2 => (fun i' : Fin 6 => if h : i'.val < 2 then
      (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) ⟨i'.val, h⟩ j else 0) (Fin.castAdd 4 i)) =
      Pi.single j (1 : ZMod 2) := by
    funext i
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, Pi.single]
  have h2 : (fun k : Fin 4 => (fun i' : Fin 6 => if h : i'.val < 2 then
      (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) ⟨i'.val, h⟩ j else 0) (Fin.natAdd 2 k)) = 0 := by
    funext k
    simp [show ¬ (2 + k.val < 2) by omega]
  rw [hval1, hval2, h1, h2, eElt_zero, mul_one, eElt_single]

theorem G24Vertex2.eElt_block_omega (k u : G) (n : Fin 4 → G) :
    eElt (v2Frame k u n)
        (fun i : Fin 6 => if h : i.val < 2 then om ⟨i.val, h⟩ 1 else 0) =
      u * (k * u * k⁻¹) := by
  let fU : Fin 2 → G := show Fin 2 → G from ![u, k * u * k⁻¹]
  rw [v2Frame_eq_append, eElt_eq_castAdd_mul_natAdd]
  have hval1 : (fun i : Fin 2 => Fin.append fU n (Fin.castAdd 4 i)) = fU := by
    funext i
    exact Fin.append_left fU n i
  have hval2 : (fun j : Fin 4 => Fin.append fU n (Fin.natAdd 2 j)) = n := by
    funext j
    exact Fin.append_right fU n j
  have h1 : (fun i : Fin 2 => (fun i' : Fin 6 => if h : i'.val < 2 then
      om ⟨i'.val, h⟩ 1 else 0) (Fin.castAdd 4 i)) = fun _ : Fin 2 => (1 : ZMod 2) := by
    funext i
    fin_cases i <;> simp [om]
  have h2 : (fun k : Fin 4 => (fun i' : Fin 6 => if h : i'.val < 2 then
      om ⟨i'.val, h⟩ 1 else 0) (Fin.natAdd 2 k)) = 0 := by
    funext k
    simp [show ¬ (2 + k.val < 2) by omega]
  rw [hval1, hval2, h1, h2, eElt_zero, mul_one]
  have hlist : List.finRange 2 = [0, 1] := rfl
  simpa [eElt, List.ofFn_eq_map, hlist, ZMod.val_one, fU]

theorem G24Frame2.exists_act [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G} (hu : u ∈ F.W)
    (hu' : u ∉ centerOf (dsQ L2 L1 S)) (hn : F.IsNLift n) :
    ∃ X, F.IsAct u n X := by
  classical
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let fU : Fin 2 → G := show Fin 2 → G from ![u, F.k * u * F.k⁻¹]
  have hfUW : ∀ i, fU i ∈ F.W := by
    intro i
    fin_cases i
    · simpa [fU] using hu
    · simpa [fU] using (Subgroup.mem_normalizer_iff.mp (F.k_le_normalizer_W) u).mp hu
  have hUa : ∀ j : Fin 2, F.a *
      (show Fin 2 → G from ![u, F.k * u * F.k⁻¹]) j * F.a⁻¹ *
      (eElt (v2Frame F.k u n) fun i => if h : i.val < 2 then
        (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) ⟨i.val, h⟩ j else 0)⁻¹ ∈
        centerOf (dsQ L2 L1 S) := by
    intro j
    rw [G24Vertex2.eElt_block_one F.k u n j]
    have hmem := (F.mem_W (fU j)).mp (hfUW j)
    have hcomm := hmem.2 F.a F.a_mem.2
    have heq : F.a * fU j * F.a⁻¹ * (fU j)⁻¹ = ⁅fU j, F.a⁆⁻¹ := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact Z2.inv_mem hcomm
  have hUb : ∀ j : Fin 2, F.b *
      (show Fin 2 → G from ![u, F.k * u * F.k⁻¹]) j * F.b⁻¹ *
      (eElt (v2Frame F.k u n) fun i => if h : i.val < 2 then
        (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) ⟨i.val, h⟩ j else 0)⁻¹ ∈
        centerOf (dsQ L2 L1 S) := by
    intro j
    rw [G24Vertex2.eElt_block_one F.k u n j]
    have hmem := (F.mem_W (fU j)).mp (hfUW j)
    have hcomm := hmem.2 F.b F.b_mem.2
    have heq : F.b * fU j * F.b⁻¹ * (fU j)⁻¹ = ⁅fU j, F.b⁆⁻¹ := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact Z2.inv_mem hcomm
  have hUk : ∀ j : Fin 2, F.k *
      (show Fin 2 → G from ![u, F.k * u * F.k⁻¹]) j * F.k⁻¹ *
      (eElt (v2Frame F.k u n) fun i => if h : i.val < 2 then
        om ⟨i.val, h⟩ j else 0)⁻¹ ∈ centerOf (dsQ L2 L1 S) := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · have hvec : (fun i : Fin 6 => if h : i.val < 2 then om ⟨i.val, h⟩ 0 else 0) =
          fun i : Fin 6 => if h : i.val < 2 then
            (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) ⟨i.val, h⟩ 1 else 0 := by
        funext i
        fin_cases i <;> simp [om, Matrix.one_apply]
      rw [hvec, G24Vertex2.eElt_block_one F.k u n 1]
      have h1 : (show Fin 2 → G from ![u, F.k * u * F.k⁻¹]) 0 = u := rfl
      have h2 : (show Fin 2 → G from ![u, F.k * u * F.k⁻¹]) 1 =
          F.k * u * F.k⁻¹ := rfl
      rw [h1, h2]
      have hone : F.k * u * F.k⁻¹ * (F.k * u * F.k⁻¹)⁻¹ = 1 := mul_inv_cancel _
      rw [hone]
      exact Z2.one_mem
    · fin_cases i
      have hj : ((fun i : Fin 1 => i) ⟨0, by omega⟩).succ = (1 : Fin 2) :=
        Fin.ext (by simp)
      rw [hj, G24Vertex2.eElt_block_omega F.k u n]
      exact k_conj_mem_center F hD hu
  have haP : (⟨F.a, (F.A_le F.a_mem.1).1⟩ : ↥(L2 ⊔ bigB L1 L2 S)) =
      ⟨F.a, (F.A_le F.a_mem.1).1⟩ := rfl
  obtain ⟨Xa, hXa⟩ := exists_act_for F hD hu hu' hn F.a
    ⟨F.a, (F.A_le F.a_mem.1).1⟩ rfl 1 aN (F.FN_a _ rfl) hUa
  obtain ⟨Xb, hXb⟩ := exists_act_for F hD hu hu' hn F.b
    ⟨F.b, (F.A_le F.b_mem.1).1⟩ rfl 1 bN (F.FN_b _ rfl) hUb
  obtain ⟨Xk, hXk⟩ := exists_act_for F hD hu hu' hn F.k F.kP rfl om F.Mk rfl hUk
  refine ⟨![Xa, Xb, Xk], ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro j
    simpa [Matrix.cons_val_zero] using hXa j
  · intro j
    simpa [Matrix.cons_val_one, Matrix.head_cons] using hXb j
  · intro j
    simpa [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using hXk j

theorem G24Frame2.mat_eq_of_actions [Finite G] (F : G24Frame2 L1 L2 S)
    (hD : G24LocalData L1 L2 S) {u : G} {n : Fin 4 → G} (hu : u ∈ F.W)
    (hu' : u ∉ centerOf (dsQ L2 L1 S)) (hn : F.IsNLift n) (g : G)
    {M M' : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (h1 : ∀ j : Fin 6, g * v2Frame F.k u n j * g⁻¹ *
      (eElt (v2Frame F.k u n) fun i => M i j)⁻¹ ∈ centerOf (dsQ L2 L1 S))
    (h2 : ∀ j : Fin 6, g * v2Frame F.k u n j * g⁻¹ *
      (eElt (v2Frame F.k u n) fun i => M' i j)⁻¹ ∈ centerOf (dsQ L2 L1 S)) : M = M' := by
  classical
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf (dsQ L2 L1 S)
  let f := v2Frame F.k u n
  obtain ⟨hfQ, hfC, hfSq, hfCm, -⟩ := F.frame_spec hD hu hn
  have hZQ : Z2 ≤ Q2 := inf_le_left
  have hZcQ : ∀ y ∈ Z2, ∀ x ∈ Q2, y * x = x * y :=
    (F.special_data hD).2.2.2.1
  haveI : (Z2.subgroupOf Q2).Normal := Subgroup.normal_of_le_center fun z hz =>
    Subgroup.mem_center_iff.mpr fun x => Subtype.ext (hZcQ z hz x x.2).symm
  ext i j
  let B : Fin 6 → ZMod 2 := fun k => M k j
  let B' : Fin 6 → ZMod 2 := fun k => M' k j
  have hBQ : eElt f B ∈ Q2 := eElt_mem_of_forall_mem hfQ B
  have hB'Q : eElt f B' ∈ Q2 := eElt_mem_of_forall_mem hfQ B'
  have hxQ : g * f j * g⁻¹ ∈ Q2 := by
    have hm := h1 j
    have heq : g * f j * g⁻¹ = (g * f j * g⁻¹ * (eElt f B)⁻¹) * eElt f B := by
      group
    rw [heq]
    exact Q2.mul_mem (hZQ hm) hBQ
  have hq1 : (QuotientGroup.mk ⟨g * f j * g⁻¹, hxQ⟩ : ↥Q2 ⧸ Z2.subgroupOf Q2) =
      QuotientGroup.mk ⟨eElt f B, hBQ⟩ := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [Subgroup.mem_subgroupOf, div_eq_mul_inv]
    exact h1 j
  have hq2 : (QuotientGroup.mk ⟨g * f j * g⁻¹, hxQ⟩ : ↥Q2 ⧸ Z2.subgroupOf Q2) =
      QuotientGroup.mk ⟨eElt f B', hB'Q⟩ := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [Subgroup.mem_subgroupOf, div_eq_mul_inv]
    exact h2 j
  have hmk := hq1.symm.trans hq2
  have hmem : eElt f B * (eElt f B')⁻¹ ∈ Z2 := by
    have := QuotientGroup.eq_iff_div_mem.mp hmk
    rwa [Subgroup.mem_subgroupOf, div_eq_mul_inv] at this
  have hveq := F.eElt_eq_of_mul_inv_mem hD hu hu' hn hmem
  have hcol := congrFun hveq i
  simpa [B, B'] using hcol

end CFSG.Quasithin.F112R.St84
