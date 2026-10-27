module

public import CFSG.RankThree.PartTwo.Sec21.Item233TablesBasic
public import CFSG.RankThree.PartTwo.Sec21.Item233TablesMatrix
public import CFSG.RankThree.PartTwo.KFacts.KS21SylowL44
import CFSG.LieType.Universal.SpecialLinear
import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec21.TablesL44

open Matrix CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.L44
open CFSG.RankThree.PartTwo.Sec21.Tables
open CFSG.Assembly (IsElemAbelian)

@[expose] def ω : F4ˣ := exists_omega_data.choose

theorem orderOf_ω : orderOf ω = 3 := exists_omega_data.choose_spec.1

theorem ω_pow_three : ω ^ 3 = 1 := exists_omega_data.choose_spec.2.1

@[expose] def eω (a : ZMod 3) : F4 := ((ω ^ a.val : F4ˣ) : F4)

theorem eω_add (a b : ZMod 3) : eω (a + b) = eω a * eω b := by
  rw [eω, eω, eω, ZMod.val_add, ← pow_eq_pow_mod _ ω_pow_three, pow_add, Units.val_mul]

theorem eω_zero : eω 0 = 1 := by simp [eω]

theorem eω_injective : Function.Injective eω := by
  intro a b h
  have h' : ω ^ a.val = ω ^ b.val := Units.ext h
  have := pow_inj_mod.mp h'
  rw [orderOf_ω, Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at this
  exact ZMod.val_injective 3 this

theorem eω_ne_zero (a : ZMod 3) : eω a ≠ 0 := Units.ne_zero _

@[expose] def dg (x : Fin 4 → ZMod 3) : Matrix (Fin 4) (Fin 4) F4 := diagonal fun i => eω (x i)

theorem dg_add (x y : Fin 4 → ZMod 3) : dg (x + y) = dg x * dg y := by
  rw [dg, dg, dg, diagonal_mul_diagonal]
  congr 1
  funext i
  exact eω_add _ _

theorem dg_zero : dg 0 = 1 := by
  rw [dg]
  simp [eω_zero]

theorem det_dg {x : Fin 4 → ZMod 3} (hx : ∑ i, x i = 0) : (dg x).det = 1 := by
  rw [dg, det_diagonal]
  have h : ∀ s : Finset (Fin 4), ∏ i ∈ s, eω (x i) = eω (∑ i ∈ s, x i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [eω_zero]
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, eω_add]
  rw [h, hx, eω_zero]

@[expose] def ext (v : Fin 3 → ZMod 3) : Fin 4 → ZMod 3 := ![v 0, v 1, v 2, -(v 0 + v 1 + v 2)]

theorem sum_ext (v : Fin 3 → ZMod 3) : ∑ i, ext v i = 0 := by
  simp only [ext, Fin.sum_univ_four]
  simp
  abel

theorem ext_add (v w : Fin 3 → ZMod 3) : ext (v + w) = ext v + ext w := by
  funext i
  fin_cases i <;> simp [ext]
  abel

theorem ext_zero : ext 0 = 0 := by
  decide

theorem ext_injective : Function.Injective ext := by
  intro v w h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 2

@[expose] def δ : Multiplicative (Fin 3 → ZMod 3) →* M where
  toFun v := ⟨dg (ext (Multiplicative.toAdd v)), det_dg (sum_ext _)⟩
  map_one' := Subtype.ext (by
    change dg (ext 0) = 1
    rw [ext_zero, dg_zero])
  map_mul' v w := Subtype.ext (by
    change dg (ext (Multiplicative.toAdd v + Multiplicative.toAdd w)) = _
    rw [ext_add, dg_add]
    rfl)

theorem coe_δ (v : Fin 3 → ZMod 3) :
    ((δ (Multiplicative.ofAdd v) : M) : Matrix (Fin 4) (Fin 4) F4) = dg (ext v) := rfl

theorem δ_injective : Function.Injective δ := by
  intro v w h
  have h' := congrArg (fun g : M => (g : Matrix (Fin 4) (Fin 4) F4)) h
  change dg (ext (Multiplicative.toAdd v)) = dg (ext (Multiplicative.toAdd w)) at h'
  apply Multiplicative.toAdd.injective
  apply ext_injective
  funext i
  have := congrFun₂ h' i i
  simp only [dg, diagonal_apply_eq] at this
  exact eω_injective this

@[expose] def A0 : Subgroup M := δ.range

theorem isElemAbelian_A0 : IsElemAbelian 3 A0 := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, v, rfl⟩ ⟨_, w, rfl⟩
    apply Subtype.ext
    change δ v * δ w = δ w * δ v
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨v, rfl⟩
    rw [← map_pow]
    have : v ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      rw [show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]
    rw [this, map_one]

theorem card_A0 : Nat.card A0 = 3 ^ 3 := by
  rw [A0, ← Nat.card_congr (MonoidHom.ofInjective δ_injective).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem exists_map_conj_eq_A0 {A' : Subgroup M} (hA' : IsElemAbelian 3 A')
    (hcard : Nat.card A' = 3 ^ 3) : ∃ x : M, A'.map (MulAut.conj x).toMonoidHom = A0 := by
  obtain ⟨T, hTe, hfuse⟩ := hasFusionTarget_M
  obtain ⟨y, hy⟩ := hfuse A0 isElemAbelian_A0
  obtain ⟨z, hz⟩ := hfuse A' hA'
  have hT27 : Nat.card T ≤ 3 ^ 3 := maxEA_M.1 T hTe
  have hc : ∀ (X : Subgroup M) (u : M),
      Nat.card (X.map (MulAut.conj u).toMonoidHom) = Nat.card X :=
    fun X u => Subgroup.card_map_of_injective (MulAut.conj u).injective
  have hyT : A0.map (MulAut.conj y).toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge hy (by rw [hc, card_A0]; exact hT27)
  have hzT : A'.map (MulAut.conj z).toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge hz (by rw [hc, hcard]; exact hT27)
  refine ⟨y⁻¹ * z, ?_⟩
  rw [← map_conj_map_conj, hzT, ← hyT, map_conj_map_conj, inv_mul_cancel]
  ext g
  simp

@[expose] def res (y : Fin 4 → ZMod 3) : Fin 3 → ZMod 3 := ![y 0, y 1, y 2]

theorem ext_res {y : Fin 4 → ZMod 3} (hy : ∑ i, y i = 0) : ext (res y) = y := by
  rw [Fin.sum_univ_four] at hy
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · change -(y 0 + y 1 + y 2) = y 3
    rw [neg_eq_iff_add_eq_zero]
    exact hy

theorem res_ext (v : Fin 3 → ZMod 3) : res (ext v) = v := by
  funext i
  fin_cases i <;> rfl

theorem reindexSL_δ (σ : Equiv.Perm (Fin 4)) (v : Fin 3 → ZMod 3) :
    reindexSL σ (δ (Multiplicative.ofAdd v)) = δ (Multiplicative.ofAdd (res (ext v ∘ σ))) := by
  apply Subtype.ext
  have hsum : ∑ i, (ext v ∘ σ) i = 0 := by
    change ∑ i, ext v (σ i) = 0
    rw [Equiv.sum_comp σ (ext v)]
    exact sum_ext v
  rw [coe_reindexSL, coe_δ, coe_δ, ext_res hsum, dg, dg, submatrix_diagonal_equiv]
  rfl

theorem map_reindexSL_A0 (σ : Equiv.Perm (Fin 4)) : A0.map (reindexSL σ).toMonoidHom = A0 := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨_, (reindexSL_δ σ (Multiplicative.toAdd v)).symm⟩
  · rw [Subgroup.card_map_of_injective (reindexSL σ).injective]

theorem map_top_mulEquiv {X : Type*} [Group X] (φ : X ≃* X) :
    (⊤ : Subgroup X).map φ.toMonoidHom = ⊤ := by
  rw [← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr φ.surjective

@[expose] def std : Fin 3 → (Fin 3 → ZMod 3) := ![![1, 2, 0], ![1, 1, 2], ![1, 1, 1]]

theorem exists_perm_std : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ∃ σ : Equiv.Perm (Fin 4), ∃ i : Fin 3,
    ext v ∘ σ = ext (std i) ∨ ext v ∘ σ = ext (2 • std i) := by
  decide

theorem zpowers_sq {X : Type*} [Group X] {x : X} (hx : x ^ 3 = 1) :
    Subgroup.zpowers (x ^ 2) = Subgroup.zpowers x := by
  apply le_antisymm
  · exact (Subgroup.zpowers_le).mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2)
  · refine (Subgroup.zpowers_le).mpr ?_
    have h2 : (x ^ 2) ^ 2 = x := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, hx, one_mul, pow_one]
    have h3 : (x ^ 2) ^ 2 ∈ Subgroup.zpowers (x ^ 2) :=
      Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
    rwa [h2] at h3

theorem δ_pow_three (v : Fin 3 → ZMod 3) : δ (Multiplicative.ofAdd v) ^ 3 = 1 := by
  rw [← map_pow]
  have : (Multiplicative.ofAdd v) ^ 3 = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_pow, toAdd_ofAdd, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    rw [show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]
  rw [this, map_one]

theorem δ_two_smul (v : Fin 3 → ZMod 3) :
    δ (Multiplicative.ofAdd (2 • v)) = δ (Multiplicative.ofAdd v) ^ 2 := by
  rw [← map_pow]
  rfl

theorem orderThreeAt_of_std (h : ∀ i : Fin 3,
    OrderThreeAt (⊤ : Subgroup M) A0 (Subgroup.zpowers (δ (Multiplicative.ofAdd (std i))))) :
    ∀ B : Subgroup M, B ≤ A0 → Nat.card B = 3 → OrderThreeAt (⊤ : Subgroup M) A0 B := by
  intro B hBA hB3
  have hB1 : B ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hB3
    omega
  obtain ⟨⟨b, hbB⟩, hb'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
  have hb1 : b ≠ 1 := fun e => hb' (Subtype.ext e)
  obtain ⟨v, rfl⟩ := hBA hbB
  have hv : Multiplicative.toAdd v ≠ 0 := by
    intro h0
    apply hb1
    have : v = 1 := Multiplicative.toAdd.injective h0
    rw [this, map_one]
  obtain ⟨σ, i, hσ⟩ := exists_perm_std _ hv
  have hBb := eq_zpowers_of_card_three hB3 hbB hb1
  set φ := reindexSL (K := F4) σ
  have hmapB : B.map φ.toMonoidHom = Subgroup.zpowers (δ (Multiplicative.ofAdd (std i))) := by
    rw [hBb, MonoidHom.map_zpowers]
    change Subgroup.zpowers (reindexSL σ (δ v)) = _
    rw [show v = Multiplicative.ofAdd (Multiplicative.toAdd v) from rfl, reindexSL_δ]
    rcases hσ with hσ | hσ
    · rw [hσ, res_ext]
    · rw [hσ, res_ext, δ_two_smul, zpowers_sq (δ_pow_three _)]
  have hA : A0.map φ.symm.toMonoidHom = A0 := by
    have h1 := congrArg (Subgroup.map φ.symm.toMonoidHom) (map_reindexSL_A0 σ)
    rwa [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id M from by
      ext; simp, Subgroup.map_id, eq_comm] at h1
  have hB : (B.map φ.toMonoidHom).map φ.symm.toMonoidHom = B := by
    rw [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id M from by
      ext; simp, Subgroup.map_id]
  have := (h i).map φ.symm
  rwa [map_top_mulEquiv, hA, ← hmapB, hB] at this

theorem isBlockDiag_of_mem_centralizer {v : Fin 3 → ZMod 3} {g : M}
    (hg : g ∈ Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M)) :
    IsBlockDiag (ext v) (g : Matrix (Fin 4) (Fin 4) F4) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have h := congrArg (fun x : M => (x : Matrix (Fin 4) (Fin 4) F4)) hg
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_δ, dg] at h
  exact IsBlockDiag.of_comp (t := ext v) eω_injective (isBlockDiag_of_commute h)

theorem mem_centralizer_of_isBlockDiag {v : Fin 3 → ZMod 3} {g : M}
    (hg : IsBlockDiag (ext v) (g : Matrix (Fin 4) (Fin 4) F4)) :
    g ∈ Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_δ, dg]
  exact commute_of_isBlockDiag (hg.comp eω)

theorem mem_centralizer_of_constant {v w : Fin 3 → ZMod 3}
    (hw : ∀ i j, ext v i = ext v j → ext w i = ext w j) :
    δ (Multiplicative.ofAdd w) ∈ Subgroup.centralizer
      (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M) : Set M) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_δ, dg]
  exact commute_diagonal_of_isBlockDiag (s := fun i => eω (ext w i))
    (fun i j h => by rw [hw i j h]) (isBlockDiag_of_mem_centralizer hg)

theorem isIdOutside_δ {c : Set (Fin 4)} {w : Fin 3 → ZMod 3} (hw : ∀ i, i ∉ c → ext w i = 0) :
    IsIdOutside c ((δ (Multiplicative.ofAdd w) : M) : Matrix (Fin 4) (Fin 4) F4) := by
  rw [coe_δ, dg]
  exact isIdOutside_diagonal fun i hi => by rw [hw i hi, eω_zero]

theorem layerCent_top_zpowers (b : M) :
    layerCent (⊤ : Subgroup M) (Subgroup.zpowers b) =
      inSubgroup CFSG.layer (Subgroup.centralizer ({b} : Set M)) := by
  rw [layerCent, top_inf_eq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem block_normal {v : Fin 3 → ZMod 3} {κ : ZMod 3} {S : Subgroup M}
    (hS : ∀ x : M, x ∈ S ↔ IsIdOutside {i | ext v i = κ} (x : Matrix (Fin 4) (Fin 4) F4)) :
    S ≤ Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M) ∧
      Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M) ≤
        Subgroup.normalizer (S : Set M) := by
  set C := Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M)
  refine ⟨fun x hx => mem_centralizer_of_isBlockDiag ((hS x).mp hx).isBlockDiag, ?_⟩
  have key : ∀ g ∈ C, ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
    intro g hg s hs
    rw [hS] at hs ⊢
    have hgg : (g : Matrix (Fin 4) (Fin 4) F4) * ((g⁻¹ : M) : Matrix (Fin 4) (Fin 4) F4) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h := IsIdOutside.conj (isBlockDiag_of_mem_centralizer hg)
      (isBlockDiag_of_mem_centralizer (C.inv_mem hg)) hgg hs
    simpa [Matrix.SpecialLinearGroup.coe_mul] using h
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨key g hg s, fun h => ?_⟩
  have := key g⁻¹ (C.inv_mem hg) _ h
  simpa [mul_assoc] using this

theorem block_le_layer {v : Fin 3 → ZMod 3} {κ : ZMod 3} {S : Subgroup M}
    (hS : ∀ x : M, x ∈ S ↔ IsIdOutside {i | ext v i = κ} (x : Matrix (Fin 4) (Fin 4) F4))
    (hq : CFSG.IsQuasisimple S) :
    S ≤ layerCent (⊤ : Subgroup M) (Subgroup.zpowers (δ (Multiplicative.ofAdd v))) := by
  rw [layerCent_top_zpowers]
  exact le_inSubgroup_layer_of_normal (block_normal hS).1 (block_normal hS).2 hq

theorem layerCent_le_centralizer_δ (v : Fin 3 → ZMod 3) :
    layerCent (⊤ : Subgroup M) (Subgroup.zpowers (δ (Multiplicative.ofAdd v))) ≤
      Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M) := by
  rw [layerCent_top_zpowers]
  exact Subgroup.map_subtype_le _

theorem inner_of_witness {v : Fin 3 → ZMod 3} (u : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3))
    (hu : ∀ w, δ (Multiplicative.ofAdd (u w)) ∈
      layerCent (⊤ : Subgroup M) (Subgroup.zpowers (δ (Multiplicative.ofAdd v))))
    (hc : ∀ w i j, ext v i = ext v j → ext (w - u w) i = ext (w - u w) j) :
    ∀ a ∈ A0, ∃ y ∈ layerCent (⊤ : Subgroup M) (Subgroup.zpowers (δ (Multiplicative.ofAdd v))),
      y⁻¹ * a ∈ Subgroup.centralizer ((layerCent (⊤ : Subgroup M)
        (Subgroup.zpowers (δ (Multiplicative.ofAdd v))) : Subgroup M) : Set M) := by
  rintro _ ⟨w, rfl⟩
  refine ⟨_, hu (Multiplicative.toAdd w), ?_⟩
  have e : (δ (Multiplicative.ofAdd (u (Multiplicative.toAdd w))))⁻¹ * δ w =
      δ (Multiplicative.ofAdd (Multiplicative.toAdd w - u (Multiplicative.toAdd w))) := by
    rw [← map_inv, ← map_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd]
    abel
  rw [e]
  exact Subgroup.centralizer_le (layerCent_le_centralizer_δ v)
    (mem_centralizer_of_constant (hc _))

@[expose] def m23 (A : Matrix (Fin 2) (Fin 2) F4) : Matrix (Fin 4) (Fin 4) F4 :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, A 0 0, A 0 1; 0, 0, A 1 0, A 1 1]

@[expose] def m01 (A : Matrix (Fin 2) (Fin 2) F4) : Matrix (Fin 4) (Fin 4) F4 :=
  !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def m012 (A : Matrix (Fin 3) (Fin 3) F4) : Matrix (Fin 4) (Fin 4) F4 :=
  !![A 0 0, A 0 1, A 0 2, 0; A 1 0, A 1 1, A 1 2, 0; A 2 0, A 2 1, A 2 2, 0; 0, 0, 0, 1]

theorem det_m23 (A : Matrix (Fin 2) (Fin 2) F4) : (m23 A).det = A.det := by
  rw [Matrix.det_fin_two, det_succ_row_zero, Fin.sum_univ_four]
  simp [m23, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix]

theorem det_m01 (A : Matrix (Fin 2) (Fin 2) F4) : (m01 A).det = A.det := by
  rw [Matrix.det_fin_two, det_succ_row _ 3, Fin.sum_univ_four]
  simp [m01, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix]
  ring

theorem det_m012 (A : Matrix (Fin 3) (Fin 3) F4) : (m012 A).det = A.det := by
  rw [Matrix.det_fin_three, det_succ_row _ 3, Fin.sum_univ_four]
  simp [m012, Fin.succAbove, Matrix.det_fin_three, Matrix.submatrix]
  ring

theorem m23_mul (A B : Matrix (Fin 2) (Fin 2) F4) : m23 (A * B) = m23 A * m23 B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m23, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem m01_mul (A B : Matrix (Fin 2) (Fin 2) F4) : m01 (A * B) = m01 A * m01 B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m01, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem m012_mul (A B : Matrix (Fin 3) (Fin 3) F4) : m012 (A * B) = m012 A * m012 B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m012, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]

theorem m23_one : m23 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m23]

theorem m01_one : m01 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m01]

theorem m012_one : m012 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m012]

@[expose] def ι23 : SpecialLinearGroup (Fin 2) F4 →* M where
  toFun A := ⟨m23 A, by rw [det_m23]; exact A.2⟩
  map_one' := Subtype.ext m23_one
  map_mul' A B := Subtype.ext (m23_mul _ _)

@[expose] def ι01 : SpecialLinearGroup (Fin 2) F4 →* M where
  toFun A := ⟨m01 A, by rw [det_m01]; exact A.2⟩
  map_one' := Subtype.ext m01_one
  map_mul' A B := Subtype.ext (m01_mul _ _)

@[expose] def ι012 : SpecialLinearGroup (Fin 3) F4 →* M where
  toFun A := ⟨m012 A, by rw [det_m012]; exact A.2⟩
  map_one' := Subtype.ext m012_one
  map_mul' A B := Subtype.ext (m012_mul _ _)

theorem coe_ι23 (A : SpecialLinearGroup (Fin 2) F4) :
    ((ι23 A : M) : Matrix (Fin 4) (Fin 4) F4) = m23 A := rfl

theorem coe_ι01 (A : SpecialLinearGroup (Fin 2) F4) :
    ((ι01 A : M) : Matrix (Fin 4) (Fin 4) F4) = m01 A := rfl

theorem coe_ι012 (A : SpecialLinearGroup (Fin 3) F4) :
    ((ι012 A : M) : Matrix (Fin 4) (Fin 4) F4) = m012 A := rfl

theorem ι23_injective : Function.Injective ι23 := by
  intro A B h
  have h' : m23 A = m23 B := congrArg Subtype.val h
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [m23] using congrFun₂ h' 2 2
  · simpa [m23] using congrFun₂ h' 2 3
  · simpa [m23] using congrFun₂ h' 3 2
  · simpa [m23] using congrFun₂ h' 3 3

theorem ι01_injective : Function.Injective ι01 := by
  intro A B h
  have h' : m01 A = m01 B := congrArg Subtype.val h
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [m01] using congrFun₂ h' 0 0
  · simpa [m01] using congrFun₂ h' 0 1
  · simpa [m01] using congrFun₂ h' 1 0
  · simpa [m01] using congrFun₂ h' 1 1

theorem ι012_injective : Function.Injective ι012 := by
  intro A B h
  have h' : m012 A = m012 B := congrArg Subtype.val h
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [m012] using congrFun₂ h' 0 0
  · simpa [m012] using congrFun₂ h' 0 1
  · simpa [m012] using congrFun₂ h' 0 2
  · simpa [m012] using congrFun₂ h' 1 0
  · simpa [m012] using congrFun₂ h' 1 1
  · simpa [m012] using congrFun₂ h' 1 2
  · simpa [m012] using congrFun₂ h' 2 0
  · simpa [m012] using congrFun₂ h' 2 1
  · simpa [m012] using congrFun₂ h' 2 2

theorem mem_range_ι23_iff (x : M) :
    x ∈ ι23.range ↔ IsIdOutside {i : Fin 4 | i = 2 ∨ i = 3} (x : Matrix (Fin 4) (Fin 4) F4) := by
  constructor
  · rintro ⟨A, rfl⟩
    rw [coe_ι23]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [m23]
  · intro h
    set A : Matrix (Fin 2) (Fin 2) F4 := !![(x : Matrix (Fin 4) (Fin 4) F4) 2 2,
      (x : Matrix (Fin 4) (Fin 4) F4) 2 3; (x : Matrix (Fin 4) (Fin 4) F4) 3 2,
      (x : Matrix (Fin 4) (Fin 4) F4) 3 3] with hA
    have hx : (x : Matrix (Fin 4) (Fin 4) F4) = m23 A := by
      ext i j
      fin_cases i <;> fin_cases j <;> first
        | (refine (h _ _ ?_).trans ?_ <;> simp [m23] <;> done)
        | (simp [m23, hA])
    have hdet : A.det = 1 := by rw [← det_m23, ← hx]; exact x.2
    exact ⟨⟨A, hdet⟩, Subtype.ext hx.symm⟩

theorem mem_range_ι01_iff (x : M) :
    x ∈ ι01.range ↔ IsIdOutside {i : Fin 4 | i = 0 ∨ i = 1} (x : Matrix (Fin 4) (Fin 4) F4) := by
  constructor
  · rintro ⟨A, rfl⟩
    rw [coe_ι01]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [m01]
  · intro h
    set A : Matrix (Fin 2) (Fin 2) F4 := !![(x : Matrix (Fin 4) (Fin 4) F4) 0 0,
      (x : Matrix (Fin 4) (Fin 4) F4) 0 1; (x : Matrix (Fin 4) (Fin 4) F4) 1 0,
      (x : Matrix (Fin 4) (Fin 4) F4) 1 1] with hA
    have hx : (x : Matrix (Fin 4) (Fin 4) F4) = m01 A := by
      ext i j
      fin_cases i <;> fin_cases j <;> first
        | (refine (h _ _ ?_).trans ?_ <;> simp [m01] <;> done)
        | (simp [m01, hA])
    have hdet : A.det = 1 := by rw [← det_m01, ← hx]; exact x.2
    exact ⟨⟨A, hdet⟩, Subtype.ext hx.symm⟩

theorem mem_range_ι012_iff (x : M) :
    x ∈ ι012.range ↔ IsIdOutside {i : Fin 4 | i ≠ 3} (x : Matrix (Fin 4) (Fin 4) F4) := by
  constructor
  · rintro ⟨A, rfl⟩
    rw [coe_ι012]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [m012]
  · intro h
    set A : Matrix (Fin 3) (Fin 3) F4 := Matrix.of fun i j =>
      (x : Matrix (Fin 4) (Fin 4) F4) (Fin.castSucc i) (Fin.castSucc j) with hA
    have hx : (x : Matrix (Fin 4) (Fin 4) F4) = m012 A := by
      ext i j
      fin_cases i <;> fin_cases j <;> first
        | (refine (h _ _ ?_).trans ?_ <;> simp [m012] <;> done)
        | (simp [m012, hA])
    have hdet : A.det = 1 := by rw [← det_m012, ← hx]; exact x.2
    exact ⟨⟨A, hdet⟩, Subtype.ext hx.symm⟩

theorem isQuasisimple_SL2 : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 2) F4) := by
  refine isQuasisimple_of_isSimpleGroup isSimpleGroup_SL2 ?_
  refine ⟨⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩, ⟨!![1, 0; 1, 1], by simp [det_fin_two]⟩, ?_⟩
  intro h
  have h' := congrArg
    (fun x : SpecialLinearGroup (Fin 2) F4 => (x : Matrix (Fin 2) (Fin 2) F4) 0 0) h
  change (!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F4) 0 0 =
    (!![1, 0; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F4) 0 0 at h'
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h'

theorem isQuasisimple_SL3 : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 3) F4) :=
  CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F4 le_rfl

theorem isQuasisimple_range_ι23 : CFSG.IsQuasisimple ι23.range :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective ι23_injective) isQuasisimple_SL2

theorem isQuasisimple_range_ι01 : CFSG.IsQuasisimple ι01.range :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective ι01_injective) isQuasisimple_SL2

theorem isQuasisimple_range_ι012 : CFSG.IsQuasisimple ι012.range :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective ι012_injective)
    isQuasisimple_SL3

abbrev bs (i : Fin 3) : M := δ (Multiplicative.ofAdd (std i))

abbrev Bs (i : Fin 3) : Subgroup M := Subgroup.zpowers (bs i)

theorem card_zpowers_δ {w : Fin 3 → ZMod 3} (hw : w ≠ 0) :
    Nat.card (Subgroup.zpowers (δ (Multiplicative.ofAdd w))) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_zpowers]
  refine orderOf_eq_prime (δ_pow_three w) fun h => hw ?_
  have h1 : δ (Multiplicative.ofAdd w) = δ 1 := by rw [h, map_one]
  exact Multiplicative.ofAdd.injective (δ_injective h1)

theorem δ_mem_A0 (w : Fin 3 → ZMod 3) : δ (Multiplicative.ofAdd w) ∈ A0 := ⟨_, rfl⟩

theorem zpowers_δ_le_A0 (w : Fin 3 → ZMod 3) : Subgroup.zpowers (δ (Multiplicative.ofAdd w)) ≤ A0 :=
  (Subgroup.zpowers_le).mpr (δ_mem_A0 w)

theorem δ_nsmul (n : ℕ) (w : Fin 3 → ZMod 3) :
    δ (Multiplicative.ofAdd (n • w)) = δ (Multiplicative.ofAdd w) ^ n := by
  rw [ofAdd_nsmul, map_pow]

theorem fib0_0 : {i : Fin 4 | ext (std 0) i = 0} = {i : Fin 4 | i = 2 ∨ i = 3} := by
  ext i
  fin_cases i <;> decide

theorem fib1_1 : {i : Fin 4 | ext (std 1) i = 1} = {i : Fin 4 | i = 0 ∨ i = 1} := by
  ext i
  fin_cases i <;> decide

theorem fib1_2 : {i : Fin 4 | ext (std 1) i = 2} = {i : Fin 4 | i = 2 ∨ i = 3} := by
  ext i
  fin_cases i <;> decide

theorem fib2_1 : {i : Fin 4 | ext (std 2) i = 1} = {i : Fin 4 | i ≠ 3} := by
  ext i
  fin_cases i <;> decide

theorem range_ι23_le_Y0 : ι23.range ≤ layerCent (⊤ : Subgroup M) (Bs 0) :=
  block_le_layer (κ := 0) (fun x => by rw [fib0_0]; exact mem_range_ι23_iff x)
    isQuasisimple_range_ι23

theorem range_ι01_le_Y1 : ι01.range ≤ layerCent (⊤ : Subgroup M) (Bs 1) :=
  block_le_layer (κ := 1) (fun x => by rw [fib1_1]; exact mem_range_ι01_iff x)
    isQuasisimple_range_ι01

theorem range_ι23_le_Y1 : ι23.range ≤ layerCent (⊤ : Subgroup M) (Bs 1) :=
  block_le_layer (κ := 2) (fun x => by rw [fib1_2]; exact mem_range_ι23_iff x)
    isQuasisimple_range_ι23

theorem range_ι012_le_Y2 : ι012.range ≤ layerCent (⊤ : Subgroup M) (Bs 2) :=
  block_le_layer (κ := 1) (fun x => by rw [fib2_1]; exact mem_range_ι012_iff x)
    isQuasisimple_range_ι012

theorem δ_mem_range_ι23 {w : Fin 3 → ZMod 3} (hw : ∀ i : Fin 4, ¬(i = 2 ∨ i = 3) → ext w i = 0) :
    δ (Multiplicative.ofAdd w) ∈ ι23.range :=
  (mem_range_ι23_iff _).mpr (isIdOutside_δ hw)

theorem δ_mem_range_ι01 {w : Fin 3 → ZMod 3} (hw : ∀ i : Fin 4, ¬(i = 0 ∨ i = 1) → ext w i = 0) :
    δ (Multiplicative.ofAdd w) ∈ ι01.range :=
  (mem_range_ι01_iff _).mpr (isIdOutside_δ hw)

theorem δ_mem_range_ι012 {w : Fin 3 → ZMod 3} (hw : ∀ i : Fin 4, ¬(i ≠ 3) → ext w i = 0) :
    δ (Multiplicative.ofAdd w) ∈ ι012.range :=
  (mem_range_ι012_iff _).mpr (isIdOutside_δ hw)

@[expose] def u23 (w : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 := ![0, 0, w 2 - (w 0 + w 1)]

@[expose] def u01 (w : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 :=
  ![w 0 - 2 * (w 0 + w 1), w 1 - 2 * (w 0 + w 1), 0]

theorem u23_supp : ∀ w : Fin 3 → ZMod 3, ∀ i : Fin 4, ¬(i = 2 ∨ i = 3) → ext (u23 w) i = 0 := by
  decide

theorem u01_supp : ∀ w : Fin 3 → ZMod 3, ∀ i : Fin 4, ¬(i = 0 ∨ i = 1) → ext (u01 w) i = 0 := by
  decide

theorem inner_b0 : ∀ a ∈ A0, ∃ y ∈ layerCent (⊤ : Subgroup M) (Bs 0),
    y⁻¹ * a ∈ Subgroup.centralizer ((layerCent (⊤ : Subgroup M) (Bs 0) : Subgroup M) : Set M) :=
  inner_of_witness u23 (fun w => range_ι23_le_Y0 (δ_mem_range_ι23 (u23_supp w))) (by decide)

theorem inner_b1 : ∀ a ∈ A0, ∃ y ∈ layerCent (⊤ : Subgroup M) (Bs 1),
    y⁻¹ * a ∈ Subgroup.centralizer ((layerCent (⊤ : Subgroup M) (Bs 1) : Subgroup M) : Set M) := by
  refine inner_of_witness (fun w => u01 w + u23 w) (fun w => ?_) (by decide)
  rw [ofAdd_add, map_mul]
  exact Subgroup.mul_mem _ (range_ι01_le_Y1 (δ_mem_range_ι01 (u01_supp w)))
    (range_ι23_le_Y1 (δ_mem_range_ι23 (u23_supp w)))

theorem decomp_b1 : ∀ w : Fin 3 → ZMod 3,
    w = ![w 0 - 2 * (w 0 + w 1), w 1 - 2 * (w 0 + w 1), 0] +
      ![0, 0, w 2 - 2 * (2 * (w 0 + w 1))] + (2 * (w 0 + w 1)).val • std 1 := by
  decide

theorem supp_b1_a : ∀ w : Fin 3 → ZMod 3, ∀ i : Fin 4, ¬(i = 0 ∨ i = 1) →
    ext ![w 0 - 2 * (w 0 + w 1), w 1 - 2 * (w 0 + w 1), 0] i = 0 := by
  decide

theorem supp_b1_b : ∀ w : Fin 3 → ZMod 3, ∀ i : Fin 4, ¬(i = 2 ∨ i = 3) →
    ext ![0, 0, w 2 - 2 * (2 * (w 0 + w 1))] i = 0 := by
  decide

theorem good_b1 : A0 ≤ layerCent (⊤ : Subgroup M) (Bs 1) ⊔ Bs 1 := by
  rintro _ ⟨w, rfl⟩
  obtain ⟨w, rfl⟩ : ∃ w' : Fin 3 → ZMod 3, Multiplicative.ofAdd w' = w :=
    ⟨Multiplicative.toAdd w, rfl⟩
  rw [decomp_b1 w, ofAdd_add, ofAdd_add, map_mul, map_mul, δ_nsmul]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_)
    (Subgroup.mem_sup_left ?_)) (Subgroup.mem_sup_right (Subgroup.pow_mem _
      (Subgroup.mem_zpowers _) _))
  · exact range_ι01_le_Y1 (δ_mem_range_ι01 (supp_b1_a _))
  · exact range_ι23_le_Y1 (δ_mem_range_ι23 (supp_b1_b _))

theorem good_map (φ : M ≃* M) (hA : A0.map φ.toMonoidHom = A0) {X : Subgroup M}
    (h : A0 ≤ layerCent (⊤ : Subgroup M) X ⊔ X) :
    A0 ≤ layerCent (⊤ : Subgroup M) (X.map φ.toMonoidHom) ⊔ X.map φ.toMonoidHom := by
  rw [← hA, ← map_top_mulEquiv φ, ← map_layerCent, ← Subgroup.map_sup]
  exact Subgroup.map_mono h

abbrev X' : Subgroup M := Subgroup.zpowers (δ (Multiplicative.ofAdd ![1, 2, 2]))

theorem X'_eq : X' = (Bs 1).map (reindexSL (K := F4) (Equiv.swap 1 3)).toMonoidHom := by
  rw [MonoidHom.map_zpowers]
  change _ = Subgroup.zpowers (reindexSL (Equiv.swap 1 3) (bs 1))
  rw [reindexSL_δ]
  congr 3

theorem good_X' : A0 ≤ layerCent (⊤ : Subgroup M) X' ⊔ X' := by
  rw [X'_eq]
  exact good_map _ (map_reindexSL_A0 _) good_b1

theorem card_X' : Nat.card X' = 3 := card_zpowers_δ (by decide)

theorem X'_le_Y0 : X' ≤ layerCent (⊤ : Subgroup M) (Bs 0) ⊔ Bs 0 := by
  refine (Subgroup.zpowers_le).mpr ?_
  have e : (![1, 2, 2] : Fin 3 → ZMod 3) = ![0, 0, 2] + std 0 := by decide
  rw [e, ofAdd_add, map_mul]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (range_ι23_le_Y0 (δ_mem_range_ι23 ?_)))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  decide

@[expose] def f33 : Subgroup.centralizer ({bs 2} : Set M) →* F4 where
  toFun g := ((g : M) : Matrix (Fin 4) (Fin 4) F4) 3 3
  map_one' := by simp
  map_mul' g h := by
    have hg := isBlockDiag_of_mem_centralizer g.2
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_four]
    rw [hg 3 0 (by decide), hg 3 1 (by decide), hg 3 2 (by decide)]
    simp

theorem layerCent_b2_le : layerCent (⊤ : Subgroup M) (Bs 2) ≤ ι012.range := by
  rw [layerCent_top_zpowers]
  set C := Subgroup.centralizer ({bs 2} : Set M)
  set f : C →* F4ˣ := f33.toHomUnits
  have hcomm : ⁅C, C⁆ ≤ f.ker.map C.subtype := by
    have e : (commutator C).map C.subtype = ⁅C, C⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    rw [← e]
    exact Subgroup.map_mono (Abelianization.commutator_subset_ker f)
  refine (inSubgroup_layer_le_of_commutator_le hcomm).trans ?_
  rintro _ ⟨g, hg, rfl⟩
  have h33 : ((g : M) : Matrix (Fin 4) (Fin 4) F4) 3 3 = 1 := by
    have := congrArg Units.val (MonoidHom.mem_ker.mp hg)
    simpa [f, f33] using this
  have hgb := isBlockDiag_of_mem_centralizer g.2
  change (g : M) ∈ ι012.range
  rw [mem_range_ι012_iff]
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij
  all_goals first
    | (exact h33.trans (by simp))
    | (rw [hgb _ _ (by decide)]; simp)

theorem layerCent_b2_eq : layerCent (⊤ : Subgroup M) (Bs 2) = ι012.range :=
  le_antisymm layerCent_b2_le range_ι012_le_Y2

theorem orderThreeAt_std (i : Fin 3) : OrderThreeAt (⊤ : Subgroup M) A0 (Bs i) := by
  fin_cases i
  ·
    exact ⟨Or.inl inner_b0, Bs 0, X', zpowers_δ_le_A0 _, card_zpowers_δ (by decide), le_sup_right,
      zpowers_δ_le_A0 _, card_X', X'_le_Y0, good_X'⟩
  ·
    exact ⟨Or.inl inner_b1, Bs 1, Bs 1, zpowers_δ_le_A0 _, card_zpowers_δ (by decide),
      le_sup_right, zpowers_δ_le_A0 _, card_zpowers_δ (by decide), le_sup_right, good_b1⟩
  ·
    refine ⟨Or.inr ⟨(MulEquiv.subgroupCongr layerCent_b2_eq).trans
      (MonoidHom.ofInjective ι012_injective).symm⟩, Bs 0, X', zpowers_δ_le_A0 _,
      card_zpowers_δ (by decide), ?_, zpowers_δ_le_A0 _, card_X', X'_le_Y0, good_X'⟩
    refine le_sup_of_le_left ((Subgroup.zpowers_le).mpr ?_)
    exact range_ι012_le_Y2 (δ_mem_range_ι012 (by decide))

theorem orderThreeAt_A0 : ∀ B : Subgroup M, B ≤ A0 → Nat.card B = 3 →
    OrderThreeAt (⊤ : Subgroup M) A0 B :=
  orderThreeAt_of_std orderThreeAt_std

theorem terminalOrderThreeL44 : TerminalOrderThreeL44 := by
  intro G _ _ I A hAI hAe ⟨e⟩ hA B hBA hB3
  apply OrderThreeAt.of_subgroupOf hAI hBA
  set e' : I ≃* M := e.trans equivSL
  have hA'e : IsElemAbelian 3 ((A.subgroupOf I).map e'.toMonoidHom) :=
    CFSG.RankThree.PartTwo.Sec21.isElemAbelian_map (isElemAbelian_subgroupOf hAe I) _
  have hcardA : Nat.card ((A.subgroupOf I).map e'.toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective e'.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAI).toEquiv, hA]
  obtain ⟨x, hx⟩ := exists_map_conj_eq_A0 hA'e hcardA
  set φ : I ≃* M := e'.trans (MulAut.conj x)
  have hφA : (A.subgroupOf I).map φ.toMonoidHom = A0 := by
    rw [← hx, Subgroup.map_map]
    rfl
  have hB' : (B.subgroupOf I).map φ.toMonoidHom ≤ A0 := by
    rw [← hφA]
    exact Subgroup.map_mono (fun x hx => hBA hx)
  have hcardB : Nat.card ((B.subgroupOf I).map φ.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBA.trans hAI)).toEquiv, hB3]
  have h := (orderThreeAt_A0 _ hB' hcardB).map φ.symm
  have hsymm : ∀ X : Subgroup I, (X.map φ.toMonoidHom).map φ.symm.toMonoidHom = X := by
    intro X
    rw [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id I from by
      ext; simp, Subgroup.map_id]
  rwa [← hφA, hsymm, hsymm, show (⊤ : Subgroup M).map φ.symm.toMonoidHom = ⊤ from by
    rw [← MonoidHom.range_eq_map]; exact MonoidHom.range_eq_top.mpr φ.symm.surjective] at h

end CFSG.RankThree.PartTwo.Sec21.TablesL44
