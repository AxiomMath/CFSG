module

public import CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
public import CFSG.RankThree.Asc83Table.Reduction
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelSelector
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.RankThree.PartTwo.Census.Criteria

public section

namespace CFSG.RankThree.PartTwo.KFacts.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
open Matrix

variable {k : Type*} [Field k]

section Field

variable {u : kˣ}

theorem val_mul_self_add (hk : Nat.card k = 4) (hu : u ≠ 1) :
    (u : k) * u + u + 1 = 0 := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have h := LinearFieldFour.omega_mul_omega hk u.ne_zero (fun h => hu (Units.ext h))
  rw [h]
  linear_combination CharTwo.add_self_eq_zero ((u : k) + 1)

theorem val_ne_one (hu : u ≠ 1) : (u : k) ≠ 1 := fun h => hu (Units.ext h)

theorem units_eq (hk : Nat.card k = 4) (hu : u ≠ 1) (c : kˣ) : c = 1 ∨ c = u ∨ c = u * u := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  rcases LinearFieldFour.eq_zero_or_eq_one_or hk u.ne_zero (val_ne_one hu) c with h | h | h | h
  · exact absurd h c.ne_zero
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Or.inl (Units.ext h))
  · refine Or.inr (Or.inr (Units.ext ?_))
    rw [h, Units.val_mul, LinearFieldFour.omega_mul_omega hk u.ne_zero (val_ne_one hu)]

end Field

section Matrices

variable {ω : k}

@[expose] def rM : Matrix (Fin 3) (Fin 3) k := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def hiM (ω : k) : Matrix (Fin 3) (Fin 3) k := !![ω * ω, 0, 0; 0, 1, 0; 0, 0, ω]

@[expose] def fM (ω : k) : Matrix (Fin 3) (Fin 3) k := !![1, 1, 1; ω * ω, 1, ω; ω, 1, ω * ω]

@[expose] def jM (ω : k) : Matrix (Fin 3) (Fin 3) k := !![1, ω, ω; ω, 1, ω; 1, 1, ω * ω]

theorem coe_rSL' : ((rSL : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = rM :=
  coe_rSL

variable [CharP k 2] (hω : ω * ω + ω + 1 = 0)
include hω

theorem det_fM : (fM ω).det = 1 := by
  simp only [fM, det_fin_three]
  simp
  grind

theorem det_jM : (jM ω).det = 1 := by
  simp only [jM, det_fin_three]
  simp
  grind

theorem rM_mul_hM : rM * LinearFieldFour.hM ω = ω • (LinearFieldFour.hM ω * rM) := by
  simp only [rM, LinearFieldFour.hM, mul_fin_three, smul_of, smul_cons, smul_empty]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals grind

theorem hM_mul_hiM : LinearFieldFour.hM ω * hiM ω = 1 := by
  simp only [hiM, LinearFieldFour.hM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [one_apply] <;> grind

theorem fM_mul_hM : fM ω * LinearFieldFour.hM ω = rM * fM ω := by
  simp only [fM, LinearFieldFour.hM, rM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> grind

theorem fM_mul_rM : fM ω * rM = ω • hiM ω * fM ω := by
  simp only [fM, hiM, rM, mul_fin_three, smul_of, smul_cons, smul_empty]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> grind

theorem jM_mul_hM : jM ω * LinearFieldFour.hM ω = rM * hiM ω * jM ω := by
  simp only [jM, LinearFieldFour.hM, rM, hiM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> grind

theorem jM_mul_rM : jM ω * rM = (ω • (hiM ω * rM * hiM ω)) * jM ω := by
  simp only [jM, rM, hiM, mul_fin_three, smul_of, smul_cons, smul_empty]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> grind

omit hω in
theorem eq_diagonal_of_commute_hM (hω : ω * ω + ω + 1 = 0) (hω1 : ω ≠ 1)
    {M : Matrix (Fin 3) (Fin 3) k}
    (h : M * LinearFieldFour.hM ω = LinearFieldFour.hM ω * M) :
    M = diagonal ![M 0 0, M 1 1, M 2 2] := by
  have e : ∀ i j, (M * LinearFieldFour.hM ω) i j = (LinearFieldFour.hM ω * M) i j :=
    fun i j => by rw [h]
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  simp [LinearFieldFour.hM, Matrix.mul_apply, Fin.sum_univ_three] at e01 e02 e10 e12 e20 e21
  have h01 : M 0 1 = 0 := by grind
  have h02 : M 0 2 = 0 := by grind
  have h10 : M 1 0 = 0 := by grind
  have h12 : M 1 2 = 0 := by grind
  have h20 : M 2 0 = 0 := by grind
  have h21 : M 2 1 = 0 := by grind
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21]

end Matrices


section Elements

variable {u : kˣ}

@[expose] def hSL (u : kˣ) : Matrix.SpecialLinearGroup (Fin 3) k := dHom (u, 1)

theorem coe_hSL (hk : Nat.card k = 4) :
    (hSL u : Matrix (Fin 3) (Fin 3) k) = LinearFieldFour.hM (u : k) := by
  have h3 := LinearThreeFourOuter.units_pow_three hk u
  have hinv : (((u * 1)⁻¹ : kˣ) : k) = u * u := by
    have h : u * (u * u) = 1 := by rw [← pow_three]; exact h3
    rw [mul_one, inv_eq_of_mul_eq_one_right h, Units.val_mul]
  rw [hSL, coe_dHom, hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem exists_smul_of_proj_commute {g x : Matrix.SpecialLinearGroup (Fin 3) k}
    (h : proj 3 k g * proj 3 k x = proj 3 k x * proj 3 k g) :
    ∃ c : kˣ, c ^ 3 = 1 ∧ (x : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k) =
      (c : k) • ((g : Matrix (Fin 3) (Fin 3) k) * (x : Matrix (Fin 3) (Fin 3) k)) := by
  rw [← map_mul, ← map_mul, proj_eq_proj_iff] at h
  obtain ⟨c, hc, hz⟩ := mem_scalars.mp h
  refine ⟨c, hc, ?_⟩
  calc (x : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k) =
        ((x * g : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) :=
        (Matrix.SpecialLinearGroup.coe_mul x g).symm
    _ = ((g * x : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
        (((g * x)⁻¹ * (x * g) : Matrix.SpecialLinearGroup (Fin 3) k) :
          Matrix (Fin 3) (Fin 3) k) := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    _ = _ := by
        rw [hz, scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
          Matrix.SpecialLinearGroup.coe_mul]

theorem mem_dSet_of_commute [CharP k 2] {ω : k} (hω : ω * ω + ω + 1 = 0) (hω1 : ω ≠ 1)
    {x : Matrix.SpecialLinearGroup (Fin 3) k}
    (h : (x : Matrix (Fin 3) (Fin 3) k) * LinearFieldFour.hM ω = LinearFieldFour.hM ω * x) :
    x ∈ dSet := by
  have hd := eq_diagonal_of_commute_hM hω hω1 h
  have hdet : (x : Matrix (Fin 3) (Fin 3) k).det = 1 := x.2
  rw [hd, det_diagonal, Fin.prod_univ_three] at hdet
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hdet
  have h0 : (x : Matrix (Fin 3) (Fin 3) k) 0 0 ≠ 0 := by
    intro h0; rw [h0] at hdet; simp at hdet
  have h1 : (x : Matrix (Fin 3) (Fin 3) k) 1 1 ≠ 0 := by
    intro h1; rw [h1] at hdet; simp at hdet
  refine ⟨Units.mk0 _ h0, Units.mk0 _ h1, hd.trans ?_⟩
  congr 1
  ext i
  fin_cases i
  · rfl
  · rfl
  · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Units.val_inv_eq_inv_val, Units.val_mul, Units.val_mk0, Fin.isValue]
    field_simp
    linear_combination hdet

theorem hSL_mem_qSub : hSL u ∈ (qSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k)) :=
  Subgroup.subset_closure (Or.inl (mem_dSet_iff.mpr ⟨_, rfl⟩))

theorem rSL_mem_qSub : (rSL : Matrix.SpecialLinearGroup (Fin 3) k) ∈ qSub :=
  Subgroup.subset_closure (Or.inr rfl)

theorem mem_qSub_of_commute (hk : Nat.card k = 4) (hu : u ≠ 1)
    {g : Matrix.SpecialLinearGroup (Fin 3) k}
    (h : proj 3 k g * proj 3 k (hSL u) = proj 3 k (hSL u) * proj 3 k g) : g ∈ qSub := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hω := val_mul_self_add hk hu
  have hω1 := val_ne_one hu
  obtain ⟨c, -, hc⟩ := exists_smul_of_proj_commute h
  rw [coe_hSL hk] at hc
  set H := LinearFieldFour.hM (u : k)
  set G := (g : Matrix (Fin 3) (Fin 3) k)
  have hRH := rM_mul_hM hω
  rcases units_eq hk hu c with rfl | rfl | rfl
  · rw [Units.val_one, one_smul] at hc
    exact Subgroup.subset_closure (Or.inl (mem_dSet_of_commute hω hω1 hc.symm))
  · have hx : ((g * rSL : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * H =
        H * ((g * rSL : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_rSL', Matrix.mul_assoc, hRH, Matrix.mul_smul,
        ← Matrix.mul_assoc H, hc, Matrix.smul_mul, Matrix.mul_assoc]
    have hmem : g * rSL ∈ (qSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k)) :=
      Subgroup.subset_closure (Or.inl (mem_dSet_of_commute hω hω1 hx))
    simpa using mul_mem hmem (inv_mem rSL_mem_qSub)
  · have hx : ((g * rSL * rSL : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
        H = H * ((g * rSL * rSL : Matrix.SpecialLinearGroup (Fin 3) k) :
          Matrix (Fin 3) (Fin 3) k) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rSL',
        Matrix.mul_assoc, hRH, Matrix.mul_smul, ← Matrix.mul_assoc _ H, Matrix.mul_assoc G,
        hRH, Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← Matrix.mul_assoc H,
        ← Matrix.mul_assoc H,
        hc, Matrix.smul_mul, Matrix.smul_mul, Units.val_mul]
      simp only [Matrix.mul_assoc]
      rfl
    have hmem : g * rSL * rSL ∈ (qSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k)) :=
      Subgroup.subset_closure (Or.inl (mem_dSet_of_commute hω hω1 hx))
    simpa using mul_mem hmem (inv_mem (mul_mem rSL_mem_qSub rSL_mem_qSub))

end Elements

section EZero

variable (k) in
@[expose] def eZero : Subgroup (projectiveSL 3 k) :=
  (qSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k)).map (proj 3 k)

theorem card_eZero (hk : Nat.card k = 4) : Nat.card (eZero k) = 9 :=
  card_map_proj_qSub hk

theorem pow_three_of_mem_eZero (hk : Nat.card k = 4) {x : projectiveSL 3 k} (hx : x ∈ eZero k) :
    x ^ 3 = 1 :=
  pow_three_of_mem_map_proj hk hx

theorem isElementaryAbelian_eZero (hk : Nat.card k = 4) : CFSG.IsElementaryAbelian 3 (eZero k) :=
  isElementaryAbelian_three_of_card (card_eZero hk) fun _ hx => pow_three_of_mem_eZero hk hx

theorem commute_of_mem_eZero (hk : Nat.card k = 4) {x y : projectiveSL 3 k} (hx : x ∈ eZero k)
    (hy : y ∈ eZero k) : x * y = y * x := by
  exact congrArg Subtype.val
    ((isElementaryAbelian_eZero hk).toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

variable {u : kˣ}

@[expose] def aP (u : kˣ) : projectiveSL 3 k := proj 3 k (hSL u)

@[expose] def bP : projectiveSL 3 k := proj 3 k rSL

theorem aP_mem_eZero : aP u ∈ eZero k := ⟨_, hSL_mem_qSub, rfl⟩

theorem aP_ne_one (hk : Nat.card k = 4) (hu : u ≠ 1) : aP u ≠ 1 := by
  intro h
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp h)
  rw [coe_hSL hk] at hc
  have h0 := congrFun (congrFun hc 0) 0
  have h1 := congrFun (congrFun hc 1) 1
  simp [LinearFieldFour.hM, scalar_apply] at h0 h1
  exact val_ne_one hu (h0.trans h1.symm)

theorem bP_mem_eZero : (bP : projectiveSL 3 k) ∈ eZero k := ⟨_, rSL_mem_qSub, rfl⟩

theorem dHom_diag_mem_scalars (hk : Nat.card k = 4) (c : kˣ) : dHom (c, c) ∈ scalars 3 k := by
  have hc := LinearThreeFourOuter.units_pow_three hk c
  refine mem_scalars.mpr ⟨c, hc, ?_⟩
  rw [coe_dHom, scalar_apply]
  congr 1
  funext i
  fin_cases i
  · rfl
  · rfl
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    rw [inv_eq_of_mul_eq_one_right (by rw [← pow_three']; exact hc)]

theorem exists_proj_dHom_eq (hk : Nat.card k = 4) (hu : u ≠ 1) (p : kˣ × kˣ) :
    ∃ i : ℕ, i < 3 ∧ proj 3 k (dHom p) = aP u ^ i := by
  have hp : p = (p.2, p.2) * (p.1 * p.2⁻¹, 1) := by
    ext
    · simp [mul_comm p.2, mul_assoc]
    · simp
  have hz : proj 3 k (dHom (p.2, p.2)) = 1 := proj_eq_one_iff.mpr (dHom_diag_mem_scalars hk _)
  rw [hp, map_mul, map_mul, hz, one_mul]
  rcases units_eq hk hu (p.1 * p.2⁻¹) with h | h | h <;> rw [h]
  · exact ⟨0, by norm_num, by rw [pow_zero, show ((1 : kˣ), (1 : kˣ)) = 1 from rfl, map_one,
      map_one]⟩
  · exact ⟨1, by norm_num, by rw [pow_one]; rfl⟩
  · refine ⟨2, by norm_num, ?_⟩
    rw [show ((u * u : kˣ), (1 : kˣ)) = (u, 1) * (u, 1) by ext <;> simp, map_mul, map_mul, sq]
    rfl

theorem exists_eq_aP_pow_mul_bP_pow (hk : Nat.card k = 4) (hu : u ≠ 1) {x : projectiveSL 3 k}
    (hx : x ∈ eZero k) : ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ x = aP u ^ i * bP ^ j := by
  obtain ⟨g, hg, rfl⟩ := hx
  rw [coe_qSub] at hg
  obtain ⟨⟨p, j⟩, rfl⟩ := hg
  obtain ⟨i, hi, hpi⟩ := exists_proj_dHom_eq hk hu p
  exact ⟨i, j, hi, j.2, by rw [qElt, map_mul, hpi, map_pow]; rfl⟩

theorem eZero_eq_closure (hk : Nat.card k = 4) (hu : u ≠ 1) :
    eZero k = Subgroup.closure {aP u, bP} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨i, j, -, -, rfl⟩ := exists_eq_aP_pow_mul_bP_pow hk hu hx
    exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
      (pow_mem (Subgroup.subset_closure (by simp)) _)
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact aP_mem_eZero
    · exact bP_mem_eZero

end EZero

section Normalizer

variable {u : kˣ}

@[expose] def zSL (u : kˣ) : Matrix.SpecialLinearGroup (Fin 3) k := dHom (u, u)

theorem coe_zSL (hk : Nat.card k = 4) :
    (zSL u : Matrix (Fin 3) (Fin 3) k) = (u : k) • (1 : Matrix (Fin 3) (Fin 3) k) := by
  have h3 := LinearThreeFourOuter.units_pow_three hk u
  have hinv : (((u * u)⁻¹ : kˣ) : k) = u := by
    have h : u * u * u = 1 := by rw [← pow_three']; exact h3
    rw [inv_eq_of_mul_eq_one_right h]
  rw [zSL, coe_dHom, hinv, smul_one_eq_diagonal]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem zSL_mem_scalars (hk : Nat.card k = 4) : zSL u ∈ scalars 3 k :=
  dHom_diag_mem_scalars hk u

theorem coe_hSL_inv (hk : Nat.card k = 4) (hu : u ≠ 1) :
    (((hSL u)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      hiM (u : k) := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have h := hM_mul_hiM (val_mul_self_add hk hu)
  calc (((hSL u)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        (((hSL u)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
          (LinearFieldFour.hM (u : k) * hiM (u : k)) := by rw [h, Matrix.mul_one]
    _ = hiM (u : k) := by
        rw [← coe_hSL hk, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

@[expose] def fSL (hk : Nat.card k = 4) (hu : u ≠ 1) : Matrix.SpecialLinearGroup (Fin 3) k :=
  ⟨fM (u : k), by
    have := LinearFieldFour.charP_two_of_card_eq_four hk
    exact det_fM (val_mul_self_add hk hu)⟩

@[expose] def jSL (hk : Nat.card k = 4) (hu : u ≠ 1) : Matrix.SpecialLinearGroup (Fin 3) k :=
  ⟨jM (u : k), by
    have := LinearFieldFour.charP_two_of_card_eq_four hk
    exact det_jM (val_mul_self_add hk hu)⟩

variable (hk : Nat.card k = 4) (hu : u ≠ 1)
include hk hu

theorem fSL_mul_hSL : fSL hk hu * hSL u = rSL * fSL hk hu := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_hSL hk, coe_rSL']
  exact fM_mul_hM (val_mul_self_add hk hu)

theorem fSL_mul_rSL : fSL hk hu * rSL = zSL u * (hSL u)⁻¹ * fSL hk hu := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_zSL hk, coe_hSL_inv hk hu, coe_rSL', Matrix.smul_mul,
    Matrix.one_mul]
  exact fM_mul_rM (val_mul_self_add hk hu)

theorem jSL_mul_hSL : jSL hk hu * hSL u = rSL * (hSL u)⁻¹ * jSL hk hu := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_hSL hk, coe_hSL_inv hk hu, coe_rSL']
  exact jM_mul_hM (val_mul_self_add hk hu)

theorem jSL_mul_rSL :
    jSL hk hu * rSL = zSL u * ((hSL u)⁻¹ * rSL * (hSL u)⁻¹) * jSL hk hu := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [coe_zSL hk, coe_hSL_inv hk hu, coe_rSL', Matrix.smul_mul, Matrix.one_mul]
  exact jM_mul_rM (val_mul_self_add hk hu)

end Normalizer

section Centralizer

variable {u : kˣ}

@[expose] def fP (hk : Nat.card k = 4) (hu : u ≠ 1) : projectiveSL 3 k := proj 3 k (fSL hk hu)

@[expose] def jP (hk : Nat.card k = 4) (hu : u ≠ 1) : projectiveSL 3 k := proj 3 k (jSL hk hu)

theorem centralizer_inv_singleton {G : Type*} [Group G] (y : G) :
    Subgroup.centralizer ({y⁻¹} : Set G) = Subgroup.centralizer {y} := by
  ext z
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc z * y = y * (y⁻¹ * z) * y := by group
      _ = y * (z * y⁻¹) * y := by rw [h]
      _ = y * z := by group
  · intro h
    calc z * y⁻¹ = y⁻¹ * (y * z) * y⁻¹ := by group
      _ = y⁻¹ * (z * y) * y⁻¹ := by rw [h]
      _ = y⁻¹ * z := by group

theorem centralizer_conj_eq {G : Type*} [Group G] {E : Subgroup G} {n y : G}
    (hn : n ∈ Subgroup.normalizer (E : Set G)) (hy : Subgroup.centralizer ({y} : Set G) = E) :
    Subgroup.centralizer ({n * y * n⁻¹} : Set G) = E := by
  ext z
  rw [Subgroup.mem_centralizer_singleton_iff]
  have key : z * (n * y * n⁻¹) = n * y * n⁻¹ * z ↔ n⁻¹ * z * n * y = y * (n⁻¹ * z * n) := by
    constructor
    · intro h
      calc n⁻¹ * z * n * y = n⁻¹ * (z * (n * y * n⁻¹)) * n := by group
        _ = n⁻¹ * (n * y * n⁻¹ * z) * n := by rw [h]
        _ = y * (n⁻¹ * z * n) := by group
    · intro h
      calc z * (n * y * n⁻¹) = n * (n⁻¹ * z * n * y) * n⁻¹ := by group
        _ = n * (y * (n⁻¹ * z * n)) * n⁻¹ := by rw [h]
        _ = n * y * n⁻¹ * z := by group
  rw [key, ← Subgroup.mem_centralizer_singleton_iff, hy]
  have hn' := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) z)
  rw [inv_inv] at hn'
  exact hn'.symm

variable (hk : Nat.card k = 4) (hu : u ≠ 1)
include hk hu

omit hu in
theorem proj_zSL : proj 3 k (zSL u) = 1 := proj_eq_one_iff.mpr (zSL_mem_scalars hk)

theorem fP_mul_aP : fP hk hu * aP u = bP * fP hk hu := by
  rw [fP, aP, bP, ← map_mul, fSL_mul_hSL hk hu, map_mul]

theorem fP_mul_bP : fP hk hu * bP = (aP u)⁻¹ * fP hk hu := by
  rw [fP, aP, bP, ← map_mul, fSL_mul_rSL hk hu, map_mul, map_mul, proj_zSL hk, one_mul,
    map_inv]

theorem jP_mul_aP : jP hk hu * aP u = bP * (aP u)⁻¹ * jP hk hu := by
  rw [jP, aP, bP, ← map_mul, jSL_mul_hSL hk hu, map_mul, map_mul, map_inv]

theorem jP_mul_bP : jP hk hu * bP = (aP u)⁻¹ * bP * (aP u)⁻¹ * jP hk hu := by
  rw [jP, aP, bP, ← map_mul, jSL_mul_rSL hk hu, map_mul, map_mul, proj_zSL hk, one_mul,
    map_mul, map_mul, map_inv]

theorem fP_conj_aP : fP hk hu * aP u * (fP hk hu)⁻¹ = bP := by
  rw [fP_mul_aP hk hu, mul_inv_cancel_right]

theorem fP_conj_bP : fP hk hu * bP * (fP hk hu)⁻¹ = (aP u)⁻¹ := by
  rw [fP_mul_bP hk hu, mul_inv_cancel_right]

theorem jP_conj_aP : jP hk hu * aP u * (jP hk hu)⁻¹ = bP * (aP u)⁻¹ := by
  rw [jP_mul_aP hk hu, mul_inv_cancel_right]

theorem jP_conj_bP : jP hk hu * bP * (jP hk hu)⁻¹ = (aP u)⁻¹ * bP * (aP u)⁻¹ := by
  rw [jP_mul_bP hk hu, mul_inv_cancel_right]

theorem fP_mem_normalizer : fP hk hu ∈ Subgroup.normalizer (eZero k : Set (projectiveSL 3 k)) := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  rw [eZero_eq_closure hk hu]
  refine CFSG.RankThree.Asc83Table.mem_normalizer_closure_of_conj_mem ?_
  rintro _ (rfl | rfl)
  · rw [fP_conj_aP hk hu]
    exact Subgroup.subset_closure (by simp)
  · rw [fP_conj_bP hk hu]
    exact inv_mem (Subgroup.subset_closure (by simp))

theorem jP_mem_normalizer : jP hk hu ∈ Subgroup.normalizer (eZero k : Set (projectiveSL 3 k)) := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  rw [eZero_eq_closure hk hu]
  refine CFSG.RankThree.Asc83Table.mem_normalizer_closure_of_conj_mem ?_
  have ha : aP u ∈ Subgroup.closure ({aP u, bP} : Set (projectiveSL 3 k)) :=
    Subgroup.subset_closure (by simp)
  have hb : bP ∈ Subgroup.closure ({aP u, bP} : Set (projectiveSL 3 k)) :=
    Subgroup.subset_closure (by simp)
  rintro _ (rfl | rfl)
  · rw [jP_conj_aP hk hu]
    exact mul_mem hb (inv_mem ha)
  · rw [jP_conj_bP hk hu]
    exact mul_mem (mul_mem (inv_mem ha) hb) (inv_mem ha)

theorem centralizer_aP : Subgroup.centralizer ({aP u} : Set (projectiveSL 3 k)) = eZero k := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    obtain ⟨g, rfl⟩ := proj_surjective 3 k x
    exact ⟨g, mem_qSub_of_commute hk hu hx, rfl⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commute_of_mem_eZero hk hx aP_mem_eZero

end Centralizer

section CentralizerAll

theorem sq_eq_inv_of_pow_three {G : Type*} [Group G] {y : G} (h : y ^ 3 = 1) : y ^ 2 = y⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h)

theorem exists_units_ne_one (hk : Nat.card k = 4) : ∃ u : kˣ, u ≠ 1 := by
  obtain ⟨ω, hω0, hω1⟩ := LinearFieldFour.exists_ne_zero_ne_one hk
  exact ⟨Units.mk0 ω hω0, fun h => hω1 (by simpa using congrArg Units.val h)⟩

theorem centralizer_eq_eZero (hk : Nat.card k = 4) {x : projectiveSL 3 k} (hx : x ∈ eZero k)
    (hx1 : x ≠ 1) : Subgroup.centralizer ({x} : Set (projectiveSL 3 k)) = eZero k := by
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  have ha3 : aP u ^ 3 = 1 := pow_three_of_mem_eZero hk aP_mem_eZero
  have hb3 : (bP : projectiveSL 3 k) ^ 3 = 1 := pow_three_of_mem_eZero hk bP_mem_eZero
  have hab : Commute (aP u) bP := commute_of_mem_eZero hk aP_mem_eZero bP_mem_eZero
  have hA := centralizer_aP hk hu
  have hB : Subgroup.centralizer ({bP} : Set (projectiveSL 3 k)) = eZero k := by
    rw [← fP_conj_aP hk hu]
    exact centralizer_conj_eq (fP_mem_normalizer hk hu) hA
  have hC : Subgroup.centralizer ({bP * (aP u)⁻¹} : Set (projectiveSL 3 k)) = eZero k := by
    rw [← jP_conj_aP hk hu]
    exact centralizer_conj_eq (jP_mem_normalizer hk hu) hA
  have hD : Subgroup.centralizer ({aP u * bP} : Set (projectiveSL 3 k)) = eZero k := by
    have h1 : (fP hk hu)⁻¹ * bP * fP hk hu = aP u := by
      rw [← fP_conj_aP hk hu]
      group
    have h2 : (fP hk hu)⁻¹ * aP u * fP hk hu = bP⁻¹ := by
      calc (fP hk hu)⁻¹ * aP u * fP hk hu = ((fP hk hu)⁻¹ * (aP u)⁻¹ * fP hk hu)⁻¹ := by group
        _ = ((fP hk hu)⁻¹ * (fP hk hu * bP * (fP hk hu)⁻¹) * fP hk hu)⁻¹ := by
            rw [fP_conj_bP hk hu]
        _ = bP⁻¹ := by group
    have h3 : aP u * bP = (fP hk hu)⁻¹ * (bP * (aP u)⁻¹) * (fP hk hu)⁻¹⁻¹ := by
      calc aP u * bP = ((fP hk hu)⁻¹ * bP * fP hk hu) * ((fP hk hu)⁻¹ * aP u * fP hk hu)⁻¹ := by
            rw [h1, h2, inv_inv]
        _ = (fP hk hu)⁻¹ * (bP * (aP u)⁻¹) * (fP hk hu)⁻¹⁻¹ := by group
    rw [h3]
    exact centralizer_conj_eq (inv_mem (fP_mem_normalizer hk hu)) hC
  obtain ⟨i, j, hi, hj, rfl⟩ := exists_eq_aP_pow_mul_bP_pow hk hu hx
  interval_cases i <;> interval_cases j
  · simp at hx1
  · simpa using hB
  · rw [pow_zero, one_mul, sq_eq_inv_of_pow_three hb3, centralizer_inv_singleton, hB]
  · simpa using hA
  · simpa using hD
  · rw [pow_one, sq_eq_inv_of_pow_three hb3, show aP u * bP⁻¹ = (bP * (aP u)⁻¹)⁻¹ by group,
      centralizer_inv_singleton, hC]
  · rw [sq_eq_inv_of_pow_three ha3, pow_zero, mul_one, centralizer_inv_singleton, hA]
  · rw [sq_eq_inv_of_pow_three ha3, pow_one, (hab.inv_left).eq, hC]
  · rw [sq_eq_inv_of_pow_three ha3, sq_eq_inv_of_pow_three hb3, ← _root_.mul_inv_rev, ← hab.eq,
      centralizer_inv_singleton, hD]

end CentralizerAll

section Sylow

theorem card_projectiveSL (hk : Nat.card k = 4) : Nat.card (projectiveSL 3 k) = 20160 :=
  GL3TwoFixedModel.card_projectiveSL_three_four hk

theorem factorization_card (hk : Nat.card k = 4) :
    (Nat.card (projectiveSL 3 k)).factorization 3 = 2 := by
  rw [card_projectiveSL hk]
  exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
    (show 20160 = 3 ^ 2 * 2240 by norm_num) (by norm_num)

theorem card_eZero_eq (hk : Nat.card k = 4) :
    Nat.card (eZero k) = 3 ^ (Nat.card (projectiveSL 3 k)).factorization 3 := by
  rw [factorization_card hk, card_eZero hk]
  norm_num

@[expose] noncomputable def eZeroSylow (hk : Nat.card k = 4) : Sylow 3 (projectiveSL 3 k) :=
  haveI := LinearFieldFour.finite_of_card_eq_four hk
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  Sylow.ofCard (eZero k) (card_eZero_eq hk)

theorem coe_eZeroSylow (hk : Nat.card k = 4) :
    ((eZeroSylow hk : Sylow 3 (projectiveSL 3 k)) : Subgroup (projectiveSL 3 k)) = eZero k :=
  rfl

theorem exists_eq_map_conj_eZero (hk : Nat.card k = 4) {E : Subgroup (projectiveSL 3 k)}
    (hE : Nat.card E = 9) :
    ∃ g : projectiveSL 3 k, E = (eZero k).map (MulAut.conj g).toMonoidHom := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE' : Nat.card E = 3 ^ (Nat.card (projectiveSL 3 k)).factorization 3 := by
    rw [factorization_card hk, hE]
    norm_num
  exact CFSG.RankThree.Asc83Table.exists_sylow_eq_map (card_eZero_eq hk) (Sylow.ofCard E hE')

theorem centralizer_conj_map {G : Type*} [Group G] (g y : G) :
    Subgroup.centralizer ({g * y * g⁻¹} : Set G) =
      (Subgroup.centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext z
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    refine ⟨g⁻¹ * z * g, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * z * g * y = g⁻¹ * (z * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹ * z) * g := by rw [h]
      _ = y * (g⁻¹ * z * g) := by group
  · rintro ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hw
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * w * g⁻¹ * (g * y * g⁻¹) = g * (w * y) * g⁻¹ := by group
      _ = g * (y * w) * g⁻¹ := by rw [hw]
      _ = g * y * g⁻¹ * (g * w * g⁻¹) := by group

theorem centralizer_eq_of_card_eq_nine (hk : Nat.card k = 4) {E : Subgroup (projectiveSL 3 k)}
    (hE : Nat.card E = 9) {x : projectiveSL 3 k} (hx : x ∈ E) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set (projectiveSL 3 k)) = E := by
  obtain ⟨g, rfl⟩ := exists_eq_map_conj_eZero hk hE
  obtain ⟨y, hy, rfl⟩ := hx
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hx1 (map_one _)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hx1 ⊢
  rw [centralizer_conj_map, centralizer_eq_eZero hk hy hy1]

theorem isElementaryAbelian_of_card_eq_nine (hk : Nat.card k = 4) {E : Subgroup (projectiveSL 3 k)}
    (hE : Nat.card E = 9) : CFSG.IsElementaryAbelian 3 E := by
  obtain ⟨g, rfl⟩ := exists_eq_map_conj_eZero hk hE
  exact CFSG.RankThree.Asc83Table.IsElementaryAbelian.map_hom _ (isElementaryAbelian_eZero hk)

theorem eq_bot_of_le_normalizer (hk : Nat.card k = 4) {E Y : Subgroup (projectiveSL 3 k)}
    (hE : Nat.card E = 9) (hY : ¬ 3 ∣ Nat.card Y)
    (hEY : E ≤ Subgroup.normalizer (Y : Set (projectiveSL 3 k))) : Y = ⊥ := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := isElementaryAbelian_of_card_eq_nine hk hE
  have hpow : ∀ m : E, m ^ 3 = 1 := fun m =>
    Subtype.ext (by simpa using elemPow_eq_one_of_isElementaryAbelian (A := E) m.1 m.2)
  rw [CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 3
    Nat.prime_three E Y (fun m => hpow m) (by rw [hE]; norm_num) hY hEY]
  refine iSup₂_eq_bot.mpr fun m hm => ?_
  have hm1 : (m : projectiveSL 3 k) ≠ 1 := fun h => hm (Subtype.ext h)
  rw [centralizer_eq_of_card_eq_nine hk hE m.2 hm1]
  refine eq_bot_iff.mpr fun z hz => ?_
  have h1 : Nat.card (Y ⊓ E : Subgroup (projectiveSL 3 k)) ∣ Nat.card Y :=
    Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card (Y ⊓ E : Subgroup (projectiveSL 3 k)) ∣ 9 :=
    hE ▸ Subgroup.card_dvd_of_le inf_le_right
  have h3 : Nat.card (Y ⊓ E : Subgroup (projectiveSL 3 k)) = 1 := by
    have hmem : Nat.card (Y ⊓ E : Subgroup (projectiveSL 3 k)) ∈ Nat.divisors 9 :=
      Nat.mem_divisors.2 ⟨h2, by norm_num⟩
    rw [show Nat.divisors 9 = {1, 3, 9} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · exact h
    · rw [h] at h1; exact absurd h1 hY
    · rw [h] at h1; exact absurd ((show 3 ∣ 9 by norm_num).trans h1) hY
  rw [Subgroup.card_eq_one] at h3
  rw [h3] at hz
  exact hz

end Sylow

section Rank

variable {u : kˣ}

@[expose] noncomputable def eZeroBasis (hk : Nat.card k = 4) (hu : u ≠ 1) :
    CFSG.RankThree.Asc83Table.E9Basis (projectiveSL 3 k) where
  a := aP u
  b := bP
  ha := pow_three_of_mem_eZero hk aP_mem_eZero
  hb := pow_three_of_mem_eZero hk bP_mem_eZero
  hab := commute_of_mem_eZero hk aP_mem_eZero bP_mem_eZero
  card := by rw [← eZero_eq_closure hk hu]; exact card_eZero hk

theorem eZeroBasis_sub (hk : Nat.card k = 4) (hu : u ≠ 1) : (eZeroBasis hk hu).sub = eZero k :=
  (eZero_eq_closure hk hu).symm

theorem pRank_three_projectiveSL (hk : Nat.card k = 4) :
    CFSG.pRank 3 (projectiveSL 3 k) = 2 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  exact CFSG.RankThree.Asc83Table.e9_pRank (eZeroBasis hk hu) (factorization_card hk)

theorem aP_eq_hP (hk : Nat.card k = 4) :
    aP u = LinearFieldFour.hP (u : k) (LinearFieldFour.omega_cube hk u.ne_zero) := by
  rw [aP, LinearFieldFour.hP]
  congr 1
  exact Subtype.ext (coe_hSL hk)

theorem mul_ne_mul_of_orderOf (hk : Nat.card k = 4) {a t : projectiveSL 3 k} (ha : orderOf a = 3)
    (ht : orderOf t = 2) : a * t ≠ t * a := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have hS9 : Nat.card (S : Subgroup (projectiveSL 3 k)) = 9 := by
    rw [Sylow.card_eq_multiplicity, factorization_card hk]
    norm_num
  have ha1 : a ≠ 1 := by
    rintro rfl
    simp at ha
  have hC := centralizer_eq_of_card_eq_nine hk hS9 (hS (Subgroup.mem_zpowers a)) ha1
  intro hat
  have htS : t ∈ (S : Subgroup (projectiveSL 3 k)) := by
    rw [← hC, Subgroup.mem_centralizer_singleton_iff]
    exact hat.symm
  have h := orderOf_dvd_natCard (⟨t, htS⟩ : (S : Subgroup (projectiveSL 3 k)))
  rw [Subgroup.orderOf_mk, ht, hS9] at h
  norm_num at h

theorem localRank_three_projectiveSL {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4) :
    CFSG.Assembly.RankThreeEven.localRank 3 (projectiveSL 3 k) = 1 := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  refine le_antisymm (CFSG.RankThree.PartTwo.Census.localRank_three_le_one_of_forall_ne
    fun a t ha ht => mul_ne_mul_of_orderOf hk ha ht) ?_
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  have h3 := LinearFieldFour.omega_cube hk u.ne_zero
  set ω : k := (u : k)
  let xHom : Multiplicative k →* projectiveSL 3 k :=
    { toFun := fun c => LinearFieldFour.xP (Multiplicative.toAdd c)
      map_one' := (LinearFieldFour.xP_eq_one_iff 0).mpr rfl
      map_mul' := fun c d => LinearFieldFour.xP_add _ _ }
  have hxHom : ∀ c : k, xHom (Multiplicative.ofAdd c) = LinearFieldFour.xP c := fun _ => rfl
  set T := xHom.range
  have hT : T ≠ ⊥ := by
    intro h
    have hmem : LinearFieldFour.xP (1 : k) ∈ T := ⟨Multiplicative.ofAdd 1, rfl⟩
    rw [h, Subgroup.mem_bot, LinearFieldFour.xP_eq_one_iff] at hmem
    exact one_ne_zero hmem
  have hT2 : IsPGroup 2 T := by
    rintro ⟨_, c, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change xHom c ^ 2 = 1
    rw [sq, ← map_mul, show c * c = 1 from ?_, map_one]
    change Multiplicative.ofAdd (Multiplicative.toAdd c + Multiplicative.toAdd c) = 1
    rw [CharTwo.add_self_eq_zero]
    rfl
  have hconj : ∀ c : k, aP u * LinearFieldFour.xP c * (aP u)⁻¹ = LinearFieldFour.xP (ω * c) := by
    intro c
    rw [aP_eq_hP hk]
    exact LinearFieldFour.hP_conj_xP h3 c
  have hnorm : aP u ∈ Subgroup.normalizer (T : Set (projectiveSL 3 k)) := by
    refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨?_, ?_⟩
    · rintro ⟨c, rfl⟩
      exact ⟨Multiplicative.ofAdd (ω * Multiplicative.toAdd c), (hconj _).symm⟩
    · rintro ⟨c, hc⟩
      refine ⟨Multiplicative.ofAdd (ω * ω * Multiplicative.toAdd c), ?_⟩
      rw [hxHom]
      have h1 := hconj (ω * ω * Multiplicative.toAdd c)
      rw [← mul_assoc, ← mul_assoc, h3, one_mul] at h1
      have h2 : aP u * LinearFieldFour.xP (ω * ω * Multiplicative.toAdd c) * (aP u)⁻¹ =
          aP u * h * (aP u)⁻¹ := by rw [h1, ← hc]; rfl
      simpa using h2
  have hE : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers (aP u)) :=
    ⟨inferInstance, fun x hx => by
      obtain ⟨n, rfl⟩ := hx
      simp only
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
        pow_three_of_mem_eZero hk aP_mem_eZero, _root_.one_zpow]⟩
  have ha1 := aP_ne_one hk hu
  have hcard : Nat.card (Subgroup.zpowers (aP u)) = 3 ^ 1 := by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (pow_three_of_mem_eZero hk aP_mem_eZero) ha1
  exact CFSG.RankThree.PartTwo.Census.le_localRank_of_le_normalizer Nat.prime_three hT hT2 hE
    hcard ((Subgroup.zpowers_le).mpr hnorm)

end Rank

end CFSG.RankThree.PartTwo.KFacts.L34
