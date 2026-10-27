module

public import CFSG.Quasithin.Background.SmithB42LnL5Par
public import CFSG.Quasithin.Background.SmithB51LnModel

public section

namespace CFSG.Quasithin.B42Ln

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix

theorem card_dot_eq_zero : ∀ v : Fin 5 → ZMod 2, v ≠ 0 →
    (Finset.univ.filter fun φ : Fin 5 → ZMod 2 => φ ⬝ᵥ v = 0).card = 16 := by
  decide

theorem exists_coord_eq_one : ∀ v : Fin 5 → ZMod 2, v ≠ 0 → ∃ i, v i = 1 := by decide

variable {B : Subgroup G5}

@[expose] def rowOf (i₀ : Fin 5) (b : G5) : Fin 5 → ZMod 2 :=
  fun j => (b : Matrix (Fin 5) (Fin 5) (ZMod 2)) i₀ j - (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) i₀ j

@[expose] def colOf (j₀ : Fin 5) (b : G5) : Fin 5 → ZMod 2 :=
  fun i => (b : Matrix (Fin 5) (Fin 5) (ZMod 2)) i j₀ - (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) i j₀

theorem rowOf_of_isTv {i₀ : Fin 5} {b : G5} {v φ : Fin 5 → ZMod 2} (h : IsTv b v φ)
    (hv : v i₀ = 1) : rowOf i₀ b = φ := by
  funext j
  simp only [rowOf, h.1, Matrix.add_apply, vecMulVec_apply, hv, one_mul]
  abel

theorem colOf_of_isTv {j₀ : Fin 5} {b : G5} {v φ : Fin 5 → ZMod 2} (h : IsTv b v φ)
    (hφ : φ j₀ = 1) : colOf j₀ b = v := by
  funext i
  simp only [colOf, h.1, Matrix.add_apply, vecMulVec_apply, hφ, mul_one]
  abel

theorem rowOf_one (i₀ : Fin 5) : rowOf i₀ 1 = 0 := by
  funext j
  simp [rowOf]

theorem colOf_one (j₀ : Fin 5) : colOf j₀ 1 = 0 := by
  funext i
  simp [colOf]

theorem card_le_of_center {v : Fin 5 → ZMod 2} (hv0 : v ≠ 0)
    (hB : ∀ b ∈ B, b ≠ 1 → ∃ φ, IsTv b v φ) :
    Nat.card B ≤ 16 ∧ (Nat.card B = 16 → ∀ φ : Fin 5 → ZMod 2, φ ⬝ᵥ v = 0 → φ ≠ 0 →
      ∃ b ∈ B, IsTv b v φ) := by
  classical
  obtain ⟨i₀, hi₀⟩ := exists_coord_eq_one v hv0
  set S := Finset.univ.filter fun φ : Fin 5 → ZMod 2 => φ ⬝ᵥ v = 0 with hS
  have hval : ∀ b : ↥B, rowOf i₀ (b : G5) ∈ S := by
    intro b
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases hb : (b : G5) = 1
    · rw [hb, rowOf_one, zero_dotProduct]
    · obtain ⟨φ, hφ⟩ := hB b b.2 hb
      rw [rowOf_of_isTv hφ hi₀]
      exact hφ.2.2.2
  set f : ↥B → ↥S := fun b => ⟨rowOf i₀ (b : G5), hval b⟩ with hf
  have hinj : Function.Injective f := by
    intro b b' h
    have h' : rowOf i₀ (b : G5) = rowOf i₀ (b' : G5) := congrArg Subtype.val h
    apply Subtype.ext
    by_cases hb : (b : G5) = 1 <;> by_cases hb' : (b' : G5) = 1
    · rw [hb, hb']
    · exfalso
      obtain ⟨φ, hφ⟩ := hB b' b'.2 hb'
      rw [hb, rowOf_one, rowOf_of_isTv hφ hi₀] at h'
      exact hφ.2.2.1 h'.symm
    · exfalso
      obtain ⟨φ, hφ⟩ := hB b b.2 hb
      rw [hb', rowOf_one, rowOf_of_isTv hφ hi₀] at h'
      exact hφ.2.2.1 h'
    · obtain ⟨φ, hφ⟩ := hB b b.2 hb
      obtain ⟨φ', hφ'⟩ := hB b' b'.2 hb'
      rw [rowOf_of_isTv hφ hi₀, rowOf_of_isTv hφ' hi₀] at h'
      apply Subtype.ext
      rw [hφ.1, hφ'.1, h']
  have hcardS : Fintype.card ↥S = 16 := by
    rw [Fintype.card_coe, hS, card_dot_eq_zero v hv0]
  have hle : Nat.card B ≤ 16 := by
    rw [← hcardS, Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective f hinj
  refine ⟨hle, fun h16 φ hφv hφ0 => ?_⟩
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [hcardS, ← Nat.card_eq_fintype_card, h16]
  obtain ⟨b, hb⟩ := hbij.2 ⟨φ, by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hφv⟩⟩
  have hb' : rowOf i₀ (b : G5) = φ := congrArg Subtype.val hb
  refine ⟨b, b.2, ?_⟩
  by_cases hb1 : (b : G5) = 1
  · rw [hb1, rowOf_one] at hb'
    exact absurd hb'.symm hφ0
  · obtain ⟨φ', hφ'⟩ := hB b b.2 hb1
    rw [rowOf_of_isTv hφ' hi₀] at hb'
    exact hb' ▸ hφ'

theorem card_dot_eq_zero' : ∀ φ : Fin 5 → ZMod 2, φ ≠ 0 →
    (Finset.univ.filter fun w : Fin 5 → ZMod 2 => φ ⬝ᵥ w = 0).card = 16 := by
  decide

theorem card_le_of_axis {φ : Fin 5 → ZMod 2} (hφ0 : φ ≠ 0)
    (hB : ∀ b ∈ B, b ≠ 1 → ∃ v, IsTv b v φ) :
    Nat.card B ≤ 16 ∧ (Nat.card B = 16 → ∀ w : Fin 5 → ZMod 2, φ ⬝ᵥ w = 0 → w ≠ 0 →
      ∃ b ∈ B, IsTv b w φ) := by
  classical
  obtain ⟨j₀, hj₀⟩ := exists_coord_eq_one φ hφ0
  set S := Finset.univ.filter fun w : Fin 5 → ZMod 2 => φ ⬝ᵥ w = 0 with hS
  have hval : ∀ b : ↥B, colOf j₀ (b : G5) ∈ S := by
    intro b
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases hb : (b : G5) = 1
    · rw [hb, colOf_one, dotProduct_zero]
    · obtain ⟨v, hv⟩ := hB b b.2 hb
      rw [colOf_of_isTv hv hj₀]
      exact hv.2.2.2
  set f : ↥B → ↥S := fun b => ⟨colOf j₀ (b : G5), hval b⟩ with hf
  have hinj : Function.Injective f := by
    intro b b' h
    have h' : colOf j₀ (b : G5) = colOf j₀ (b' : G5) := congrArg Subtype.val h
    apply Subtype.ext
    by_cases hb : (b : G5) = 1 <;> by_cases hb' : (b' : G5) = 1
    · rw [hb, hb']
    · exfalso
      obtain ⟨v, hv⟩ := hB b' b'.2 hb'
      rw [hb, colOf_one, colOf_of_isTv hv hj₀] at h'
      exact hv.2.1 h'.symm
    · exfalso
      obtain ⟨v, hv⟩ := hB b b.2 hb
      rw [hb', colOf_one, colOf_of_isTv hv hj₀] at h'
      exact hv.2.1 h'
    · obtain ⟨v, hv⟩ := hB b b.2 hb
      obtain ⟨v', hv'⟩ := hB b' b'.2 hb'
      rw [colOf_of_isTv hv hj₀, colOf_of_isTv hv' hj₀] at h'
      apply Subtype.ext
      rw [hv.1, hv'.1, h']
  have hcardS : Fintype.card ↥S = 16 := by
    rw [Fintype.card_coe, hS, card_dot_eq_zero' φ hφ0]
  have hle : Nat.card B ≤ 16 := by
    rw [← hcardS, Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective f hinj
  refine ⟨hle, fun h16 w hwφ hw0 => ?_⟩
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [hcardS, ← Nat.card_eq_fintype_card, h16]
  obtain ⟨b, hb⟩ := hbij.2 ⟨w, by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hwφ⟩⟩
  have hb' : colOf j₀ (b : G5) = w := congrArg Subtype.val hb
  refine ⟨b, b.2, ?_⟩
  by_cases hb1 : (b : G5) = 1
  · rw [hb1, colOf_one] at hb'
    exact absurd hb'.symm hw0
  · obtain ⟨v', hv'⟩ := hB b b.2 hb1
    rw [colOf_of_isTv hv' hj₀] at hb'
    exact hb' ▸ hv'

theorem coe_mul_inv (g : G5) :
    (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * ((g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem coe_inv_mul (g : G5) :
    ((g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem eTM_eq (i j : Fin 5) (hij : i ≠ j) :
    eTM i j = 1 + vecMulVec (Pi.single i 1) (Pi.single j 1) := by
  revert i j
  decide

theorem eT_mem_conj_of_center {v : Fin 5 → ZMod 2} (hv0 : v ≠ 0)
    (hB : ∀ b ∈ B, b ≠ 1 → ∃ φ, IsTv b v φ) (h16 : Nat.card B = 16) {g : G5} {k : Fin 5}
    (hg : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v = Pi.single k 1) {j : Fin 5} (hjk : k ≠ j) :
    ∃ b ∈ B, g * b * g⁻¹ = eT k j hjk := by
  set ψ : Fin 5 → ZMod 2 := Pi.single j 1 ᵥ* (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) with hψ
  have hgv : ((g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Pi.single k 1 = v := by
    rw [← hg, mulVec_mulVec, coe_inv_mul, one_mulVec]
  have hψv : ψ ⬝ᵥ v = 0 := by
    rw [hψ, ← dotProduct_mulVec, hg]
    simp [Pi.single_apply, hjk, dotProduct]
  have hψ0 : ψ ≠ 0 := by
    intro h0
    have := congrArg (· ᵥ* ((g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2))) h0
    simp only [hψ, vecMul_vecMul, coe_mul_inv, vecMul_one, zero_vecMul] at this
    exact absurd (congrFun this j) (by simp)
  obtain ⟨b, hb, hbt⟩ := (card_le_of_center hv0 hB).2 h16 ψ hψv hψ0
  refine ⟨b, hb, Subtype.ext ?_⟩
  show (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (b : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
    ((g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = eTM k j
  rw [hbt.1, eTM_eq k j hjk, mul_add, mul_one, add_mul, coe_mul_inv, mul_vecMulVec,
    vecMulVec_mul, hg, hψ, vecMul_vecMul, coe_mul_inv, vecMul_one]

theorem eT_mem_conj_of_axis {φ : Fin 5 → ZMod 2} (hφ0 : φ ≠ 0)
    (hB : ∀ b ∈ B, b ≠ 1 → ∃ v, IsTv b v φ) (h16 : Nat.card B = 16) {g : G5} {k : Fin 5}
    (hg : Pi.single k 1 ᵥ* (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) = φ) {j : Fin 5} (hjk : j ≠ k) :
    ∃ b ∈ B, g * b * g⁻¹ = eT j k hjk := by
  set w : Fin 5 → ZMod 2 := ((g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Pi.single j 1
    with hw
  have hφg : φ ᵥ* ((g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = Pi.single k 1 := by
    rw [← hg, vecMul_vecMul, coe_mul_inv, vecMul_one]
  have hφw : φ ⬝ᵥ w = 0 := by
    rw [hw, dotProduct_mulVec, hφg]
    simp [Pi.single_apply, hjk, dotProduct]
  have hw0 : w ≠ 0 := by
    intro h0
    have := congrArg ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ ·) h0
    simp only [hw, mulVec_mulVec, coe_mul_inv, one_mulVec, mulVec_zero] at this
    exact absurd (congrFun this j) (by simp)
  obtain ⟨b, hb, hbt⟩ := (card_le_of_axis hφ0 hB).2 h16 w hφw hw0
  refine ⟨b, hb, Subtype.ext ?_⟩
  show (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (b : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
    ((g⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = eTM j k
  rw [hbt.1, eTM_eq j k hjk, mul_add, mul_one, add_mul, coe_mul_inv, mul_vecMulVec,
    vecMulVec_mul, hw, mulVec_mulVec, coe_mul_inv, one_mulVec, hφg]

theorem exists_mulVec_eq_G5 {x y : Fin 5 → ZMod 2} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : G5, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x = y := by
  obtain ⟨g, hg⟩ := B5.Ln.exists_mulVec_eq hx hy
  refine ⟨(CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 5 (ZMod 2)).symm g, ?_⟩
  have h := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 5 (ZMod 2)
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 5 (ZMod 2)).symm g)
  rw [MulEquiv.apply_symm_apply] at h
  rw [← hg, B5.Ln.mat]
  exact congrArg (· *ᵥ x) h.symm

theorem exists_conj_center {v : Fin 5 → ZMod 2} (hv0 : v ≠ 0) (k : Fin 5) :
    ∃ g : G5, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v = Pi.single k 1 :=
  exists_mulVec_eq_G5 hv0 (by simp)

theorem exists_conj_axis {φ : Fin 5 → ZMod 2} (hφ0 : φ ≠ 0) (k : Fin 5) :
    ∃ g : G5, Pi.single k 1 ᵥ* (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) = φ := by
  obtain ⟨h, hh⟩ := exists_mulVec_eq_G5 (x := Pi.single k 1) (by simp) hφ0
  refine ⟨⟨(h : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ, by rw [det_transpose]; exact h.2⟩, ?_⟩
  show Pi.single k 1 ᵥ* (h : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ = φ
  rw [vecMul_transpose, hh]

end CFSG.Quasithin.B42Ln
