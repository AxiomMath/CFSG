module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFBlock
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFLin
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFGF4

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429F

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.RonanK429E
open Matrix
open scoped Matrix commutatorElement MatrixGroups

namespace L6

@[expose] def r1M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0,1,0,0,0,0; 1,1,0,0,0,0; 0,0,1,0,0,0; 0,0,0,1,0,0; 0,0,0,0,1,0; 0,0,0,0,0,1]

@[expose] def r2M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0,1,0,0,0,0; 1,1,0,0,0,0; 0,0,0,1,0,0; 0,0,1,1,0,0; 0,0,0,0,1,0; 0,0,0,0,0,1]

@[expose] def toK1 : Fin 6 → Fin 4 ⊕ Fin 2 :=
  ![.inr 0, .inr 1, .inl 0, .inl 1, .inl 2, .inl 3]

@[expose] def fromK1 : Fin 4 ⊕ Fin 2 → Fin 6 :=
  Sum.elim (fun i => ![2, 3, 4, 5] i) (fun i => ![0, 1] i)

@[expose] def split1 : Fin 6 ≃ Fin 4 ⊕ Fin 2 where
  toFun := toK1
  invFun := fromK1
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

@[expose] def toK2 : Fin 6 → Fin 2 ⊕ (Fin 2 ⊕ Fin 2) :=
  ![.inr (.inl 0), .inr (.inl 1), .inr (.inr 0), .inr (.inr 1), .inl 0, .inl 1]

@[expose] def fromK2 : Fin 2 ⊕ (Fin 2 ⊕ Fin 2) → Fin 6 :=
  Sum.elim (fun i => ![4, 5] i) (Sum.elim (fun i => ![0, 1] i) (fun i => ![2, 3] i))

@[expose] def split2 : Fin 6 ≃ Fin 2 ⊕ (Fin 2 ⊕ Fin 2) where
  toFun := toK2
  invFun := fromK2
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

theorem comm_rho_cases : ∀ B : Matrix (Fin 2) (Fin 2) (ZMod 2), B * rhoM = rhoM * B →
    B = 0 ∨ B = 1 ∨ B = rhoM ∨ B = rhoM * rhoM := by
  decide +kernel

theorem comm_of_commute_rho : ∀ A B : Matrix (Fin 2) (Fin 2) (ZMod 2), A * rhoM = rhoM * A →
    B * rhoM = rhoM * B → A * B = B * A := by
  decide +kernel

theorem pow_seven_two : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 2), A ^ 7 = 1 → A = 1 := by
  decide +kernel

@[expose] def rhoCands : List (Matrix (Fin 2) (Fin 2) (ZMod 2)) := [0, 1, rhoM, rhoM * rhoM]

set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 400000 in
theorem four_check : ∀ P ∈ rhoCands, ∀ Q ∈ rhoCands, ∀ R ∈ rhoCands, ∀ T ∈ rhoCands,
    (fromBlocks P Q R T : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) ^ 7 = 1 →
      P = 1 ∧ Q = 0 ∧ R = 0 ∧ T = 1 := by
  decide +kernel

theorem four_pow_seven {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)}
    (hX : X * fromBlocks rhoM 0 0 rhoM = fromBlocks rhoM 0 0 rhoM * X) (h7 : X ^ 7 = 1) :
    X = 1 := by
  obtain ⟨P, Q, R, T, rfl⟩ : ∃ P Q R T : Matrix (Fin 2) (Fin 2) (ZMod 2),
      X = fromBlocks P Q R T := ⟨_, _, _, _, (fromBlocks_toBlocks X).symm⟩
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hX
  obtain ⟨h1, h2, h3, h4⟩ := fromBlocks_inj.mp hX
  have hmem : ∀ B : Matrix (Fin 2) (Fin 2) (ZMod 2), B * rhoM = rhoM * B → B ∈ rhoCands := by
    intro B hB
    rcases comm_rho_cases B hB with rfl | rfl | rfl | rfl <;> simp [rhoCands]
  obtain ⟨rfl, rfl, rfl, rfl⟩ :=
    four_check P (hmem P h1) Q (hmem Q h2) R (hmem R h3) T (hmem T h4) h7
  exact fromBlocks_one

theorem bl_r1M : bl split1 r1M = fromBlocks 1 0 0 rhoM := by decide +kernel

theorem bl_r1_add_sq : bl split1 (r1M + r1M ^ 2) = fromBlocks 0 0 0 1 := by decide +kernel

theorem bl_r2M : bl split2 r2M = fromBlocks 1 0 0 (fromBlocks rhoM 0 0 rhoM) := by
  decide +kernel

theorem bl_r2_add_sq : bl split2 (r2M + r2M ^ 2) = fromBlocks 0 0 0 1 := by decide +kernel

theorem isBlockDiag_of_commute_r1 {X : Matrix (Fin 6) (Fin 6) (ZMod 2)} (h : X * r1M = r1M * X) :
    IsBlockDiag (bl split1 X) ∧
      (bl split1 X).toBlocks₂₂ * rhoM = rhoM * (bl split1 X).toBlocks₂₂ := by
  have hE : X * (r1M + r1M ^ 2) = (r1M + r1M ^ 2) * X := by
    rw [Matrix.mul_add, Matrix.add_mul, h, (Commute.pow_right (show Commute X r1M from h) 2).eq]
  have hbd : IsBlockDiag (bl split1 X) :=
    isBlockDiag_of_commute (by rw [← bl_r1_add_sq, ← bl_mul, ← bl_mul, hE])
  refine ⟨hbd, ?_⟩
  have h' := bl_commute split1 h
  rw [eq_fromBlocks_of_isBlockDiag hbd, bl_r1M, fromBlocks_diag_mul, fromBlocks_diag_mul] at h'
  exact (fromBlocks_inj.mp h').2.2.2

theorem no_seven_r2 {X : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hX : X * r2M = r2M * X)
    (h7 : X ^ 7 = 1) : X = 1 := by
  have hE : X * (r2M + r2M ^ 2) = (r2M + r2M ^ 2) * X := by
    rw [Matrix.mul_add, Matrix.add_mul, hX, (Commute.pow_right (show Commute X r2M from hX) 2).eq]
  have hbd : IsBlockDiag (bl split2 X) :=
    isBlockDiag_of_commute (by rw [← bl_r2_add_sq, ← bl_mul, ← bl_mul, hE])
  obtain ⟨X2, X4, hXeq⟩ : ∃ (X2 : Matrix (Fin 2) (Fin 2) (ZMod 2))
      (X4 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)),
      bl split2 X = fromBlocks X2 0 0 X4 :=
    ⟨_, _, eq_fromBlocks_of_isBlockDiag hbd⟩
  have hc : X4 * fromBlocks rhoM 0 0 rhoM = fromBlocks rhoM 0 0 rhoM * X4 := by
    have h := bl_commute split2 hX
    rw [hXeq, bl_r2M, fromBlocks_diag_mul, fromBlocks_diag_mul] at h
    exact (fromBlocks_inj.mp h).2.2.2
  have hpow : fromBlocks (X2 ^ 7) 0 0 (X4 ^ 7) = fromBlocks 1 0 0 1 := by
    rw [fromBlocks_one, ← fromBlocks_diag_pow, ← hXeq, ← bl_pow, h7, bl_one]
  have hX2 : X2 ^ 7 = 1 := (fromBlocks_inj.mp hpow).1
  have hX4 : X4 ^ 7 = 1 := (fromBlocks_inj.mp hpow).2.2.2
  have h2 : X2 = 1 := pow_seven_two X2 hX2
  have h4 : X4 = 1 := four_pow_seven hc hX4
  apply bl_injective split2
  rw [hXeq, h2, h4, bl_one, fromBlocks_one]

theorem not_seven_dvd_r2 (s : SL(6, ZMod 2)) (hs : (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) = r2M) :
    ¬ 7 ∣ Nat.card (Subgroup.centralizer ({s} : Set SL(6, ZMod 2))) := by
  intro hdvd
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.centralizer ({s} : Set SL(6, ZMod 2))) 7 hdvd
  have hcomm : (g : SL(6, ZMod 2)) * s = s * g := Subgroup.mem_centralizer_singleton_iff.mp g.2
  have hmat : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) * r2M =
      r2M * (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    have h' := congrArg (fun z : SL(6, ZMod 2) => (z : Matrix (Fin 6) (Fin 6) (ZMod 2))) hcomm
    simp only [Matrix.SpecialLinearGroup.coe_mul, hs] at h'
    exact h'
  have hg7 : g ^ 7 = 1 := by
    rw [← hg]
    exact pow_orderOf_eq_one g
  have hgpow : (g : SL(6, ZMod 2)) ^ 7 = 1 := by
    rw [← Subgroup.coe_pow, hg7, Subgroup.coe_one]
  have hmat7 : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 7 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hgpow, Matrix.SpecialLinearGroup.coe_one]
  have hone : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := no_seven_r2 hmat hmat7
  have hgone : (g : SL(6, ZMod 2)) = 1 :=
    Subtype.ext (by rw [hone, Matrix.SpecialLinearGroup.coe_one])
  have hg1 : g = 1 := Subtype.ext hgone
  rw [hg1, orderOf_one] at hg
  norm_num at hg

@[expose] def emb4 (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  (fromBlocks A 0 0 1).submatrix split1 split1

theorem bl_emb4 (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    bl split1 (emb4 A) = fromBlocks A 0 0 1 :=
  bl_submatrix split1 _

theorem emb4_mul (A B : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    emb4 (A * B) = emb4 A * emb4 B := by
  apply bl_injective split1
  rw [bl_mul, bl_emb4, bl_emb4, bl_emb4, fromBlocks_diag_mul, Matrix.mul_one]

theorem emb4_one : emb4 1 = 1 := by
  apply bl_injective split1
  rw [bl_emb4, bl_one, fromBlocks_one]

theorem det_emb4 (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) : (emb4 A).det = A.det := by
  rw [emb4, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one,
    mul_one]

@[expose] def iota4 : SL(4, ZMod 2) →* SL(6, ZMod 2) where
  toFun A := ⟨emb4 (A : Matrix (Fin 4) (Fin 4) (ZMod 2)), by
    rw [det_emb4]
    exact Matrix.SpecialLinearGroup.det_coe A⟩
  map_one' := Subtype.ext emb4_one
  map_mul' A B := Subtype.ext
    (emb4_mul (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (B : Matrix (Fin 4) (Fin 4) (ZMod 2)))

theorem coe_iota4 (C : SL(4, ZMod 2)) :
    ((iota4 C : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      emb4 (C : Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
  rfl

theorem iota4_injective : Function.Injective iota4 := by
  intro A B h
  apply Subtype.ext
  have h1 := congrArg (fun z : SL(6, ZMod 2) => bl split1 (z : Matrix (Fin 6) (Fin 6) (ZMod 2))) h
  simp only [coe_iota4, bl_emb4] at h1
  exact (fromBlocks_inj.mp h1).1

theorem mem_range_iota4 (z : SL(6, ZMod 2))
    (hz : IsBlockDiag (bl split1 (z : Matrix (Fin 6) (Fin 6) (ZMod 2))))
    (hz' : IsBlockDiag (bl split1 ((z⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))))
    (h1 : (bl split1 (z : Matrix (Fin 6) (Fin 6) (ZMod 2))).toBlocks₂₂ = 1) :
    z ∈ iota4.range := by
  set P := (bl split1 (z : Matrix (Fin 6) (Fin 6) (ZMod 2))).toBlocks₁₁ with hPdef
  set P' := (bl split1 ((z⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))).toBlocks₁₁
    with hP'def
  have hPP' : P * P' = 1 := by
    have h := congrArg (fun w : SL(6, ZMod 2) =>
      (bl split1 (w : Matrix (Fin 6) (Fin 6) (ZMod 2))).toBlocks₁₁) (mul_inv_cancel z)
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, bl_mul,
      IsBlockDiag.toBlocks₁₁_mul hz hz', bl_one, toBlocks₁₁_one] at h
    exact h
  have hzeq : bl split1 (z : Matrix (Fin 6) (Fin 6) (ZMod 2)) = fromBlocks P 0 0 1 := by
    rw [eq_fromBlocks_of_isBlockDiag hz, h1]
  refine ⟨mkSL P P' hPP', ?_⟩
  apply Subtype.ext
  show emb4 P = (z : Matrix (Fin 6) (Fin 6) (ZMod 2))
  apply bl_injective split1
  rw [bl_emb4, hzeq]

theorem comm_r1_of_mem (s : SL(6, ZMod 2)) (hs : (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) = r1M)
    {w : SL(6, ZMod 2)} (hw : w ∈ Subgroup.centralizer ({s} : Set SL(6, ZMod 2))) :
    (w : Matrix (Fin 6) (Fin 6) (ZMod 2)) * r1M = r1M * (w : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
  have h : w * s = s * w := Subgroup.mem_centralizer_singleton_iff.mp hw
  have h' := congrArg (fun z : SL(6, ZMod 2) => (z : Matrix (Fin 6) (Fin 6) (ZMod 2))) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, hs] at h'
  exact h'

theorem iota4_le_centralizer (s : SL(6, ZMod 2))
    (hs : (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) = r1M) :
    iota4.range ≤ Subgroup.centralizer ({s} : Set SL(6, ZMod 2)) := by
  rintro _ ⟨A, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hs, coe_iota4]
  apply bl_injective split1
  rw [bl_mul, bl_mul, bl_emb4, bl_r1M, fromBlocks_diag_mul, fromBlocks_diag_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]

theorem commutator_mem_iota4 (s : SL(6, ZMod 2)) (hs : (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) = r1M)
    (x : SL(6, ZMod 2)) (hx : x ∈ Subgroup.centralizer ({s} : Set SL(6, ZMod 2)))
    (y : SL(6, ZMod 2)) (hy : y ∈ Subgroup.centralizer ({s} : Set SL(6, ZMod 2))) :
    ⁅x, y⁆ ∈ iota4.range := by
  set C := Subgroup.centralizer ({s} : Set SL(6, ZMod 2)) with hCdef
  have hbd : ∀ w ∈ C, IsBlockDiag (bl split1 (w : Matrix (Fin 6) (Fin 6) (ZMod 2))) :=
    fun w hw => (isBlockDiag_of_commute_r1 (comm_r1_of_mem s hs hw)).1
  have hrho : ∀ w ∈ C, (bl split1 (w : Matrix (Fin 6) (Fin 6) (ZMod 2))).toBlocks₂₂ * rhoM =
      rhoM * (bl split1 (w : Matrix (Fin 6) (Fin 6) (ZMod 2))).toBlocks₂₂ :=
    fun w hw => (isBlockDiag_of_commute_r1 (comm_r1_of_mem s hs hw)).2
  have hxi : x⁻¹ ∈ C := C.inv_mem hx
  have hyi : y⁻¹ ∈ C := C.inv_mem hy
  have hc : ⁅x, y⁆ ∈ C := by
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem hx hy) hxi) hyi
  have hci : ⁅x, y⁆⁻¹ ∈ C := C.inv_mem hc
  refine mem_range_iota4 _ (hbd _ hc) (hbd _ hci) ?_
  have b22 : ∀ u ∈ C, ∀ w ∈ C,
      (bl split1 ((u * w : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))).toBlocks₂₂ =
        (bl split1 (u : Matrix (Fin 6) (Fin 6) (ZMod 2))).toBlocks₂₂ *
          (bl split1 (w : Matrix (Fin 6) (Fin 6) (ZMod 2))).toBlocks₂₂ := by
    intro u hu w hw
    rw [Matrix.SpecialLinearGroup.coe_mul, bl_mul, IsBlockDiag.toBlocks₂₂_mul (hbd u hu) (hbd w hw)]
  have hinv : ∀ u ∈ C, (bl split1 (u : Matrix (Fin 6) (Fin 6) (ZMod 2))).toBlocks₂₂ *
      (bl split1 ((u⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))).toBlocks₂₂ = 1 := by
    intro u hu
    rw [← b22 u hu _ (C.inv_mem hu), mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, bl_one,
      toBlocks₂₂_one]
  rw [commutatorElement_def, b22 _ (C.mul_mem (C.mul_mem hx hy) hxi) _ hyi,
    b22 _ (C.mul_mem hx hy) _ hxi, b22 _ hx _ hy]
  set X2 := (bl split1 (x : Matrix (Fin 6) (Fin 6) (ZMod 2))).toBlocks₂₂ with hX2
  set Y2 := (bl split1 (y : Matrix (Fin 6) (Fin 6) (ZMod 2))).toBlocks₂₂ with hY2
  set X2' := (bl split1 ((x⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))).toBlocks₂₂
    with hX2'
  set Y2' := (bl split1 ((y⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))).toBlocks₂₂
    with hY2'
  have hc1 : Y2 * X2' = X2' * Y2 := comm_of_commute_rho _ _ (hrho y hy) (hrho _ hxi)
  have hi1 : X2 * X2' = 1 := hinv x hx
  have hi2 : Y2 * Y2' = 1 := hinv y hy
  calc X2 * Y2 * X2' * Y2' = X2 * (Y2 * X2') * Y2' := by rw [Matrix.mul_assoc X2]
    _ = X2 * (X2' * Y2) * Y2' := by rw [hc1]
    _ = (X2 * X2') * (Y2 * Y2') := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hi1, hi2, Matrix.one_mul]

theorem comm_rep3M_of_mem (s : SL(6, ZMod 2)) (hs : (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) = rep3M)
    {w : SL(6, ZMod 2)} (hw : w ∈ Subgroup.centralizer ({s} : Set SL(6, ZMod 2))) :
    (w : Matrix (Fin 6) (Fin 6) (ZMod 2)) * rep3M =
      rep3M * (w : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
  have h : w * s = s * w := Subgroup.mem_centralizer_singleton_iff.mp hw
  have h' := congrArg (fun z : SL(6, ZMod 2) => (z : Matrix (Fin 6) (Fin 6) (ZMod 2))) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, hs] at h'
  exact h'

theorem ros_comm_rep3M (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 2)) :
    ros A * rep3M = rep3M * ros A := by
  rw [← ros_scalar_omega, ← map_mul, ← map_mul]
  congr 1
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
  exact mul_comm _ _

theorem rosSL_le_centralizer (s : SL(6, ZMod 2))
    (hs : (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) = rep3M) :
    rosSL.range ≤ Subgroup.centralizer ({s} : Set SL(6, ZMod 2)) := by
  rintro _ ⟨A, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hs, coe_rosSL]
  exact ros_comm_rep3M _

theorem commutator_mem_rosSL (s : SL(6, ZMod 2))
    (hs : (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) = rep3M)
    (x : SL(6, ZMod 2)) (hx : x ∈ Subgroup.centralizer ({s} : Set SL(6, ZMod 2)))
    (y : SL(6, ZMod 2)) (hy : y ∈ Subgroup.centralizer ({s} : Set SL(6, ZMod 2))) :
    ⁅x, y⁆ ∈ rosSL.range := by
  have hX1 : (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
      ((x⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hX2 : ((x⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
      (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hY1 : (y : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
      ((y⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hY2 : ((y⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
      (y : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨A, hA⟩ := exists_rosSL_of_commute hX1 hX2 hY1 hY2
    (comm_rep3M_of_mem s hs hx) (comm_rep3M_of_mem s hs hy)
  refine ⟨A, Subtype.ext ?_⟩
  rw [hA, commutatorElement_def]
  simp only [Matrix.SpecialLinearGroup.coe_mul]

theorem exists_not_comm_SL4 : ∃ a b : SL(4, ZMod 2), a * b ≠ b * a := by
  refine ⟨mkSL !![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
      !![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide),
    mkSL !![1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 1, 0; 0, 0, 0, 1]
      !![1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide), fun h => ?_⟩
  have h' := congrArg (fun z : SL(4, ZMod 2) => (z : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_mkSL] at h'
  exact absurd h' (by decide)

end L6

theorem L6.good429_r1 (s : SL(6, ZMod 2))
    (hs : (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) = L6.r1M) :
    Good429 (Subgroup.centralizer ({s} : Set SL(6, ZMod 2))) := by
  haveI : IsSimpleGroup SL(4, ZMod 2) := isSimpleGroup_SL_zmod_two (by norm_num)
  haveI : Group.IsPerfect SL(4, ZMod 2) := isPerfect_of_simple L6.exists_not_comm_SL4
  haveI : IsSimpleGroup L6.iota4.range :=
    (MonoidHom.ofInjective L6.iota4_injective).symm.isSimpleGroup
  haveI : Group.IsPerfect L6.iota4.range :=
    Group.IsPerfect.ofSurjective (f := L6.iota4.rangeRestrict) L6.iota4.rangeRestrict_surjective
  have hcard : Nat.card L6.iota4.range = 20160 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective L6.iota4_injective).toEquiv, card_SL4_zmod_two]
  have h6 : ∃ g : L6.iota4.range, orderOf g = 6 := by
    obtain ⟨g, hg, -⟩ := CFSG.RankThree.PartTwo.Sec8.Item8ModelProof.exists_orderOf_six (ZMod 2)
    exact ⟨MonoidHom.ofInjective L6.iota4_injective g, by rw [MulEquiv.orderOf_eq]; exact hg⟩
  have hgood : Good429 L6.iota4.range :=
    good429_self hcard (B := 28) (by norm_num) (by norm_num) (by decide +kernel)
      (not_isType429_quot_of_simple_20160 hcard h6)
  refine Good429.of_perfect_le (L6.iota4_le_centralizer s hs) ?_ hgood
  intro K hKC hKp
  exact le_of_commutator_mem (fun a ha b hb => L6.commutator_mem_iota4 s hs a ha b hb) hKC hKp

theorem L6.good429_r2 (s : SL(6, ZMod 2)) (hs : (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) = L6.r2M) :
    Good429 (Subgroup.centralizer ({s} : Set SL(6, ZMod 2))) := by
  have hCN : Nat.card (Subgroup.centralizer ({s} : Set SL(6, ZMod 2))) ∣ 20158709760 := by
    have h := Subgroup.card_subgroup_dvd_card (Subgroup.centralizer ({s} : Set SL(6, ZMod 2)))
    rwa [card_SL6_zmod_two] at h
  have h7 : ¬ 7 ∣ Nat.card (Subgroup.centralizer ({s} : Set SL(6, ZMod 2))) :=
    L6.not_seven_dvd_r2 s hs
  exact good429_of_not_dvd (B := 2800) hCN (by norm_num) (by norm_num) [7]
    (by simpa using h7) (by decide +kernel)

theorem L6.good429_r3 (s : SL(6, ZMod 2)) (hs : (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) = rep3M) :
    Good429 (Subgroup.centralizer ({s} : Set SL(6, ZMod 2))) := by
  haveI : Group.IsPerfect SL(3, GaloisField 2 2) := isPerfect_SL3_gf4
  haveI : Group.IsPerfect rosSL.range :=
    Group.IsPerfect.ofSurjective (f := rosSL.rangeRestrict) rosSL.rangeRestrict_surjective
  have hcard : Nat.card rosSL.range = 60480 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective rosSL_injective).toEquiv, card_SL3_gf4]
  have hcomm : ∀ a ∈ Subgroup.centralizer ({s} : Set SL(6, ZMod 2)),
      ∀ b ∈ Subgroup.centralizer ({s} : Set SL(6, ZMod 2)), ⁅a, b⁆ ∈ rosSL.range :=
    fun a ha b hb => commutator_mem_rosSL s hs a ha b hb
  have hgood : Good429 rosSL.range :=
    good429_self hcard (B := 40) (by norm_num) (by norm_num) (by decide +kernel)
      (not_isType429_quot_of_noEqOK hcard (B := 40) (by norm_num) (by norm_num) (by decide +kernel))
  exact Good429.of_perfect_le (rosSL_le_centralizer s hs)
    (fun K hKC hKp => le_of_commutator_mem hcomm hKC hKp) hgood

end CFSG.RankThree.PartTwo.Sec4.RonanK429F
