module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsGood
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHL4Blocks
public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofProj

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

section Blocks2

variable {K : Type} [Field K]

@[expose] def BlockDiag2 (M : Matrix (Fin 4) (Fin 4) K) : Prop :=
  M 0 2 = 0 ∧ M 0 3 = 0 ∧ M 1 2 = 0 ∧ M 1 3 = 0 ∧
    M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 3 0 = 0 ∧ M 3 1 = 0

@[expose] def l4Up2 (B : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![B 0 0, B 0 1, 0, 0; B 1 0, B 1 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def l4Low2 (B : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, B 0 0, B 0 1; 0, 0, B 1 0, B 1 1]

theorem l4Up2_one : l4Up2 (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l4Up2]

theorem l4Low2_one : l4Low2 (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l4Low2]

theorem l4Up2_mul (X Y : Matrix (Fin 2) (Fin 2) K) : l4Up2 (X * Y) = l4Up2 X * l4Up2 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [l4Up2, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four]

theorem l4Low2_mul (X Y : Matrix (Fin 2) (Fin 2) K) : l4Low2 (X * Y) = l4Low2 X * l4Low2 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [l4Low2, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four]

theorem det_l4Up2 (X : Matrix (Fin 2) (Fin 2) K) : (l4Up2 X).det = X.det := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, l4Up2, Fin.succAbove]

theorem det_l4Low2 (X : Matrix (Fin 2) (Fin 2) K) : (l4Low2 X).det = X.det := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, l4Low2, Fin.succAbove]

theorem l4Up2_submatrix (X : Matrix (Fin 2) (Fin 2) K) :
    (l4Up2 X).submatrix ![0, 1] ![0, 1] = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l4Up2]

theorem l4Low2_submatrix (X : Matrix (Fin 2) (Fin 2) K) :
    (l4Low2 X).submatrix ![2, 3] ![2, 3] = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l4Low2]

theorem l4Up2_injective : Function.Injective (l4Up2 : Matrix (Fin 2) (Fin 2) K → _) := by
  intro X Y h
  calc X = (l4Up2 X).submatrix ![0, 1] ![0, 1] := (l4Up2_submatrix X).symm
    _ = (l4Up2 Y).submatrix ![0, 1] ![0, 1] := by rw [h]
    _ = Y := l4Up2_submatrix Y

theorem l4Low2_injective : Function.Injective (l4Low2 : Matrix (Fin 2) (Fin 2) K → _) := by
  intro X Y h
  calc X = (l4Low2 X).submatrix ![2, 3] ![2, 3] := (l4Low2_submatrix X).symm
    _ = (l4Low2 Y).submatrix ![2, 3] ![2, 3] := by rw [h]
    _ = Y := l4Low2_submatrix Y

@[expose] noncomputable def blkUp : GL (Fin 2) K →* GL (Fin 4) K where
  toFun X :=
    { val := l4Up2 (X : Matrix (Fin 2) (Fin 2) K)
      inv := l4Up2 ((X⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      val_inv := by
        rw [← l4Up2_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, l4Up2_one]
      inv_val := by
        rw [← l4Up2_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, l4Up2_one] }
  map_one' := Units.ext (by simp [l4Up2_one])
  map_mul' X Y := Units.ext (by simp [l4Up2_mul])

@[expose] noncomputable def blkLow : GL (Fin 2) K →* GL (Fin 4) K where
  toFun X :=
    { val := l4Low2 (X : Matrix (Fin 2) (Fin 2) K)
      inv := l4Low2 ((X⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      val_inv := by
        rw [← l4Low2_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, l4Low2_one]
      inv_val := by
        rw [← l4Low2_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, l4Low2_one] }
  map_one' := Units.ext (by simp [l4Low2_one])
  map_mul' X Y := Units.ext (by simp [l4Low2_mul])

theorem coe_blkUp (X : GL (Fin 2) K) :
    ((blkUp X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      l4Up2 (X : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem coe_blkLow (X : GL (Fin 2) K) :
    ((blkLow X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      l4Low2 (X : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem blkUp_injective : Function.Injective (blkUp (K := K)) := by
  intro X Y h
  apply Units.ext
  apply l4Up2_injective
  exact congrArg Units.val h

theorem blkLow_injective : Function.Injective (blkLow (K := K)) := by
  intro X Y h
  apply Units.ext
  apply l4Low2_injective
  exact congrArg Units.val h

theorem l4Up2_mul_l4Low2_comm (X Y : Matrix (Fin 2) (Fin 2) K) :
    l4Up2 X * l4Low2 Y = l4Low2 Y * l4Up2 X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [l4Up2, l4Low2, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four]

theorem blkUp_blkLow_comm (X Y : GL (Fin 2) K) : blkUp X * blkLow Y = blkLow Y * blkUp X := by
  apply Units.ext
  simp only [Units.val_mul, coe_blkUp, coe_blkLow]
  exact l4Up2_mul_l4Low2_comm _ _

theorem l4E_blockdiag_eq (c : Matrix (Fin 4) (Fin 4) K) (h : BlockDiag2 c) :
    c = l4Up2 (c.submatrix ![0, 1] ![0, 1]) * l4Low2 (c.submatrix ![2, 3] ![2, 3]) := by
  obtain ⟨h02, h03, h12, h13, h20, h21, h30, h31⟩ := h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [l4Up2, l4Low2, Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13, h20, h21,
      h30, h31]

theorem l4E_units_blockdiag {c : GL (Fin 4) K} (h : BlockDiag2 (c : Matrix (Fin 4) (Fin 4) K))
    {X Y : GL (Fin 2) K}
    (hX : (X : Matrix (Fin 2) (Fin 2) K) = (c : Matrix (Fin 4) (Fin 4) K).submatrix ![0, 1] ![0, 1])
    (hY : (Y : Matrix (Fin 2) (Fin 2) K) =
      (c : Matrix (Fin 4) (Fin 4) K).submatrix ![2, 3] ![2, 3]) :
    c = blkUp X * blkLow Y := by
  apply Units.ext
  rw [Units.val_mul, coe_blkUp, coe_blkLow, hX, hY]
  exact l4E_blockdiag_eq _ h

theorem l4E_det_conj (X B : GL (Fin 2) K) :
    ((X * B * X⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det =
      (B : Matrix (Fin 2) (Fin 2) K).det := by
  have h : (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ) (X * B * X⁻¹) =
      (GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ) B := by
    rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
  have h' := congrArg Units.val h
  rwa [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply] at h'

theorem l4E_conj_blkUp (X Y B : GL (Fin 2) K) :
    blkUp X * blkLow Y * blkUp B * (blkUp X * blkLow Y)⁻¹ = blkUp (X * B * X⁻¹) := by
  have h : blkLow Y * blkUp B * (blkLow Y)⁻¹ = blkUp B := by
    rw [← blkUp_blkLow_comm B Y, mul_inv_cancel_right]
  calc blkUp X * blkLow Y * blkUp B * (blkUp X * blkLow Y)⁻¹
      = blkUp X * (blkLow Y * blkUp B * (blkLow Y)⁻¹) * (blkUp X)⁻¹ := by group
    _ = blkUp X * blkUp B * (blkUp X)⁻¹ := by rw [h]
    _ = blkUp (X * B * X⁻¹) := by rw [map_mul, map_mul, map_inv]

theorem l4E_conj_blkLow (X Y B : GL (Fin 2) K) :
    blkUp X * blkLow Y * blkLow B * (blkUp X * blkLow Y)⁻¹ = blkLow (Y * B * Y⁻¹) := by
  have h : blkUp X * blkLow (Y * B * Y⁻¹) * (blkUp X)⁻¹ = blkLow (Y * B * Y⁻¹) := by
    rw [blkUp_blkLow_comm X, mul_inv_cancel_right]
  calc blkUp X * blkLow Y * blkLow B * (blkUp X * blkLow Y)⁻¹
      = blkUp X * (blkLow Y * blkLow B * (blkLow Y)⁻¹) * (blkUp X)⁻¹ := by group
    _ = blkUp X * blkLow (Y * B * Y⁻¹) * (blkUp X)⁻¹ := by rw [map_mul, map_mul, map_inv]
    _ = blkLow (Y * B * Y⁻¹) := h

theorem l4E_comm_blkUp {c : GL (Fin 4) K} {X Y : GL (Fin 2) K} (hc : c = blkUp X * blkLow Y)
    {B : GL (Fin 2) K} (h : blkUp B * c = c * blkUp B) : B * X = X * B := by
  apply blkUp_injective
  have h1 : blkUp (B * X) * blkLow Y = blkUp (X * B) * blkLow Y := by
    calc blkUp (B * X) * blkLow Y = blkUp B * (blkUp X * blkLow Y) := by rw [map_mul]; group
      _ = blkUp B * c := by rw [hc]
      _ = c * blkUp B := h
      _ = blkUp X * blkLow Y * blkUp B := by rw [hc]
      _ = blkUp X * (blkLow Y * blkUp B) := by group
      _ = blkUp X * (blkUp B * blkLow Y) := by rw [← blkUp_blkLow_comm B Y]
      _ = blkUp X * blkUp B * blkLow Y := by group
      _ = blkUp (X * B) * blkLow Y := by rw [map_mul]
  exact mul_right_cancel h1

theorem l4E_comm_blkLow {c : GL (Fin 4) K} {X Y : GL (Fin 2) K} (hc : c = blkUp X * blkLow Y)
    {B : GL (Fin 2) K} (h : blkLow B * c = c * blkLow B) : B * Y = Y * B := by
  apply blkLow_injective
  have h1 : blkUp X * blkLow (B * Y) = blkUp X * blkLow (Y * B) := by
    calc blkUp X * blkLow (B * Y) = blkUp X * (blkLow B * blkLow Y) := by rw [map_mul]
      _ = (blkUp X * blkLow B) * blkLow Y := by group
      _ = (blkLow B * blkUp X) * blkLow Y := by rw [blkUp_blkLow_comm X B]
      _ = blkLow B * (blkUp X * blkLow Y) := by group
      _ = blkLow B * c := by rw [hc]
      _ = c * blkLow B := h
      _ = (blkUp X * blkLow Y) * blkLow B := by rw [hc]
      _ = blkUp X * (blkLow Y * blkLow B) := by group
      _ = blkUp X * blkLow (Y * B) := by rw [map_mul]
  exact mul_left_cancel h1

theorem l4E_blkUp_mem {D : GL (Fin 4) K} {d : Fin 4 → K}
    (hD : (D : Matrix (Fin 4) (Fin 4) K) = diagonal d) (h01 : d 0 = d 1) (B : GL (Fin 2) K) :
    blkUp B ∈ Subgroup.centralizer ({D} : Set (GL (Fin 4) K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hD, coe_blkUp]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l4Up2, mul_diagonal, diagonal_mul, h01, mul_comm]

theorem l4E_blkLow_mem {D : GL (Fin 4) K} {d : Fin 4 → K}
    (hD : (D : Matrix (Fin 4) (Fin 4) K) = diagonal d) (h23 : d 2 = d 3) (B : GL (Fin 2) K) :
    blkLow B ∈ Subgroup.centralizer ({D} : Set (GL (Fin 4) K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hD, coe_blkLow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [l4Low2, mul_diagonal, diagonal_mul, h23, mul_comm]

theorem l4E_blockDiag2_of_mem {D : GL (Fin 4) K} {d : Fin 4 → K}
    (hD : (D : Matrix (Fin 4) (Fin 4) K) = diagonal d) {M : GL (Fin 4) K}
    (hM : M ∈ Subgroup.centralizer ({D} : Set (GL (Fin 4) K)))
    (h02 : d 0 ≠ d 2) (h03 : d 0 ≠ d 3) (h12 : d 1 ≠ d 2) (h13 : d 1 ≠ d 3)
    (h20 : d 2 ≠ d 0) (h21 : d 2 ≠ d 1) (h30 : d 3 ≠ d 0) (h31 : d 3 ≠ d 1) :
    BlockDiag2 (M : Matrix (Fin 4) (Fin 4) K) := by
  unfold BlockDiag2
  exact ⟨l4_entry_eq_zero hD hM h02, l4_entry_eq_zero hD hM h03, l4_entry_eq_zero hD hM h12,
    l4_entry_eq_zero hD hM h13, l4_entry_eq_zero hD hM h20, l4_entry_eq_zero hD hM h21,
    l4_entry_eq_zero hD hM h30, l4_entry_eq_zero hD hM h31⟩

end Blocks2

theorem l4E_map_eq_one_of_comm {X Y : Type*} [Group X] [Group.IsPerfect X] [Group Y]
    (φ : X →* Y) (h : ∀ x y : X, φ x * φ y = φ y * φ x) (x : X) : φ x = 1 := by
  have hc : commutator X ≤ φ.ker := by
    show ⁅(⊤ : Subgroup X), ⊤⁆ ≤ φ.ker
    refine Subgroup.commutator_le.mpr ?_
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h a b
  rw [Group.IsPerfect.commutator_eq_top] at hc
  exact hc (Subgroup.mem_top x)

section TwoBlocks

variable {K : Type} [Field K]

theorem l4Eps_good_two_blocks [Finite K] {G : Subgroup (GL (Fin 4) K)}
    {Q₂ : Subgroup (GL (Fin 2) K)} (hQ₂ : IsQuasisimple Q₂)
    (hQ₂det : ∀ B ∈ Q₂, (B : Matrix (Fin 2) (Fin 2) K).det = 1)
    (hE₁ : ∀ B ∈ Q₂, blkUp B ∈ G) (hE₂ : ∀ B ∈ Q₂, blkLow B ∈ G)
    (hβ2 : ∀ M ∈ G, BlockDiag2 (M : Matrix (Fin 4) (Fin 4) K) →
      (∀ B : GL (Fin 2) K, (B : Matrix (Fin 2) (Fin 2) K) =
          (M : Matrix (Fin 4) (Fin 4) K).submatrix ![0, 1] ![0, 1] →
        (B : Matrix (Fin 2) (Fin 2) K).det = 1 → B ∈ Q₂) ∧
      (∀ B : GL (Fin 2) K, (B : Matrix (Fin 2) (Fin 2) K) =
          (M : Matrix (Fin 4) (Fin 4) K).submatrix ![2, 3] ![2, 3] →
        (B : Matrix (Fin 2) (Fin 2) K).det = 1 → B ∈ Q₂))
    (hfin : ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* Q₂) → EpsQuot X → False)
    {D : GL (Fin 4) K} {d : Fin 4 → K} (hD : (D : Matrix (Fin 4) (Fin 4) K) = diagonal d)
    (h01 : d 0 = d 1) (h20 : d 2 ≠ d 0) (h30 : d 3 ≠ d 0) :
    GoodEps (Subgroup.centralizer ({D} : Set (GL (Fin 4) K)) ⊓ G) := by
  intro L hLC hLp hLs hT
  haveI := hLp
  have e02 : d 0 ≠ d 2 := fun h => h20 h.symm
  have e03 : d 0 ≠ d 3 := fun h => h30 h.symm
  have e12 : d 1 ≠ d 2 := fun h => h20 (h.symm.trans h01.symm)
  have e13 : d 1 ≠ d 3 := fun h => h30 (h.symm.trans h01.symm)
  have e21 : d 2 ≠ d 1 := fun h => h20 (h.trans h01.symm)
  have e31 : d 3 ≠ d 1 := fun h => h30 (h.trans h01.symm)
  set H : Subgroup (GL (Fin 4) K) := Subgroup.centralizer ({D} : Set (GL (Fin 4) K)) with hH
  set C : Subgroup (GL (Fin 4) K) := H ⊓ G with hC
  have hz : ∀ M ∈ H, BlockDiag2 (M : Matrix (Fin 4) (Fin 4) K) := fun M hM =>
    l4E_blockDiag2_of_mem hD hM e02 e03 e12 e13 h20 e21 h30 e31
  have hLH : L ≤ H := hLC.trans inf_le_left
  have hLG : L ≤ G := hLC.trans inf_le_right
  have hf₁ : Function.Injective (![0, 1] : Fin 2 → Fin 4) := by decide
  have hf₂ : Function.Injective (![2, 3] : Fin 2 → Fin 4) := by decide
  have hr₁ : ∀ k : Fin 4, (∀ l : Fin 2, (![0, 1] : Fin 2 → Fin 4) l ≠ k) → k = 2 ∨ k = 3 := by
    decide
  have hr₂ : ∀ k : Fin 4, (∀ l : Fin 2, (![2, 3] : Fin 2 → Fin 4) l ≠ k) → k = 0 ∨ k = 1 := by
    decide
  have hv₁ : ∀ (i : Fin 2) (k : Fin 4), (∀ l : Fin 2, (![0, 1] : Fin 2 → Fin 4) l ≠ k) →
      d ((![0, 1] : Fin 2 → Fin 4) i) ≠ d k := by
    intro i k hk
    rcases hr₁ k hk with rfl | rfl <;> fin_cases i
    · exact e02
    · exact e12
    · exact e03
    · exact e13
  have hv₂ : ∀ (i : Fin 2) (k : Fin 4), (∀ l : Fin 2, (![2, 3] : Fin 2 → Fin 4) l ≠ k) →
      d ((![2, 3] : Fin 2 → Fin 4) i) ≠ d k := by
    intro i k hk
    rcases hr₂ k hk with rfl | rfl <;> fin_cases i
    · exact h20
    · exact h30
    · exact e21
    · exact e31
  set b₁ : H →* GL (Fin 2) K := l4BlockHom H ![0, 1] hf₁
    (fun M hM i k hk => l4_entry_eq_zero hD hM (hv₁ i k hk)) with hb₁
  set b₂ : H →* GL (Fin 2) K := l4BlockHom H ![2, 3] hf₂
    (fun M hM i k hk => l4_entry_eq_zero hD hM (hv₂ i k hk)) with hb₂
  have hdec : ∀ (c : GL (Fin 4) K) (hc : c ∈ H),
      c = blkUp (b₁ ⟨c, hc⟩) * blkLow (b₂ ⟨c, hc⟩) := fun c hc =>
    l4E_units_blockdiag (hz c hc) rfl rfl
  set Q₁ : Subgroup (GL (Fin 4) K) := Q₂.map blkUp with hQ₁
  have hQ₁C : Q₁ ≤ C := by
    intro x hx
    obtain ⟨B, hB, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨l4E_blkUp_mem hD h01 B, hE₁ B hB⟩
  have hconj1 : ∀ g ∈ C, ∀ q ∈ Q₁, g * q * g⁻¹ ∈ Q₁ := by
    intro g hg q hq
    obtain ⟨B, hB, rfl⟩ := Subgroup.mem_map.mp hq
    obtain ⟨hgH, hgG⟩ := hg
    have hgeq := hdec g hgH
    have hMH : g * blkUp B * g⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem hgH (l4E_blkUp_mem hD h01 B)) (H.inv_mem hgH)
    have hMG : g * blkUp B * g⁻¹ ∈ G :=
      G.mul_mem (G.mul_mem hgG (hE₁ B hB)) (G.inv_mem hgG)
    set X := b₁ ⟨g, hgH⟩ with hX
    set Y := b₂ ⟨g, hgH⟩ with hY
    have hM : g * blkUp B * g⁻¹ = blkUp (X * B * X⁻¹) := by
      rw [hgeq]
      exact l4E_conj_blkUp X Y B
    have hdetM : ((X * B * X⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      rw [l4E_det_conj]
      exact hQ₂det B hB
    have hsub : ((X * B * X⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        ((g * blkUp B * g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).submatrix
          ![0, 1] ![0, 1] := by
      rw [hM, coe_blkUp, l4Up2_submatrix]
    rw [hM]
    exact Subgroup.mem_map_of_mem blkUp ((hβ2 _ hMG (hz _ hMH)).1 _ hsub hdetM)
  have hQ₁n : (Q₁.subgroupOf C).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hconj1 (g : GL (Fin 4) K) g.2 _ hn
    simpa using this⟩
  have eQ : (Q₁.subgroupOf C) ≃* Q₂ :=
    (Subgroup.subgroupOfEquivOfLe hQ₁C).trans
      (Subgroup.equivMapOfInjective Q₂ blkUp blkUp_injective).symm
  have hQ₁q : IsQuasisimple (Q₁.subgroupOf C) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eQ.symm hQ₂
  have eL : (L.subgroupOf C) ≃* L := Subgroup.subgroupOfEquivOfLe hLC
  haveI hL'p : Group.IsPerfect (L.subgroupOf C) :=
    Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  have hL'T : EpsQuot (L.subgroupOf C) := EpsQuot.congr eL.symm hT
  have hL'S : IsSimpleGroup (L.subgroupOf C ⧸ CFSG.pCore 2 (L.subgroupOf C)) :=
    isSimpleGroup_of_isTypeEps' hL'T.1
  have hU : ∀ l ∈ L, ((l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).submatrix ![0, 1] ![0, 1] =
      1 := by
    rcases eq_or_commutator_eq_bot_of_normal_quasisimple hLs hL'S hQ₁n hQ₁q with hEq | hcomm
    · exact (hfin L ⟨eL.symm.trans ((MulEquiv.subgroupCongr hEq).trans eQ)⟩ hT).elim
    · have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      have hcomm' : ∀ B ∈ Q₂, ∀ l ∈ L, blkUp B * (l : GL (Fin 4) K) = l * blkUp B := by
        intro B hB l hl
        have hq : (⟨blkUp B, hQ₁C (Subgroup.mem_map_of_mem blkUp hB)⟩ : C) ∈ Q₁.subgroupOf C :=
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem blkUp hB)
        have hl' : (⟨l, hLC hl⟩ : C) ∈ L.subgroupOf C := Subgroup.mem_subgroupOf.mpr hl
        have h := Subgroup.mem_centralizer_iff.mp (hcent hq) _ hl'
        exact (congrArg Subtype.val h).symm
      have hxc : ∀ l : L, ∀ B ∈ Q₂, B * b₁ ⟨l.1, hLH l.2⟩ = b₁ ⟨l.1, hLH l.2⟩ * B :=
        fun l B hB => l4E_comm_blkUp (hdec l.1 (hLH l.2)) (hcomm' B hB l.1 l.2)
      have hφmem : ∀ l : L, b₁ ⟨l.1, hLH l.2⟩ ∈ Q₂ := fun l =>
        (hβ2 _ (hLG l.2) (hz _ (hLH l.2))).1 _ rfl
          (l4_det_eq_one_of_isPerfect (b₁.comp (Subgroup.inclusion hLH)) l)
      have hone : ∀ l : L, b₁ ⟨l.1, hLH l.2⟩ = 1 := by
        intro l
        refine l4E_map_eq_one_of_comm (b₁.comp (Subgroup.inclusion hLH)) ?_ l
        intro x y
        exact (hxc x _ (hφmem y)).symm
      intro l hl
      have h := congrArg Units.val (hone ⟨l, hl⟩)
      rw [Units.val_one] at h
      exact h
  have hD2 : ∀ l ∈ L, ((l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).submatrix ![2, 3] ![2, 3] =
      1 := by
    by_cases h23 : d 2 = d 3
    · set Q₃ : Subgroup (GL (Fin 4) K) := Q₂.map blkLow with hQ₃
      have hQ₃C : Q₃ ≤ C := by
        intro x hx
        obtain ⟨B, hB, rfl⟩ := Subgroup.mem_map.mp hx
        exact ⟨l4E_blkLow_mem hD h23 B, hE₂ B hB⟩
      have hconj3 : ∀ g ∈ C, ∀ q ∈ Q₃, g * q * g⁻¹ ∈ Q₃ := by
        intro g hg q hq
        obtain ⟨B, hB, rfl⟩ := Subgroup.mem_map.mp hq
        obtain ⟨hgH, hgG⟩ := hg
        have hgeq := hdec g hgH
        have hMH : g * blkLow B * g⁻¹ ∈ H :=
          H.mul_mem (H.mul_mem hgH (l4E_blkLow_mem hD h23 B)) (H.inv_mem hgH)
        have hMG : g * blkLow B * g⁻¹ ∈ G :=
          G.mul_mem (G.mul_mem hgG (hE₂ B hB)) (G.inv_mem hgG)
        set X := b₁ ⟨g, hgH⟩ with hX
        set Y := b₂ ⟨g, hgH⟩ with hY
        have hM : g * blkLow B * g⁻¹ = blkLow (Y * B * Y⁻¹) := by
          rw [hgeq]
          exact l4E_conj_blkLow X Y B
        have hdetM : ((Y * B * Y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
          rw [l4E_det_conj]
          exact hQ₂det B hB
        have hsub : ((Y * B * Y⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
            ((g * blkLow B * g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).submatrix
              ![2, 3] ![2, 3] := by
          rw [hM, coe_blkLow, l4Low2_submatrix]
        rw [hM]
        exact Subgroup.mem_map_of_mem blkLow ((hβ2 _ hMG (hz _ hMH)).2 _ hsub hdetM)
      have hQ₃n : (Q₃.subgroupOf C).Normal := ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        have := hconj3 (g : GL (Fin 4) K) g.2 _ hn
        simpa using this⟩
      have eQ₃ : (Q₃.subgroupOf C) ≃* Q₂ :=
        (Subgroup.subgroupOfEquivOfLe hQ₃C).trans
          (Subgroup.equivMapOfInjective Q₂ blkLow blkLow_injective).symm
      have hQ₃q : IsQuasisimple (Q₃.subgroupOf C) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eQ₃.symm hQ₂
      intro l hl
      rcases eq_or_commutator_eq_bot_of_normal_quasisimple hLs hL'S hQ₃n hQ₃q with hEq3 | hcomm3
      · exact (hfin L ⟨eL.symm.trans ((MulEquiv.subgroupCongr hEq3).trans eQ₃)⟩ hT).elim
      · have hcent3 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm3
        have hcomm3' : ∀ B ∈ Q₂, ∀ l ∈ L, blkLow B * (l : GL (Fin 4) K) = l * blkLow B := by
          intro B hB l hl
          have hq : (⟨blkLow B, hQ₃C (Subgroup.mem_map_of_mem blkLow hB)⟩ : C) ∈
              Q₃.subgroupOf C :=
            Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem blkLow hB)
          have hl' : (⟨l, hLC hl⟩ : C) ∈ L.subgroupOf C := Subgroup.mem_subgroupOf.mpr hl
          have h := Subgroup.mem_centralizer_iff.mp (hcent3 hq) _ hl'
          exact (congrArg Subtype.val h).symm
        have hyc : ∀ l : L, ∀ B ∈ Q₂, B * b₂ ⟨l.1, hLH l.2⟩ = b₂ ⟨l.1, hLH l.2⟩ * B :=
          fun l B hB => l4E_comm_blkLow (hdec l.1 (hLH l.2)) (hcomm3' B hB l.1 l.2)
        have hymem : ∀ l : L, b₂ ⟨l.1, hLH l.2⟩ ∈ Q₂ := fun l =>
          (hβ2 _ (hLG l.2) (hz _ (hLH l.2))).2 _ rfl
            (l4_det_eq_one_of_isPerfect (b₂.comp (Subgroup.inclusion hLH)) l)
        have hytriv : ∀ l : L, b₂ ⟨l.1, hLH l.2⟩ = 1 := by
          intro l
          refine l4E_map_eq_one_of_comm (b₂.comp (Subgroup.inclusion hLH)) ?_ l
          intro x y
          exact (hyc x _ (hymem y)).symm
        have h := congrArg Units.val (hytriv ⟨l, hl⟩)
        rw [Units.val_one] at h
        exact h
    ·
      have e32 : d 3 ≠ d 2 := fun h => h23 h.symm
      have hk2 : ∀ k : Fin 4, (∀ l : Fin 1, (![2] : Fin 1 → Fin 4) l ≠ k) → d 2 ≠ d k := by
        intro k hk
        fin_cases k
        · exact h20
        · exact e21
        · exact absurd rfl (hk 0)
        · exact h23
      have hk3 : ∀ k : Fin 4, (∀ l : Fin 1, (![3] : Fin 1 → Fin 4) l ≠ k) → d 3 ≠ d k := by
        intro k hk
        fin_cases k
        · exact h30
        · exact e31
        · exact e32
        · exact absurd rfl (hk 0)
      have hv3 : ∀ (i : Fin 1) (k : Fin 4), (∀ l : Fin 1, (![2] : Fin 1 → Fin 4) l ≠ k) →
          d ((![2] : Fin 1 → Fin 4) i) ≠ d k := by
        intro i k hk
        fin_cases i
        exact hk2 k hk
      have hv4 : ∀ (i : Fin 1) (k : Fin 4), (∀ l : Fin 1, (![3] : Fin 1 → Fin 4) l ≠ k) →
          d ((![3] : Fin 1 → Fin 4) i) ≠ d k := by
        intro i k hk
        fin_cases i
        exact hk3 k hk
      have hi2 : Function.Injective (![2] : Fin 1 → Fin 4) := by decide
      have hi3 : Function.Injective (![3] : Fin 1 → Fin 4) := by decide
      set b₃ : H →* GL (Fin 1) K := l4BlockHom H ![2] hi2
        (fun M hM i k hk => l4_entry_eq_zero hD hM (hv3 i k hk)) with hb₃
      set b₄ : H →* GL (Fin 1) K := l4BlockHom H ![3] hi3
        (fun M hM i k hk => l4_entry_eq_zero hD hM (hv4 i k hk)) with hb₄
      intro l hl
      have h22 : ((l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 2 = 1 := by
        have h := l4_det_eq_one_of_isPerfect (b₃.comp (Subgroup.inclusion hLH)) ⟨l, hl⟩
        rw [Matrix.det_fin_one] at h
        exact h
      have h33 : ((l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 3 = 1 := by
        have h := l4_det_eq_one_of_isPerfect (b₄.comp (Subgroup.inclusion hLH)) ⟨l, hl⟩
        rw [Matrix.det_fin_one] at h
        exact h
      have h23' : ((l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 3 = 0 :=
        l4_entry_eq_zero hD (hLH hl) h23
      have h32' : ((l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 2 = 0 :=
        l4_entry_eq_zero hD (hLH hl) e32
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, h22, h33, h23', h32']
  have hLtriv : ∀ l ∈ L, (l : GL (Fin 4) K) = 1 := by
    intro l hl
    apply Units.ext
    rw [Units.val_one, l4E_blockdiag_eq _ (hz l (hLH hl)), hU l hl, hD2 l hl, l4Up2_one,
      l4Low2_one, mul_one]
  haveI : Nontrivial L := hT.nontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : L)
  exact hx (Subtype.ext (hLtriv x.1 x.2))

end TwoBlocks

section ThreeOne

variable {K : Type} [Field K]

theorem l4Eps_good_three_one [Finite K] {G : Subgroup (GL (Fin 4) K)}
    {Q : Subgroup (GL (Fin 3) K)} (hQ : IsQuasisimple Q) (hE : ∀ B ∈ Q, l4BlkGL3 B ∈ G)
    (hβ : ∀ M ∈ G, ∀ B : GL (Fin 3) K,
      (B : Matrix (Fin 3) (Fin 3) K) =
        (M : Matrix (Fin 4) (Fin 4) K).submatrix Fin.castSucc Fin.castSucc →
      (∀ i : Fin 3, (M : Matrix (Fin 4) (Fin 4) K) (Fin.castSucc i) 3 = 0 ∧
        (M : Matrix (Fin 4) (Fin 4) K) 3 (Fin.castSucc i) = 0) →
      (B : Matrix (Fin 3) (Fin 3) K).det = 1 → B ∈ Q)
    {D : GL (Fin 4) K} (hDG : D ∈ G) {d : Fin 4 → K}
    (hD : (D : Matrix (Fin 4) (Fin 4) K) = diagonal d) (h01 : d 0 = d 1) (h12 : d 1 = d 2)
    (h23 : d 2 ≠ d 3) (hdet : (D : Matrix (Fin 4) (Fin 4) K).det = 1) (hD3 : D ^ 3 = 1) :
    GoodEps (Subgroup.centralizer ({D} : Set (GL (Fin 4) K)) ⊓ G) := by
  intro L hLC hLp hLs hT
  haveI := hLp
  set H := Subgroup.centralizer ({D} : Set (GL (Fin 4) K)) with hH
  set C := H ⊓ G with hC
  have hd : ∀ i : Fin 3, d (Fin.castSucc i) = d 0 := by
    intro i
    fin_cases i
    · rfl
    · exact h01.symm
    · exact (h01.trans h12).symm
  have hd3 : d 3 ≠ d 0 := fun h => h23 ((h01.trans h12).symm.trans h.symm)
  have hcs : ∀ k : Fin 4, (∀ l : Fin 3, (Fin.castSucc l : Fin 4) ≠ k) → k = 3 := by decide
  have hv : ∀ i k, (∀ l, (Fin.castSucc l : Fin 4) ≠ k) → d (Fin.castSucc i) ≠ d k := by
    intro i k hk
    rw [hcs k hk, hd i]
    exact hd3.symm
  have hv3 : ∀ i k, (∀ l, (![3] : Fin 1 → Fin 4) l ≠ k) → d (![3] i) ≠ d k := by
    intro i k hk
    fin_cases i
    fin_cases k
    · exact hd3
    · show d 3 ≠ d 1
      rw [← h01]; exact hd3
    · show d 3 ≠ d 2
      rw [← h12, ← h01]; exact hd3
    · exact absurd rfl (hk 0)
  have hinj3 : Function.Injective (![3] : Fin 1 → Fin 4) := by decide
  set b : H →* GL (Fin 3) K := l4BlockHom H Fin.castSucc (Fin.castSucc_injective 3)
    (fun M hM i k hk => l4_entry_eq_zero hD hM (hv i k hk)) with hb
  set b3 : H →* GL (Fin 1) K := l4BlockHom H ![3] hinj3
    (fun M hM i k hk => l4_entry_eq_zero hD hM (hv3 i k hk)) with hb3
  set β : C →* GL (Fin 3) K := b.comp (Subgroup.inclusion inf_le_left) with hβdef
  have hβc : ∀ c : C, ((β c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((c : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).submatrix Fin.castSucc Fin.castSucc :=
    fun c => rfl
  have hz3 : ∀ M ∈ H, ∀ i : Fin 3, (M : Matrix (Fin 4) (Fin 4) K) (Fin.castSucc i) 3 = 0 ∧
      (M : Matrix (Fin 4) (Fin 4) K) 3 (Fin.castSucc i) = 0 := fun M hM i =>
    ⟨l4_entry_eq_zero hD hM (by rw [hd i]; exact hd3.symm),
      l4_entry_eq_zero hD hM (by rw [hd i]; exact hd3)⟩
  have hDH : D ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set Dc : C := ⟨D, hDH, hDG⟩ with hDc
  set z : GL (Fin 3) K := β Dc with hz
  have hzmat : (z : Matrix (Fin 3) (Fin 3) K) = diagonal (fun _ => d 0) := by
    rw [hz, hβc, show ((Dc : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = diagonal d from hD,
      submatrix_diagonal _ _ (Fin.castSucc_injective 3)]
    congr 1
    funext i
    exact hd i
  have hμ3 : d 0 ^ 3 = 1 := by
    have hm : (D : Matrix (Fin 4) (Fin 4) K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hD3, Units.val_one]
    rw [hD, diagonal_pow] at hm
    have := congrFun (congrFun hm 0) 0
    simpa [diagonal_apply_eq] using this
  have hlam : d 3 = 1 := by
    have e1 : d 1 = d 0 := h01.symm
    have e2 : d 2 = d 0 := (h01.trans h12).symm
    rw [hD, det_diagonal, Fin.prod_univ_four, e1, e2] at hdet
    have h' : d 0 ^ 3 * d 3 = 1 := by rw [← hdet]; ring
    rwa [hμ3, one_mul] at h'
  have hμ1 : d 0 ≠ 1 := fun h => hd3 (hlam.trans h.symm)
  have hzQ : z ∈ Q := by
    refine hβ D hDG z (hβc Dc) (hz3 D hDH) ?_
    rw [hzmat, det_diagonal, Fin.prod_univ_three, ← hμ3]
    ring
  have hzc : ∀ q ∈ Q, q * z = z * q := by
    intro q _
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hzmat]
    ext i j
    simp [mul_diagonal, diagonal_mul, mul_comm]
  have hzo : orderOf z = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply orderOf_eq_prime
    · have hD3' : Dc ^ 3 = 1 := Subtype.ext hD3
      rw [hz, ← map_pow, hD3', map_one]
    · intro h1
      have h00 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h1
      simp only [hzmat, diagonal_apply_eq, Units.val_one, one_apply_eq] at h00
      exact hμ1 h00
  have hLH : L ≤ H := hLC.trans inf_le_left
  have hβinj : Function.Injective (β.comp (Subgroup.inclusion hLC)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have e : ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).submatrix Fin.castSucc
        Fin.castSucc = 1 := congrArg Units.val hx
    have e3 : ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 3 = 1 := by
      have h1 := l4_det_eq_one_of_isPerfect (b3.comp (Subgroup.inclusion hLH)) x
      rw [Matrix.det_fin_one] at h1
      exact h1
    have hxH : (x : GL (Fin 4) K) ∈ H := hLH x.2
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using congrFun (congrFun e 0) 0
    · simpa using congrFun (congrFun e 0) 1
    · simpa using congrFun (congrFun e 0) 2
    · simpa using (hz3 _ hxH 0).1
    · simpa using congrFun (congrFun e 1) 0
    · simpa using congrFun (congrFun e 1) 1
    · simpa using congrFun (congrFun e 1) 2
    · simpa using (hz3 _ hxH 1).1
    · simpa using congrFun (congrFun e 2) 0
    · simpa using congrFun (congrFun e 2) 1
    · simpa using congrFun (congrFun e 2) 2
    · simpa using (hz3 _ hxH 2).1
    · simpa using (hz3 _ hxH 0).2
    · simpa using (hz3 _ hxH 1).2
    · simpa using (hz3 _ hxH 2).2
    · simpa using e3
  have hKQ : ∀ k : L, β (Subgroup.inclusion hLC k) ∈ Q := by
    intro k
    have hkC : (k : GL (Fin 4) K) ∈ C := hLC k.2
    exact hβ k hkC.2 _ rfl (hz3 k hkC.1)
      (l4_det_eq_one_of_isPerfect (β.comp (Subgroup.inclusion hLC)) k)
  have hQC : Q ≤ β.range := by
    intro B hB
    refine ⟨⟨l4BlkGL3 B, l4BlkGL3_mem_centralizer hD h01 h12 B, hE B hB⟩, ?_⟩
    apply Units.ext
    rw [hβc]
    exact l4Blk3_submatrix _
  exact false_of_quasisimple_block_on hLC hLs β hβinj hQC hKQ hQ hzQ hzc hzo hT

end ThreeOne

theorem l4Eps_pattern : ∀ a : Fin 4 → ZMod 3, (∃ i j, a i ≠ a j) →
    ∃ σ : Equiv.Perm (Fin 4),
      (a (σ 0) = a (σ 1) ∧ a (σ 2) ≠ a (σ 0) ∧ a (σ 3) ≠ a (σ 0)) ∨
      (a (σ 0) = a (σ 1) ∧ a (σ 1) = a (σ 2) ∧ a (σ 2) ≠ a (σ 3)) := by
  decide +kernel

section Diag

variable {K : Type} [Field K]

theorem l4Eps_good_of_mulEquiv {S : Type} [Group S] (φ : S ≃* S) {P : Subgroup S}
    (hP : ∀ g, g ∈ P ↔ φ g ∈ P) {x : S} (h : GoodEps (Subgroup.centralizer ({x} : Set S) ⊓ P)) :
    GoodEps (Subgroup.centralizer ({φ x} : Set S) ⊓ P) := by
  have hmap : (Subgroup.centralizer ({x} : Set S) ⊓ P).map φ.toMonoidHom =
      Subgroup.centralizer ({φ x} : Set S) ⊓ P := by
    ext w
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨z, ⟨hzc, hzP⟩, rfl⟩
      exact ⟨by rw [← map_mul, ← map_mul, hzc], (hP z).mp hzP⟩
    · rintro ⟨hwc, hwP⟩
      refine ⟨φ.symm w, ⟨φ.injective ?_, (hP _).mpr (by rwa [MulEquiv.apply_symm_apply])⟩,
        MulEquiv.apply_symm_apply φ w⟩
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hwc
  rw [← hmap]
  exact h.map_mulEquiv φ

theorem l4Eps_good_diag [Finite K] {ω : K} (hω : IsPrimitiveRoot ω 3)
    {G : Subgroup (GL (Fin 4) K)} {Q : Subgroup (GL (Fin 3) K)} (hQ : IsQuasisimple Q)
    (hGdet : ∀ g ∈ G, (g : Matrix (Fin 4) (Fin 4) K).det = 1)
    (hGσ : ∀ (σ : Equiv.Perm (Fin 4)) (g : GL (Fin 4) K),
      g ∈ G ↔ Sec21.Tables.reindexGL σ g ∈ G)
    (hE : ∀ B ∈ Q, l4BlkGL3 B ∈ G)
    (hβ : ∀ M ∈ G, ∀ B : GL (Fin 3) K,
      (B : Matrix (Fin 3) (Fin 3) K) =
        (M : Matrix (Fin 4) (Fin 4) K).submatrix Fin.castSucc Fin.castSucc →
      (∀ i : Fin 3, (M : Matrix (Fin 4) (Fin 4) K) (Fin.castSucc i) 3 = 0 ∧
        (M : Matrix (Fin 4) (Fin 4) K) 3 (Fin.castSucc i) = 0) →
      (B : Matrix (Fin 3) (Fin 3) K).det = 1 → B ∈ Q)
    {Q₂ : Subgroup (GL (Fin 2) K)} (hQ₂ : IsQuasisimple Q₂)
    (hQ₂det : ∀ B ∈ Q₂, (B : Matrix (Fin 2) (Fin 2) K).det = 1)
    (hE₁ : ∀ B ∈ Q₂, blkUp B ∈ G) (hE₂ : ∀ B ∈ Q₂, blkLow B ∈ G)
    (hβ2 : ∀ M ∈ G, BlockDiag2 (M : Matrix (Fin 4) (Fin 4) K) →
      (∀ B : GL (Fin 2) K, (B : Matrix (Fin 2) (Fin 2) K) =
          (M : Matrix (Fin 4) (Fin 4) K).submatrix ![0, 1] ![0, 1] →
        (B : Matrix (Fin 2) (Fin 2) K).det = 1 → B ∈ Q₂) ∧
      (∀ B : GL (Fin 2) K, (B : Matrix (Fin 2) (Fin 2) K) =
          (M : Matrix (Fin 4) (Fin 4) K).submatrix ![2, 3] ![2, 3] →
        (B : Matrix (Fin 2) (Fin 2) K).det = 1 → B ∈ Q₂))
    (hfin : ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* Q₂) → EpsQuot X → False)
    {D : GL (Fin 4) K} (hDG : D ∈ G) (hD3 : D ^ 3 = 1) {a : Fin 4 → ZMod 3}
    (hD : (D : Matrix (Fin 4) (Fin 4) K) = diagonal (fun i => ω ^ (a i).val))
    (ha : ∃ i j, a i ≠ a j) :
    GoodEps (Subgroup.centralizer ({D} : Set (GL (Fin 4) K)) ⊓ G) := by
  set d : Fin 4 → K := fun i => ω ^ (a i).val with hd
  have hne : ∀ i j, a i ≠ a j → d i ≠ d j := fun i j hij h =>
    hij (ZMod.val_injective 3 (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))
  have heq : ∀ i j, a i = a j → d i = d j := fun i j hij => by
    simp only [hd, hij]
  have hT : ∀ σ : Equiv.Perm (Fin 4),
      GoodEps (Subgroup.centralizer ({Sec21.Tables.reindexGL σ D} : Set (GL (Fin 4) K)) ⊓ G) →
      GoodEps (Subgroup.centralizer ({D} : Set (GL (Fin 4) K)) ⊓ G) := by
    intro σ h
    have h' := l4Eps_good_of_mulEquiv (Sec21.Tables.reindexGL σ).symm (P := G)
      (fun g => by rw [hGσ σ ((Sec21.Tables.reindexGL σ).symm g), MulEquiv.apply_symm_apply]) h
    rwa [MulEquiv.symm_apply_apply] at h'
  have hσD : ∀ σ : Equiv.Perm (Fin 4),
      ((Sec21.Tables.reindexGL σ D : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        diagonal (d ∘ σ) := by
    intro σ
    rw [Sec21.Tables.coe_reindexGL, hD, submatrix_diagonal_equiv]
  rcases l4Eps_pattern a ha with ⟨σ, h | h⟩
  · apply hT σ
    exact l4Eps_good_two_blocks hQ₂ hQ₂det hE₁ hE₂ hβ2 hfin (hσD σ) (heq _ _ h.1)
      (hne _ _ h.2.1) (hne _ _ h.2.2)
  · apply hT σ
    have hDσ : Sec21.Tables.reindexGL σ D ∈ G := (hGσ σ D).mp hDG
    exact l4Eps_good_three_one hQ hE hβ hDσ (hσD σ) (heq _ _ h.1) (heq _ _ h.2.1)
      (hne _ _ h.2.2) (hGdet _ hDσ) (by rw [← map_pow, hD3, map_one])

theorem l4Eps_good_of_conj [Finite K] (h3 : (3 : K) ≠ 0) {ω : K} (hω : IsPrimitiveRoot ω 3)
    {G : Subgroup (GL (Fin 4) K)} {Q : Subgroup (GL (Fin 3) K)} (hQ : IsQuasisimple Q)
    (hGdet : ∀ g ∈ G, (g : Matrix (Fin 4) (Fin 4) K).det = 1)
    (hGσ : ∀ (σ : Equiv.Perm (Fin 4)) (g : GL (Fin 4) K),
      g ∈ G ↔ Sec21.Tables.reindexGL σ g ∈ G)
    (hE : ∀ B ∈ Q, l4BlkGL3 B ∈ G)
    (hβ : ∀ M ∈ G, ∀ B : GL (Fin 3) K,
      (B : Matrix (Fin 3) (Fin 3) K) =
        (M : Matrix (Fin 4) (Fin 4) K).submatrix Fin.castSucc Fin.castSucc →
      (∀ i : Fin 3, (M : Matrix (Fin 4) (Fin 4) K) (Fin.castSucc i) 3 = 0 ∧
        (M : Matrix (Fin 4) (Fin 4) K) 3 (Fin.castSucc i) = 0) →
      (B : Matrix (Fin 3) (Fin 3) K).det = 1 → B ∈ Q)
    {Q₂ : Subgroup (GL (Fin 2) K)} (hQ₂ : IsQuasisimple Q₂)
    (hQ₂det : ∀ B ∈ Q₂, (B : Matrix (Fin 2) (Fin 2) K).det = 1)
    (hE₁ : ∀ B ∈ Q₂, blkUp B ∈ G) (hE₂ : ∀ B ∈ Q₂, blkLow B ∈ G)
    (hβ2 : ∀ M ∈ G, BlockDiag2 (M : Matrix (Fin 4) (Fin 4) K) →
      (∀ B : GL (Fin 2) K, (B : Matrix (Fin 2) (Fin 2) K) =
          (M : Matrix (Fin 4) (Fin 4) K).submatrix ![0, 1] ![0, 1] →
        (B : Matrix (Fin 2) (Fin 2) K).det = 1 → B ∈ Q₂) ∧
      (∀ B : GL (Fin 2) K, (B : Matrix (Fin 2) (Fin 2) K) =
          (M : Matrix (Fin 4) (Fin 4) K).submatrix ![2, 3] ![2, 3] →
        (B : Matrix (Fin 2) (Fin 2) K).det = 1 → B ∈ Q₂))
    (hfin : ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* Q₂) → EpsQuot X → False)
    (hZ3 : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin 4) u ∈ G → u ^ 3 = 1 → u = 1)
    {A : GL (Fin 4) K} (hAG : A ∈ G) (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) {g : GL (Fin 4) K}
    (hg : ∀ h, h ∈ G ↔ g * h * g⁻¹ ∈ G) {a : Fin 4 → ZMod 3}
    (hD : ((g * A * g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal (fun i => ω ^ (a i).val)) :
    GoodEps (Subgroup.centralizer ({A} : Set (GL (Fin 4) K)) ⊓ G) := by
  set D : GL (Fin 4) K := g * A * g⁻¹ with hDdef
  have hDG : D ∈ G := (hg A).mp hAG
  have hD3 : D ^ 3 = 1 := by rw [hDdef, conj_pow, hA3, mul_one, mul_inv_cancel]
  have ha : ∃ i j, a i ≠ a j := by
    by_contra hcon
    push Not at hcon
    set c : Kˣ := Units.mk0 (ω ^ (a 0).val) (pow_ne_zero _ (hω.ne_zero (by norm_num))) with hc
    have hDs : D = GeneralLinearGroup.scalar (Fin 4) c := by
      apply Units.ext
      rw [hD, GeneralLinearGroup.coe_scalar]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hc, hcon i 0]
      · simp [diagonal_apply_ne _ hij, hij]
    have hcen : ∀ x : GL (Fin 4) K, x * GeneralLinearGroup.scalar (Fin 4) c =
        GeneralLinearGroup.scalar (Fin 4) c * x := fun x =>
      Subgroup.mem_center_iff.mp (by
        rw [GeneralLinearGroup.center_eq_range_scalar]; exact ⟨c, rfl⟩) x
    have hAs : A = GeneralLinearGroup.scalar (Fin 4) c := by
      have e : A = g⁻¹ * D * g := by rw [hDdef]; group
      rw [e, hDs, mul_assoc, ← hcen g, ← mul_assoc, inv_mul_cancel, one_mul]
    have hc3 : c ^ 3 = 1 := by
      have e := hA3
      rw [hAs, ← map_pow] at e
      exact (Sec21.Item228Census3Proof.scalar_eq_one_iff (ι := Fin 4)).mp e
    exact hA1 (by rw [hAs, hZ3 c (hAs ▸ hAG) hc3, map_one])
  have h := l4Eps_good_diag hω hQ hGdet hGσ hE hβ hQ₂ hQ₂det hE₁ hE₂ hβ2 hfin hDG hD3 hD ha
  have h' := GoodEps.conj_of_normalizes (k := g⁻¹) (fun h => by
    rw [hg (g⁻¹ * h * g⁻¹⁻¹), show g * (g⁻¹ * h * g⁻¹⁻¹) * g⁻¹ = h by group]) h
  rwa [show g⁻¹ * D * g⁻¹⁻¹ = A by rw [hDdef]; group] at h'

end Diag

section Proj

variable {K : Type} [Field K]

open Sec21.Item228Census3Proof in
theorem l4Eps_good_proj [Finite K] (G : Subgroup (GL (Fin 4) K))
    (hZ4 : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin 4) u ∈ G → u ^ 4 = 1)
    (hgood : ∀ A : G, A ^ 3 = 1 → A ≠ 1 →
      GoodEps (Subgroup.centralizer ({(A : GL (Fin 4) K)} : Set (GL (Fin 4) K)) ⊓ G))
    (y : projImage G) (hy : orderOf y = 3) :
    GoodEps (Subgroup.centralizer ({y} : Set (projImage G))) := by
  have hZ3 : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin 4) u ∈ G → u ^ 3 = 1 → u = 1 :=
    fun u hu h3 => by
      calc u = u ^ 4 * (u ^ 3)⁻¹ := by group
        _ = 1 := by rw [hZ4 u hu, h3, inv_one, one_mul]
  obtain ⟨A, hAy, hA3, hA1⟩ := exists_lift_cube G hZ4 y hy
  rw [← hAy, centralizer_projRestrict G A hA3 hZ3]
  have hcen : ∀ g : G, g ∈ (projRestrict G).ker → ∃ u : Kˣ,
      GeneralLinearGroup.scalar (Fin 4) u = (g : GL (Fin 4) K) := fun g hg =>
    (projRestrict_eq_one_iff G).mp hg
  have hcomm : ∀ (u : Kˣ) (x : GL (Fin 4) K), x * GeneralLinearGroup.scalar (Fin 4) u =
      GeneralLinearGroup.scalar (Fin 4) u * x := fun u x =>
    Subgroup.mem_center_iff.mp (by
      rw [GeneralLinearGroup.center_eq_range_scalar]; exact ⟨u, rfl⟩) x
  have hZ : (projRestrict G).ker ≤ Subgroup.center G := by
    intro g hg
    obtain ⟨u, hu⟩ := hcen g hg
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ← hu]
    exact hcomm u h
  have h2 : IsPGroup 2 (projRestrict G).ker := by
    intro g
    obtain ⟨u, hu⟩ := hcen g g.2
    refine ⟨2, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hu4 : u ^ 4 = 1 := hZ4 u (hu ▸ (g : G).2)
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hu, ← map_pow, show 2 ^ 2 = 4 by norm_num, hu4, map_one]
  have hC : (projRestrict G).ker ≤ Subgroup.centralizer ({A} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp (hZ hg) A).symm
  refine GoodEps.map_of_central (projRestrict G) (projRestrict_surjective G) hZ h2 hC ?_
  apply GoodEps.of_map G.subtype G.subtype_injective
  rw [RonanK429H.map_centralizer_singleton G.subtype G.subtype_injective A, Subgroup.range_subtype]
  exact hgood A hA3 hA1

end Proj

end CFSG.RankThree.PartTwo.Sec4.RonanEps
