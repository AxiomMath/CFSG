module

public import CFSG.LocalAnalysis.StandardType.FF81.ConstructYSix

public section

namespace CFSG.StandardType.FF81.Blocks

open Matrix CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open scoped MatrixGroups

@[expose] def permSL {N : ℕ} (σ : Equiv.Perm (Fin N)) : SL(N, ZMod 2) :=
  ⟨σ.permMatrix (ZMod 2), by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> decide⟩

theorem coe_permSL_conj {N : ℕ} {σ : Equiv.Perm (Fin N)} (hσ : σ.symm = σ)
    (M : Matrix (Fin N) (Fin N) (ZMod 2)) :
    (permSL σ : Matrix (Fin N) (Fin N) (ZMod 2)) * M * (permSL σ : Matrix (Fin N) (Fin N) (ZMod 2)) =
      M.submatrix σ σ := by
  change σ.permMatrix (ZMod 2) * M * σ.permMatrix (ZMod 2) = _
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    Matrix.submatrix_submatrix, hσ]
  rfl

theorem permSL_mul_self {N : ℕ} {σ : Equiv.Perm (Fin N)} (hσ : σ.symm = σ) :
    permSL σ * permSL σ = 1 := by
  apply Subtype.ext
  have h := coe_permSL_conj hσ 1
  rw [Matrix.mul_one, Matrix.submatrix_one_equiv] at h
  rw [Matrix.SpecialLinearGroup.coe_mul, h, Matrix.SpecialLinearGroup.coe_one]

abbrev tr6 (i j : Fin 6) (h : i ≠ j := by decide) : SL(6, ZMod 2) :=
  Matrix.SpecialLinearGroup.transvection h (1 : ZMod 2)

@[expose] def rev6Perm : Equiv.Perm (Fin 6) := Equiv.swap 0 4 * Equiv.swap 1 3

theorem rev6Perm_symm : rev6Perm.symm = rev6Perm := by decide

abbrev rev6 : SL(6, ZMod 2) := permSL rev6Perm

abbrev sw02 : SL(6, ZMod 2) := permSL (Equiv.swap 0 2)
abbrev sw03 : SL(6, ZMod 2) := permSL (Equiv.swap 0 3)
@[expose] def sw0345Perm : Equiv.Perm (Fin 6) := Equiv.swap 0 3 * Equiv.swap 4 5

abbrev sw0345 : SL(6, ZMod 2) := permSL sw0345Perm

theorem sw03_eq : sw03 = tr6 0 3 * tr6 3 0 * tr6 0 3 := by decide

theorem sw0345_eq : sw0345 = sw03 * (tr6 4 5 * tr6 5 4 * tr6 4 5) := by decide

theorem sw02_mul_self : sw02 * sw02 = 1 := permSL_mul_self (Equiv.symm_swap 0 2)

theorem block0_tvU : blockSL2 (ZMod 2) 5 0 tvU = tr6 0 1 := by decide
theorem block0_tvD : blockSL2 (ZMod 2) 5 0 tvD = tr6 1 0 := by decide
theorem block1_tvU : blockSL2 (ZMod 2) 5 1 tvU = tr6 1 2 := by decide
theorem block1_tvD : blockSL2 (ZMod 2) 5 1 tvD = tr6 2 1 := by decide
theorem block3_tvU : blockSL2 (ZMod 2) 5 3 tvU = tr6 3 4 := by decide
theorem block3_tvD : blockSL2 (ZMod 2) 5 3 tvD = tr6 4 3 := by decide
theorem block4_tvU : blockSL2 (ZMod 2) 5 4 tvU = tr6 4 5 := by decide
theorem block4_tvD : blockSL2 (ZMod 2) 5 4 tvD = tr6 5 4 := by decide

theorem rev6_conj_block0 : ∀ A : SL(2, ZMod 2), ∃ B : SL(2, ZMod 2),
    rev6 * blockSL2 (ZMod 2) 5 0 A * rev6 = blockSL2 (ZMod 2) 5 3 B := by decide

theorem rev6_conj_block1 : ∀ A : SL(2, ZMod 2), ∃ B : SL(2, ZMod 2),
    rev6 * blockSL2 (ZMod 2) 5 1 A * rev6 = blockSL2 (ZMod 2) 5 2 B := by decide

theorem rev6_conj_block3 : ∀ A : SL(2, ZMod 2), ∃ B : SL(2, ZMod 2),
    rev6 * blockSL2 (ZMod 2) 5 3 A * rev6 = blockSL2 (ZMod 2) 5 0 B := by decide

theorem rev6_mul_self : rev6 * rev6 = 1 := permSL_mul_self rev6Perm_symm

theorem commute_rev6 (g : SL(6, ZMod 2)) (h0 : ∀ A, Commute g (blockSL2 (ZMod 2) 5 0 A))
    (h3 : ∀ A, Commute g (blockSL2 (ZMod 2) 5 3 A)) : Commute g rev6 := by
  set G := (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) with hG
  obtain ⟨hc0, hr1, -⟩ := entries_of_commute_single (single_comm_of_commute _ (block0_tvU ▸ h0 tvU))
  obtain ⟨hc1, hr0, -⟩ := entries_of_commute_single (single_comm_of_commute _ (block0_tvD ▸ h0 tvD))
  obtain ⟨hc3, hr4, -⟩ := entries_of_commute_single (single_comm_of_commute _ (block3_tvU ▸ h3 tvU))
  obtain ⟨hc4, hr3, -⟩ := entries_of_commute_single (single_comm_of_commute _ (block3_tvD ▸ h3 tvD))
  have d0 := diag_eq_one_of_row hr0
  have d1 := diag_eq_one_of_row hr1
  have d3 := diag_eq_one_of_row hr3
  have d4 := diag_eq_one_of_row hr4
  have hconj : (rev6 : Matrix (Fin 6) (Fin 6) (ZMod 2)) * G * (rev6 : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      G := by
    rw [coe_permSL_conj rev6Perm_symm]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hG, rev6Perm, Equiv.swap_apply_def, hc0, hc1, hc3, hc4, hr0, hr1, hr3, hr4, d0, d1, d3, d4]
  apply Subtype.ext
  change G * (rev6 : Matrix (Fin 6) (Fin 6) (ZMod 2)) = (rev6 : Matrix (Fin 6) (Fin 6) (ZMod 2)) * G
  have hrr : (rev6 : Matrix (Fin 6) (Fin 6) (ZMod 2)) * (rev6 : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 :=
    congrArg Subtype.val rev6_mul_self
  calc G * (rev6 : Matrix (Fin 6) (Fin 6) (ZMod 2))
      = (rev6 : Matrix (Fin 6) (Fin 6) (ZMod 2)) * G * (rev6 : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
          (rev6 : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by rw [hconj]
    _ = (rev6 : Matrix (Fin 6) (Fin 6) (ZMod 2)) * G := by rw [Matrix.mul_assoc, hrr, Matrix.mul_one]

theorem tr30_eq : tr6 3 0 = sw02 * blockSL2 (ZMod 2) 5 2 tvD * sw02 := by decide

theorem tr03_eq : tr6 0 3 = sw02 * blockSL2 (ZMod 2) 5 2 tvU * sw02 := by decide

theorem sw02_commute_block4 : ∀ B : SL(2, ZMod 2),
    sw02 * blockSL2 (ZMod 2) 5 4 B = blockSL2 (ZMod 2) 5 4 B * sw02 := by decide

theorem root03_commute_block1 : ∀ A B : SL(2, ZMod 2),
    sw02 * blockSL2 (ZMod 2) 5 2 A * sw02 * blockSL2 (ZMod 2) 5 1 B =
      blockSL2 (ZMod 2) 5 1 B * (sw02 * blockSL2 (ZMod 2) 5 2 A * sw02) := by decide

theorem tr34_tr30 : tr6 3 4 * tr6 3 0 = tr6 3 0 * tr6 3 4 := by decide
theorem tr34_tr54 : tr6 3 4 * tr6 5 4 = tr6 5 4 * tr6 3 4 := by decide
theorem tr34_sw03 :
    tr6 3 4 * (sw03 * tr6 3 4 * sw03) = sw03 * tr6 3 4 * sw03 * tr6 3 4 := by decide
theorem tr34_sw0345 :
    tr6 3 4 * (sw0345 * tr6 3 4 * sw0345) = sw0345 * tr6 3 4 * sw0345 * tr6 3 4 := by decide
theorem tr43_tr03 : tr6 4 3 * tr6 0 3 = tr6 0 3 * tr6 4 3 := by decide
theorem tr43_tr45 : tr6 4 3 * tr6 4 5 = tr6 4 5 * tr6 4 3 := by decide
theorem tr43_sw03 :
    tr6 4 3 * (sw03 * tr6 4 3 * sw03) = sw03 * tr6 4 3 * sw03 * tr6 4 3 := by decide
theorem tr43_sw0345 :
    tr6 4 3 * (sw0345 * tr6 4 3 * sw0345) = sw0345 * tr6 4 3 * sw0345 * tr6 4 3 := by decide

theorem tr34_commute_block0 : ∀ A : SL(2, ZMod 2),
    tr6 3 4 * blockSL2 (ZMod 2) 5 0 A = blockSL2 (ZMod 2) 5 0 A * tr6 3 4 := by decide
theorem tr43_commute_block0 : ∀ A : SL(2, ZMod 2),
    tr6 4 3 * blockSL2 (ZMod 2) 5 0 A = blockSL2 (ZMod 2) 5 0 A * tr6 4 3 := by decide
theorem tr50_commute_block2 : ∀ A : SL(2, ZMod 2),
    tr6 5 0 * blockSL2 (ZMod 2) 5 2 A = blockSL2 (ZMod 2) 5 2 A * tr6 5 0 := by decide
theorem tr05_commute_block2 : ∀ A : SL(2, ZMod 2),
    tr6 0 5 * blockSL2 (ZMod 2) 5 2 A = blockSL2 (ZMod 2) 5 2 A * tr6 0 5 := by decide
theorem tr34_tr05 : tr6 3 4 * tr6 0 5 = tr6 0 5 * tr6 3 4 := by decide
theorem tr50_tr43 : tr6 5 0 * tr6 4 3 = tr6 4 3 * tr6 5 0 := by decide
theorem tr34_tr43_ne : tr6 3 4 * tr6 4 3 ≠ tr6 4 3 * tr6 3 4 := by decide
theorem tr34_ne_one : tr6 3 4 ≠ 1 := by decide
theorem tr43_ne_one : tr6 4 3 ≠ 1 := by decide

def mk30 (a b c d : ZMod 2) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; a, 0, 0, 1, b, 0; 0, 0, 0, 0, 1, 0;
    c, 0, 0, 0, d, 1]

def mk03 (a b c d : ZMod 2) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, a, 0, b; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, c, 1, d;
    0, 0, 0, 0, 0, 1]

theorem mk30_cases : ∀ a b c d : ZMod 2,
    mk30 a b c d * (mk30 a b c d).submatrix (Equiv.swap (0 : Fin 6) 3) (Equiv.swap (0 : Fin 6) 3) =
      (mk30 a b c d).submatrix (Equiv.swap (0 : Fin 6) 3) (Equiv.swap (0 : Fin 6) 3) * mk30 a b c d →
    mk30 a b c d * (mk30 a b c d).submatrix sw0345Perm sw0345Perm =
      (mk30 a b c d).submatrix sw0345Perm sw0345Perm * mk30 a b c d →
    mk30 a b c d = 1 ∨ mk30 a b c d = (tr6 3 4 : Matrix (Fin 6) (Fin 6) (ZMod 2)) ∨
      mk30 a b c d = (tr6 5 0 : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
  decide

theorem mk03_cases : ∀ a b c d : ZMod 2,
    mk03 a b c d * (mk03 a b c d).submatrix (Equiv.swap (0 : Fin 6) 3) (Equiv.swap (0 : Fin 6) 3) =
      (mk03 a b c d).submatrix (Equiv.swap (0 : Fin 6) 3) (Equiv.swap (0 : Fin 6) 3) * mk03 a b c d →
    mk03 a b c d * (mk03 a b c d).submatrix sw0345Perm sw0345Perm =
      (mk03 a b c d).submatrix sw0345Perm sw0345Perm * mk03 a b c d →
    mk03 a b c d = 1 ∨ mk03 a b c d = (tr6 4 3 : Matrix (Fin 6) (Fin 6) (ZMod 2)) ∨
      mk03 a b c d = (tr6 0 5 : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
  decide

theorem sw0345Perm_symm : sw0345Perm.symm = sw0345Perm := by decide

theorem commute_permSL_conj {σ : Equiv.Perm (Fin 6)} (hσ : σ.symm = σ) {x : SL(6, ZMod 2)}
    (h : Commute x (permSL σ * x * permSL σ)) :
    (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) * (x : Matrix (Fin 6) (Fin 6) (ZMod 2)).submatrix σ σ =
      (x : Matrix (Fin 6) (Fin 6) (ZMod 2)).submatrix σ σ * x := by
  have h' := congrArg (fun y : SL(6, ZMod 2) => (y : Matrix (Fin 6) (Fin 6) (ZMod 2))) h.eq
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h'
  rwa [coe_permSL_conj hσ] at h'

theorem x1_cases (x : SL(6, ZMod 2)) (h12 : Commute x (tr6 1 2)) (h21 : Commute x (tr6 2 1))
    (h30 : Commute x (tr6 3 0)) (h54 : Commute x (tr6 5 4))
    (hp : Commute x (sw03 * x * sw03)) (hq : Commute x (sw0345 * x * sw0345)) :
    x = 1 ∨ x = tr6 3 4 ∨ x = tr6 5 0 := by
  set X := (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) with hX
  obtain ⟨hc1, hr2, -⟩ := entries_of_commute_single (single_comm_of_commute _ h12)
  obtain ⟨hc2, hr1, -⟩ := entries_of_commute_single (single_comm_of_commute _ h21)
  obtain ⟨hc3, hr0, h30d⟩ := entries_of_commute_single (single_comm_of_commute _ h30)
  obtain ⟨hc5, hr4, h54d⟩ := entries_of_commute_single (single_comm_of_commute _ h54)
  have d0 := diag_eq_one_of_row hr0
  have d1 := diag_eq_one_of_row hr1
  have d2 := diag_eq_one_of_row hr2
  have d4 := diag_eq_one_of_row hr4
  have hform : X = mk30 (X 3 0) (X 3 4) (X 5 0) (X 5 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hX, mk30, hc1, hc2, hc3, hc5, hr0, hr1, hr2, hr4, d0, d1, d2, d4, h30d, h54d]
  have hp' := commute_permSL_conj (Equiv.symm_swap 0 3) hp
  have hq' := commute_permSL_conj sw0345Perm_symm hq
  rw [← hX, hform] at hp' hq'
  rcases mk30_cases _ _ _ _ hp' hq' with h | h | h
  · exact Or.inl (Subtype.ext (hform.trans h))
  · exact Or.inr (Or.inl (Subtype.ext (hform.trans h)))
  · exact Or.inr (Or.inr (Subtype.ext (hform.trans h)))

theorem x2_cases (x : SL(6, ZMod 2)) (h12 : Commute x (tr6 1 2)) (h21 : Commute x (tr6 2 1))
    (h03 : Commute x (tr6 0 3)) (h45 : Commute x (tr6 4 5))
    (hp : Commute x (sw03 * x * sw03)) (hq : Commute x (sw0345 * x * sw0345)) :
    x = 1 ∨ x = tr6 4 3 ∨ x = tr6 0 5 := by
  set X := (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) with hX
  obtain ⟨hc1, hr2, -⟩ := entries_of_commute_single (single_comm_of_commute _ h12)
  obtain ⟨hc2, hr1, -⟩ := entries_of_commute_single (single_comm_of_commute _ h21)
  obtain ⟨hc0, hr3, h03d⟩ := entries_of_commute_single (single_comm_of_commute _ h03)
  obtain ⟨hc4, hr5, h45d⟩ := entries_of_commute_single (single_comm_of_commute _ h45)
  have d1 := diag_eq_one_of_row hr1
  have d2 := diag_eq_one_of_row hr2
  have d3 := diag_eq_one_of_row hr3
  have d5 := diag_eq_one_of_row hr5
  have hform : X = mk03 (X 0 3) (X 0 5) (X 4 3) (X 4 5) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hX, mk03, hc0, hc1, hc2, hc4, hr1, hr2, hr3, hr5, d1, d2, d3, d5, h03d, h45d]
  have hp' := commute_permSL_conj (Equiv.symm_swap 0 3) hp
  have hq' := commute_permSL_conj sw0345Perm_symm hq
  rw [← hX, hform] at hp' hq'
  rcases mk03_cases _ _ _ _ hp' hq' with h | h | h
  · exact Or.inl (Subtype.ext (hform.trans h))
  · exact Or.inr (Or.inl (Subtype.ext (hform.trans h)))
  · exact Or.inr (Or.inr (Subtype.ext (hform.trans h)))

end CFSG.StandardType.FF81.Blocks

namespace CFSG.StandardType.FF81

open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair blockSL2)
open Blocks
open scoped MatrixGroups

theorem commute_of_tvU_tvD {H : Type} [Group H] (f : SL(2, ZMod 2) →* H) {a : H}
    (hU : Commute (f tvU) a) (hD : Commute (f tvD) a) (A : SL(2, ZMod 2)) :
    Commute (f A) a := by
  rcases sl2_cases A with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [map_one]
    exact Commute.one_left a
  · exact hU
  · exact hD
  · rw [map_mul]
    exact hU.mul_left hD
  · rw [map_mul]
    exact hD.mul_left hU
  · rw [map_mul, map_mul]
    exact (hU.mul_left hD).mul_left hU

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G} {K : ℕ → Subgroup G} {t : G}

theorem FrameSystem.commute_five_or (hA : HypA G 5 b L) (hF : FrameSystem 5 b L K t)
    {ψL ψg : SL(5 + 1, ZMod 2) →* G} (hψLinj : Function.Injective ψL) (hψLrange : ψL.range = L)
    (hψLblk : ∀ i : Fin 5, (blockSL2 (ZMod 2) 5 i).range.map ψL = K ((i : ℕ) + 2))
    (hψginj : Function.Injective ψg) (hψgrange : ψg.range = ⨆ i : Fin 5, K (i : ℕ))
    (hψgblk : ∀ i : Fin 5, (blockSL2 (ZMod 2) 5 i).range.map ψg = K (i : ℕ)) :
    (∀ a ∈ K 1, ∀ c ∈ K 5, a * c = c * a) ∨
      ∀ a ∈ (K 4).map (MulAut.conj (ψg rev6)).toMonoidHom, ∀ c ∈ K 5, a * c = c * a := by
  obtain ⟨g, hgb, hgL, hgc⟩ := hF.tau
  set α : G := ψg rev6 with hαdef
  have hαmem : α ∈ L.map (MulAut.conj g).toMonoidHom := hgL ▸ hψgrange ▸ ⟨_, rfl⟩
  have hαα : α * α = 1 := by rw [hαdef, ← map_mul, rev6_mul_self, map_one]
  have hαinv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hαα
  have hconjg : ∀ x, α * ψg x * α⁻¹ = ψg (rev6 * x * rev6) := by
    intro x
    rw [hαinv, hαdef, map_mul, map_mul]
  have hmemg : ∀ (i : Fin 5) (A : SL(2, ZMod 2)), ψg (blockSL2 (ZMod 2) 5 i A) ∈ K (i : ℕ) := by
    intro i A
    rw [← hψgblk i]
    exact ⟨_, ⟨A, rfl⟩, rfl⟩
  have hmemL : ∀ (i : Fin 5) (A : SL(2, ZMod 2)),
      ψL (blockSL2 (ZMod 2) 5 i A) ∈ K ((i : ℕ) + 2) := by
    intro i A
    rw [← hψLblk i]
    exact ⟨_, ⟨A, rfl⟩, rfl⟩
  have hexg : ∀ (i : Fin 5), ∀ x ∈ K (i : ℕ), ∃ A, ψg (blockSL2 (ZMod 2) 5 i A) = x := by
    intro i x hx
    rw [← hψgblk i] at hx
    obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hx
    exact ⟨A, rfl⟩
  have hexL : ∀ (i : Fin 5), ∀ x ∈ K ((i : ℕ) + 2), ∃ A, ψL (blockSL2 (ZMod 2) 5 i A) = x := by
    intro i x hx
    rw [← hψLblk i] at hx
    obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hx
    exact ⟨A, rfl⟩
  have hLmem : ∀ x, ψL x ∈ L := fun x => hψLrange ▸ ⟨x, rfl⟩
  have hb0 : b ∈ K 0 := by
    rw [hF.K0]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hbα : α * b * α⁻¹ ∈ K 3 := by
    obtain ⟨A, hA'⟩ := hexg 0 b hb0
    obtain ⟨B, hB⟩ := rev6_conj_block0 A
    rw [← hA', hconjg, hB]
    exact hmemg 3 B
  set ψ3 : SL(5 + 1, ZMod 2) →* G := (MulAut.conj α).toMonoidHom.comp ψL with hψ3def
  have hψ3 : ∀ x, ψ3 x = α * ψL x * α⁻¹ := fun x => rfl
  have hψ3inj : Function.Injective ψ3 := (MulAut.conj α).injective.comp hψLinj
  have hψ3range : ψ3.range = L.map (MulAut.conj α).toMonoidHom := by
    rw [hψ3def, MonoidHom.range_comp, hψLrange]
  have hN3 : Subgroup.centralizer ({α * b * α⁻¹} : Set G) ≤
      Subgroup.normalizer ((ψ3.range : Subgroup G) : Set G) := by
    rw [hψ3range]
    exact hA.centralizer_conj_le_normalizer α
  have hαK6 : ∀ k ∈ K 6, α * k * α⁻¹ = k := by
    intro k hk
    rw [← hgc k hk α hαmem, mul_assoc, mul_inv_cancel, mul_one]
  have hK6 : K 6 ≤ ψ3.range := by
    intro k hk
    obtain ⟨y, rfl⟩ : k ∈ ψL.range := hψLrange ▸ hF.le_L (by norm_num) (by norm_num) hk
    exact ⟨y, by rw [hψ3, hαK6 _ hk]⟩
  obtain ⟨W, hW⟩ := hF.sysL.2.2.2 (4 : Fin 5) (3 : Fin 5) (Or.inr rfl)
  obtain ⟨β, hβmem, hβ⟩ := LinearBlockStandardPair.exists_conj_two hW
  replace hβmem : β ∈ K 6 ⊔ K 5 := hβmem
  replace hβ : (K 6).map (MulAut.conj β).toMonoidHom = K 5 := hβ
  have hK3c : ∀ j : Fin 5, ((j : ℕ) = 3 ∨ (j : ℕ) = 4) →
      ∀ x ∈ K ((j : ℕ) + 2), ∀ y ∈ K 3, x * y = y * x := by
    intro j hj x hx y hy
    exact hF.sysL.2.2.1 j (1 : Fin 5)
      (fun h => by rcases hj with hj | hj <;> simp_all [Fin.ext_iff])
      (by unfold adjA; simp only [Fin.val_one]; omega) x hx y hy
  have hβc : β ∈ Subgroup.centralizer ({α * b * α⁻¹} : Set G) := by
    have hle : K 6 ⊔ K 5 ≤ Subgroup.centralizer ({α * b * α⁻¹} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_) <;>
        rw [Subgroup.mem_centralizer_singleton_iff]
      · exact hK3c 4 (Or.inr rfl) x hx _ hbα
      · exact hK3c 3 (Or.inl rfl) x hx _ hbα
    exact hle hβmem
  have hK5 : K 5 ≤ ψ3.range := by
    rw [← hβ, ← map_conj_eq_of_mem_normalizer (hN3 hβc)]
    exact Subgroup.map_mono hK6
  have hag4 : ∀ A, ψ3 (blockSL2 (ZMod 2) 5 4 A) = ψL (blockSL2 (ZMod 2) 5 4 A) := fun A => by
    rw [hψ3, hαK6 _ (hmemL 4 A)]
  have hsN : ψL sw02 ∈ Subgroup.normalizer
      ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    apply hA.centralizer_conj_le_normalizer g
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨B, hB⟩ := hexL 4 _ hgb
    rw [← hB, ← map_mul, ← map_mul, sw02_commute_block4 B]
  have hag03 : ∀ A, ψ3 (sw02 * blockSL2 (ZMod 2) 5 2 A * sw02) =
      ψL (sw02 * blockSL2 (ZMod 2) 5 2 A * sw02) := by
    intro A
    have h4 : ψL (blockSL2 (ZMod 2) 5 2 A) ∈ L.map (MulAut.conj g).toMonoidHom := by
      rw [← hgL]
      exact Subgroup.mem_iSup_of_mem (4 : Fin 5) (hmemL 2 A)
    have hmLg : ψL (sw02 * blockSL2 (ZMod 2) 5 2 A * sw02) ∈
        L.map (MulAut.conj g).toMonoidHom := by
      have h := (Subgroup.mem_normalizer_iff.1 hsN _).1 h4
      have hinv : (ψL sw02)⁻¹ = ψL sw02 := by
        rw [← map_inv, inv_eq_of_mul_eq_one_right sw02_mul_self]
      rwa [hinv, ← map_mul, ← map_mul] at h
    obtain ⟨y, hy⟩ : ψL (sw02 * blockSL2 (ZMod 2) 5 2 A * sw02) ∈ ψg.range := by
      rw [hψgrange, hgL]
      exact hmLg
    have hy0 : ∀ B, Commute y (blockSL2 (ZMod 2) 5 0 B) := fun B => hψginj (by
      rw [map_mul, map_mul, hy]
      exact (hF.comm_L _ (hmemg 0 B) _ (hLmem _)).symm)
    have hy3 : ∀ B, Commute y (blockSL2 (ZMod 2) 5 3 B) := by
      intro B
      obtain ⟨C, hC⟩ := hexL 1 _ (hmemg 3 B)
      exact hψginj (by
        rw [map_mul, map_mul, hy, ← hC, ← map_mul, ← map_mul, root03_commute_block1 A C])
    have hyα : α * ψg y * α⁻¹ = ψg y := by
      rw [hconjg, mul_assoc, (commute_rev6 y hy0 hy3).eq, ← mul_assoc, rev6_mul_self, one_mul]
    rw [hψ3, ← hy, hyα]
  have hag30 : ψ3 (tr6 3 0) = ψL (tr6 3 0) := by rw [tr30_eq]; exact hag03 tvD
  have hag03' : ψ3 (tr6 0 3) = ψL (tr6 0 3) := by rw [tr03_eq]; exact hag03 tvU
  have hag45 : ψ3 (tr6 4 5) = ψL (tr6 4 5) := by rw [← block4_tvU]; exact hag4 tvU
  have hag54 : ψ3 (tr6 5 4) = ψL (tr6 5 4) := by rw [← block4_tvD]; exact hag4 tvD
  have hagsw : ψ3 sw03 = ψL sw03 := by
    rw [sw03_eq, map_mul, map_mul, map_mul, map_mul, hag30, hag03']
  have hagsw' : ψ3 sw0345 = ψL sw0345 := by
    rw [sw0345_eq, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, hagsw, hag45, hag54]
  have htr : ∀ x y m m', ψ3 x = ψL y → ψ3 m = ψL m' → y * m' = m' * y → Commute x m := by
    intro x y m m' hx hm h
    exact hψ3inj (by rw [map_mul, map_mul, hx, hm, ← map_mul, ← map_mul, h])
  have hconj : ∀ x y s, ψ3 x = ψL y → ψ3 s = ψL s → ψ3 (s * x * s) = ψL (s * y * s) := by
    intro x y s hx hs
    rw [map_mul, map_mul, hx, hs, ← map_mul, ← map_mul]
  have hblk1 : ∀ x y, ψ3 x = ψL y → ∀ B, Commute x (blockSL2 (ZMod 2) 5 1 B) := by
    intro x y hx B
    have hk : ψ3 (blockSL2 (ZMod 2) 5 1 B) ∈ K 0 := by
      rw [hψ3]
      obtain ⟨B', hB'⟩ := hexg 3 _ (hmemL 1 B)
      rw [← hB', hconjg]
      obtain ⟨C, hC⟩ := rev6_conj_block3 B'
      rw [hC]
      exact hmemg 0 C
    exact hψ3inj (by rw [map_mul, map_mul, hx]; exact (hF.comm_L _ hk _ (hLmem y)).symm)
  obtain ⟨x1, hx1⟩ := hK5 (show ψL (tr6 3 4) ∈ K 5 by rw [← block3_tvU]; exact hmemL 3 tvU)
  obtain ⟨x2, hx2⟩ := hK5 (show ψL (tr6 4 3) ∈ K 5 by rw [← block3_tvD]; exact hmemL 3 tvD)
  have hx1c := x1_cases x1 (block1_tvU ▸ hblk1 x1 _ hx1 tvU) (block1_tvD ▸ hblk1 x1 _ hx1 tvD)
    (htr _ _ _ _ hx1 hag30 tr34_tr30) (htr _ _ _ _ hx1 hag54 tr34_tr54)
    (htr _ _ _ _ hx1 (hconj _ _ _ hx1 hagsw) tr34_sw03)
    (htr _ _ _ _ hx1 (hconj _ _ _ hx1 hagsw') tr34_sw0345)
  have hx2c := x2_cases x2 (block1_tvU ▸ hblk1 x2 _ hx2 tvU) (block1_tvD ▸ hblk1 x2 _ hx2 tvD)
    (htr _ _ _ _ hx2 hag03' tr43_tr03) (htr _ _ _ _ hx2 hag45 tr43_tr45)
    (htr _ _ _ _ hx2 (hconj _ _ _ hx2 hagsw) tr43_sw03)
    (htr _ _ _ _ hx2 (hconj _ _ _ hx2 hagsw') tr43_sw0345)
  have hx12 : x1 * x2 ≠ x2 * x1 := fun h => tr34_tr43_ne (hψLinj (by
    rw [map_mul, map_mul, ← hx1, ← hx2, ← map_mul, ← map_mul, h]))
  have hK5c : ∀ a, Commute (ψL (tr6 3 4)) a → Commute (ψL (tr6 4 3)) a → ∀ c ∈ K 5, a * c = c * a := by
    intro a hU hD c hc
    obtain ⟨A, rfl⟩ := hexL 3 c hc
    have hU' : Commute ((ψL.comp (blockSL2 (ZMod 2) 5 3)) tvU) a := by
      rw [MonoidHom.comp_apply, block3_tvU]; exact hU
    have hD' : Commute ((ψL.comp (blockSL2 (ZMod 2) 5 3)) tvD) a := by
      rw [MonoidHom.comp_apply, block3_tvD]; exact hD
    exact (commute_of_tvU_tvD _ hU' hD' A).eq.symm
  rcases hx1c with h1 | h1 | h1
  · exact absurd (hψLinj (by rw [← hx1, h1, map_one, map_one])) tr34_ne_one
  · rcases hx2c with h2 | h2 | h2
    · exact absurd (hψLinj (by rw [← hx2, h2, map_one, map_one])) tr43_ne_one
    ·
      left
      intro a ha
      obtain ⟨B, rfl⟩ := hexg 1 a ha
      obtain ⟨C, hC⟩ := rev6_conj_block1 B
      obtain ⟨A', hA'⟩ := hexL 0 _ (hmemg 2 C)
      have ha' : ψ3 (blockSL2 (ZMod 2) 5 0 A') = ψg (blockSL2 (ZMod 2) 5 1 B) := by
        rw [hψ3, hA', ← hC, ← hconjg, hαinv, ← mul_assoc, ← mul_assoc, hαα, one_mul,
          mul_assoc, hαα, mul_one]
      rw [← ha']
      refine hK5c _ ?_ ?_
      · rw [← hx1, h1]
        exact Commute.map (tr34_commute_block0 A') ψ3
      · rw [← hx2, h2]
        exact Commute.map (tr43_commute_block0 A') ψ3
    · exact absurd (by rw [h1, h2]; exact tr34_tr05) hx12
  · rcases hx2c with h2 | h2 | h2
    · exact absurd (hψLinj (by rw [← hx2, h2, map_one, map_one])) tr43_ne_one
    · exact absurd (by rw [h1, h2]; exact tr50_tr43) hx12
    ·
      right
      intro a ha
      obtain ⟨k, hk, rfl⟩ := ha
      obtain ⟨A', rfl⟩ := hexL 2 k hk
      refine hK5c _ ?_ ?_
      · change ψL (tr6 3 4) * ψ3 (blockSL2 (ZMod 2) 5 2 A') = ψ3 (blockSL2 (ZMod 2) 5 2 A') * ψL (tr6 3 4)
        rw [← hx1, h1, ← map_mul, ← map_mul, tr50_commute_block2 A']
      · change ψL (tr6 4 3) * ψ3 (blockSL2 (ZMod 2) 5 2 A') = ψ3 (blockSL2 (ZMod 2) 5 2 A') * ψL (tr6 4 3)
        rw [← hx2, h2, ← map_mul, ← map_mul, tr05_commute_block2 A']

theorem FrameSystem.commute_one_five_or (hA : HypA G 5 b L) (hF : FrameSystem 5 b L K t) :
    (∀ a ∈ K 1, ∀ c ∈ K 5, a * c = c * a) ∨
      ∃ ψg : SL(5 + 1, ZMod 2) →* G, Function.Injective ψg ∧
        ψg.range = ⨆ i : Fin 5, K (i : ℕ) ∧
        (∀ i : Fin 5, (blockSL2 (ZMod 2) 5 i).range.map ψg = K (i : ℕ)) ∧
        ∀ a ∈ (K 4).map (MulAut.conj (ψg rev6)).toMonoidHom, ∀ c ∈ K 5, a * c = c * a := by
  obtain ⟨ψL, hψLinj, hψLrange, hψLblk⟩ := hF.sysL.exists_injective_marking (by norm_num)
  obtain ⟨ψg, hψginj, hψgrange, hψgblk⟩ := hF.sysL'.exists_injective_marking (by norm_num)
  rcases hF.commute_five_or hA hψLinj hψLrange hψLblk hψginj hψgrange hψgblk with h | h
  · exact Or.inl h
  · exact Or.inr ⟨ψg, hψginj, hψgrange, hψgblk, h⟩

end CFSG.StandardType.FF81
