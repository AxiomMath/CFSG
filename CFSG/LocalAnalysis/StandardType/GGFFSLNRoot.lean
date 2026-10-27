module

public import CFSG.LocalAnalysis.StandardType.GGFFModelNDefs
public import CFSG.LocalAnalysis.StandardType.GGFFSLNDefs
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFBlock
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFGF4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.GGFF

open scoped MatrixGroups
open Matrix
open CFSG.RankThree.PartTwo.Sec4.RonanK429F

private def e0 : Fin 6 ≃ (Fin 2 ⊕ Fin 2) ⊕ Fin 2 :=
  ((finSumFinEquiv : Fin 4 ⊕ Fin 2 ≃ Fin 6).symm).trans
    (Equiv.sumCongr (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm (Equiv.refl (Fin 2)))

private def rc : Fin 4 → Matrix (Fin 2) (Fin 2) (ZMod 2) := ![0, 1, rhoM, rhoM * rhoM]

private def K1b : Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) (ZMod 2) :=
  fromBlocks (fromBlocks rhoM 0 0 rhoM) 0 0 1

private def K2b : Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) (ZMod 2) :=
  fromBlocks 1 0 0 rhoM

private def Wb : Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) (ZMod 2) :=
  fromBlocks (fromBlocks rhoM 0 0 1) 0 0 1

private def Rb : Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) (ZMod 2) :=
  fromBlocks (fromBlocks 1 1 0 1) 0 0 1

private def Rb' : Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) (ZMod 2) :=
  fromBlocks (fromBlocks 1 0 1 1) 0 0 1

private def cand (A B C D E : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) (ZMod 2) :=
  fromBlocks (fromBlocks A B C D) 0 0 E

private theorem bl_e0_K1 : bl e0 (W6.t1M * W6.t2M) = K1b := by decide +kernel

private theorem bl_e0_K2 : bl e0 W6.t3M = K2b := by decide +kernel

private theorem bl_e0_W : bl e0 W6.t1M = Wb := by decide +kernel

private theorem bl_e0_R : bl e0 N6.r0M = Rb := by decide +kernel

private theorem bl_e0_R' : bl e0 N6.r0'M = Rb' := by decide +kernel

private theorem check6 (i j k l m : Fin 4) :
    cand (rc i) (rc j) (rc k) (rc l) (rc m) * cand (rc i) (rc j) (rc k) (rc l) (rc m) = 1 →
    cand (rc i) (rc j) (rc k) (rc l) (rc m) *
        (Wb * cand (rc i) (rc j) (rc k) (rc l) (rc m) * Wb ^ 2) =
      Wb ^ 2 * cand (rc i) (rc j) (rc k) (rc l) (rc m) * Wb →
    cand (rc i) (rc j) (rc k) (rc l) (rc m) = 1 ∨ ∃ a : Fin 3,
      cand (rc i) (rc j) (rc k) (rc l) (rc m) = Wb ^ (a : ℕ) * Rb * Wb ^ (2 * (a : ℕ)) ∨
      cand (rc i) (rc j) (rc k) (rc l) (rc m) = Wb ^ (a : ℕ) * Rb' * Wb ^ (2 * (a : ℕ)) := by
  decide +kernel +revert

private theorem cjp_eq_pow {G : Type} [Group G] {w u : G} (hw : w ^ 3 = 1) (a : Fin 3) :
    cjp w a u = w ^ (a : ℕ) * u * w ^ (2 * (a : ℕ)) := by
  have h : w ^ (a : ℕ) * w ^ (2 * (a : ℕ)) = 1 := by
    rw [← pow_add, show (a : ℕ) + 2 * (a : ℕ) = 3 * (a : ℕ) by ring, pow_mul, hw, one_pow]
  unfold cjp
  rw [mul_eq_one_iff_inv_eq.mp h]

private theorem rootRel_iff_of_pow_three {G : Type} [Group G] {w u : G} (hw : w ^ 3 = 1) :
    RootRel w u ↔ u * (w * u * w ^ 2) = w ^ 2 * u * w := by
  have h1 : w ^ 2 * w = 1 := by rw [← pow_succ]; simpa using hw
  have h2 : w * w ^ 2 = 1 := by rw [← pow_succ']; simpa using hw
  unfold RootRel
  rw [mul_eq_one_iff_inv_eq.mp h2, mul_eq_one_iff_inv_eq.mp h1]

private theorem rootRel_matrix_of {n : ℕ} {w u : SL(n, ZMod 2)} (hw : w ^ 3 = 1)
    (h : RootRel w u) :
    (u : Matrix (Fin n) (Fin n) (ZMod 2)) *
        ((w : Matrix (Fin n) (Fin n) (ZMod 2)) * (u : Matrix (Fin n) (Fin n) (ZMod 2)) *
          (w : Matrix (Fin n) (Fin n) (ZMod 2)) ^ 2) =
      (w : Matrix (Fin n) (Fin n) (ZMod 2)) ^ 2 * (u : Matrix (Fin n) (Fin n) (ZMod 2)) *
        (w : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  rw [rootRel_iff_of_pow_three hw] at h
  have h' := congrArg (fun z : SL(n, ZMod 2) => (z : Matrix (Fin n) (Fin n) (ZMod 2))) h
  simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow] using h'

private theorem exists_rc (A : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (h : A * rhoM = rhoM * A) : ∃ i : Fin 4, A = rc i := by
  decide +kernel +revert

private theorem candidate6_block
    (M : Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) (ZMod 2))
    (hM2 : M * M = 1) (hK1 : M * K1b = K1b * M) (hK2 : M * K2b = K2b * M)
    (hrel : M * (Wb * M * Wb ^ 2) = Wb ^ 2 * M * Wb) :
    M = 1 ∨ ∃ a : Fin 3, M = Wb ^ (a : ℕ) * Rb * Wb ^ (2 * (a : ℕ)) ∨
      M = Wb ^ (a : ℕ) * Rb' * Wb ^ (2 * (a : ℕ)) := by
  have hP : K2b + K2b ^ 2 = fromBlocks 0 0 0 1 := by decide +kernel
  have hE : M * fromBlocks 0 0 0 1 = fromBlocks 0 0 0 1 * M := by
    rw [← hP, Matrix.mul_add, Matrix.add_mul, hK2,
      (Commute.pow_right (show Commute M K2b from hK2) 2).eq]
  obtain ⟨M4, E, hMeq⟩ : ∃ (M4 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))
      (E : Matrix (Fin 2) (Fin 2) (ZMod 2)), M = fromBlocks M4 0 0 E :=
    ⟨_, _, eq_fromBlocks_of_isBlockDiag (isBlockDiag_of_commute hE)⟩
  have hK1' : M4 * fromBlocks rhoM 0 0 rhoM = fromBlocks rhoM 0 0 rhoM * M4 := by
    have h : fromBlocks M4 0 0 E * K1b = K1b * fromBlocks M4 0 0 E := by rw [← hMeq]; exact hK1
    simp only [K1b, fromBlocks_diag_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact (fromBlocks_inj.mp h).1
  have hEcomm : E * rhoM = rhoM * E := by
    have h : fromBlocks M4 0 0 E * K2b = K2b * fromBlocks M4 0 0 E := by rw [← hMeq]; exact hK2
    simp only [K2b, fromBlocks_diag_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact (fromBlocks_inj.mp h).2.2.2
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D : Matrix (Fin 2) (Fin 2) (ZMod 2),
      M4 = fromBlocks A B C D := ⟨_, _, _, _, (fromBlocks_toBlocks M4).symm⟩
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hK1'
  obtain ⟨h1, h2, h3, h4⟩ := fromBlocks_inj.mp hK1'
  obtain ⟨i, rfl⟩ := exists_rc A h1
  obtain ⟨j, rfl⟩ := exists_rc B h2
  obtain ⟨k, rfl⟩ := exists_rc C h3
  obtain ⟨l, rfl⟩ := exists_rc D h4
  obtain ⟨m, rfl⟩ := exists_rc E hEcomm
  have hMeq' : M = cand (rc i) (rc j) (rc k) (rc l) (rc m) := hMeq
  rw [hMeq'] at hM2 hrel ⊢
  exact check6 i j k l m hM2 hrel

private theorem root_char_matrix6 (e : Fin 6 ≃ (Fin 2 ⊕ Fin 2) ⊕ Fin 2)
    (K1 K2 W R R' X : Matrix (Fin 6) (Fin 6) (ZMod 2))
    (hK1 : bl e K1 = K1b) (hK2 : bl e K2 = K2b) (hW : bl e W = Wb)
    (hR : bl e R = Rb) (hR' : bl e R' = Rb')
    (hX2 : X * X = 1) (hXK1 : X * K1 = K1 * X) (hXK2 : X * K2 = K2 * X)
    (hrel : X * (W * X * W ^ 2) = W ^ 2 * X * W) :
    X = 1 ∨ ∃ a : Fin 3, X = W ^ (a : ℕ) * R * W ^ (2 * (a : ℕ)) ∨
      X = W ^ (a : ℕ) * R' * W ^ (2 * (a : ℕ)) := by
  have hM2 : bl e X * bl e X = 1 := by rw [← bl_mul, hX2, bl_one]
  have hMK1 : bl e X * K1b = K1b * bl e X := by rw [← hK1, ← bl_mul, ← bl_mul, hXK1]
  have hMK2 : bl e X * K2b = K2b * bl e X := by rw [← hK2, ← bl_mul, ← bl_mul, hXK2]
  have hMrel : bl e X * (Wb * bl e X * Wb ^ 2) = Wb ^ 2 * bl e X * Wb := by
    have h := congrArg (bl e) hrel
    simp only [bl_mul, bl_pow, hW] at h
    exact h
  obtain h := candidate6_block (bl e X) hM2 hMK1 hMK2 hMrel
  rcases h with h | ⟨a, h | h⟩
  · left
    apply bl_injective e
    rw [h, bl_one]
  · right; refine ⟨a, Or.inl ?_⟩
    apply bl_injective e
    rw [h]
    simp only [bl_mul, bl_pow, hW, hR]
  · right; refine ⟨a, Or.inr ?_⟩
    apply bl_injective e
    rw [h]
    simp only [bl_mul, bl_pow, hW, hR']

private theorem root_char_of_matrix6 (u w r r' : SL(6, ZMod 2)) (hw : w ^ 3 = 1)
    (h : (u : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 ∨ ∃ a : Fin 3,
      (u : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        (w : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ (a : ℕ) *
          (r : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
          (w : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ (2 * (a : ℕ)) ∨
      (u : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        (w : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ (a : ℕ) *
          (r' : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
          (w : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ (2 * (a : ℕ))) :
    u = 1 ∨ ∃ a : Fin 3, u = cjp w a r ∨ u = cjp w a r' := by
  rcases h with h | ⟨a, h | h⟩
  · left
    apply Subtype.ext
    rw [h, Matrix.SpecialLinearGroup.coe_one]
  · right; refine ⟨a, Or.inl ?_⟩
    apply Subtype.ext
    rw [cjp_eq_pow hw a, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow]
    exact h
  · right; refine ⟨a, Or.inr ?_⟩
    apply Subtype.ext
    rw [cjp_eq_pow hw a, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow]
    exact h

private theorem root_char_SL6_j0 (u : SL(6, ZMod 2)) (hu2 : u * u = 1)
    (h1 : u * (W6.T 0 * W6.T 1) = (W6.T 0 * W6.T 1) * u)
    (h2 : u * W6.T 2 = W6.T 2 * u) (hrel : RootRel (W6.T 0) u) :
    u = 1 ∨ ∃ a : Fin 3, u = cjp (W6.T 0) a (N6.r 0) ∨ u = cjp (W6.T 0) a (N6.r' 0) := by
  set U : Matrix (Fin 6) (Fin 6) (ZMod 2) := (u : Matrix (Fin 6) (Fin 6) (ZMod 2)) with hU
  have hU2 : U * U = 1 := by
    have h := congrArg (fun z : SL(6, ZMod 2) => (z : Matrix (Fin 6) (Fin 6) (ZMod 2))) hu2
    simpa [← hU, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h
  have hUK1 : U * (W6.t1M * W6.t2M) = (W6.t1M * W6.t2M) * U := by
    have h := congrArg (fun z : SL(6, ZMod 2) => (z : Matrix (Fin 6) (Fin 6) (ZMod 2))) h1
    simpa [← hU, Matrix.SpecialLinearGroup.coe_mul, W6.coe_T] using h
  have hUK2 : U * W6.t3M = W6.t3M * U := by
    have h := congrArg (fun z : SL(6, ZMod 2) => (z : Matrix (Fin 6) (Fin 6) (ZMod 2))) h2
    simpa [← hU, W6.coe_T] using h
  have hrelm : U * (W6.t1M * U * W6.t1M ^ 2) = W6.t1M ^ 2 * U * W6.t1M := by
    have h := rootRel_matrix_of (n := 6) (w := W6.T 0) (u := u) (W6.pow_T 0) hrel
    simpa [← hU, W6.coe_T] using h
  have key := root_char_matrix6 e0 (W6.t1M * W6.t2M) W6.t3M W6.t1M N6.r0M N6.r0'M U
    bl_e0_K1 bl_e0_K2 bl_e0_W bl_e0_R bl_e0_R' hU2 hUK1 hUK2 hrelm
  exact root_char_of_matrix6 u (W6.T 0) (N6.r 0) (N6.r' 0) (W6.pow_T 0) key

private def tau6 : Fin 6 ≃ Fin 6 where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

private def e1 : Fin 6 ≃ (Fin 2 ⊕ Fin 2) ⊕ Fin 2 := tau6.trans e0

private theorem bl_e1_K1 : bl e1 (W6.t2M * W6.t3M) = K1b := by decide +kernel

private theorem bl_e1_K2 : bl e1 W6.t1M = K2b := by decide +kernel

private theorem bl_e1_W : bl e1 W6.t2M = Wb := by decide +kernel

private theorem bl_e1_R : bl e1 N6.r1M = Rb := by decide +kernel

private theorem bl_e1_R' : bl e1 N6.r1'M = Rb' := by decide +kernel

private theorem root_char_SL6_j1 (u : SL(6, ZMod 2)) (hu2 : u * u = 1)
    (h1 : u * (W6.T 1 * W6.T 2) = (W6.T 1 * W6.T 2) * u)
    (h2 : u * W6.T 0 = W6.T 0 * u) (hrel : RootRel (W6.T 1) u) :
    u = 1 ∨ ∃ a : Fin 3, u = cjp (W6.T 1) a (N6.r 1) ∨ u = cjp (W6.T 1) a (N6.r' 1) := by
  set U : Matrix (Fin 6) (Fin 6) (ZMod 2) := (u : Matrix (Fin 6) (Fin 6) (ZMod 2)) with hU
  have hU2 : U * U = 1 := by
    have h := congrArg (fun z : SL(6, ZMod 2) => (z : Matrix (Fin 6) (Fin 6) (ZMod 2))) hu2
    simpa [← hU, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h
  have hUK1 : U * (W6.t2M * W6.t3M) = (W6.t2M * W6.t3M) * U := by
    have h := congrArg (fun z : SL(6, ZMod 2) => (z : Matrix (Fin 6) (Fin 6) (ZMod 2))) h1
    simpa [← hU, Matrix.SpecialLinearGroup.coe_mul, W6.coe_T] using h
  have hUK2 : U * W6.t1M = W6.t1M * U := by
    have h := congrArg (fun z : SL(6, ZMod 2) => (z : Matrix (Fin 6) (Fin 6) (ZMod 2))) h2
    simpa [← hU, W6.coe_T] using h
  have hrelm : U * (W6.t2M * U * W6.t2M ^ 2) = W6.t2M ^ 2 * U * W6.t2M := by
    have h := rootRel_matrix_of (n := 6) (w := W6.T 1) (u := u) (W6.pow_T 1) hrel
    simpa [← hU, W6.coe_T] using h
  have key := root_char_matrix6 e1 (W6.t2M * W6.t3M) W6.t1M W6.t2M N6.r1M N6.r1'M U
    bl_e1_K1 bl_e1_K2 bl_e1_W bl_e1_R bl_e1_R' hU2 hUK1 hUK2 hrelm
  exact root_char_of_matrix6 u (W6.T 1) (N6.r 1) (N6.r' 1) (W6.pow_T 1) key

theorem root_char_SL6 : ∀ j, ∀ u : SL(6, ZMod 2), u * u = 1 →
    u * rootK₁ W6.T j = rootK₁ W6.T j * u → u * rootK₂ W6.T j = rootK₂ W6.T j * u →
    RootRel (rootW W6.T j) u →
    u = 1 ∨ ∃ a : Fin 3, u = cjp (rootW W6.T j) a (N6.r j) ∨ u = cjp (rootW W6.T j) a (N6.r' j) := by
  intro j u hu2 h1 h2 hrel
  fin_cases j
  · exact root_char_SL6_j0 u hu2 h1 h2 hrel
  · exact root_char_SL6_j1 u hu2 h1 h2 hrel

private def e7 : Fin 7 ≃ ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) ⊕ Fin 1 :=
  ((finSumFinEquiv : Fin 6 ⊕ Fin 1 ≃ Fin 7).symm).trans
    (Equiv.sumCongr e0 (Equiv.refl (Fin 1)))

private def e7' : Fin 7 ≃ ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) ⊕ Fin 1 :=
  ((finSumFinEquiv : Fin 6 ⊕ Fin 1 ≃ Fin 7).symm).trans
    (Equiv.sumCongr e1 (Equiv.refl (Fin 1)))

private theorem one_of_sq_one_fin1 (c : Matrix (Fin 1) (Fin 1) (ZMod 2)) (h : c * c = 1) :
    c = 1 := by
  decide +kernel +revert

private theorem bl_e7_K1 :
    bl e7 (W7.t1M * W7.t2M) = fromBlocks K1b 0 0 1 := by decide +kernel

private theorem bl_e7_K2 : bl e7 W7.t3M = fromBlocks K2b 0 0 1 := by decide +kernel

private theorem bl_e7_W : bl e7 W7.t1M = fromBlocks Wb 0 0 1 := by decide +kernel

private theorem bl_e7_R : bl e7 N7.r0M = fromBlocks Rb 0 0 1 := by decide +kernel

private theorem bl_e7_R' : bl e7 N7.r0'M = fromBlocks Rb' 0 0 1 := by decide +kernel

private theorem bl_e7_P :
    bl e7 (1 + W7.t1M * W7.t2M + (W7.t1M * W7.t2M) ^ 2 + W7.t3M + W7.t3M ^ 2) =
      fromBlocks 0 0 0 1 := by decide +kernel

private theorem bl_e7'_K1 :
    bl e7' (W7.t2M * W7.t3M) = fromBlocks K1b 0 0 1 := by decide +kernel

private theorem bl_e7'_K2 : bl e7' W7.t1M = fromBlocks K2b 0 0 1 := by decide +kernel

private theorem bl_e7'_W : bl e7' W7.t2M = fromBlocks Wb 0 0 1 := by decide +kernel

private theorem bl_e7'_R : bl e7' N7.r1M = fromBlocks Rb 0 0 1 := by decide +kernel

private theorem bl_e7'_R' : bl e7' N7.r1'M = fromBlocks Rb' 0 0 1 := by decide +kernel

private theorem bl_e7'_P :
    bl e7' (1 + W7.t2M * W7.t3M + (W7.t2M * W7.t3M) ^ 2 + W7.t1M + W7.t1M ^ 2) =
      fromBlocks 0 0 0 1 := by decide +kernel

private theorem root_char_matrix7 (e : Fin 7 ≃ ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) ⊕ Fin 1)
    (K1 K2 W R R' X : Matrix (Fin 7) (Fin 7) (ZMod 2))
    (hK1 : bl e K1 = fromBlocks K1b 0 0 1) (hK2 : bl e K2 = fromBlocks K2b 0 0 1)
    (hW : bl e W = fromBlocks Wb 0 0 1) (hR : bl e R = fromBlocks Rb 0 0 1)
    (hR' : bl e R' = fromBlocks Rb' 0 0 1)
    (hP : bl e (1 + K1 + K1 ^ 2 + K2 + K2 ^ 2) = fromBlocks 0 0 0 1)
    (hX2 : X * X = 1) (hXK1 : X * K1 = K1 * X) (hXK2 : X * K2 = K2 * X)
    (hrel : X * (W * X * W ^ 2) = W ^ 2 * X * W) :
    X = 1 ∨ ∃ a : Fin 3, X = W ^ (a : ℕ) * R * W ^ (2 * (a : ℕ)) ∨
      X = W ^ (a : ℕ) * R' * W ^ (2 * (a : ℕ)) := by
  have hK1sq : X * K1 ^ 2 = K1 ^ 2 * X :=
    (Commute.pow_right (show Commute X K1 from hXK1) 2).eq
  have hK2sq : X * K2 ^ 2 = K2 ^ 2 * X :=
    (Commute.pow_right (show Commute X K2 from hXK2) 2).eq
  have hXP : X * (1 + K1 + K1 ^ 2 + K2 + K2 ^ 2) = (1 + K1 + K1 ^ 2 + K2 + K2 ^ 2) * X := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hXK1, hK1sq,
      hXK2, hK2sq]
  have hE : bl e X * fromBlocks 0 0 0 1 = fromBlocks 0 0 0 1 * bl e X := by
    rw [← hP, ← bl_mul, ← bl_mul, hXP]
  obtain ⟨M6, c, hXeq⟩ : ∃ (M6 : Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) ((Fin 2 ⊕ Fin 2) ⊕ Fin 2)
        (ZMod 2)) (c : Matrix (Fin 1) (Fin 1) (ZMod 2)), bl e X = fromBlocks M6 0 0 c :=
    ⟨_, _, eq_fromBlocks_of_isBlockDiag (isBlockDiag_of_commute hE)⟩
  have hsq : fromBlocks (M6 * M6) 0 0 (c * c) = fromBlocks 1 0 0 1 := by
    rw [← fromBlocks_diag_mul, ← hXeq, ← bl_mul, hX2, bl_one, fromBlocks_one]
  have hM6sq : M6 * M6 = 1 := (fromBlocks_inj.mp hsq).1
  have hc : c = 1 := one_of_sq_one_fin1 c (fromBlocks_inj.mp hsq).2.2.2
  have hXeq' : bl e X = fromBlocks M6 0 0 1 := by rw [hXeq, hc]
  have hM6K1 : M6 * K1b = K1b * M6 := by
    have h := bl_commute e hXK1
    rw [hXeq', hK1] at h
    simp only [fromBlocks_diag_mul, Matrix.mul_one] at h
    exact (fromBlocks_inj.mp h).1
  have hM6K2 : M6 * K2b = K2b * M6 := by
    have h := bl_commute e hXK2
    rw [hXeq', hK2] at h
    simp only [fromBlocks_diag_mul, Matrix.mul_one] at h
    exact (fromBlocks_inj.mp h).1
  have hM6rel : M6 * (Wb * M6 * Wb ^ 2) = Wb ^ 2 * M6 * Wb := by
    have h := congrArg (bl e) hrel
    simp only [bl_mul, bl_pow, hW, hXeq', fromBlocks_diag_mul, fromBlocks_diag_pow, one_pow,
      Matrix.mul_one] at h
    exact (fromBlocks_inj.mp h).1
  obtain h := candidate6_block M6 hM6sq hM6K1 hM6K2 hM6rel
  rcases h with h | ⟨a, h | h⟩
  · left
    apply bl_injective e
    rw [hXeq', h, fromBlocks_one, bl_one]
  · right; refine ⟨a, Or.inl ?_⟩
    apply bl_injective e
    rw [hXeq', h]
    simp only [bl_mul, bl_pow, hW, hR, fromBlocks_diag_mul, fromBlocks_diag_pow, one_pow,
      Matrix.mul_one]
  · right; refine ⟨a, Or.inr ?_⟩
    apply bl_injective e
    rw [hXeq', h]
    simp only [bl_mul, bl_pow, hW, hR', fromBlocks_diag_mul, fromBlocks_diag_pow, one_pow,
      Matrix.mul_one]

private theorem root_char_of_matrix7 (u w r r' : SL(7, ZMod 2)) (hw : w ^ 3 = 1)
    (h : (u : Matrix (Fin 7) (Fin 7) (ZMod 2)) = 1 ∨ ∃ a : Fin 3,
      (u : Matrix (Fin 7) (Fin 7) (ZMod 2)) =
        (w : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ (a : ℕ) *
          (r : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
          (w : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ (2 * (a : ℕ)) ∨
      (u : Matrix (Fin 7) (Fin 7) (ZMod 2)) =
        (w : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ (a : ℕ) *
          (r' : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
          (w : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ (2 * (a : ℕ))) :
    u = 1 ∨ ∃ a : Fin 3, u = cjp w a r ∨ u = cjp w a r' := by
  rcases h with h | ⟨a, h | h⟩
  · left
    apply Subtype.ext
    rw [h, Matrix.SpecialLinearGroup.coe_one]
  · right; refine ⟨a, Or.inl ?_⟩
    apply Subtype.ext
    rw [cjp_eq_pow hw a, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow]
    exact h
  · right; refine ⟨a, Or.inr ?_⟩
    apply Subtype.ext
    rw [cjp_eq_pow hw a, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow]
    exact h

private theorem root_char_SL7_j0 (u : SL(7, ZMod 2)) (hu2 : u * u = 1)
    (h1 : u * (W7.T 0 * W7.T 1) = (W7.T 0 * W7.T 1) * u)
    (h2 : u * W7.T 2 = W7.T 2 * u) (hrel : RootRel (W7.T 0) u) :
    u = 1 ∨ ∃ a : Fin 3, u = cjp (W7.T 0) a (N7.r 0) ∨ u = cjp (W7.T 0) a (N7.r' 0) := by
  set U : Matrix (Fin 7) (Fin 7) (ZMod 2) := (u : Matrix (Fin 7) (Fin 7) (ZMod 2)) with hU
  have hU2 : U * U = 1 := by
    have h := congrArg (fun z : SL(7, ZMod 2) => (z : Matrix (Fin 7) (Fin 7) (ZMod 2))) hu2
    simpa [← hU, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h
  have hUK1 : U * (W7.t1M * W7.t2M) = (W7.t1M * W7.t2M) * U := by
    have h := congrArg (fun z : SL(7, ZMod 2) => (z : Matrix (Fin 7) (Fin 7) (ZMod 2))) h1
    simpa [← hU, Matrix.SpecialLinearGroup.coe_mul, W7.coe_T] using h
  have hUK2 : U * W7.t3M = W7.t3M * U := by
    have h := congrArg (fun z : SL(7, ZMod 2) => (z : Matrix (Fin 7) (Fin 7) (ZMod 2))) h2
    simpa [← hU, W7.coe_T] using h
  have hrelm : U * (W7.t1M * U * W7.t1M ^ 2) = W7.t1M ^ 2 * U * W7.t1M := by
    have h := rootRel_matrix_of (n := 7) (w := W7.T 0) (u := u) (W7.pow_T 0) hrel
    simpa [← hU, W7.coe_T] using h
  have key := root_char_matrix7 e7 (W7.t1M * W7.t2M) W7.t3M W7.t1M N7.r0M N7.r0'M U
    bl_e7_K1 bl_e7_K2 bl_e7_W bl_e7_R bl_e7_R' bl_e7_P hU2 hUK1 hUK2 hrelm
  exact root_char_of_matrix7 u (W7.T 0) (N7.r 0) (N7.r' 0) (W7.pow_T 0) key

private theorem root_char_SL7_j1 (u : SL(7, ZMod 2)) (hu2 : u * u = 1)
    (h1 : u * (W7.T 1 * W7.T 2) = (W7.T 1 * W7.T 2) * u)
    (h2 : u * W7.T 0 = W7.T 0 * u) (hrel : RootRel (W7.T 1) u) :
    u = 1 ∨ ∃ a : Fin 3, u = cjp (W7.T 1) a (N7.r 1) ∨ u = cjp (W7.T 1) a (N7.r' 1) := by
  set U : Matrix (Fin 7) (Fin 7) (ZMod 2) := (u : Matrix (Fin 7) (Fin 7) (ZMod 2)) with hU
  have hU2 : U * U = 1 := by
    have h := congrArg (fun z : SL(7, ZMod 2) => (z : Matrix (Fin 7) (Fin 7) (ZMod 2))) hu2
    simpa [← hU, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h
  have hUK1 : U * (W7.t2M * W7.t3M) = (W7.t2M * W7.t3M) * U := by
    have h := congrArg (fun z : SL(7, ZMod 2) => (z : Matrix (Fin 7) (Fin 7) (ZMod 2))) h1
    simpa [← hU, Matrix.SpecialLinearGroup.coe_mul, W7.coe_T] using h
  have hUK2 : U * W7.t1M = W7.t1M * U := by
    have h := congrArg (fun z : SL(7, ZMod 2) => (z : Matrix (Fin 7) (Fin 7) (ZMod 2))) h2
    simpa [← hU, W7.coe_T] using h
  have hrelm : U * (W7.t2M * U * W7.t2M ^ 2) = W7.t2M ^ 2 * U * W7.t2M := by
    have h := rootRel_matrix_of (n := 7) (w := W7.T 1) (u := u) (W7.pow_T 1) hrel
    simpa [← hU, W7.coe_T] using h
  have key := root_char_matrix7 e7' (W7.t2M * W7.t3M) W7.t1M W7.t2M N7.r1M N7.r1'M U
    bl_e7'_K1 bl_e7'_K2 bl_e7'_W bl_e7'_R bl_e7'_R' bl_e7'_P hU2 hUK1 hUK2 hrelm
  exact root_char_of_matrix7 u (W7.T 1) (N7.r 1) (N7.r' 1) (W7.pow_T 1) key

theorem root_char_SL7 : ∀ j, ∀ u : SL(7, ZMod 2), u * u = 1 →
    u * rootK₁ W7.T j = rootK₁ W7.T j * u → u * rootK₂ W7.T j = rootK₂ W7.T j * u →
    RootRel (rootW W7.T j) u →
    u = 1 ∨ ∃ a : Fin 3, u = cjp (rootW W7.T j) a (N7.r j) ∨ u = cjp (rootW W7.T j) a (N7.r' j) := by
  intro j u hu2 h1 h2 hrel
  fin_cases j
  · exact root_char_SL7_j0 u hu2 h1 h2 hrel
  · exact root_char_SL7_j1 u hu2 h1 h2 hrel

end CFSG.StandardType.GGFF

end
