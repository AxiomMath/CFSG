module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp4CenDefs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp4Cen

open Matrix

abbrev C0 : Subgroup GL6 := Subgroup.centralizer {u0}

@[expose] def topIdx (i : Fin 4) : Fin 6 := ⟨i.val, Nat.lt_of_lt_of_le i.isLt (by norm_num)⟩

private theorem topIdx_injective : Function.Injective topIdx := fun _ _ h => by
  have := congrArg Fin.val h
  exact Fin.ext this

private theorem topIdx_ne_four (i : Fin 4) : topIdx i ≠ 4 := by
  fin_cases i <;> decide

private theorem topIdx_ne_five (i : Fin 4) : topIdx i ≠ 5 := by
  fin_cases i <;> decide

private theorem fin6_cases (i : Fin 6) : (∃ j : Fin 4, i = topIdx j) ∨ i = 4 ∨ i = 5 := by
  fin_cases i
  · exact Or.inl ⟨0, rfl⟩
  · exact Or.inl ⟨1, rfl⟩
  · exact Or.inl ⟨2, rfl⟩
  · exact Or.inl ⟨3, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

private theorem sum6 {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ k, f k = ∑ k : Fin 4, f (topIdx k) + f 4 + f 5 := by
  simp only [Fin.sum_univ_six, Fin.sum_univ_four]
  rfl

private theorem one_topIdx (i j : Fin 4) : (1 : M6) (topIdx i) (topIdx j) = (1 : M4) i j := by
  simp [Matrix.one_apply, topIdx_injective.eq_iff]

private theorem mul_U0_col4 (m : M6) (i : Fin 6) : (m * U0) i 4 = m i 5 := by
  simp [Matrix.mul_apply, Fin.sum_univ_six, U0]

private theorem mul_U0_col5 (m : M6) (i : Fin 6) : (m * U0) i 5 = m i 4 + m i 5 := by
  simp [Matrix.mul_apply, Fin.sum_univ_six, U0]

private theorem U0_mul_row4 (m : M6) (j : Fin 6) : (U0 * m) 4 j = m 5 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_six, U0]

private theorem U0_mul_row5 (m : M6) (j : Fin 6) : (U0 * m) 5 j = m 4 j + m 5 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_six, U0]

private theorem mul_U0_top (m : M6) (i : Fin 6) (j : Fin 4) :
    (m * U0) i (topIdx j) = m i (topIdx j) := by
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six, U0, topIdx]

private theorem U0_mul_top (m : M6) (i : Fin 4) (j : Fin 6) :
    (U0 * m) (topIdx i) j = m (topIdx i) j := by
  fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_six, U0, topIdx]

private theorem U0_topIdx (i j : Fin 4) : U0 (topIdx i) (topIdx j) = (1 : M4) i j := by
  have h := U0_mul_top (1 : M6) i (topIdx j)
  rw [Matrix.mul_one] at h
  rw [h, one_topIdx]

private theorem U0sq_topIdx (i j : Fin 4) : U0sq (topIdx i) (topIdx j) = (1 : M4) i j := by
  rw [← U0_mul_U0, U0_mul_top, U0_topIdx]

theorem commute_U0_iff {m : M6} : m * U0 = U0 * m ↔
    (∀ i : Fin 4, m (topIdx i) 4 = 0 ∧ m (topIdx i) 5 = 0 ∧ m 4 (topIdx i) = 0 ∧
      m 5 (topIdx i) = 0) ∧ m 5 4 = m 4 5 ∧ m 5 5 = m 4 4 + m 4 5 := by
  constructor
  · intro h
    have e : ∀ i j, (m * U0) i j = (U0 * m) i j := fun i j => by rw [h]
    refine ⟨fun i => ?_, ?_, ?_⟩
    · have e1 := e (topIdx i) 4
      have e2 := e (topIdx i) 5
      have e3 := e 4 (topIdx i)
      have e4 := e 5 (topIdx i)
      rw [mul_U0_col4, U0_mul_top] at e1
      rw [mul_U0_col5, U0_mul_top] at e2
      rw [mul_U0_top, U0_mul_row4] at e3
      rw [mul_U0_top, U0_mul_row5] at e4
      have h4 : m (topIdx i) 4 = 0 := by simpa using e2
      have h4' : m 4 (topIdx i) = 0 := by simpa using e4
      exact ⟨h4, e1.trans h4, h4', e3.symm ▸ h4'⟩
    · have e1 := e 4 4
      rw [mul_U0_col4, U0_mul_row4] at e1
      exact e1.symm
    · have e1 := e 4 5
      rw [mul_U0_col5, U0_mul_row4] at e1
      exact e1.symm
  · rintro ⟨hlo, h54, h55⟩
    ext i j
    rcases fin6_cases i with ⟨i, rfl⟩ | rfl | rfl <;>
      rcases fin6_cases j with ⟨j, rfl⟩ | rfl | rfl
    · rw [mul_U0_top, U0_mul_top]
    · rw [mul_U0_col4, U0_mul_top, (hlo i).1, (hlo i).2.1]
    · rw [mul_U0_col5, U0_mul_top, (hlo i).1, (hlo i).2.1, add_zero]
    · rw [mul_U0_top, U0_mul_row4, (hlo j).2.2.1, (hlo j).2.2.2]
    · rw [mul_U0_col4, U0_mul_row4, h54]
    · rw [mul_U0_col5, U0_mul_row4, h55]
    · rw [mul_U0_top, U0_mul_row5, (hlo j).2.2.1, (hlo j).2.2.2, add_zero]
    · rw [mul_U0_col4, U0_mul_row5, h55, h54]
    · rw [mul_U0_col5, U0_mul_row5, h54]

theorem mem_C0_iff (g : GL6) : g ∈ C0 ↔ (g : M6) * U0 = U0 * (g : M6) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => congrArg Units.val h, fun h => Units.ext h⟩

theorem u0_mem_C0 : u0 ∈ C0 := Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem zpowers_u0_le_C0 : Subgroup.zpowers u0 ≤ C0 :=
  Subgroup.zpowers_le.mpr u0_mem_C0

private theorem eq_of_block {m T : M6} (hm : m * U0 = U0 * m) (hT : T * U0 = U0 * T)
    (htl : ∀ i j : Fin 4, m (topIdx i) (topIdx j) = T (topIdx i) (topIdx j))
    (h44 : m 4 4 = T 4 4) (h45 : m 4 5 = T 4 5) : m = T := by
  obtain ⟨hm1, hm2, hm3⟩ := commute_U0_iff.mp hm
  obtain ⟨hT1, hT2, hT3⟩ := commute_U0_iff.mp hT
  ext i j
  rcases fin6_cases i with ⟨i, rfl⟩ | rfl | rfl <;>
    rcases fin6_cases j with ⟨j, rfl⟩ | rfl | rfl
  · exact htl i j
  · rw [(hm1 i).1, (hT1 i).1]
  · rw [(hm1 i).2.1, (hT1 i).2.1]
  · rw [(hm1 j).2.2.1, (hT1 j).2.2.1]
  · exact h44
  · exact h45
  · rw [(hm1 j).2.2.2, (hT1 j).2.2.2]
  · rw [hm2, hT2, h45]
  · rw [hm3, hT3, h44, h45]

@[expose] def blkDiag (A : M4) : M6 :=
  Matrix.of fun i j =>
    if h : i.val < 4 ∧ j.val < 4 then A ⟨i, h.1⟩ ⟨j, h.2⟩ else (1 : M6) i j

private theorem blkDiag_of_not (A : M4) {i j : Fin 6} (h : ¬ (i.val < 4 ∧ j.val < 4)) :
    blkDiag A i j = (1 : M6) i j := by
  simp only [blkDiag, Matrix.of_apply, dif_neg h]

theorem blkDiag_topIdx (A : M4) (i j : Fin 4) : blkDiag A (topIdx i) (topIdx j) = A i j := by
  simp [blkDiag, topIdx]

private theorem blkDiag_top_four (A : M4) (i : Fin 4) : blkDiag A (topIdx i) 4 = 0 := by
  rw [blkDiag_of_not A (by simp), Matrix.one_apply_ne (topIdx_ne_four i)]

private theorem blkDiag_top_five (A : M4) (i : Fin 4) : blkDiag A (topIdx i) 5 = 0 := by
  rw [blkDiag_of_not A (by simp), Matrix.one_apply_ne (topIdx_ne_five i)]

private theorem blkDiag_four_top (A : M4) (j : Fin 4) : blkDiag A 4 (topIdx j) = 0 := by
  rw [blkDiag_of_not A (by simp), Matrix.one_apply_ne (topIdx_ne_four j).symm]

private theorem blkDiag_five_top (A : M4) (j : Fin 4) : blkDiag A 5 (topIdx j) = 0 := by
  rw [blkDiag_of_not A (by simp), Matrix.one_apply_ne (topIdx_ne_five j).symm]

private theorem blkDiag_four_four (A : M4) : blkDiag A 4 4 = 1 := by
  rw [blkDiag_of_not A (by simp)]
  exact Matrix.one_apply_eq _

private theorem blkDiag_four_five (A : M4) : blkDiag A 4 5 = 0 := by
  rw [blkDiag_of_not A (by simp)]
  exact Matrix.one_apply_ne (by decide)

private theorem blkDiag_five_four (A : M4) : blkDiag A 5 4 = 0 := by
  rw [blkDiag_of_not A (by simp)]
  exact Matrix.one_apply_ne (by decide)

private theorem blkDiag_five_five (A : M4) : blkDiag A 5 5 = 1 := by
  rw [blkDiag_of_not A (by simp)]
  exact Matrix.one_apply_eq _

private theorem blkDiag_one : blkDiag (1 : M4) = 1 := by
  ext i j
  rcases fin6_cases i with ⟨i, rfl⟩ | rfl | rfl <;>
    rcases fin6_cases j with ⟨j, rfl⟩ | rfl | rfl
  · rw [blkDiag_topIdx, one_topIdx]
  · rw [blkDiag_top_four, Matrix.one_apply_ne (topIdx_ne_four i)]
  · rw [blkDiag_top_five, Matrix.one_apply_ne (topIdx_ne_five i)]
  · rw [blkDiag_four_top, Matrix.one_apply_ne (topIdx_ne_four j).symm]
  · rw [blkDiag_four_four, Matrix.one_apply_eq]
  · rw [blkDiag_four_five, Matrix.one_apply_ne (by decide)]
  · rw [blkDiag_five_top, Matrix.one_apply_ne (topIdx_ne_five j).symm]
  · rw [blkDiag_five_four, Matrix.one_apply_ne (by decide)]
  · rw [blkDiag_five_five, Matrix.one_apply_eq]

private theorem blkDiag_mul (A B : M4) : blkDiag (A * B) = blkDiag A * blkDiag B := by
  ext i j
  rcases fin6_cases i with ⟨i, rfl⟩ | rfl | rfl <;>
    rcases fin6_cases j with ⟨j, rfl⟩ | rfl | rfl <;>
    simp [Matrix.mul_apply, sum6, blkDiag_topIdx, blkDiag_top_four, blkDiag_top_five,
      blkDiag_four_top, blkDiag_five_top, blkDiag_four_four, blkDiag_four_five,
      blkDiag_five_four, blkDiag_five_five]

def blkDiagHom : M4 →* M6 where
  toFun := blkDiag
  map_one' := blkDiag_one
  map_mul' := blkDiag_mul

@[expose] noncomputable def iota : GL4 →* GL6 := Units.map blkDiagHom

theorem coe_iota (A : GL4) : ((iota A : GL6) : M6) = blkDiag (A : M4) := by
  simp [iota, blkDiagHom]

theorem iota_injective : Function.Injective iota := by
  intro A B h
  apply Units.ext
  ext i j
  have := congrArg (fun g : GL6 => (g : M6) (topIdx i) (topIdx j)) h
  simpa [coe_iota, blkDiag_topIdx] using this

theorem iota_mem (A : GL4) : iota A ∈ C0 := by
  rw [mem_C0_iff, coe_iota, commute_U0_iff]
  refine ⟨fun i => ⟨blkDiag_top_four _ i, blkDiag_top_five _ i, blkDiag_four_top _ i,
    blkDiag_five_top _ i⟩, ?_, ?_⟩
  · rw [blkDiag_five_four, blkDiag_four_five]
  · rw [blkDiag_five_five, blkDiag_four_four, blkDiag_four_five, add_zero]

def tauMat : ↥C0 →* M4 where
  toFun g := Matrix.of fun i j => ((g : GL6) : M6) (topIdx i) (topIdx j)
  map_one' := by
    ext i j
    exact one_topIdx i j
  map_mul' g h := by
    ext i j
    obtain ⟨hlo, -⟩ := commute_U0_iff.mp ((mem_C0_iff _).mp h.2)
    simp [Matrix.mul_apply, sum6, (hlo j).2.2.1, (hlo j).2.2.2]

@[expose] noncomputable def tau : ↥C0 →* GL4 := tauMat.toHomUnits

theorem coe_tau (g : ↥C0) (i j : Fin 4) :
    ((tau g : GL4) : M4) i j = ((g : GL6) : M6) (topIdx i) (topIdx j) := by
  simp [tau, tauMat]

theorem tau_iota (A : GL4) : tau ⟨iota A, iota_mem A⟩ = A := by
  apply Units.ext
  ext i j
  rw [coe_tau]
  exact blkDiag_topIdx _ i j

theorem tau_surjective : Function.Surjective tau :=
  fun A => ⟨⟨iota A, iota_mem A⟩, tau_iota A⟩

theorem tau_u0 : tau ⟨u0, u0_mem_C0⟩ = 1 := by
  apply Units.ext
  ext i j
  rw [coe_tau]
  exact U0_topIdx i j

theorem tau_eq_one_iff (g : ↥C0) : tau g = 1 ↔ (g : GL6) ∈ Subgroup.zpowers u0 := by
  constructor
  · intro hg
    have hcomm := (mem_C0_iff _).mp g.2
    obtain ⟨hlo, h54, h55⟩ := commute_U0_iff.mp hcomm
    have htl : ∀ i j : Fin 4, ((g : GL6) : M6) (topIdx i) (topIdx j) = (1 : M4) i j := by
      intro i j
      have := congrArg (fun A : GL4 => (A : M4) i j) hg
      exact this
    have hab : ¬ (((g : GL6) : M6) 4 4 = 0 ∧ ((g : GL6) : M6) 4 5 = 0) := by
      rintro ⟨h44, h45⟩
      have hrow : ∀ j : Fin 6, ((g : GL6) : M6) 4 j = 0 := by
        intro j
        rcases fin6_cases j with ⟨j, rfl⟩ | rfl | rfl
        · exact (hlo j).2.2.1
        · exact h44
        · exact h45
      have := congrFun (congrFun (Units.mul_inv (g : GL6)) 4) 4
      simp [Matrix.mul_apply, hrow] at this
    have key : ∀ a b : ZMod 2, ¬ (a = 0 ∧ b = 0) →
        (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 1) := by decide
    rcases key _ _ hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have : (g : GL6) = 1 := Units.ext (eq_of_block hcomm
        (by rw [Units.val_one, Matrix.one_mul, Matrix.mul_one])
        (fun i j => by rw [htl, Units.val_one, one_topIdx]) (by simp [ha]) (by simp [hb]))
      rw [this]
      exact one_mem _
    · have : (g : GL6) = u0 := Units.ext (eq_of_block hcomm
        ((mem_C0_iff u0).mp u0_mem_C0)
        (fun i j => by rw [htl, coe_u0, U0_topIdx]) (by simp [coe_u0, U0, ha])
        (by simp [coe_u0, U0, hb]))
      rw [this]
      exact Subgroup.mem_zpowers u0
    · have : (g : GL6) = u0⁻¹ := Units.ext (eq_of_block hcomm
        (by show U0sq * U0 = U0 * U0sq; rw [U0sq_mul_U0, U0_mul_U0sq])
        (fun i j => by show _ = U0sq (topIdx i) (topIdx j); rw [htl, U0sq_topIdx])
        (by show _ = U0sq 4 4; simp [U0sq, ha])
        (by show _ = U0sq 4 5; simp [U0sq, hb]))
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers u0)
  · intro hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    have : g = (⟨u0, u0_mem_C0⟩ : ↥C0) ^ k := Subtype.ext (by simpa using hk.symm)
    rw [this, map_zpow, tau_u0, one_zpow]

private theorem card_GL4_eq : Nat.card GL4 = 20160 := by
  rw [Matrix.card_GL_field, ZMod.card]
  simp [Fin.prod_univ_succ]

theorem ker_tau : tau.ker = (Subgroup.zpowers u0).subgroupOf C0 := by
  ext g
  rw [MonoidHom.mem_ker, tau_eq_one_iff, Subgroup.mem_subgroupOf]

theorem card_ker_tau : Nat.card tau.ker = 3 := by
  rw [ker_tau, Nat.card_congr (Subgroup.subgroupOfEquivOfLe zpowers_u0_le_C0).toEquiv,
    Nat.card_zpowers, orderOf_u0]

theorem card_C0 : Nat.card C0 = 60480 := by
  have h := Subgroup.card_ker_mul_card_of_surjective tau_surjective
  rw [card_ker_tau, card_GL4_eq] at h
  omega

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp4Cen
