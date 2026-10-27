module

public import CFSG.RankThree.PartOne.KE.E7FourStabBase
public import CFSG.RankThree.PartOne.KE.E7FourLattice

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (charVal charVal_smul_col charVal_single weylMatrix weylMatrix_apply)
open scoped Matrix

instance e7S5_fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

@[expose] def E7S5Claim (z : Fin Tag.E7.rank → ZMod 5) : Prop :=
  dualWeylStabilizer z ≤ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α}

theorem E7S5Claim_smul {z : Fin Tag.E7.rank → ZMod 5} {s : ZMod 5} (hs : s ≠ 0)
    (h : E7S5Claim z) : E7S5Claim (s • z) := by
  unfold E7S5Claim at h ⊢
  rw [rootKernel_col_smul hs, dualWeylStabilizer_col_smul hs]
  exact h

theorem e7S5_claim_of_transport {z : Fin Tag.E7.rank → ZMod 5} {a : WeylGroup Tag.E7}
    (h : ∀ x, charVal e7S5Z (a • x) = charVal z x) : E7S5Claim z := by
  intro g hg
  have hg' := (mem_dualWeylStabilizer_conj h g).1 hg
  exact (mem_closure_rootKernel_conj h g).2 (dualWeylStabilizer_e7S5Z_le hg')

theorem weylMatrix_wordProd_e7 (ω : List (Fin Tag.E7.rank)) :
    weylMatrix ((coxeterSystem Tag.E7).wordProd ω) = toMat Tag.E7.rank (e7wl ω) := by
  ext i j
  rw [weylMatrix_apply, wordProd_smul_eq_wordMat_mulVec, wordMat_e7wl]
  simp

theorem e7S5_claim_of_word {z : Fin Tag.E7.rank → ZMod 5} (ω : List (Fin Tag.E7.rank))
    (h : ∀ i : Fin Tag.E7.rank,
      ((lget (e7wl ω) 0 i + lget (e7wl ω) 5 i : ℤ) : ZMod 5) = z i) : E7S5Claim z := by
  refine e7S5_claim_of_transport (a := (coxeterSystem Tag.E7).wordProd ω) fun x => ?_
  rw [charVal_smul_eq_sum, charVal]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hcol : ∀ r : Fin Tag.E7.rank,
      ((coxeterSystem Tag.E7).wordProd ω • (Pi.single j 1 : Fin Tag.E7.rank → ℤ)) r =
        lget (e7wl ω) r j := fun r => by
    rw [← weylMatrix_apply, weylMatrix_wordProd_e7]
    rfl
  have e0 : ((coxeterSystem Tag.E7).wordProd ω • (Pi.single j 1 : Fin Tag.E7.rank → ℤ))
      (0 : Fin 7) = lget (e7wl ω) 0 j := hcol _
  have e5 : ((coxeterSystem Tag.E7).wordProd ω • (Pi.single j 1 : Fin Tag.E7.rank → ℤ))
      (5 : Fin 7) = lget (e7wl ω) 5 j := hcol _
  rw [charVal_e7S5Z, e0, e5]
  exact h j

@[expose] def e7S5Zc (ρ a b : ZMod 5) : Fin Tag.E7.rank → ZMod 5 := fun i =>
  ([a, a * (1 - ρ) + b * (1 + ρ), b, ρ * a - b, -a, -b, -ρ * a + b - ρ * b] :
    List (ZMod 5)).getD i 0

theorem e7S5Zc_smul : ∀ ρ s a b : ZMod 5, e7S5Zc ρ (s * a) (s * b) = s • e7S5Zc ρ a b := by
  decide +kernel

theorem e7S5Zc_zero : ∀ ρ : ZMod 5, e7S5Zc ρ 0 0 = 0 := by
  decide +kernel

theorem e7S5Zc_apply_zero (ρ a b : ZMod 5) : e7S5Zc ρ a b 0 = a := rfl

theorem e7S5Zc_apply_two (ρ a b : ZMod 5) : e7S5Zc ρ a b 2 = b := rfl

theorem e7S5Zc_eigen_two : ∀ a b : ZMod 5,
    ((toMat Tag.E7.rank e7F4WList).map (Int.cast : ℤ → ZMod 5))ᵀ *ᵥ e7S5Zc 2 a b =
      (2 : ZMod 5) • e7S5Zc 2 a b := by
  decide +kernel

theorem e7S5Zc_eigen_three : ∀ a b : ZMod 5,
    ((toMat Tag.E7.rank e7F4WList).map (Int.cast : ℤ → ZMod 5))ᵀ *ᵥ e7S5Zc 3 a b =
      (3 : ZMod 5) • e7S5Zc 3 a b := by
  decide +kernel

theorem pair_single' {n : ℕ} {K : Type*} [CommRing K] (i : Fin n) (z : Fin n → K) :
    pair (Pi.single i 1 : Fin n → ℤ) z = z i := by
  simp [pair, dotProduct, Pi.single_apply]

theorem toVec_e7T12VList : toVec Tag.E7.rank e7T12VList = Pi.single 0 1 := by
  funext i
  fin_cases i <;> rfl

theorem toVec_e7F4B2List : toVec Tag.E7.rank e7F4B2List = Pi.single 2 1 := by
  funext i
  fin_cases i <;> decide

theorem e7S5_eigen_eq {ρ : ZMod 5} (hρ : ρ = 2 ∨ ρ = 3) {z : Fin Tag.E7.rank → ZMod 5}
    (hz : ((toMat Tag.E7.rank e7F4WList).map (Int.cast : ℤ → ZMod 5))ᵀ *ᵥ z = ρ • z) :
    z = e7S5Zc ρ (z 0) (z 2) := by
  have hu : ((toMat Tag.E7.rank e7F4WList).map (Int.cast : ℤ → ZMod 5))ᵀ *ᵥ
      e7S5Zc ρ (z 0) (z 2) = ρ • e7S5Zc ρ (z 0) (z 2) := by
    rcases hρ with rfl | rfl
    · exact e7S5Zc_eigen_two _ _
    · exact e7S5Zc_eigen_three _ _
  have hd : ((toMat Tag.E7.rank e7F4WList).map (Int.cast : ℤ → ZMod 5))ᵀ *ᵥ
      (z - e7S5Zc ρ (z 0) (z 2)) = ρ • (z - e7S5Zc ρ (z 0) (z 2)) := by
    rw [Matrix.mulVec_sub, hz, hu, smul_sub]
  have hρ1 : ρ ≠ 1 := by
    rcases hρ with rfl | rfl <;> decide
  have hF : ∀ x ∈ e7F4FList,
      pair (toVec Tag.E7.rank x) (z - e7S5Zc ρ (z 0) (z 2)) = 0 := by
    intro x hx
    have hfix : (toMat Tag.E7.rank e7F4WList) *ᵥ toVec Tag.E7.rank x = toVec Tag.E7.rank x := by
      rw [← toVec_lmulVec, e7F4W_fixes x hx]
    exact pair_eq_zero_of_fixed hd hρ1 hfix
  have h1 : pair (toVec Tag.E7.rank e7T12VList) (z - e7S5Zc ρ (z 0) (z 2)) = 0 := by
    rw [toVec_e7T12VList, pair_single', Pi.sub_apply, e7S5Zc_apply_zero, sub_self]
  have h2 : pair (toVec Tag.E7.rank e7F4B2List) (z - e7S5Zc ρ (z 0) (z 2)) = 0 := by
    rw [toVec_e7F4B2List, pair_single', Pi.sub_apply, e7S5Zc_apply_two, sub_self]
  have h0 : z - e7S5Zc ρ (z 0) (z 2) = 0 :=
    eq_zero_of_pair_cols_eq_zero (B := toMat Tag.E7.rank (lcols Tag.E7.rank e7F4ColsList))
      (by rw [e7F4Cols_det]; exact isUnit_one.neg) fun j => e7F4_cols_pair hd hF h1 h2 j
  exact sub_eq_zero.1 h0

theorem e7S5_claim_2_1_0 : E7S5Claim (e7S5Zc 2 1 0) :=
  e7S5_claim_of_word [0, 2, 5, 4, 3, 1, 2, 3, 4, 5, 6, 5, 4] (by decide +kernel)

theorem e7S5_claim_2_1_1 : E7S5Claim (e7S5Zc 2 1 1) :=
  e7S5_claim_of_word [0, 2, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4] (by decide +kernel)

theorem e7S5_claim_2_1_2 : E7S5Claim (e7S5Zc 2 1 2) :=
  e7S5_claim_of_word [0, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 4, 3, 1, 2, 3, 4, 5] (by decide +kernel)

theorem e7S5_claim_2_1_3 : E7S5Claim (e7S5Zc 2 1 3) :=
  e7S5_claim_of_word [0, 2, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3] (by decide +kernel)

theorem e7S5_claim_2_1_4 : E7S5Claim (e7S5Zc 2 1 4) :=
  e7S5_claim_of_word [0, 2, 3, 1, 4, 3, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 6, 5, 4, 3, 1, 2] (by decide +kernel)

theorem e7S5_claim_2_0_1 : E7S5Claim (e7S5Zc 2 0 1) :=
  e7S5_claim_of_word [0, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 4, 3] (by decide +kernel)

theorem e7S5_claim_3_1_0 : E7S5Claim (e7S5Zc 3 1 0) :=
  e7S5_claim_of_word [0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4] (by decide +kernel)

theorem e7S5_claim_3_1_1 : E7S5Claim (e7S5Zc 3 1 1) :=
  e7S5_claim_of_word [0, 2, 3, 4, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 4, 3, 1] (by decide +kernel)

theorem e7S5_claim_3_1_2 : E7S5Claim (e7S5Zc 3 1 2) :=
  e7S5_claim_of_word [0, 2, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4] (by decide +kernel)

theorem e7S5_claim_3_1_3 : E7S5Claim (e7S5Zc 3 1 3) :=
  e7S5_claim_of_word [0, 2, 3, 4, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2] (by decide +kernel)

theorem e7S5_claim_3_1_4 : E7S5Claim (e7S5Zc 3 1 4) :=
  e7S5_claim_of_word [0, 2, 3, 1, 4, 3, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 6, 5, 4, 3, 2] (by decide +kernel)

theorem e7S5_claim_3_0_1 : E7S5Claim (e7S5Zc 3 0 1) :=
  e7S5_claim_of_word [0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3] (by decide +kernel)


theorem e7S5_claim_one {ρ : ZMod 5} (hρ : ρ = 2 ∨ ρ = 3) (j : ZMod 5) :
    E7S5Claim (e7S5Zc ρ 1 j) := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by revert j; decide
  rcases hρ with rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl | rfl
  · exact e7S5_claim_2_1_0
  · exact e7S5_claim_2_1_1
  · exact e7S5_claim_2_1_2
  · exact e7S5_claim_2_1_3
  · exact e7S5_claim_2_1_4
  · exact e7S5_claim_3_1_0
  · exact e7S5_claim_3_1_1
  · exact e7S5_claim_3_1_2
  · exact e7S5_claim_3_1_3
  · exact e7S5_claim_3_1_4

theorem e7S5_claim_zero_one {ρ : ZMod 5} (hρ : ρ = 2 ∨ ρ = 3) : E7S5Claim (e7S5Zc ρ 0 1) := by
  rcases hρ with rfl | rfl
  · exact e7S5_claim_2_0_1
  · exact e7S5_claim_3_0_1

theorem e7S5_claim_eigen {ρ : ZMod 5} (hρ : ρ = 2 ∨ ρ = 3) {z : Fin Tag.E7.rank → ZMod 5}
    (hz0 : z ≠ 0)
    (hz : ((toMat Tag.E7.rank e7F4WList).map (Int.cast : ℤ → ZMod 5))ᵀ *ᵥ z = ρ • z) :
    E7S5Claim z := by
  have h := e7S5_eigen_eq hρ hz
  by_cases ha : z 0 = 0
  · have hb : z 2 ≠ 0 := by
      intro hb
      apply hz0
      rw [h, ha, hb]
      exact e7S5Zc_zero ρ
    have e : z = z 2 • e7S5Zc ρ 0 1 := by
      rw [← e7S5Zc_smul, mul_zero, mul_one, ← ha, ← h]
    rw [e]
    exact E7S5Claim_smul hb (e7S5_claim_zero_one hρ)
  · have e : z = z 0 • e7S5Zc ρ 1 ((z 0)⁻¹ * z 2) := by
      rw [← e7S5Zc_smul, mul_one, mul_inv_cancel_left₀ ha, ← h]
    rw [e]
    exact E7S5Claim_smul ha (e7S5_claim_one hρ _)

end CFSG.RankThree.PartOne.KE
