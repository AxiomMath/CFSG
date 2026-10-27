module

public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3Field
public import CFSG.LocalAnalysis.UniquenessCase.UCInspConjN
public import CFSG.LocalAnalysis.UniquenessCase.UCInspPair2
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL2Abs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
open Matrix
open scoped MatrixGroups

namespace InspL3

theorem mul_inv_eq_of_mul_eq {K : Type} [Field K] {P X G : SL(3, K)}
    (h : (P : Matrix (Fin 3) (Fin 3) K) * (X : Matrix (Fin 3) (Fin 3) K) =
      (G : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K)) :
    P * X * P⁻¹ = G := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  calc (P : Matrix (Fin 3) (Fin 3) K) * (X : Matrix (Fin 3) (Fin 3) K) *
        adjugate (P : Matrix (Fin 3) (Fin 3) K)
      = ((G : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K)) *
          adjugate (P : Matrix (Fin 3) (Fin 3) K) := by rw [h]
    _ = (G : Matrix (Fin 3) (Fin 3) K) *
          ((P : Matrix (Fin 3) (Fin 3) K) * adjugate (P : Matrix (Fin 3) (Fin 3) K)) :=
        Matrix.mul_assoc _ _ _
    _ = (G : Matrix (Fin 3) (Fin 3) K) * ((P : Matrix (Fin 3) (Fin 3) K).det • 1) := by
        rw [Matrix.mul_adjugate]
    _ = (G : Matrix (Fin 3) (Fin 3) K) := by rw [P.2, one_smul, Matrix.mul_one]

def cycSL (K : Type) [Field K] : SL(3, K) :=
  Subtype.mk (cycMat (F := K)) (by rw [Matrix.det_fin_three]; simp [cycMat])

section Odd

variable (K : Type) [Field K]

def xOdd : SL(3, K) :=
  Subtype.mk !![1, 0, 0; 0, -1, 0; 0, 0, -1]
    (by rw [Matrix.det_fin_three]; simp)

def yOdd : SL(3, K) :=
  Subtype.mk !![-1, 0, 0; 0, -1, 0; 0, 0, 1]
    (by rw [Matrix.det_fin_three]; simp)

theorem neg_one_ne_one (h2 : (2 : K) ≠ 0) : (-1 : K) ≠ 1 := by
  intro h
  apply h2
  have h1 : (-1 : K) + 1 = 0 := neg_add_cancel 1
  rw [h] at h1
  rwa [one_add_one_eq_two] at h1

theorem xOdd_mul_self : xOdd K * xOdd K = 1 := by
  apply Subtype.ext
  change (xOdd K : Matrix (Fin 3) (Fin 3) K) * (xOdd K : Matrix (Fin 3) (Fin 3) K) = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xOdd, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem yOdd_mul_self : yOdd K * yOdd K = 1 := by
  apply Subtype.ext
  change (yOdd K : Matrix (Fin 3) (Fin 3) K) * (yOdd K : Matrix (Fin 3) (Fin 3) K) = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [yOdd, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem xOdd_mul_yOdd_eq : xOdd K * yOdd K = yOdd K * xOdd K := by
  apply Subtype.ext
  change (xOdd K : Matrix (Fin 3) (Fin 3) K) * (yOdd K : Matrix (Fin 3) (Fin 3) K) =
    (yOdd K : Matrix (Fin 3) (Fin 3) K) * (xOdd K : Matrix (Fin 3) (Fin 3) K)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xOdd, yOdd, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem xOdd_ne_one (h2 : (2 : K) ≠ 0) : xOdd K ≠ 1 := by
  intro h
  apply neg_one_ne_one K h2
  have h11 := congrFun (congrFun (congrArg (fun z : SL(3, K) =>
    (z : Matrix (Fin 3) (Fin 3) K)) h) 1) 1
  simpa [xOdd] using h11

theorem yOdd_ne_one (h2 : (2 : K) ≠ 0) : yOdd K ≠ 1 := by
  intro h
  apply neg_one_ne_one K h2
  have h00 := congrFun (congrFun (congrArg (fun z : SL(3, K) =>
    (z : Matrix (Fin 3) (Fin 3) K)) h) 0) 0
  simpa [yOdd] using h00

theorem xOdd_ne_yOdd (h2 : (2 : K) ≠ 0) : xOdd K ≠ yOdd K := by
  intro h
  apply neg_one_ne_one K h2
  have h00 := congrFun (congrFun (congrArg (fun z : SL(3, K) =>
    (z : Matrix (Fin 3) (Fin 3) K)) h) 0) 0
  have h00' : (1 : K) = -1 := by simpa [xOdd, yOdd] using h00
  exact h00'.symm

theorem cycMat_mul_xOdd : (cycMat (F := K) : Matrix (Fin 3) (Fin 3) K) *
    (xOdd K : Matrix (Fin 3) (Fin 3) K) =
    ((xOdd K * yOdd K : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * cycMat (F := K) := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMat, xOdd, yOdd, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem cycMat_mul_yOdd : (cycMat (F := K) : Matrix (Fin 3) (Fin 3) K) *
    (yOdd K : Matrix (Fin 3) (Fin 3) K) =
    (xOdd K : Matrix (Fin 3) (Fin 3) K) * cycMat (F := K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMat, xOdd, yOdd, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem exists_inspPair_cycSL_odd (h2 : (2 : K) ≠ 0) :
    ∃ S : Subgroup (SL(3, K)), InspPair 2 (Subgroup.zpowers (cycSL K)) S := by
  have hdx : cycSL K * xOdd K * (cycSL K)⁻¹ = xOdd K * yOdd K :=
    mul_inv_eq_of_mul_eq (cycMat_mul_xOdd K)
  have hdy : cycSL K * yOdd K * (cycSL K)⁻¹ = xOdd K :=
    mul_inv_eq_of_mul_eq (cycMat_mul_yOdd K)
  obtain ⟨S, hEa, hcard, hnorm, hcomm⟩ :=
    exists_klein_of_triple (xOdd_mul_self K) (yOdd_mul_self K) (xOdd_mul_yOdd_eq K)
      (xOdd_ne_one K h2) (yOdd_ne_one K h2) (xOdd_ne_yOdd K h2) hdx hdy
  refine ⟨S, IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num), hEa.1, ?_, hnorm, hcomm⟩
  intro hbot
  simp [hbot] at hcard

end Odd

section Even

variable (K : Type) [Field K] [CharP K 2]

def xEven : SL(3, K) :=
  Subtype.mk !![0, 1, 0; 1, 0, 0; 1, 1, 1]
    (by rw [Matrix.det_fin_three]; simp [CharTwo.neg_eq])

def yEven : SL(3, K) :=
  Subtype.mk !![0, 0, 1; 1, 1, 1; 1, 0, 0]
    (by rw [Matrix.det_fin_three]; simp [CharTwo.neg_eq])

theorem xEven_mul_self : xEven K * xEven K = 1 := by
  apply Subtype.ext
  change (xEven K : Matrix (Fin 3) (Fin 3) K) * (xEven K : Matrix (Fin 3) (Fin 3) K) = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xEven, Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

theorem yEven_mul_self : yEven K * yEven K = 1 := by
  apply Subtype.ext
  change (yEven K : Matrix (Fin 3) (Fin 3) K) * (yEven K : Matrix (Fin 3) (Fin 3) K) = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [yEven, Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

theorem xEven_mul_yEven_eq : xEven K * yEven K = yEven K * xEven K := by
  apply Subtype.ext
  change (xEven K : Matrix (Fin 3) (Fin 3) K) * (yEven K : Matrix (Fin 3) (Fin 3) K) =
    (yEven K : Matrix (Fin 3) (Fin 3) K) * (xEven K : Matrix (Fin 3) (Fin 3) K)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xEven, yEven, Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

theorem xEven_ne_one : xEven K ≠ 1 := by
  intro h
  have h00 := congrFun (congrFun (congrArg (fun z : SL(3, K) =>
    (z : Matrix (Fin 3) (Fin 3) K)) h) 0) 0
  have h00' : (0 : K) = 1 := by simpa [xEven] using h00
  exact zero_ne_one h00'

theorem yEven_ne_one : yEven K ≠ 1 := by
  intro h
  have h00 := congrFun (congrFun (congrArg (fun z : SL(3, K) =>
    (z : Matrix (Fin 3) (Fin 3) K)) h) 0) 0
  have h00' : (0 : K) = 1 := by simpa [yEven] using h00
  exact zero_ne_one h00'

theorem xEven_ne_yEven : xEven K ≠ yEven K := by
  intro h
  have h01 := congrFun (congrFun (congrArg (fun z : SL(3, K) =>
    (z : Matrix (Fin 3) (Fin 3) K)) h) 0) 1
  have h01' : (1 : K) = 0 := by simpa [xEven, yEven] using h01
  exact one_ne_zero h01'

theorem cycMat_mul_xEven : (cycMat (F := K) : Matrix (Fin 3) (Fin 3) K) *
    (xEven K : Matrix (Fin 3) (Fin 3) K) =
    ((xEven K * yEven K : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * cycMat (F := K) := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMat, xEven, yEven, Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

theorem cycMat_mul_yEven : (cycMat (F := K) : Matrix (Fin 3) (Fin 3) K) *
    (yEven K : Matrix (Fin 3) (Fin 3) K) =
    (xEven K : Matrix (Fin 3) (Fin 3) K) * cycMat (F := K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMat, xEven, yEven, Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

theorem exists_inspPair_cycSL_two :
    ∃ S : Subgroup (SL(3, K)), InspPair 2 (Subgroup.zpowers (cycSL K)) S := by
  have hdx : cycSL K * xEven K * (cycSL K)⁻¹ = xEven K * yEven K :=
    mul_inv_eq_of_mul_eq (cycMat_mul_xEven K)
  have hdy : cycSL K * yEven K * (cycSL K)⁻¹ = xEven K :=
    mul_inv_eq_of_mul_eq (cycMat_mul_yEven K)
  obtain ⟨S, hEa, hcard, hnorm, hcomm⟩ :=
    exists_klein_of_triple (xEven_mul_self K) (yEven_mul_self K) (xEven_mul_yEven_eq K)
      (xEven_ne_one K) (yEven_ne_one K) (xEven_ne_yEven K) hdx hdy
  refine ⟨S, IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num), hEa.1, ?_, hnorm, hcomm⟩
  intro hbot
  simp [hbot] at hcard

end Even

theorem cube_eq_one_of_no_root {K : Type} [Field K] (hω : ∀ c : K, c ^ 2 + c + 1 ≠ 0) :
    ∀ c : K, c ^ 3 = 1 → c = 1 := by
  intro c hc
  by_contra hc1
  apply hω c
  have h : (c - 1) * (c ^ 2 + c + 1) = 0 := by
    have e : (c - 1) * (c ^ 2 + c + 1) = c ^ 3 - 1 := by ring
    rw [e, hc, sub_self]
  exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hc1)

theorem center_SL3_eq_bot {K : Type} [Field K] (hcube : ∀ c : K, c ^ 3 = 1 → c = 1) :
    Subgroup.center SL(3, K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  rw [Subgroup.mem_bot]
  have hr1 : r = 1 := hcube r hr
  apply Subtype.ext
  rw [← hrA, hr1, map_one]
  rfl

theorem cycMat_cube {K : Type} [Field K] : cycMat (F := K) * cycMat * cycMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem cycMat_det {K : Type} [Field K] : (cycMat (F := K)).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [cycMat]

theorem cycMat_ne_scalar {K : Type} [Field K] (c : K) :
    cycMat (F := K) ≠ c • (1 : Matrix (Fin 3) (Fin 3) K) := by
  intro h
  have h02 := congrFun (congrFun h 0) 2
  have h02' : (1 : K) = 0 := by simpa [cycMat, Matrix.smul_apply] using h02
  exact one_ne_zero h02'

theorem inspPair_sl3_of_std {K : Type} [Field K] (h3 : (3 : K) ≠ 0)
    (hω : ∀ c : K, c ^ 2 + c + 1 ≠ 0)
    (hstd : ∃ S : Subgroup (SL(3, K)), InspPair 2 (Subgroup.zpowers (cycSL K)) S)
    (D : Subgroup (SL(3, K))) (hD : Nat.card D = 3) :
    ∃ U : Subgroup (SL(3, K)), InspPair 2 D U := by
  obtain ⟨d, hDd, hd3, hd1⟩ := exists_gen_of_card_three D hD
  have hcube : ∀ c : K, c ^ 3 = 1 → c = 1 := cube_eq_one_of_no_root hω
  have hmul3 : ∀ x : SL(3, K), x ^ 3 = 1 →
      (x : Matrix (Fin 3) (Fin 3) K) * x * x = 1 := by
    intro x hx
    have := congrArg (fun y : SL(3, K) => (y : Matrix (Fin 3) (Fin 3) K)) hx
    simpa [pow_succ] using this
  have hdns : ∀ c : K, (d : Matrix (Fin 3) (Fin 3) K) ≠
      c • (1 : Matrix (Fin 3) (Fin 3) K) := by
    intro c hc
    have h1 := hmul3 d hd3
    rw [hc] at h1
    have hc3 : c ^ 3 = 1 := by
      have h2 := congrFun (congrFun h1 0) 0
      have h2' : c * (c * c) = 1 := by
        simpa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_apply] using h2
      linear_combination h2'
    have hc1 : c = 1 := hcube c hc3
    apply hd1
    apply Subtype.ext
    rw [hc, hc1, one_smul]
    rfl
  obtain ⟨Q, hQ⟩ := exists_conj3 h3 hω (cycMat (F := K)) (d : Matrix (Fin 3) (Fin 3) K)
    cycMat_cube cycMat_det cycMat_ne_scalar (hmul3 d hd3) d.2 hdns
  obtain ⟨S, hS⟩ := hstd
  have hconj : conjSLnEquiv Q (cycSL K) = d := conjSLnEquiv_eq_of_mul_eq Q hQ
  have hconj' : (conjSLnEquiv Q).toMonoidHom (cycSL K) = d := hconj
  refine ⟨S.map (conjSLnEquiv Q).toMonoidHom, ?_⟩
  have h := hS.map (conjSLnEquiv Q)
  rw [MonoidHom.map_zpowers, hconj', ← hDd] at h
  exact h

end InspL3

theorem insp2L3_psl (G : Type) [Group G] [Finite G] (p f : ℕ) (hq : p ^ f % 3 = 2)
    (hL : LieModel G .PSL 3 p f) (D : Subgroup G) (hD : Nat.card D = 3) :
    ∃ U : Subgroup G, InspPair 2 D U := by
  have hadm := hL.admissible
  rcases hL with ⟨-, ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · have hp : p.Prime := hadm.1
    have hf : 1 ≤ f := hadm.2.1
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fintype K := Fintype.ofFinite K
    have hKc : CharP K p :=
      charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
    have hq' : Nat.card K % 3 = 2 := by rw [hK]; exact hq
    have hcube := cube_roots_trivial hq'
    have h3 : (3 : K) ≠ 0 := three_ne_zero_of_card_mod hf hK hq'
    have hω := no_root_of_cube_trivial h3 hcube
    let e₁ : G ≃* PSL(3, K) :=
      e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm
    let e₂ : PSL(3, K) ≃* SL(3, K) :=
      (QuotientGroup.quotientMulEquivOfEq (InspL3.center_SL3_eq_bot hcube)).trans
        QuotientGroup.quotientBot
    let e' : G ≃* SL(3, K) := e₁.trans e₂
    have hstd : ∃ S : Subgroup (SL(3, K)),
        InspPair 2 (Subgroup.zpowers (InspL3.cycSL K)) S := by
      by_cases hp2 : p = 2
      · subst hp2
        exact InspL3.exists_inspPair_cycSL_two K
      · exact InspL3.exists_inspPair_cycSL_odd K (by
          intro h2
          have h2' : ((2 : ℕ) : K) = 0 := by simpa using h2
          have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).1 h2'
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd))
    obtain ⟨U', hpair⟩ := InspL3.inspPair_sl3_of_std h3 hω hstd (D.map e'.toMonoidHom)
      (by rw [Subgroup.card_map_of_injective e'.injective, hD])
    exact ⟨U'.map e'.symm.toMonoidHom, InspPair.of_map_equiv e' hpair⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

end CFSG.LocalAnalysis.UniquenessCase.UCK
