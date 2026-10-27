module

public import CFSG.Milestones.ASVolI.A3L3.Sylow
public import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.ASVolI

open Matrix CFSG.RankThree.SubgroupLists CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts

variable {p : ℕ} {K : Type} [Field K]

theorem burnsideA315y_u3_exists_xyc (hU : UnitaryFieldData p 1 K) (hp2 : p ≠ 2) :
    ∃ x y cc : K, cc ^ 2 * (x ^ 2 + y ^ 2) = -1 ∧ hU.bar x = x ∧ hU.bar y = y ∧
      hU.bar cc = -cc := by
  haveI : Fact p.Prime := ⟨hU.prime⟩
  haveI := hU.finite
  haveI : CharP K p := hU.charP
  haveI : Fintype K := Fintype.ofFinite K
  have hp := hU.prime
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  obtain ⟨ν₀, hν₀⟩ := FiniteField.exists_nonsquare hchar
  have hν₀0 : ν₀ ≠ 0 := by
    rintro rfl
    exact hν₀ ⟨0, by ring⟩
  have heuler : ν₀ ^ (p / 2) = -1 := by
    rcases ZMod.pow_div_two_eq_neg_one_or_one (p := p) hν₀0 with h | h
    · exact absurd ((ZMod.euler_criterion p hν₀0).mpr h) hν₀
    · exact h
  obtain ⟨x₀, y₀, hxy₀⟩ := ZMod.sq_add_sq p (-ν₀⁻¹)
  set φ : ZMod p →+* K := ZMod.castHom (dvd_refl p) K with hφ
  obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := (hp.eq_two_or_odd'.resolve_left hp2)
  have hpk : p / 2 = k := by omega
  have hν0 : φ ν₀ ≠ 0 := (map_ne_zero φ).mpr hν₀0
  have hsq : IsSquare (φ ν₀) := by
    have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    rw [FiniteField.isSquare_iff hK2 hν0]
    have hcard : Fintype.card K = p ^ 2 := by
      rw [← Nat.card_eq_fintype_card, hU.card]
    have hdiv : p ^ 2 / 2 = (p - 1) * (k + 1) := by
      rw [hk]
      have : (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
      rw [this, Nat.add_sub_cancel]
      omega
    rw [hcard, hdiv, pow_mul, ← map_pow, ZMod.pow_card_sub_one_eq_one hν₀0, map_one, one_pow]
  obtain ⟨cc, hcc⟩ := hsq
  refine ⟨φ x₀, φ y₀, cc, ?_, ?_, ?_, ?_⟩
  · rw [sq cc, ← hcc, ← map_pow, ← map_pow, ← map_add, hxy₀, ← map_mul, mul_neg,
      mul_inv_cancel₀ hν₀0, map_neg, map_one]
  · rw [hU.bar_apply, pow_one, ← map_pow, ZMod.pow_card]
  · rw [hU.bar_apply, pow_one, ← map_pow, ZMod.pow_card]
  · rw [hU.bar_apply, pow_one, hk, pow_succ, pow_mul, sq, ← hcc, ← map_pow, ← hpk, heuler,
      map_neg, map_one, neg_one_mul]

@[expose] noncomputable def burnsideA315y_u3Mk (hU : UnitaryFieldData p 1 K)
    (A : Matrix (Fin 3) (Fin 3) K) (hA : (A.map hU.bar)ᵀ * A = 1) : ↥(unitaryIsom3 hU) :=
  ⟨⟨A, (A.map hU.bar)ᵀ, mul_eq_one_comm.mp hA, hA⟩, hA⟩

theorem burnsideA315y_u3Mk_val (hU : UnitaryFieldData p 1 K) (A : Matrix (Fin 3) (Fin 3) K)
    (hA : (A.map hU.bar)ᵀ * A = 1) :
    (((burnsideA315y_u3Mk hU A hA : ↥(unitaryIsom3 hU)) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = A :=
  rfl

theorem burnsideA315y_u3_mem (hU : UnitaryFieldData p 1 K) (g : ↥(unitaryIsom3 hU)) :
    ((((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).map hU.bar)ᵀ *
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 :=
  g.2

theorem burnsideA315y_u3_entry (hU : UnitaryFieldData p 1 K) (g : ↥(unitaryIsom3 hU))
    (i j : Fin 3) :
    hU.bar (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 i) *
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 j +
      hU.bar (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 i) *
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 j +
      hU.bar (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 i) *
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 j =
      (1 : Matrix (Fin 3) (Fin 3) K) i j := by
  have h := congrFun (congrFun (burnsideA315y_u3_mem hU g) i) j
  rw [Matrix.mul_apply, Fin.sum_univ_three] at h
  simpa using h

theorem burnsideA315y_u3_norm_det (hU : UnitaryFieldData p 1 K) (g : ↥(unitaryIsom3 hU)) :
    hU.bar (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det) *
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  have h := congrArg Matrix.det (burnsideA315y_u3_mem hU g)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det] at h
  exact h

theorem burnsideA315y_u3_scalar_mem (hU : UnitaryFieldData p 1 K) {μ : Kˣ}
    (hμ : hU.bar (μ : K) * μ = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) μ ∈ unitaryIsom3 hU := by
  rw [mem_unitaryIsom3, Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, Matrix.diagonal, hμ]

theorem burnsideA315y_u3_dgl_mem (hU : UnitaryFieldData p 1 K) {s : Kˣ}
    (hs : hU.bar (s : K) * s = 1) : burnsideA315y_dgl s ∈ unitaryIsom3 hU := by
  rw [mem_unitaryIsom3, burnsideA315y_dgl_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, blkMat, hs]

theorem burnsideA315y_u3_blkMat_conjTr (hU : UnitaryFieldData p 1 K)
    (A : Matrix (Fin 2) (Fin 2) K) :
    ((blkMat A 1).map hU.bar)ᵀ = blkMat ((A.map hU.bar)ᵀ) 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkMat]

theorem burnsideA315y_u3_blkMat_mem (hU : UnitaryFieldData p 1 K) {A : Matrix (Fin 2) (Fin 2) K}
    (hA : (A.map hU.bar)ᵀ * A = 1) : ((blkMat A 1).map hU.bar)ᵀ * blkMat A 1 = 1 := by
  rw [burnsideA315y_u3_blkMat_conjTr, blkMat_mul, hA, mul_one, blkMat_one]

theorem burnsideA315y_u3_negDiag3_mem (hU : UnitaryFieldData p 1 K) :
    negDiag3 K ∈ unitaryIsom3 hU := by
  rw [mem_unitaryIsom3, coe_negDiag3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal]

theorem burnsideA315y_u3_qa_unitary (hU : UnitaryFieldData p 1 K) :
    ((burnsideA315y_qa K).map hU.bar)ᵀ * burnsideA315y_qa K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideA315y_qa, Matrix.mul_apply, Fin.sum_univ_two]

theorem burnsideA315y_u3_qb_unitary (hU : UnitaryFieldData p 1 K) {x y cc : K}
    (hdet : cc ^ 2 * (x ^ 2 + y ^ 2) = -1) (hx : hU.bar x = x) (hy : hU.bar y = y)
    (hc : hU.bar cc = -cc) :
    ((cc • burnsideA315y_qb x y).map hU.bar)ᵀ * (cc • burnsideA315y_qb x y) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideA315y_qb, Matrix.mul_apply, Fin.sum_univ_two, hx, hy, hc] <;>
    first | ring1 | linear_combination (-1 : K) * hdet

theorem burnsideA315y_u3_ker (hU : UnitaryFieldData p 1 K) (g : ↥(unitaryIsom3 hU)) :
    psuConj hU g = 1 ↔
      ∃ μ : Kˣ, (g : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) μ := by
  constructor
  · intro hg
    obtain ⟨-, c, -, hc⟩ :=
      eq_one_of_psuConj_mul_psuField_eq_one g 1 (by rw [map_one, mul_one, hg])
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    ext x
    induction x using QuotientGroup.induction_on with
    | H y =>
      rw [psuConj_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [coe_suConj, Subgroup.coe_inv, hc, ← (commute_scalar c (y : GL (Fin 3) K)).eq,
        mul_inv_cancel_right]

section Model

variable (hU : UnitaryFieldData p 1 K) [Finite K] (two_ne : (2 : K) ≠ 0) {x y cc : K}
  (hdet : cc ^ 2 * (x ^ 2 + y ^ 2) = -1) (hx : hU.bar x = x) (hy : hU.bar y = y)
  (hc : hU.bar cc = -cc)

@[expose] noncomputable def burnsideA315y_u3zh : ↥(unitaryIsom3 hU) :=
  ⟨negDiag3 K, burnsideA315y_u3_negDiag3_mem hU⟩

@[expose] noncomputable def burnsideA315y_u3Da : ↥(unitaryIsom3 hU) :=
  burnsideA315y_u3Mk hU (blkMat (burnsideA315y_qa K) 1)
    (burnsideA315y_u3_blkMat_mem hU (burnsideA315y_u3_qa_unitary hU))

@[expose] noncomputable def burnsideA315y_u3Db : ↥(unitaryIsom3 hU) :=
  burnsideA315y_u3Mk hU (blkMat (cc • burnsideA315y_qb x y) 1)
    (burnsideA315y_u3_blkMat_mem hU (burnsideA315y_u3_qb_unitary hU hdet hx hy hc))

@[expose] noncomputable def burnsideA315y_u3Model :
    burnsideA315y_Model K (MulAut (unitaryPSU hU 3)) :=
  burnsideA315y_Model.ofData (unitaryIsom3 hU) (psuConj hU) (burnsideA315y_u3_ker hU)
    (burnsideA315y_u3zh hU) rfl x y cc hdet (burnsideA315y_u3Da hU)
    (burnsideA315y_u3Db hU hdet hx hy hc) rfl rfl two_ne

theorem burnsideA315y_u3_hS₀ :
    ¬ 2 ∣ (burnsideA315y_u3Model hU two_ne hdet hx hy hc).S₀.relIndex
      (burnsideA315y_u3Model hU two_ne hdet hx hy hc).C₁ :=
  burnsideA315y_Model.ofData_relIndex _ _ _ _ _ _ _ _ _ _ _ _ _ _

end Model

end CFSG.ASVolI
