module

public import CFSG.RankThree.PartTwo.Sec8.Hering611RSp62Model
public import CFSG.Quasithin.H13.L32NSp4S6

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611R

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.AGLEmbedding.KFactProofs.Sp62Local
open CFSG.Quasithin.H13
open CFSG.ComponentClassification.PresentationLocal

@[expose] def emb (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0;
    0, N 0 0, N 0 1, 0, N 0 3, N 0 2;
    0, N 1 0, N 1 1, 0, N 1 3, N 1 2;
    0, 0, 0, 1, 0, 0;
    0, N 3 0, N 3 1, 0, N 3 3, N 3 2;
    0, N 2 0, N 2 1, 0, N 2 3, N 2 2]

theorem emb_one : emb 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb]

set_option maxHeartbeats 1000000 in
theorem emb_mul (N N' : Matrix (Fin 4) (Fin 4) (ZMod 2)) : emb (N * N') = emb N * emb N' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [emb, Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four] <;> ring

theorem sympEq {N : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : N.transpose * antidiagGram * N = antidiagGram) (a b : Fin 4) :
    N 0 a * N 3 b + N 1 a * N 2 b + N 2 a * N 1 b + N 3 a * N 0 b = antidiagGram a b := by
  have := congrFun (congrFun h a) b
  simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, antidiagGram,
    Matrix.of_apply] at this
  simp at this
  simp only [antidiagGram, Matrix.of_apply]
  linear_combination this

theorem isoMat_emb {N : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : N.transpose * antidiagGram * N = antidiagGram) : IsoMat (emb N) := by
  have e := sympEq h
  have e00 : N 0 0 * N 3 0 + N 1 0 * N 2 0 + N 2 0 * N 1 0 + N 3 0 * N 0 0 = 0 := by
    simpa [antidiagGram] using e 0 0
  have e01 : N 0 0 * N 3 1 + N 1 0 * N 2 1 + N 2 0 * N 1 1 + N 3 0 * N 0 1 = 0 := by
    simpa [antidiagGram] using e 0 1
  have e02 : N 0 0 * N 3 2 + N 1 0 * N 2 2 + N 2 0 * N 1 2 + N 3 0 * N 0 2 = 0 := by
    simpa [antidiagGram] using e 0 2
  have e03 : N 0 0 * N 3 3 + N 1 0 * N 2 3 + N 2 0 * N 1 3 + N 3 0 * N 0 3 = 1 := by
    simpa [antidiagGram] using e 0 3
  have e10 : N 0 1 * N 3 0 + N 1 1 * N 2 0 + N 2 1 * N 1 0 + N 3 1 * N 0 0 = 0 := by
    simpa [antidiagGram] using e 1 0
  have e11 : N 0 1 * N 3 1 + N 1 1 * N 2 1 + N 2 1 * N 1 1 + N 3 1 * N 0 1 = 0 := by
    simpa [antidiagGram] using e 1 1
  have e12 : N 0 1 * N 3 2 + N 1 1 * N 2 2 + N 2 1 * N 1 2 + N 3 1 * N 0 2 = 1 := by
    simpa [antidiagGram] using e 1 2
  have e13 : N 0 1 * N 3 3 + N 1 1 * N 2 3 + N 2 1 * N 1 3 + N 3 1 * N 0 3 = 0 := by
    simpa [antidiagGram] using e 1 3
  have e20 : N 0 2 * N 3 0 + N 1 2 * N 2 0 + N 2 2 * N 1 0 + N 3 2 * N 0 0 = 0 := by
    simpa [antidiagGram] using e 2 0
  have e21 : N 0 2 * N 3 1 + N 1 2 * N 2 1 + N 2 2 * N 1 1 + N 3 2 * N 0 1 = 1 := by
    simpa [antidiagGram] using e 2 1
  have e22 : N 0 2 * N 3 2 + N 1 2 * N 2 2 + N 2 2 * N 1 2 + N 3 2 * N 0 2 = 0 := by
    simpa [antidiagGram] using e 2 2
  have e23 : N 0 2 * N 3 3 + N 1 2 * N 2 3 + N 2 2 * N 1 3 + N 3 2 * N 0 3 = 0 := by
    simpa [antidiagGram] using e 2 3
  have e30 : N 0 3 * N 3 0 + N 1 3 * N 2 0 + N 2 3 * N 1 0 + N 3 3 * N 0 0 = 1 := by
    simpa [antidiagGram] using e 3 0
  have e31 : N 0 3 * N 3 1 + N 1 3 * N 2 1 + N 2 3 * N 1 1 + N 3 3 * N 0 1 = 0 := by
    simpa [antidiagGram] using e 3 1
  have e32 : N 0 3 * N 3 2 + N 1 3 * N 2 2 + N 2 3 * N 1 2 + N 3 3 * N 0 2 = 0 := by
    simpa [antidiagGram] using e 3 2
  have e33 : N 0 3 * N 3 3 + N 1 3 * N 2 3 + N 2 3 * N 1 3 + N 3 3 * N 0 3 = 0 := by
    simpa [antidiagGram] using e 3 3
  unfold IsoMat
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [emb, KGCert.g22Form, Matrix.mul_apply, Fin.sum_univ_six]
  all_goals first
    | linear_combination e00
    | linear_combination e01
    | linear_combination e02
    | linear_combination e03
    | linear_combination e10
    | linear_combination e11
    | linear_combination e12
    | linear_combination e13
    | linear_combination e20
    | linear_combination e21
    | linear_combination e22
    | linear_combination e23
    | linear_combination e30
    | linear_combination e31
    | linear_combination e32
    | linear_combination e33

theorem emb_injective : Function.Injective emb := by
  intro N N' h
  ext a b
  have := congrFun (congrFun h (![1, 2, 5, 4] a)) (![1, 2, 5, 4] b)
  fin_cases a <;> fin_cases b <;> simpa [emb] using this

theorem emb_mul_S0 (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) : emb N * S0 = S0 * emb N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [emb, S0, Matrix.mul_apply, Fin.sum_univ_six]

theorem col_of_fixes {M : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (h0 : M.mulVec (Pi.single 0 1) = Pi.single 0 1)
    (h3 : M.mulVec (Pi.single 3 1) = Pi.single 3 1) :
    M 0 0 = 1 ∧ M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 3 0 = 0 ∧ M 4 0 = 0 ∧ M 5 0 = 0 ∧
      M 0 3 = 0 ∧ M 1 3 = 0 ∧ M 2 3 = 0 ∧ M 3 3 = 1 ∧ M 4 3 = 0 ∧ M 5 3 = 0 := by
  rw [Matrix.mulVec_single_one] at h0 h3
  have a0 := fun i => congrFun h0 i
  have a3 := fun i => congrFun h3 i
  simp [Pi.single_apply] at a0 a3
  exact ⟨by simpa using a0 0, by simpa using a0 1, by simpa using a0 2, by simpa using a0 3,
    by simpa using a0 4, by simpa using a0 5, by simpa using a3 0, by simpa using a3 1,
    by simpa using a3 2, by simpa using a3 3, by simpa using a3 4, by simpa using a3 5⟩

set_option maxHeartbeats 2000000 in
theorem exists_emb_of_fixes {M : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hM : IsoMat M)
    (h0 : M.mulVec (Pi.single 0 1) = Pi.single 0 1)
    (h3 : M.mulVec (Pi.single 3 1) = Pi.single 3 1) :
    ∃ N : Matrix (Fin 4) (Fin 4) (ZMod 2),
      N.transpose * antidiagGram * N = antidiagGram ∧ M = emb N := by
  obtain ⟨c00, c10, c20, c30, c40, c50, c03, c13, c23, c33, c43, c53⟩ := col_of_fixes h0 h3
  have I : ∀ p q : Fin 6, M 0 p * M 3 q + M 3 p * M 0 q + M 1 p * M 4 q + M 4 p * M 1 q +
      M 2 p * M 5 q + M 5 p * M 2 q = KGCert.g22Form p q := by
    intro p q
    have := congrFun (congrFun hM p) q
    simp only [IsoMat, Matrix.mul_apply, Fin.sum_univ_six, Matrix.transpose_apply] at this
    fin_cases p <;> fin_cases q <;> simp [KGCert.g22Form] at this ⊢ <;> linear_combination this
  have r01 : M 0 1 = 0 := by simpa [KGCert.g22Form, c03, c33, c13, c43, c23, c53] using I 3 1
  have r02 : M 0 2 = 0 := by simpa [KGCert.g22Form, c03, c33, c13, c43, c23, c53] using I 3 2
  have r04 : M 0 4 = 0 := by simpa [KGCert.g22Form, c03, c33, c13, c43, c23, c53] using I 3 4
  have r05 : M 0 5 = 0 := by simpa [KGCert.g22Form, c03, c33, c13, c43, c23, c53] using I 3 5
  have r31 : M 3 1 = 0 := by simpa [KGCert.g22Form, c00, c30, c10, c40, c20, c50] using I 0 1
  have r32 : M 3 2 = 0 := by simpa [KGCert.g22Form, c00, c30, c10, c40, c20, c50] using I 0 2
  have r34 : M 3 4 = 0 := by simpa [KGCert.g22Form, c00, c30, c10, c40, c20, c50] using I 0 4
  have r35 : M 3 5 = 0 := by simpa [KGCert.g22Form, c00, c30, c10, c40, c20, c50] using I 0 5
  refine ⟨Matrix.of fun a b => M (![1, 2, 5, 4] a) (![1, 2, 5, 4] b), ?_, ?_⟩
  · ext a b
    have := I (![1, 2, 5, 4] a) (![1, 2, 5, 4] b)
    fin_cases a <;> fin_cases b <;>
      simp [antidiagGram, Matrix.mul_apply, Fin.sum_univ_four, KGCert.g22Form, r01, r02, r04,
        r05, r31, r32, r34, r35] at this ⊢ <;> linear_combination this
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [emb, c00, c10, c20, c30, c40, c50, c03, c13, c23, c33, c43, c53, r01, r02, r04, r05,
        r31, r32, r34, r35]

theorem antidiagGram_mul_self : antidiagGram * antidiagGram = 1 := by
  unfold antidiagGram
  decide +kernel

@[expose] def embHom : sympFour →* H6 where
  toFun h := ofIso (emb (h.1 : Matrix (Fin 4) (Fin 4) (ZMod 2))) (isoMat_emb h.2)
  map_one' := by
    apply mat6_injective
    rw [mat6_ofIso, map_one]
    simpa using emb_one
  map_mul' h h' := by
    apply mat6_injective
    rw [map_mul, mat6_ofIso, mat6_ofIso, mat6_ofIso]
    simp [emb_mul]

theorem mat6_embHom (h : sympFour) :
    mat6 (embHom h) = emb (h.1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
  mat6_ofIso (emb (h.1 : Matrix (Fin 4) (Fin 4) (ZMod 2))) (isoMat_emb h.2)

theorem embHom_injective : Function.Injective embHom := by
  intro h h' e
  have := congrArg mat6 e
  rw [mat6_embHom, mat6_embHom] at this
  exact Subtype.ext (Units.ext (emb_injective this))

theorem embHom_mem_centralizer (h : sympFour) :
    embHom h ∈ Subgroup.centralizer ({s0} : Set H6) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply mat6_injective
  rw [map_mul, map_mul, mat6_embHom, mat6_s0]
  exact emb_mul_S0 _

theorem mem_range_embHom {g : H6} (h0 : act6 g (Pi.single 0 1) = Pi.single 0 1)
    (h3 : act6 g (Pi.single 3 1) = Pi.single 3 1) : g ∈ embHom.range := by
  obtain ⟨N, hN, hgN⟩ := exists_emb_of_fixes (mat6_isIso g) h0 h3
  have hl : (antidiagGram * N.transpose * antidiagGram) * N = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc N.transpose, hN,
      antidiagGram_mul_self]
  have hr : N * (antidiagGram * N.transpose * antidiagGram) = 1 := mul_eq_one_comm.1 hl
  let u : GL (Fin 4) (ZMod 2) := ⟨N, antidiagGram * N.transpose * antidiagGram, hr, hl⟩
  have hu : u ∈ sympFour := hN
  refine ⟨⟨u, hu⟩, ?_⟩
  apply mat6_injective
  rw [mat6_embHom]
  exact hgN.symm

noncomputable def embHomRangeEquiv : embHom.range ≃* Equiv.Perm (Fin 6) :=
  (MonoidHom.ofInjective embHom_injective).symm.trans CFSG.Quasithin.H13.Sp4Cert.sympFourEquiv

end CFSG.RankThree.PartTwo.Sec8.Hering611R
