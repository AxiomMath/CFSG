module

public import CFSG.RankThree.PartOne.K159.BorelConj
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData
public import TauCeti.LinearAlgebra.BilinearForm.Isometry
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.RankThree.PartOne.K159

open Matrix CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank

section Centralizer

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem mul_apply_sp (M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (a b : Fin 2 ⊕ Fin 2) :
    (M * N) a b = M a (.inl 0) * N (.inl 0) b + M a (.inl 1) * N (.inl 1) b +
      M a (.inr 0) * N (.inr 0) b + M a (.inr 1) * N (.inr 1) b := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

omit [CharP K 2] in
theorem blockMat_one_apply (C : Matrix (Fin 2) (Fin 2) K) :
    (∀ i j : Fin 2, blockMat (1 : Matrix (Fin 2) (Fin 2) K) C (.inl i) (.inl j) =
      (1 : Matrix (Fin 2) (Fin 2) K) i j) ∧
    (∀ i j : Fin 2, blockMat (1 : Matrix (Fin 2) (Fin 2) K) C (.inl i) (.inr j) = C i j) ∧
    (∀ i j : Fin 2, blockMat (1 : Matrix (Fin 2) (Fin 2) K) C (.inr i) (.inl j) = 0) ∧
    (∀ i j : Fin 2, blockMat (1 : Matrix (Fin 2) (Fin 2) K) C (.inr i) (.inr j) =
      (1 : Matrix (Fin 2) (Fin 2) K) i j) := by
  refine ⟨fun i j => rfl, fun i j => by simp [blockMat], fun i j => rfl, fun i j => ?_⟩
  simp [blockMat]

theorem eq_one_of_sq_eq_one_char_two {c : K} (hc : c ^ 2 = 1) : c = 1 := by
  have e : (c + 1) ^ 2 = c ^ 2 + 1 ^ 2 := CharTwo.add_sq c 1
  have h0 : (c + 1) ^ 2 = 0 := by
    rw [e, hc]
    simpa using CharTwo.add_self_eq_zero (1 : K)
  exact CharTwo.add_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h0)

theorem exists_noncomm_unipotent_sp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (x : StatedSp 2 K)
    (hx : orderOf x = p) : ∃ t ∈ unipotent 2 K, x * t ≠ t * x := by
  classical
  by_contra hcon
  push Not at hcon
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hM
  have hcommC : ∀ C : Matrix (Fin 2) (Fin 2) K, Cᵀ = C →
      M * blockMat 1 C = blockMat 1 C * M := by
    intro C hC
    obtain ⟨g, hgU, hg⟩ := exists_mem_unipotent (isUnitriangular_one (r := 2) (K := K)) hC
    have h1 := hcon g hgU
    have h2 := congrArg (fun y : StatedSp 2 K =>
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h1
    simpa [hg, hM] using h2
  have hH1 : (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : K))ᵀ = Matrix.single 0 0 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hH2 : (Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : K))ᵀ = Matrix.single 1 1 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hH3 : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K)ᵀ = !![0, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have c1 := hcommC _ hH1
  have c2 := hcommC _ hH2
  have c3 := hcommC _ hH3
  obtain ⟨hee1, hef1, hfe1, hff1⟩ := blockMat_one_apply (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : K))
  obtain ⟨hee2, hef2, hfe2, hff2⟩ := blockMat_one_apply (Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : K))
  obtain ⟨hee3, hef3, hfe3, hff3⟩ := blockMat_one_apply (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K)
  have e1 := congrFun (congrFun c1 (.inl 0)) (.inl 0)
  have e2 := congrFun (congrFun c1 (.inl 0)) (.inl 1)
  have e3 := congrFun (congrFun c1 (.inl 0)) (.inr 0)
  have e4 := congrFun (congrFun c1 (.inl 0)) (.inr 1)
  have e5 := congrFun (congrFun c1 (.inl 1)) (.inr 0)
  have e6 := congrFun (congrFun c2 (.inl 1)) (.inl 0)
  have e7 := congrFun (congrFun c2 (.inl 1)) (.inl 1)
  have e8 := congrFun (congrFun c2 (.inl 1)) (.inr 1)
  have e9 := congrFun (congrFun c2 (.inl 1)) (.inr 0)
  have e10 := congrFun (congrFun c2 (.inl 0)) (.inr 1)
  have e11 := congrFun (congrFun c3 (.inl 0)) (.inr 1)
  rw [mul_apply_sp, mul_apply_sp] at e1 e2 e3 e4 e5
  rw [mul_apply_sp, mul_apply_sp] at e6 e7 e8 e9 e10
  rw [mul_apply_sp, mul_apply_sp] at e11
  simp only [hee1, hef1, hfe1, hff1] at e1 e2 e3 e4 e5
  simp only [hee2, hef2, hfe2, hff2] at e6 e7 e8 e9 e10
  simp only [hee3, hef3, hff3] at e11
  simp at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
  set lam : K := M (.inl 0) (.inl 0) with hlam
  have df0 : M (.inr 0) (.inr 0) = lam := by linear_combination -e3
  have df1 : M (.inr 1) (.inr 1) = lam := by linear_combination -e11
  have de1 : M (.inl 1) (.inl 1) = lam := by linear_combination e8 - e11
  set N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := M - lam • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    with hN
  have hNe : ∀ (a : Fin 2 ⊕ Fin 2) (k : Fin 2), N a (.inl k) = 0 := by
    intro a k
    rcases a with i | i
    · fin_cases i <;> fin_cases k <;> simp [hN, e5, e10, de1, hlam]
    · fin_cases i <;> fin_cases k <;> simp [hN, e1, e2, e6, e7]
  have hNf : ∀ (l : Fin 2) (b : Fin 2 ⊕ Fin 2), N (.inr l) b = 0 := by
    intro l b
    rcases b with j | j
    · fin_cases l <;> fin_cases j <;> simp [hN, e1, e2, e6, e7]
    · fin_cases l <;> fin_cases j <;> simp [hN, e4, e9, df0, df1]
  have hNN : N * N = 0 := by
    ext a b
    rw [mul_apply_sp]
    simp [hNe, hNf]
  have hMsq : M * M = (lam ^ 2) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    have hMN : M = lam • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) + N := by
      rw [hN]
      abel
    have h2 : lam • N + lam • N = 0 := by
      ext a b
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
      exact CharTwo.add_self_eq_zero _
    calc M * M = (lam • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) + N) *
          (lam • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) + N) := by rw [← hMN]
      _ = (lam ^ 2) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) + (lam • N + lam • N) +
          N * N := by
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one,
          smul_smul, smul_add, sq]
        abel
      _ = (lam ^ 2) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
        rw [h2, hNN, add_zero, add_zero]
  have hxp : x ^ p = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hMp : M ^ p = 1 := by
    have := congrArg (fun y : StatedSp 2 K =>
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hxp
    simpa [hM] using this
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hMscal : M = ((lam ^ 2) ^ (k + 1)) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    calc M = M ^ (p + 1) := by rw [pow_succ, hMp, one_mul]
      _ = (M * M) ^ (k + 1) := by rw [hk, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul, sq]
      _ = ((lam ^ 2) ^ (k + 1)) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
        rw [hMsq, smul_pow, one_pow]
  have hsymp : M ∈ symplecticGroup (Fin 2) K := by
    have h1 : ((x : GL (Fin 2 ⊕ Fin 2) K)) ∈ TauCeti.GLSymplectic (Fin 2) K :=
      (SetLike.ext_iff.1 (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := 2) (K := K))
        (x : GL (Fin 2 ⊕ Fin 2) K)).1 x.2
    exact TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.1 h1
  have hν : (((lam ^ 2) ^ (k + 1)) ^ 2 : K) = 1 := by
    have hscal : Matrix.scalar (Fin 2 ⊕ Fin 2) ((lam ^ 2) ^ (k + 1)) ∈ symplecticGroup (Fin 2) K := by
      rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, ← hMscal]
      exact hsymp
    exact (CFSG.ClassicalGroups.Symplectic.scalar_mem_symplecticGroup_iff (by norm_num) _).1 hscal
  have hν1 : (lam ^ 2) ^ (k + 1) = 1 := eq_one_of_sq_eq_one_char_two hν
  have hM1 : M = 1 := by rw [hMscal, hν1, one_smul]
  have hx1 : x = 1 := Subtype.ext (Units.ext hM1)
  rw [hx1, orderOf_one] at hx
  exact hp.one_lt.ne hx

end Centralizer

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem index_borelSubgroup_two :
    (borelSubgroup 2 K).index = (Nat.card K + 1) ^ 2 * (Nat.card K ^ 2 + 1) := by
  have hSB : Nat.card (borelSubgroup 2 K) * (borelSubgroup 2 K).index =
      Nat.card (StatedSp 2 K) := (borelSubgroup 2 K).card_mul_index
  rw [card_borelSubgroup, card_statedSp] at hSB
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨a, ha⟩ : ∃ a, Nat.card K = a + 1 := ⟨Nat.card K - 1, by omega⟩
  rw [ha] at hSB ⊢
  rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)] at hSB
  have ha1 : 1 ≤ a := by omega
  have e1 : (a + 1) ^ (2 * 1) - 1 = a * (a + 2) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : (a + 1) ^ (2 * 2) - 1 = a * (a + 2) * ((a + 1) ^ 2 + 1) :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [e1, e2, Nat.add_sub_cancel] at hSB
  have hpos : 0 < (a + 1) ^ (2 ^ 2) * a ^ 2 := by positivity
  have key : ((a + 1) ^ (2 ^ 2) * a ^ 2) * (borelSubgroup 2 K).index =
      ((a + 1) ^ (2 ^ 2) * a ^ 2) * ((a + 2) ^ 2 * ((a + 1) ^ 2 + 1)) := by
    rw [hSB]
    ring
  calc (borelSubgroup 2 K).index = (a + 2) ^ 2 * ((a + 1) ^ 2 + 1) :=
        Nat.eq_of_mul_eq_mul_left hpos key
    _ = (a + 1 + 1) ^ 2 * ((a + 1) ^ 2 + 1) := by ring

theorem borelFactsGrp_statedSp_two {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1)
    (hp3 : 3 < p) : BorelFactsGrp p (StatedSp 2 K) := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨T, hT⟩ := exists_sylow_unipotent (K := K) 2 2
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hpB : p ∣ Nat.card (borelSubgroup 2 K) := by
    rw [card_borelSubgroup]
    exact Dvd.dvd.mul_left (dvd_pow hpq (by norm_num)) _
  have hpS : p ∣ Nat.card (StatedSp 2 K) := hpB.trans (Subgroup.card_subgroup_dvd_card _)
  have hBN : borelSubgroup 2 K ≤ Subgroup.normalizer (T : Subgroup (StatedSp 2 K)) := by
    rw [hT]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer unipotent_le_borelSubgroup).1
      unipotent_subgroupOf_borelSubgroup_normal
  have hidx : ¬ p ∣ (borelSubgroup 2 K).index := by
    rw [index_borelSubgroup_two]
    intro hdvd
    have h1 : ((Nat.card K : ℕ) : ZMod p) = 1 := by
      have := (ZMod.natCast_eq_zero_iff (Nat.card K - 1) p).2 hpq
      rw [Nat.cast_sub (by omega)] at this
      simpa [sub_eq_zero] using this
    have h2 := (ZMod.natCast_eq_zero_iff _ p).2 hdvd
    push_cast at h2
    rw [h1] at h2
    norm_num at h2
    have h3 : ((8 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    have h4 := (ZMod.natCast_eq_zero_iff 8 p).1 h3
    have h5 : p ∣ 2 ^ 3 := by simpa using h4
    have h6 := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h5)
    omega
  have hcent : ∀ x : StatedSp 2 K, orderOf x = p →
      ∃ t ∈ (T : Subgroup (StatedSp 2 K)), x * t ≠ t * x := by
    intro x hx
    rw [hT]
    exact exists_noncomm_unipotent_sp hp hp2 x hx
  exact BorelFactsGrp.of_borel hpS T hBN hidx hcent

end Main

section Abstract

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem nonempty_isometryGroup_mulEquiv_statedSp {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    {m : ℕ} (hdim : Module.finrank K V = 2 * m) :
    Nonempty (↥(TauCeti.BilinForm.isometryGroup B) ≃* StatedSp m K) := by
  obtain ⟨m', b, hm', hb⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis B hB hnd
  have hmm : m' = m := by omega
  subst hmm
  have hJ : (Matrix.J (Fin m') K) = fromBlocks 0 1 (-1) 0 := by
    rw [CFSG.ClassicalGroups.Symplectic.blueprintGram_eq_neg_J]
    ext i j
    simp [CharTwo.neg_eq]
  have hmap : (TauCeti.BilinForm.isometryGroup B).map
      (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv b).toMonoidHom =
      StatedSp m' K := by
    ext M
    rw [Subgroup.mem_map_equiv,
      CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometry_iff_matrix b,
      MulEquiv.apply_symm_apply, hb, hJ,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
  exact ⟨((CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv b).subgroupMap
    _).trans (MulEquiv.subgroupCongr hmap)⟩

end Abstract

end CFSG.RankThree.PartOne.K159
