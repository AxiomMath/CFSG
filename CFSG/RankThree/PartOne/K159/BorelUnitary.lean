module

public import CFSG.RankThree.PartOne.K159.BorelConj
public import CFSG.ClassicalGroups.UnitaryFlag.Triangular
import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow

public section

namespace CFSG.RankThree.PartOne.K159

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

section Centralizer

variable {f : ℕ} {E : Type} [Field E] (h : UnitaryFieldData 2 f E)

theorem barInvT_one : barInvT h (1 : Matrix (Fin 2) (Fin 2) E) = 1 := by
  rw [barInvT, Matrix.map_one _ (map_zero _) (map_one _), inv_one, transpose_one]

theorem mul_apply_hyp (M N : Matrix (HypIndex 2 0) (HypIndex 2 0) E) (a b : HypIndex 2 0) :
    (M * N) a b = M a (.inl 0) * N (.inl 0) b + M a (.inl 1) * N (.inl 1) b +
      M a (.inr (.inr 0)) * N (.inr (.inr 0)) b + M a (.inr (.inr 1)) * N (.inr (.inr 1)) b := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem exists_unitriangular_evenMat_one {C : Matrix (Fin 2) (Fin 2) E}
    (hC : C + (C.map h.bar)ᵀ = 0) :
    ∃ g ∈ hypUnitriangular h 2 0,
      ((g : GL (HypIndex 2 0) E) : Matrix (HypIndex 2 0) (HypIndex 2 0) E) = evenMat h 1 C :=
  (exists_mem_hypUnitriangular_even_iff (h := h) (evenMat h 1 C)).2
    ⟨1, C, ⟨blockTriangular_one, fun i => by simp⟩, hC, rfl⟩

theorem evenMat_one_apply (C : Matrix (Fin 2) (Fin 2) E) :
    (∀ i j : Fin 2, evenMat h 1 C (.inl i) (.inl j) = (1 : Matrix (Fin 2) (Fin 2) E) i j) ∧
    (∀ i j : Fin 2, evenMat h 1 C (.inl i) (.inr (.inr j)) = C i j) ∧
    (∀ i j : Fin 2, evenMat h 1 C (.inr (.inr i)) (.inl j) = 0) ∧
    (∀ i j : Fin 2, evenMat h 1 C (.inr (.inr i)) (.inr (.inr j)) =
      (1 : Matrix (Fin 2) (Fin 2) E) i j) := by
  refine ⟨fun i j => rfl, fun i j => by simp [evenMat], fun i j => rfl, fun i j => ?_⟩
  simp [evenMat, barInvT_one]

omit h in
theorem eq_one_of_pow_four_eq_one [CharP E 2] {c : E} (hc : c ^ 4 = 1) : c = 1 := by
  have e : (c + 1) ^ 4 = c ^ 4 + 1 := by
    calc (c + 1) ^ 4 = ((c + 1) ^ 2) ^ 2 := by ring
      _ = (c ^ 2 + 1 ^ 2) ^ 2 := by rw [CharTwo.add_sq]
      _ = (c ^ 2) ^ 2 + (1 ^ 2) ^ 2 := CharTwo.add_sq _ _
      _ = c ^ 4 + 1 := by ring
  have h4 : (c + 1) ^ 4 = 0 := by
    rw [e, hc]
    exact CharTwo.add_self_eq_zero 1
  exact CharTwo.add_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h4)

theorem exists_noncomm_hypUnitriangular {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (x : hypSU h 2 0)
    (hx : orderOf x = p) : ∃ t ∈ hypUnitriangular h 2 0, x * t ≠ t * x := by
  classical
  have hchar : CharP E 2 := h.charP
  have hfinite : Finite E := h.finite
  by_contra hcon
  push Not at hcon
  set M : Matrix (HypIndex 2 0) (HypIndex 2 0) E :=
    ((x : GL (HypIndex 2 0) E) : Matrix (HypIndex 2 0) (HypIndex 2 0) E) with hM
  have hcommC : ∀ C : Matrix (Fin 2) (Fin 2) E, C + (C.map h.bar)ᵀ = 0 →
      M * evenMat h 1 C = evenMat h 1 C * M := by
    intro C hC
    obtain ⟨g, hgU, hg⟩ := exists_unitriangular_evenMat_one h hC
    have h1 := hcon g hgU
    have h2 := congrArg (fun y : hypSU h 2 0 =>
      ((y : GL (HypIndex 2 0) E) : Matrix (HypIndex 2 0) (HypIndex 2 0) E)) h1
    simpa [hg, hM] using h2
  have hH1 : (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : E)) +
      ((Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : E)).map h.bar)ᵀ = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]
  have hH2 : (Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : E)) +
      ((Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : E)).map h.bar)ᵀ = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]
  have hH3 : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) +
      ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E).map h.bar)ᵀ = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]
  have c1 := hcommC _ hH1
  have c2 := hcommC _ hH2
  have c3 := hcommC _ hH3
  obtain ⟨hee1, hef1, hfe1, hff1⟩ :=
    evenMat_one_apply h (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : E))
  obtain ⟨hee2, hef2, hfe2, hff2⟩ :=
    evenMat_one_apply h (Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : E))
  obtain ⟨hee3, hef3, hfe3, hff3⟩ := evenMat_one_apply h (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E)
  have e1 := congrFun (congrFun c1 (.inl 0)) (.inl 0)
  have e2 := congrFun (congrFun c1 (.inl 0)) (.inl 1)
  have e3 := congrFun (congrFun c1 (.inl 0)) (.inr (.inr 0))
  have e4 := congrFun (congrFun c1 (.inl 0)) (.inr (.inr 1))
  have e5 := congrFun (congrFun c1 (.inl 1)) (.inr (.inr 0))
  have e6 := congrFun (congrFun c2 (.inl 1)) (.inl 0)
  have e7 := congrFun (congrFun c2 (.inl 1)) (.inl 1)
  have e8 := congrFun (congrFun c2 (.inl 1)) (.inr (.inr 1))
  have e9 := congrFun (congrFun c2 (.inl 1)) (.inr (.inr 0))
  have e10 := congrFun (congrFun c2 (.inl 0)) (.inr (.inr 1))
  have e11 := congrFun (congrFun c3 (.inl 0)) (.inr (.inr 1))
  rw [mul_apply_hyp, mul_apply_hyp] at e1 e2 e3 e4 e5
  rw [mul_apply_hyp, mul_apply_hyp] at e6 e7 e8 e9 e10
  rw [mul_apply_hyp, mul_apply_hyp] at e11
  simp only [hee1, hef1, hfe1, hff1] at e1 e2 e3 e4 e5
  simp only [hee2, hef2, hfe2, hff2] at e6 e7 e8 e9 e10
  simp only [hee3, hef3, hff3] at e11
  simp at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
  set lam : E := M (.inl 0) (.inl 0) with hlam
  have df0 : M (.inr (.inr 0)) (.inr (.inr 0)) = lam := by linear_combination -e3
  have df1 : M (.inr (.inr 1)) (.inr (.inr 1)) = lam := by linear_combination -e11
  have de1 : M (.inl 1) (.inl 1) = lam := by linear_combination e8 - e11
  set N : Matrix (HypIndex 2 0) (HypIndex 2 0) E := M - lam • (1 : Matrix (HypIndex 2 0) (HypIndex 2 0) E)
    with hN
  have hNe : ∀ (a : HypIndex 2 0) (k : Fin 2), N a (.inl k) = 0 := by
    intro a k
    rcases a with i | i | i
    · fin_cases i <;> fin_cases k <;> simp [hN, e5, e10, de1, hlam]
    · exact i.elim0
    · fin_cases i <;> fin_cases k <;> simp [hN, e1, e2, e6, e7]
  have hNf : ∀ (l : Fin 2) (b : HypIndex 2 0), N (.inr (.inr l)) b = 0 := by
    intro l b
    rcases b with j | j | j
    · fin_cases l <;> fin_cases j <;> simp [hN, e1, e2, e6, e7]
    · exact j.elim0
    · fin_cases l <;> fin_cases j <;> simp [hN, e4, e9, df0, df1]
  have hNN : N * N = 0 := by
    ext a b
    rw [mul_apply_hyp]
    simp [hNe, hNf]
  have hMsq : M * M = (lam ^ 2) • (1 : Matrix (HypIndex 2 0) (HypIndex 2 0) E) := by
    have hMN : M = lam • (1 : Matrix (HypIndex 2 0) (HypIndex 2 0) E) + N := by
      rw [hN]
      abel
    have h2 : lam • N + lam • N = 0 := by
      ext a b
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
      exact CharTwo.add_self_eq_zero _
    calc M * M = (lam • (1 : Matrix (HypIndex 2 0) (HypIndex 2 0) E) + N) *
          (lam • (1 : Matrix (HypIndex 2 0) (HypIndex 2 0) E) + N) := by rw [← hMN]
      _ = (lam ^ 2) • (1 : Matrix (HypIndex 2 0) (HypIndex 2 0) E) + (lam • N + lam • N) + N * N := by
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one,
          smul_smul, smul_add, sq]
        abel
      _ = (lam ^ 2) • (1 : Matrix (HypIndex 2 0) (HypIndex 2 0) E) := by rw [h2, hNN, add_zero, add_zero]
  have hxp : x ^ p = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hMp : M ^ p = 1 := by
    have := congrArg (fun y : hypSU h 2 0 =>
      ((y : GL (HypIndex 2 0) E) : Matrix (HypIndex 2 0) (HypIndex 2 0) E)) hxp
    simpa [hM] using this
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hMscal : M = ((lam ^ 2) ^ (k + 1)) • (1 : Matrix (HypIndex 2 0) (HypIndex 2 0) E) := by
    calc M = M ^ (p + 1) := by rw [pow_succ, hMp, one_mul]
      _ = (M * M) ^ (k + 1) := by rw [hk, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul, sq]
      _ = ((lam ^ 2) ^ (k + 1)) • (1 : Matrix (HypIndex 2 0) (HypIndex 2 0) E) := by
        rw [hMsq, smul_pow, one_pow]
  have hdet : M.det = 1 := (mem_hypSU.mp x.2).2
  have hν : ((lam ^ 2) ^ (k + 1)) ^ 4 = 1 := by
    rw [hMscal, Matrix.det_smul, Matrix.det_one, mul_one] at hdet
    simpa using hdet
  have hν1 : (lam ^ 2) ^ (k + 1) = 1 := eq_one_of_pow_four_eq_one hν
  have hM1 : M = 1 := by rw [hMscal, hν1, one_smul]
  have hx1 : x = 1 := Subtype.ext (Units.ext hM1)
  rw [hx1, orderOf_one] at hx
  exact hp.one_lt.ne hx

end Centralizer

section Main

variable {f : ℕ} {E : Type} [Field E] (h : UnitaryFieldData 2 f E)

theorem card_hypBorel_four :
    Nat.card (hypBorel h 2 0) = (2 ^ f) ^ 6 * (((2 ^ f) ^ 2 - 1) * (2 ^ f - 1)) := by
  have hfinite := h.finite
  obtain ⟨hU, -⟩ := unitary_order_and_Sylow h (r := 2) (ε := 0) (by norm_num) (by norm_num)
  have hle := hypUnitriangular_le_hypBorel h (r := 2) (ε := 0)
  have h1 : Nat.card ((hypUnitriangular h 2 0).subgroupOf (hypBorel h 2 0)) *
      ((hypUnitriangular h 2 0).subgroupOf (hypBorel h 2 0)).index = Nat.card (hypBorel h 2 0) :=
    ((hypUnitriangular h 2 0).subgroupOf (hypBorel h 2 0)).card_mul_index
  have h2 : Nat.card ((hypUnitriangular h 2 0).subgroupOf (hypBorel h 2 0)) =
      Nat.card (hypUnitriangular h 2 0) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h3 : ((hypUnitriangular h 2 0).subgroupOf (hypBorel h 2 0)).index =
      Nat.card (hypDiagHom h 2 0 (Nat.zero_le 1)).range :=
    card_quotient_hypUnitriangular (h := h) (r := 2) (Nat.zero_le 1)
  rw [range_hypDiagHom_even, card_evenDiagGroup (h := h) (r := 2) (by norm_num)] at h3
  have hq : 2 ≤ 2 ^ f := by
    have := h.one_le
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) this
  have hdiv : ((2 ^ f) ^ 2 - 1) ^ 2 / (2 ^ f + 1) = ((2 ^ f) ^ 2 - 1) * (2 ^ f - 1) := by
    obtain ⟨a, ha⟩ : ∃ a, 2 ^ f = a + 1 := ⟨2 ^ f - 1, by omega⟩
    rw [ha]
    have e1 : (a + 1) ^ 2 - 1 = a * (a + 2) := Nat.sub_eq_of_eq_add (by ring)
    rw [e1, Nat.add_sub_cancel]
    apply Nat.div_eq_of_eq_mul_left (by omega)
    ring
  rw [← h1, h2, hU, h3, hdiv]

theorem index_hypBorel_four :
    (hypBorel h 2 0).index = ((2 ^ f) ^ 3 + 1) * (2 ^ f + 1) * ((2 ^ f) ^ 2 + 1) := by
  have hfinite := h.finite
  obtain ⟨-, -, -, -, -, hS, -⟩ :=
    unitary_order_and_Sylow h (r := 2) (ε := 0) (by norm_num) (by norm_num)
  have hSB : Nat.card (hypBorel h 2 0) * (hypBorel h 2 0).index = Nat.card (hypSU h 2 0) :=
    (hypBorel h 2 0).card_mul_index
  have hB := card_hypBorel_four h
  have hq : 2 ≤ 2 ^ f := by
    have := h.one_le
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) this
  have e24 : Finset.Icc 2 (2 * 2 + 0) = {2, 3, 4} := by decide
  rw [e24] at hS
  simp [Finset.prod_insert] at hS
  have hq1 : 1 ≤ 2 ^ f := by omega
  have hq2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hB' : (Nat.card (hypBorel h 2 0) : ℤ) =
      ((2 : ℤ) ^ f) ^ 6 * ((((2 : ℤ) ^ f) ^ 2 - 1) * ((2 : ℤ) ^ f - 1)) := by
    rw [hB]
    push_cast [Nat.cast_sub hq1, Nat.cast_sub hq2]
    ring
  have hSB' : (Nat.card (hypBorel h 2 0) : ℤ) * ((hypBorel h 2 0).index : ℤ) =
      Nat.card (hypSU h 2 0) := by exact_mod_cast hSB
  rw [hB', hS] at hSB'
  have hQ2 : (2 : ℤ) ≤ (2 : ℤ) ^ f := by exact_mod_cast hq
  set Q : ℤ := (2 : ℤ) ^ f with hQ
  have hne : Q ^ 6 * ((Q ^ 2 - 1) * (Q - 1)) ≠ 0 := by
    have h1 : 0 < Q - 1 := by linarith
    have h2 : 0 < Q ^ 2 - 1 := by nlinarith
    have h3 : 0 < Q := by linarith
    positivity
  have key : (Q ^ 6 * ((Q ^ 2 - 1) * (Q - 1))) * ((hypBorel h 2 0).index : ℤ) =
      (Q ^ 6 * ((Q ^ 2 - 1) * (Q - 1))) * ((Q ^ 3 + 1) * (Q + 1) * (Q ^ 2 + 1)) := by
    rw [hSB']
    ring
  have := mul_left_cancel₀ hne key
  rw [hQ] at this
  exact_mod_cast this

theorem borelFactsGrp_hypSU_four {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f - 1) (hp3 : 3 < p) :
    BorelFactsGrp p (hypSU h 2 0) := by
  have hfinite := h.finite
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, ⟨T, hT⟩, -⟩ :=
    unitary_order_and_Sylow h (r := 2) (ε := 0) (by norm_num) (by norm_num)
  have hq : 2 ≤ 2 ^ f := by
    have := h.one_le
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) this
  have hpB : p ∣ Nat.card (hypBorel h 2 0) := by
    rw [card_hypBorel_four h]
    refine Dvd.dvd.mul_left (Dvd.dvd.mul_left hpq _) _
  have hpS : p ∣ Nat.card (hypSU h 2 0) := hpB.trans (Subgroup.card_subgroup_dvd_card _)
  have hBN : hypBorel h 2 0 ≤ Subgroup.normalizer (T : Subgroup (hypSU h 2 0)) := by
    rw [hT]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (hypUnitriangular_le_hypBorel h)).1
      (normal_hypUnitriangular (Nat.zero_le 1))
  have hidx : ¬ p ∣ (hypBorel h 2 0).index := by
    rw [index_hypBorel_four h]
    intro hdvd
    have h1 : ((2 ^ f : ℕ) : ZMod p) = 1 := by
      have := (ZMod.natCast_eq_zero_iff (2 ^ f - 1) p).2 hpq
      rw [Nat.cast_sub (by omega)] at this
      simpa [sub_eq_zero] using this
    have h2 := (ZMod.natCast_eq_zero_iff _ p).2 hdvd
    push_cast at h1 h2
    rw [h1] at h2
    norm_num at h2
    have h3 : ((8 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    have h4 := (ZMod.natCast_eq_zero_iff 8 p).1 h3
    have h5 : p ∣ 2 ^ 3 := by simpa using h4
    have h6 := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h5)
    omega
  have hcent : ∀ x : hypSU h 2 0, orderOf x = p →
      ∃ t ∈ (T : Subgroup (hypSU h 2 0)), x * t ≠ t * x := by
    intro x hx
    rw [hT]
    exact exists_noncomm_hypUnitriangular h hp hp2 x hx
  exact BorelFactsGrp.of_borel hpS T hBN hidx hcent

end Main

end CFSG.RankThree.PartOne.K159
