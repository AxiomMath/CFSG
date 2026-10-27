module

public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenTorus
public import CFSG.Assembly.Defs
public import TauCeti.LinearAlgebra.Matrix.Diagonal

public section

namespace CFSG.StandardType.SuSplitRootGen

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  Multiplicative

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {n r ε p : ℕ} {K : Type} [Field K]

private theorem ne_inv_self_of_isPrimitiveRoot {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime)
    (hp2 : p ≠ 2) : ζ ≠ ζ⁻¹ := by
  intro h
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have h2 : ζ ^ 2 = 1 := by
    have hmul : ζ * ζ = 1 := by
      simpa only [← h] using mul_inv_cancel₀ hζ0
    simpa [pow_two] using hmul
  have hdvd : p ∣ 2 := (hζ.pow_eq_one_iff_dvd 2).mp h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact hp.ne_one h1
  · exact hp2 h1

private theorem exists_splitEntries_ne {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime)
    (hp2 : p ≠ 2) {i j : Fin r} (hij : i ≠ j) (hε : ε ≤ 1) {a b : HypIndex r ε}
    (hab : a ≠ b)
    (hE1 : ¬ (a = .inl i ∧ b = .inl j)) (hE2 : ¬ (a = .inl j ∧ b = .inl i))
    (hF1 : ¬ (a = .inr (.inr i) ∧ b = .inr (.inr j)))
    (hF2 : ¬ (a = .inr (.inr j) ∧ b = .inr (.inr i))) :
    ∃ t : Fin r → ZMod p, t i = t j ∧
      splitEntries (ε := ε) ζ t a ≠ splitEntries (ε := ε) ζ t b := by
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have hζinv : ζ ≠ ζ⁻¹ := ne_inv_self_of_isPrimitiveRoot hζ hp hp2
  have hζinv1 : ζ⁻¹ ≠ 1 := by simpa [inv_eq_one] using hζ1
  let T0 : Fin r → ZMod p := Pi.single i 1 + Pi.single j 1
  have hT0i : T0 i = 1 := by
    simp [T0, Pi.single_eq_same, hij]
  have hT0j : T0 j = 1 := by
    simp [T0, Pi.single_eq_same, hij]
  have hT0 : T0 i = T0 j := by rw [hT0i, hT0j]
  have hT0_out : ∀ m, m ≠ i → m ≠ j → T0 m = 0 := by
    intro m hmi hmj
    simp [T0, Pi.single_eq_of_ne hmi, Pi.single_eq_of_ne hmj]
  have hT0_ei : splitEntries (ε := ε) ζ T0 (.inl i) = ζ := by
    simp [splitEntries, hT0i, ZMod.val_one]
  have hT0_ej : splitEntries (ε := ε) ζ T0 (.inl j) = ζ := by
    simp [splitEntries, hT0j, ZMod.val_one]
  have hT0_fi : splitEntries (ε := ε) ζ T0 (.inr (.inr i)) = ζ⁻¹ := by
    simp [splitEntries, hT0i, ZMod.val_one]
  have hT0_fj : splitEntries (ε := ε) ζ T0 (.inr (.inr j)) = ζ⁻¹ := by
    simp [splitEntries, hT0j, ZMod.val_one]
  have hT0_e_out : ∀ m, m ≠ i → m ≠ j → splitEntries (ε := ε) ζ T0 (.inl m) = 1 := by
    intro m hmi hmj
    simp [splitEntries, hT0_out m hmi hmj]
  have hT0_f_out : ∀ m, m ≠ i → m ≠ j → splitEntries (ε := ε) ζ T0 (.inr (.inr m)) = 1 := by
    intro m hmi hmj
    simp [splitEntries, hT0_out m hmi hmj]
  have hT0_z : ∀ l, splitEntries (ε := ε) ζ T0 (.inr (.inl l)) = 1 := fun _ => rfl
  have hTk_fix : ∀ m, m ≠ i → m ≠ j →
      (Pi.single m (1 : ZMod p) : Fin r → ZMod p) i =
        (Pi.single m (1 : ZMod p) : Fin r → ZMod p) j := by
    intro m hmi hmj
    simp [Pi.single_eq_of_ne (Ne.symm hmi), Pi.single_eq_of_ne (Ne.symm hmj)]
  have hTk_e_self : ∀ m,
      splitEntries (ε := ε) ζ (Pi.single m (1 : ZMod p) : Fin r → ZMod p) (.inl m) = ζ := by
    intro m
    simp [splitEntries, ZMod.val_one]
  have hTk_f_self : ∀ m,
      splitEntries (ε := ε) ζ (Pi.single m (1 : ZMod p) : Fin r → ZMod p) (.inr (.inr m)) =
        ζ⁻¹ := by
    intro m
    simp [splitEntries, ZMod.val_one]
  have hTk_e_out : ∀ m n, n ≠ m →
      splitEntries (ε := ε) ζ (Pi.single m (1 : ZMod p) : Fin r → ZMod p) (.inl n) = 1 := by
    intro m n hnm
    simp [splitEntries, Pi.single_eq_of_ne hnm]
  have hTk_f_out : ∀ m n, n ≠ m →
      splitEntries (ε := ε) ζ (Pi.single m (1 : ZMod p) : Fin r → ZMod p) (.inr (.inr n)) = 1 := by
    intro m n hnm
    simp [splitEntries, Pi.single_eq_of_ne hnm]
  have hTk_z : ∀ m l,
      splitEntries (ε := ε) ζ (Pi.single m (1 : ZMod p) : Fin r → ZMod p) (.inr (.inl l)) = 1 :=
    fun _ _ => rfl
  rcases a with a | k | a <;> rcases b with b | l | b
  ·
    by_cases hai : a = i
    · by_cases hbj : b = j
      · exact (hE1 ⟨by rw [hai], by rw [hbj]⟩).elim
      by_cases hbi : b = i
      · exact (hab (by rw [hai, hbi])).elim
      refine ⟨T0, hT0, ?_⟩
      rw [hai, hT0_ei, hT0_e_out b hbi hbj]
      exact hζ1
    · by_cases haj : a = j
      · by_cases hbi : b = i
        · exact (hE2 ⟨by rw [haj], by rw [hbi]⟩).elim
        by_cases hbj : b = j
        · exact (hab (by rw [haj, hbj])).elim
        refine ⟨T0, hT0, ?_⟩
        rw [haj, hT0_ej, hT0_e_out b hbi hbj]
        exact hζ1
      · by_cases hba : b = a
        · exact (hab (by rw [hba])).elim
        refine ⟨Pi.single a (1 : ZMod p), hTk_fix a hai haj, ?_⟩
        rw [hTk_e_self, hTk_e_out a b hba]
        exact hζ1
  ·
    by_cases hai : a = i ∨ a = j
    · rcases hai with hai | haj
      · refine ⟨T0, hT0, ?_⟩
        rw [hai, hT0_ei, hT0_z]
        exact hζ1
      · refine ⟨T0, hT0, ?_⟩
        rw [haj, hT0_ej, hT0_z]
        exact hζ1
    · push Not at hai
      refine ⟨Pi.single a (1 : ZMod p), hTk_fix a hai.1 hai.2, ?_⟩
      rw [hTk_e_self, hTk_z]
      exact hζ1
  ·
    by_cases hai : a = i ∨ a = j
    · rcases hai with hai | haj
      · refine ⟨T0, hT0, ?_⟩
        rw [hai, hT0_ei]
        by_cases hbi : b = i
        · rw [hbi, hT0_fi]
          exact hζinv
        · by_cases hbj : b = j
          · rw [hbj, hT0_fj]
            exact hζinv
          · rw [hT0_f_out b hbi hbj]
            exact hζ1
      · refine ⟨T0, hT0, ?_⟩
        rw [haj, hT0_ej]
        by_cases hbi : b = i
        · rw [hbi, hT0_fi]
          exact hζinv
        · by_cases hbj : b = j
          · rw [hbj, hT0_fj]
            exact hζinv
          · rw [hT0_f_out b hbi hbj]
            exact hζ1
    · push Not at hai
      by_cases hba : b = a
      · refine ⟨Pi.single a (1 : ZMod p), hTk_fix a hai.1 hai.2, ?_⟩
        rw [hTk_e_self, hba, hTk_f_self]
        exact hζinv
      · refine ⟨Pi.single a (1 : ZMod p), hTk_fix a hai.1 hai.2, ?_⟩
        rw [hTk_e_self, hTk_f_out a b hba]
        exact hζ1
  ·
    by_cases hbj : b = i ∨ b = j
    · rcases hbj with hbi | hbj
      · refine ⟨T0, hT0, ?_⟩
        rw [hT0_z, hbi, hT0_ei]
        exact hζ1.symm
      · refine ⟨T0, hT0, ?_⟩
        rw [hT0_z, hbj, hT0_ej]
        exact hζ1.symm
    · push Not at hbj
      refine ⟨Pi.single b (1 : ZMod p), hTk_fix b hbj.1 hbj.2, ?_⟩
      rw [hTk_z, hTk_e_self]
      exact hζ1.symm
  ·
    exfalso
    have hz : k = l := by
      apply Fin.ext
      have hk := k.isLt
      have hl := l.isLt
      omega
    exact hab (by rw [hz])
  ·
    by_cases hbj : b = i ∨ b = j
    · rcases hbj with hbi | hbj
      · refine ⟨T0, hT0, ?_⟩
        rw [hT0_z, hbi, hT0_fi]
        exact hζinv1.symm
      · refine ⟨T0, hT0, ?_⟩
        rw [hT0_z, hbj, hT0_fj]
        exact hζinv1.symm
    · push Not at hbj
      refine ⟨Pi.single b (1 : ZMod p), hTk_fix b hbj.1 hbj.2, ?_⟩
      rw [hTk_z, hTk_f_self]
      exact hζinv1.symm
  ·
    by_cases hbj : b = i ∨ b = j
    · rcases hbj with hbi | hbj
      · refine ⟨T0, hT0, ?_⟩
        rw [hbi, hT0_ei]
        by_cases hai : a = i
        · rw [hai, hT0_fi]
          exact hζinv.symm
        · by_cases haj : a = j
          · rw [haj, hT0_fj]
            exact hζinv.symm
          · rw [hT0_f_out a hai haj]
            exact hζ1.symm
      · refine ⟨T0, hT0, ?_⟩
        rw [hbj, hT0_ej]
        by_cases hai : a = i
        · rw [hai, hT0_fi]
          exact hζinv.symm
        · by_cases haj : a = j
          · rw [haj, hT0_fj]
            exact hζinv.symm
          · rw [hT0_f_out a hai haj]
            exact hζ1.symm
    · push Not at hbj
      by_cases hab' : a = b
      · refine ⟨Pi.single b (1 : ZMod p), hTk_fix b hbj.1 hbj.2, ?_⟩
        rw [hab', hTk_f_self, hTk_e_self]
        exact hζinv.symm
      · refine ⟨Pi.single b (1 : ZMod p), hTk_fix b hbj.1 hbj.2, ?_⟩
        rw [hTk_f_out b a hab', hTk_e_self]
        exact hζ1.symm
  ·
    by_cases hai : a = i ∨ a = j
    · rcases hai with hai | haj
      · refine ⟨T0, hT0, ?_⟩
        rw [hai, hT0_fi, hT0_z]
        exact hζinv1
      · refine ⟨T0, hT0, ?_⟩
        rw [haj, hT0_fj, hT0_z]
        exact hζinv1
    · push Not at hai
      refine ⟨Pi.single a (1 : ZMod p), hTk_fix a hai.1 hai.2, ?_⟩
      rw [hTk_f_self, hTk_z]
      exact hζinv1
  ·
    by_cases hai : a = i
    · by_cases hbj : b = j
      · exact (hF1 ⟨by rw [hai], by rw [hbj]⟩).elim
      by_cases hbi : b = i
      · exact (hab (by rw [hai, hbi])).elim
      refine ⟨T0, hT0, ?_⟩
      rw [hai, hT0_fi, hT0_f_out b hbi hbj]
      exact hζinv1
    · by_cases haj : a = j
      · by_cases hbi : b = i
        · exact (hF2 ⟨by rw [haj], by rw [hbi]⟩).elim
        by_cases hbj : b = j
        · exact (hab (by rw [haj, hbj])).elim
        refine ⟨T0, hT0, ?_⟩
        rw [haj, hT0_fj, hT0_f_out b hbi hbj]
        exact hζinv1
      · by_cases hba : b = a
        · exact (hab (by rw [hba])).elim
        refine ⟨Pi.single a (1 : ZMod p), hTk_fix a hai haj, ?_⟩
        rw [hTk_f_self, hTk_f_out a b hba]
        exact hζinv1

private theorem entry_eq_zero_of_mem_centralizer (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin r → ZMod p) →* hypSU h r ε} (hτ : IsSplitTorus h ζ τ)
    {i j : Fin r} (hij : i ≠ j) (hε : ε ≤ 1) {c : hypSU h r ε}
    (hc : c ∈ Subgroup.centralizer (torusFix τ (SlNsRootGen.swapMap i j)))
    {a b : HypIndex r ε} (hab : a ≠ b)
    (hE1 : ¬ (a = .inl i ∧ b = .inl j)) (hE2 : ¬ (a = .inl j ∧ b = .inl i))
    (hF1 : ¬ (a = .inr (.inr i) ∧ b = .inr (.inr j)))
    (hF2 : ¬ (a = .inr (.inr j) ∧ b = .inr (.inr i))) :
    (((c : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a b =
      0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, hti, hne⟩ := exists_splitEntries_ne hζ hp hp2 hij hε hab hE1 hE2 hF1 hF2
  have hmem : τ (Multiplicative.ofAdd t) ∈ torusFix τ (SlNsRootGen.swapMap i j) := by
    refine ⟨Multiplicative.ofAdd t, ?_, rfl⟩
    simpa using (SlNsRootGen.swapMap_eq_self_iff (p := p) (i := i) (j := j)).mpr hti
  have hcomm := Subgroup.mem_centralizer_iff.mp hc _ hmem
  have hmat : diagonal (splitEntries (ε := ε) ζ t) *
      (((c : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) =
      (((c : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *
        diagonal (splitEntries (ε := ε) ζ t) := by
    have := congrArg (fun g : hypSU h r ε =>
      (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K)) hcomm
    simpa [hτ t] using this
  exact TauCeti.apply_eq_zero_of_commute_diagonal hmat hne

theorem leviDual_apply_eq_zero_of_not_mem (h : UnitaryFieldData 2 n K)
    {J : Finset (Fin r)} {A : SpecialLinearGroup (Fin r) K}
    (hA : A ∈ CFSG.RankThree.CALinearPlane.coordBlockSL K J) {x y : Fin r} (hxy : x ≠ y)
    (hout : x ∉ J ∨ y ∉ J) :
    leviDual h (SpecialLinearGroup.toGL A) x y = 0 := by
  have hAinv : A⁻¹ ∈ CFSG.RankThree.CALinearPlane.coordBlockSL K J :=
    (CFSG.RankThree.CALinearPlane.coordBlockSL K J).inv_mem hA
  have hmem : ((A⁻¹ : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K) y x =
      if y = x then 1 else 0 := by
    refine (CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff.mp hAinv) y x ?_
    rcases hout with hx | hy
    · exact Or.inr hx
    · exact Or.inl hy
  unfold leviDual
  rw [← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, transpose_apply, Matrix.map_apply,
    hmem, if_neg (Ne.symm hxy), map_zero]

theorem leviSU_apply_ne_zero_splitEntries_eq (h : UnitaryFieldData 2 n K)
    {i j : Fin r} {A : SpecialLinearGroup (Fin r) K}
    (hA : A ∈ CFSG.RankThree.CALinearPlane.coordBlockSL K ({i, j} : Finset (Fin r)))
    {ζ : K} {t : Fin r → ZMod p} (hti : t i = t j) {a b : HypIndex r ε}
    (hM : (((leviSU h ε A : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) a b ≠ 0) :
    splitEntries (ε := ε) ζ t a = splitEntries (ε := ε) ζ t b := by
  rw [coe_leviSU, coe_leviGL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hM
  rcases a with x | k | x <;> rcases b with y | l | y
  ·
    simp only [blk3_inl_inl] at hM
    by_cases hxy : x = y
    · rw [hxy]
    · by_cases hxJ : x ∈ ({i, j} : Finset (Fin r))
      · by_cases hyJ : y ∈ ({i, j} : Finset (Fin r))
        · have hxi : x = i ∨ x = j := by simpa using hxJ
          have hyi : y = i ∨ y = j := by simpa using hyJ
          rcases hxi with rfl | rfl <;> rcases hyi with rfl | rfl <;>
            simp [splitEntries, hti]
        · exfalso
          exact hM (by
            rw [CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff.mp hA x y (Or.inr hyJ)]
            simp [hxy])
      · exfalso
        exact hM (by
          rw [CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff.mp hA x y (Or.inl hxJ)]
          simp [hxy])
  ·
    simp only [blk3_inl_inr_inl, Matrix.zero_apply] at hM
    exact absurd rfl hM
  ·
    simp only [blk3_inl_inr_inr, Matrix.zero_apply] at hM
    exact absurd rfl hM
  ·
    simp only [blk3_inr_inl_inl, Matrix.zero_apply] at hM
    exact absurd rfl hM
  ·
    simp only [blk3_inr_inl_inr_inl, Matrix.one_apply] at hM
    by_cases hkl : k = l
    · rw [hkl]
    · rw [if_neg hkl] at hM
      exact absurd rfl hM
  ·
    simp only [blk3_inr_inl_inr_inr, Matrix.zero_apply] at hM
    exact absurd rfl hM
  ·
    simp only [blk3_inr_inr_inl, Matrix.zero_apply] at hM
    exact absurd rfl hM
  ·
    simp only [blk3_inr_inr_inr_inl, Matrix.zero_apply] at hM
    exact absurd rfl hM
  ·
    simp only [blk3_inr_inr_inr_inr] at hM
    by_cases hxy : x = y
    · rw [hxy]
    · by_cases hxJ : x ∈ ({i, j} : Finset (Fin r))
      · by_cases hyJ : y ∈ ({i, j} : Finset (Fin r))
        · have hxi : x = i ∨ x = j := by simpa using hxJ
          have hyi : y = i ∨ y = j := by simpa using hyJ
          rcases hxi with rfl | rfl <;> rcases hyi with rfl | rfl <;>
            simp [splitEntries, hti]
        · exfalso
          exact hM (leviDual_apply_eq_zero_of_not_mem h hA hxy (Or.inr hyJ))
      · exfalso
        exact hM (leviDual_apply_eq_zero_of_not_mem h hA hxy (Or.inl hxJ))

theorem diagonal_comm_leviSU (h : UnitaryFieldData 2 n K)
    {i j : Fin r} {A : SpecialLinearGroup (Fin r) K}
    (hA : A ∈ CFSG.RankThree.CALinearPlane.coordBlockSL K ({i, j} : Finset (Fin r)))
    {ζ : K} {t : Fin r → ZMod p} (hti : t i = t j) :
    diagonal (splitEntries (ε := ε) ζ t) *
      (((leviSU h ε A : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) =
      (((leviSU h ε A : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *
        diagonal (splitEntries (ε := ε) ζ t) := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hM : (((leviSU h ε A : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) a b = 0
  · rw [hM, zero_mul, mul_zero]
  · rw [leviSU_apply_ne_zero_splitEntries_eq h hA hti hM, mul_comm]

private theorem pairBlock_le_centralizer (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    {ζ : K} {τ : Multiplicative (Fin r → ZMod p) →* hypSU h r ε} (hτ : IsSplitTorus h ζ τ)
    {i j : Fin r} :
    pairBlock h ε i j ≤
      Subgroup.centralizer (torusFix τ (SlNsRootGen.swapMap i j)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro x hx
  obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨t, ht, rfl⟩ := hy
  have hti : (Multiplicative.toAdd t) i = (Multiplicative.toAdd t) j :=
    SlNsRootGen.swapMap_eq_self_iff.mp ht
  have hy : (((τ t : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      diagonal (splitEntries (ε := ε) ζ (Multiplicative.toAdd t)) := by
    simpa using hτ (Multiplicative.toAdd t)
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hy,
    diagonal_comm_leviSU h hA hti]

theorem leviSU_injective (h : UnitaryFieldData 2 n K) :
    Function.Injective (leviSU (r := r) h ε) := by
  intro A B hAB
  have hmat : (((leviSU h ε A : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      (((leviSU h ε B : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) :=
    congrArg (fun g : GL (HypIndex r ε) K => (g : Matrix (HypIndex r ε) (HypIndex r ε) K))
      (Subtype.ext_iff.mp hAB)
  rw [coe_leviSU, coe_leviSU, coe_leviGL, coe_leviGL] at hmat
  apply Subtype.ext
  ext a b
  have := congrFun (congrFun hmat (.inl a)) (.inl b)
  simpa [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using this

private theorem diag2n_mem_coordBlockSL {d : ℕ} {k : Type} [Field k] {J : Finset (Fin d)}
    {i j : Fin d} (hij : i ≠ j) (hi : i ∈ J) (hj : j ∈ J) {a : k} (ha : a ≠ 0) :
    Matrix.SpecialLinearGroup.diag2n hij a ha ∈ CFSG.RankThree.CALinearPlane.coordBlockSL k J := by
  rw [CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff]
  intro r s hrs
  rw [Matrix.SpecialLinearGroup.diag2n_coe, Matrix.diagonal_apply]
  by_cases h : r = s
  · have hrJ : r ∉ J := by
      rcases hrs with h1 | h1
      · exact h1
      · rwa [← h] at h1
    have hri : r ≠ i := fun hri => hrJ (by rw [hri]; exact hi)
    have hrj : r ≠ j := fun hrj => hrJ (by rw [hrj]; exact hj)
    rw [ite_eq_left h, ite_eq_left h]
    simp [hri, hrj]
  · rw [ite_eq_right h, ite_eq_right h]

private theorem diag2n_pow_eq_one {d : ℕ} {k : Type} [Field k] {i j : Fin d} (hij : i ≠ j)
    {a : k} (ha : a ≠ 0) {m : ℕ} (ham : a ^ m = 1) :
    Matrix.SpecialLinearGroup.diag2n hij a ha ^ m = 1 := by
  apply Subtype.ext
  ext r s
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.diag2n_coe,
    Matrix.diagonal_pow, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply,
    Matrix.diagonal_apply, Pi.pow_apply]
  by_cases hrs : r = s
  · rw [ite_eq_left hrs, ite_eq_left hrs]
    by_cases hri : r = i
    · rw [ite_eq_left hri]
      exact ham
    · rw [ite_eq_right hri]
      by_cases hrj : r = j
      · rw [ite_eq_left hrj, inv_pow, ham, inv_one]
      · rw [ite_eq_right hrj, one_pow]
  · rw [ite_eq_right hrs, ite_eq_right hrs]

theorem isComponentOf_pairBlock (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin r → ZMod p) →* hypSU h r ε} (hτ : IsSplitTorus h ζ τ) (hε : ε ≤ 1)
    {i j : Fin r} (hij : i ≠ j) :
    IsComponentOf (pairBlock h ε i j)
      (Subgroup.centralizer (torusFix τ (SlNsRootGen.swapMap i j))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup (hypSU h r ε) :=
    Subgroup.centralizer (torusFix τ (SlNsRootGen.swapMap i j)) with hC
  have hpair_le : pairBlock h ε i j ≤ C := by
    rw [hC]
    exact pairBlock_le_centralizer h hp hτ
  have hJ : 2 ≤ ({i, j} : Finset (Fin r)).card := by
    rw [Finset.card_pair hij]
  have h4 : 4 ≤ Nat.card K := by
    rw [h.card]
    have hn : 2 ≤ 2 * n := by
      have := h.one_le
      omega
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) hn
  haveI : Finite K := h.finite
  have hqJ : CFSG.IsQuasisimple
      (CFSG.RankThree.CALinearPlane.coordBlockSL K ({i, j} : Finset (Fin r))) :=
    CFSG.RankThree.CALinearPlane.isQuasisimple_coordBlockSL hJ h4
  have hq : CFSG.IsQuasisimple (pairBlock h ε i j) := by
    rw [pairBlock]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective
        (CFSG.RankThree.CALinearPlane.coordBlockSL K ({i, j} : Finset (Fin r)))
        (leviSU h ε) (leviSU_injective h)) hqJ
  have hnormal : ((pairBlock h ε i j).subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hpair_le]
    intro x hx z hz
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp z
    have hc0 : hx ∈ xyStab h r ε := by
      have hzero : ∀ {d : hypSU h r ε}, d ∈ C → ∀ {a b : HypIndex r ε}, a ≠ b →
          (¬ (a = .inl i ∧ b = .inl j)) → (¬ (a = .inl j ∧ b = .inl i)) →
          (¬ (a = .inr (.inr i) ∧ b = .inr (.inr j))) →
          (¬ (a = .inr (.inr j) ∧ b = .inr (.inr i))) →
          (((d : hypSU h r ε) : GL (HypIndex r ε) K) :
            Matrix (HypIndex r ε) (HypIndex r ε) K) a b = 0 := by
        intro d hd a b hab hE1 hE2 hF1 hF2
        exact entry_eq_zero_of_mem_centralizer h hp hp2 hζ hτ hij hε hd hab hE1 hE2 hF1 hF2
      have hXmem : ∀ {d : hypSU h r ε}, d ∈ C → ∀ a : Fin r → K,
          (((d : hypSU h r ε) : GL (HypIndex r ε) K) :
            Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ hypXEmb r ε a ∈ hypX K r ε := by
        intro d hd a
        refine ⟨fun k => ((((d : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ hypXEmb r ε a) (.inl k), ?_⟩
        funext y
        rcases y with m | l | m
        · rfl
        · simp only [hypXEmb]
          rw [Matrix.mulVec, dotProduct]
          refine (Finset.sum_eq_zero fun z _ => ?_).symm
          rcases z with n | n | n
          · rw [hzero hd (by simp) (by simp) (by simp) (by simp) (by simp), zero_mul]
          · simp
          · simp
        · simp only [hypXEmb]
          rw [Matrix.mulVec, dotProduct]
          refine (Finset.sum_eq_zero fun z _ => ?_).symm
          rcases z with n | n | n
          · rw [hzero hd (by simp) (by simp) (by simp) (by simp) (by simp), zero_mul]
          · simp
          · simp
      have hYmem : ∀ {d : hypSU h r ε}, d ∈ C → ∀ a : Fin r → K,
          (((d : hypSU h r ε) : GL (HypIndex r ε) K) :
            Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ hypYEmb r ε a ∈ hypY K r ε := by
        intro d hd a
        refine ⟨fun k => ((((d : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ hypYEmb r ε a) (.inr (.inr k)), ?_⟩
        funext y
        rcases y with m | l | m
        · simp only [hypYEmb]
          rw [Matrix.mulVec, dotProduct]
          refine (Finset.sum_eq_zero fun z _ => ?_).symm
          rcases z with n | n | n
          · simp
          · simp
          · rw [hzero hd (by simp) (by simp) (by simp) (by simp) (by simp), zero_mul]
        · simp only [hypYEmb]
          rw [Matrix.mulVec, dotProduct]
          refine (Finset.sum_eq_zero fun z _ => ?_).symm
          rcases z with n | n | n
          · simp
          · simp
          · rw [hzero hd (by simp) (by simp) (by simp) (by simp) (by simp), zero_mul]
        · rfl
      have hXmem' : ∀ v ∈ hypX K r ε,
          (((hx : hypSU h r ε) : GL (HypIndex r ε) K) :
            Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v ∈ hypX K r ε := by
        intro v hv
        rw [eq_hypXEmb_of_mem hv]
        exact hXmem hz _
      have hXmem_inv : ∀ v ∈ hypX K r ε,
          (((hx⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
            Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v ∈ hypX K r ε := by
        intro v hv
        rw [eq_hypXEmb_of_mem hv]
        exact hXmem (C.inv_mem hz) _
      have hYmem' : ∀ v ∈ hypY K r ε,
          (((hx : hypSU h r ε) : GL (HypIndex r ε) K) :
            Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v ∈ hypY K r ε := by
        intro v hv
        rw [eq_hypYEmb_of_mem hv]
        exact hYmem hz _
      have hYmem_inv : ∀ v ∈ hypY K r ε,
          (((hx⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
            Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v ∈ hypY K r ε := by
        intro v hv
        rw [eq_hypYEmb_of_mem hv]
        exact hYmem (C.inv_mem hz) _
      rw [mem_xyStab]
      exact ⟨smul_eq_of_mulVec_mem hXmem' hXmem_inv,
        smul_eq_of_mulVec_mem hYmem' hYmem_inv⟩
    set g : xyStab h r ε := ⟨hx, hc0⟩ with hg
    set Ce : GL (Fin r) K := xBlockUnits h r ε g with hCe
    set Cei : GL (Fin r) K := Ce⁻¹ with hCei
    set Cz : Matrix (Fin ε) (Fin ε) K :=
      zBlock (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) with hCz
    set Czi : Matrix (Fin ε) (Fin ε) K :=
      zBlock ((((g⁻¹ : xyStab h r ε) : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) with hCzi
    have hMg : (((hx : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) =
        blk3 (Ce : Matrix (Fin r) (Fin r) K) 0 0 Cz 0 (leviDual h Ce) := by
      have hcoe := coe_eq_blk3 h g
      rw [← coe_xBlockUnits h g] at hcoe
      simpa [hCe, hCz, hg] using hcoe
    have hMgi : (((hx⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) =
        blk3 (Cei : Matrix (Fin r) (Fin r) K) 0 0 Czi 0 (leviDual h Cei) := by
      have hcoe := coe_eq_blk3 h (g⁻¹)
      rw [← coe_xBlockUnits h (g⁻¹), map_inv] at hcoe
      simpa [hCe, hCei, hCzi, hg] using hcoe
    have hCeCei : (Ce : Matrix (Fin r) (Fin r) K) * (Cei : Matrix (Fin r) (Fin r) K) = 1 := by
      rw [hCei, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hgg : (((g : hypSU h r ε)) * (((g⁻¹ : xyStab h r ε)) : hypSU h r ε)) = 1 := by
      have h : g * g⁻¹ = (1 : xyStab h r ε) := mul_inv_cancel g
      simpa using congrArg (fun z : xyStab h r ε => (z : hypSU h r ε)) h
    have hprod : (((hx : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *
        (((hx⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
      have := congrArg (fun z : hypSU h r ε =>
        (((z : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K)) hgg
      simpa [hg] using this
    have hzblock : Cz * Czi = 1 := by
      have hblk : blk3 (Ce : Matrix (Fin r) (Fin r) K) 0 0 Cz 0 (leviDual h Ce) *
          blk3 (Cei : Matrix (Fin r) (Fin r) K) 0 0 Czi 0 (leviDual h Cei) = 1 := by
        rwa [← hMg, ← hMgi]
      rw [blk3_mul] at hblk
      ext a b
      have := congrFun (congrFun hblk (.inr (.inl a))) (.inr (.inl b))
      simpa [Matrix.one_apply] using this
    have hCe_zero : ∀ a b : Fin r, a ≠ b →
        (a ∉ ({i, j} : Finset (Fin r)) ∨ b ∉ ({i, j} : Finset (Fin r))) →
        (Ce : Matrix (Fin r) (Fin r) K) a b = 0 := by
      intro a b hab hout
      rw [hCe, coe_xBlockUnits]
      change (((hx : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl a) (.inl b) = 0
      have hnot : ∀ {x : Fin r}, x ∉ ({i, j} : Finset (Fin r)) → x ≠ i ∧ x ≠ j := by
        intro x hx
        exact ⟨fun hxi => hx (by rw [hxi]; simp), fun hxj => hx (by rw [hxj]; simp)⟩
      refine entry_eq_zero_of_mem_centralizer h hp hp2 hζ hτ hij hε (hC ▸ hz)
        (by simpa using hab) ?_ ?_ ?_ ?_
      · rintro ⟨h1, h2⟩
        rcases hout with ha | hb
        · exact (hnot ha).1 (by simpa using h1)
        · exact (hnot hb).2 (by simpa using h2)
      · rintro ⟨h1, h2⟩
        rcases hout with ha | hb
        · exact (hnot ha).2 (by simpa using h1)
        · exact (hnot hb).1 (by simpa using h2)
      · rintro ⟨h1, h2⟩
        rcases hout with ha | hb
        · exact (hnot ha).1 (by simpa using h1)
        · exact (hnot hb).2 (by simpa using h2)
      · rintro ⟨h1, h2⟩
        rcases hout with ha | hb
        · exact (hnot ha).2 (by simpa using h1)
        · exact (hnot hb).1 (by simpa using h2)
    have hCei_zero : ∀ a b : Fin r, a ≠ b →
        (a ∉ ({i, j} : Finset (Fin r)) ∨ b ∉ ({i, j} : Finset (Fin r))) →
        (Cei : Matrix (Fin r) (Fin r) K) a b = 0 := by
      intro a b hab hout
      rw [hCei, hCe, ← map_inv (xBlockUnits h r ε) g, coe_xBlockUnits]
      have hnot : ∀ {x : Fin r}, x ∉ ({i, j} : Finset (Fin r)) → x ≠ i ∧ x ≠ j := by
        intro x hx
        exact ⟨fun hxi => hx (by rw [hxi]; simp), fun hxj => hx (by rw [hxj]; simp)⟩
      change (((hx⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl a) (.inl b) = 0
      refine entry_eq_zero_of_mem_centralizer h hp hp2 hζ hτ hij hε (hC ▸ C.inv_mem hz)
        (by simpa using hab) ?_ ?_ ?_ ?_
      · rintro ⟨h1, h2⟩
        rcases hout with ha | hb
        · exact (hnot ha).1 (by simpa using h1)
        · exact (hnot hb).2 (by simpa using h2)
      · rintro ⟨h1, h2⟩
        rcases hout with ha | hb
        · exact (hnot ha).2 (by simpa using h1)
        · exact (hnot hb).1 (by simpa using h2)
      · rintro ⟨h1, h2⟩
        rcases hout with ha | hb
        · exact (hnot ha).1 (by simpa using h1)
        · exact (hnot hb).2 (by simpa using h2)
      · rintro ⟨h1, h2⟩
        rcases hout with ha | hb
        · exact (hnot ha).2 (by simpa using h1)
        · exact (hnot hb).1 (by simpa using h2)
    have hArow : ∀ {a b : Fin r}, a ∉ ({i, j} : Finset (Fin r)) →
        ((A : Matrix (Fin r) (Fin r) K) * (Cei : Matrix (Fin r) (Fin r) K)) a b =
          (Cei : Matrix (Fin r) (Fin r) K) a b := by
      intro a b ha
      have hsum : (∑ d, (A : Matrix (Fin r) (Fin r) K) a d *
          (Cei : Matrix (Fin r) (Fin r) K) d b) =
          (A : Matrix (Fin r) (Fin r) K) a a * (Cei : Matrix (Fin r) (Fin r) K) a b := by
        refine Finset.sum_eq_single a ?_ ?_
        · intro d _ hda
          rw [CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff.mp hA a d (Or.inl ha),
            if_neg (Ne.symm hda), zero_mul]
        · intro ha'
          exact absurd (Finset.mem_univ a) ha'
      rw [Matrix.mul_apply, hsum,
        CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff.mp hA a a (Or.inl ha), if_pos rfl,
        one_mul]
    have hCerow : ∀ {X : Matrix (Fin r) (Fin r) K} {a b : Fin r},
        a ∉ ({i, j} : Finset (Fin r)) →
        ((Ce : Matrix (Fin r) (Fin r) K) * X) a b =
          (Ce : Matrix (Fin r) (Fin r) K) a a * X a b := by
      intro X a b ha
      have hsum : (∑ d, (Ce : Matrix (Fin r) (Fin r) K) a d * X d b) =
          (Ce : Matrix (Fin r) (Fin r) K) a a * X a b := by
        refine Finset.sum_eq_single a ?_ ?_
        · intro d _ hda
          rw [hCe_zero a d (Ne.symm hda) (Or.inl ha), zero_mul]
        · intro ha'
          exact absurd (Finset.mem_univ a) ha'
      rw [Matrix.mul_apply, hsum]
    have hrow : ∀ {a b : Fin r}, a ∉ ({i, j} : Finset (Fin r)) →
        ((Ce : Matrix (Fin r) (Fin r) K) * (A : Matrix (Fin r) (Fin r) K) *
            (Cei : Matrix (Fin r) (Fin r) K)) a b =
          ((Ce : Matrix (Fin r) (Fin r) K) * (Cei : Matrix (Fin r) (Fin r) K)) a b := by
      intro a b ha
      rw [Matrix.mul_assoc, hCerow (X := (A : Matrix (Fin r) (Fin r) K) *
        (Cei : Matrix (Fin r) (Fin r) K)) ha, hArow ha, ← hCerow (X :=
        (Cei : Matrix (Fin r) (Fin r) K)) ha]
    have hCei_col : ∀ {a b : Fin r}, b ∉ ({i, j} : Finset (Fin r)) →
        (((Ce : Matrix (Fin r) (Fin r) K) * (A : Matrix (Fin r) (Fin r) K)) *
            (Cei : Matrix (Fin r) (Fin r) K)) a b =
          ((Ce : Matrix (Fin r) (Fin r) K) * (A : Matrix (Fin r) (Fin r) K)) a b *
            (Cei : Matrix (Fin r) (Fin r) K) b b := by
      intro a b hb
      have hsum : (∑ d, ((Ce : Matrix (Fin r) (Fin r) K) *
          (A : Matrix (Fin r) (Fin r) K)) a d * (Cei : Matrix (Fin r) (Fin r) K) d b) =
          ((Ce : Matrix (Fin r) (Fin r) K) * (A : Matrix (Fin r) (Fin r) K)) a b *
            (Cei : Matrix (Fin r) (Fin r) K) b b := by
        refine Finset.sum_eq_single b ?_ ?_
        · intro d _ hdb
          rw [hCei_zero d b hdb (Or.inr hb), mul_zero]
        · intro hb'
          exact absurd (Finset.mem_univ b) hb'
      rw [Matrix.mul_apply, hsum]
    have hAcol : ∀ {a b : Fin r}, b ∉ ({i, j} : Finset (Fin r)) →
        ((Ce : Matrix (Fin r) (Fin r) K) * (A : Matrix (Fin r) (Fin r) K)) a b =
          (Ce : Matrix (Fin r) (Fin r) K) a b := by
      intro a b hb
      have hsum : (∑ d, (Ce : Matrix (Fin r) (Fin r) K) a d *
          (A : Matrix (Fin r) (Fin r) K) d b) =
          (Ce : Matrix (Fin r) (Fin r) K) a b * (A : Matrix (Fin r) (Fin r) K) b b := by
        refine Finset.sum_eq_single b ?_ ?_
        · intro d _ hdb
          rw [CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff.mp hA d b (Or.inr hb),
            if_neg hdb, mul_zero]
        · intro hb'
          exact absurd (Finset.mem_univ b) hb'
      rw [Matrix.mul_apply, hsum,
        CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff.mp hA b b (Or.inr hb), if_pos rfl,
        mul_one]
    have hCeCeicol : ∀ {a b : Fin r}, b ∉ ({i, j} : Finset (Fin r)) →
        ((Ce : Matrix (Fin r) (Fin r) K) * (Cei : Matrix (Fin r) (Fin r) K)) a b =
          (Ce : Matrix (Fin r) (Fin r) K) a b * (Cei : Matrix (Fin r) (Fin r) K) b b := by
      intro a b hb
      have hsum : (∑ d, (Ce : Matrix (Fin r) (Fin r) K) a d *
          (Cei : Matrix (Fin r) (Fin r) K) d b) =
          (Ce : Matrix (Fin r) (Fin r) K) a b * (Cei : Matrix (Fin r) (Fin r) K) b b := by
        refine Finset.sum_eq_single b ?_ ?_
        · intro d _ hdb
          rw [hCei_zero d b hdb (Or.inr hb), mul_zero]
        · intro hb'
          exact absurd (Finset.mem_univ b) hb'
      rw [Matrix.mul_apply, hsum]
    have hcol : ∀ {a b : Fin r}, b ∉ ({i, j} : Finset (Fin r)) →
        ((Ce : Matrix (Fin r) (Fin r) K) * (A : Matrix (Fin r) (Fin r) K) *
            (Cei : Matrix (Fin r) (Fin r) K)) a b =
          ((Ce : Matrix (Fin r) (Fin r) K) * (Cei : Matrix (Fin r) (Fin r) K)) a b := by
      intro a b hb
      rw [hCei_col hb, hAcol hb, hCeCeicol hb]
    set Ag : GL (Fin r) K := Ce * SpecialLinearGroup.toGL A * Cei with hAg
    have hAgdet : (Ag : Matrix (Fin r) (Fin r) K).det = 1 := by
      have h : Matrix.GeneralLinearGroup.det Ag = 1 := by
        rw [hAg, map_mul, map_mul, hCei, map_inv, Matrix.SpecialLinearGroup.coeToGL_det,
          mul_one, mul_inv_cancel]
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using congrArg Units.val h
    let A' : SpecialLinearGroup (Fin r) K := ⟨(Ag : Matrix (Fin r) (Fin r) K), hAgdet⟩
    have hA'toGL : SpecialLinearGroup.toGL A' = Ag := by
      apply Units.ext
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    have hA'val : ((A' : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K) =
        (Ce : Matrix (Fin r) (Fin r) K) * (A : Matrix (Fin r) (Fin r) K) *
          (Cei : Matrix (Fin r) (Fin r) K) := by
      change (Ag : Matrix (Fin r) (Fin r) K) = _
      rw [hAg, Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    have hA'mem : A' ∈ CFSG.RankThree.CALinearPlane.coordBlockSL K ({i, j} : Finset (Fin r)) := by
      rw [CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff]
      intro a b hout
      rw [hA'val]
      rcases hout with ha | hb
      · rw [hrow ha, hCeCei, Matrix.one_apply]
      · rw [hcol hb, hCeCei, Matrix.one_apply]
    have hDual : leviDual h (SpecialLinearGroup.toGL A') =
        leviDual h Ce * leviDual h (SpecialLinearGroup.toGL A) * leviDual h Cei := by
      rw [hA'toGL, hAg, leviDual_mul', leviDual_mul']
    have hMx : (((leviSU h ε A : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) =
        blk3 (A : Matrix (Fin r) (Fin r) K) 0 0 1 0
          (leviDual h (SpecialLinearGroup.toGL A)) := by
      rw [coe_leviSU, coe_leviGL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    have hMl : (((leviSU h ε A' : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) =
        blk3 (A' : Matrix (Fin r) (Fin r) K) 0 0 1 0
          (leviDual h (SpecialLinearGroup.toGL A')) := by
      rw [coe_leviSU, coe_leviGL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    have hconj : hx * leviSU h ε A * hx⁻¹ = leviSU h ε A' := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hMg, hMx, hMgi,
        blk3_mul, blk3_mul]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.mul_one,
        Matrix.one_mul]
      rw [← hA'val, hzblock, ← hDual, hMl]
    exact ⟨A', hA'mem, hconj.symm⟩
  refine ⟨hpair_le, IsSubnormal.step hpair_le hnormal (IsSubnormal.refl _), ?_⟩
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq

theorem dvd_card_pairBlock (h : UnitaryFieldData 2 n K) (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {i j : Fin r} (hij : i ≠ j) :
    p ∣ Nat.card (pairBlock h ε i j) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have hinj : Function.Injective (leviSU (r := r) h ε) := leviSU_injective h
  set D₁ : SpecialLinearGroup (Fin r) K := Matrix.SpecialLinearGroup.diag2n hij ζ hζ0 with hD1
  have hD1_mem : D₁ ∈ CFSG.RankThree.CALinearPlane.coordBlockSL K ({i, j} : Finset (Fin r)) := by
    rw [hD1]
    exact diag2n_mem_coordBlockSL hij (by simp) (by simp) hζ0
  have hD1_pow : D₁ ^ p = 1 := by
    rw [hD1]
    exact diag2n_pow_eq_one hij hζ0 hζ.pow_eq_one
  have hD1_ne : D₁ ≠ 1 := by
    intro h1
    have hii : (D₁ : Matrix (Fin r) (Fin r) K) i i = 1 := by rw [h1]; simp
    rw [hD1, Matrix.SpecialLinearGroup.diag2n_coe, Matrix.diagonal_apply_eq] at hii
    exact hζ1 (by simpa using hii)
  have hmem : leviSU h ε D₁ ∈ pairBlock h ε i j :=
    Subgroup.mem_map.mpr ⟨D₁, hD1_mem, rfl⟩
  have horder : orderOf (leviSU h ε D₁) = p := by
    rw [orderOf_injective (leviSU h ε) hinj D₁]
    exact orderOf_eq_prime hD1_pow hD1_ne
  have hdvd := Subgroup.orderOf_dvd_natCard (pairBlock h ε i j) hmem
  rwa [horder] at hdvd

end CFSG.StandardType.SuSplitRootGen

end

