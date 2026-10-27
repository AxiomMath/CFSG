module

public import CFSG.LocalAnalysis.StandardType.GGWeylSimpleSystemsConj
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
public import TauCeti.GroupTheory.Coxeter.Geometric

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.SecFiveRootRefl

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l6w2_entry_of_finiteType {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C)
    (hMe : CFSG.LieType.RootSystem.coxeterMatrix hC = M) {i j : ι} (hij : i ≠ j) :
    M.M i j = 2 ∨ M.M i j = 3 ∨ M.M i j = 4 ∨ M.M i j = 6 := by
  have hcoe : M.M i j = TauCeti.coxeterOrder (C i j * C j i) := by
    rw [← hMe]
    simp only [CFSG.LieType.RootSystem.coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  rw [hcoe]
  have hmem := TauCeti.coxeterOrder_mem (hC.apply_mul_apply_mem_of_ne hij)
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem

theorem ggFLW_entries {ι : Type} {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M) (i j : ι)
    (hij : i ≠ j) : M.M i j = 2 ∨ M.M i j = 3 ∨ M.M i j = 4 ∨ M.M i j = 6 := by
  classical
  have hM0 : GGIsWeylMatrix M := hM
  rcases hM with ⟨n, e, _hn, _hMA | ⟨_hn2, _hMB⟩ | ⟨_hn4, _hMD⟩⟩ | ⟨e, _hE6⟩ | ⟨e, _hE7⟩ |
    ⟨e, _hE8⟩ | ⟨e, _hF4⟩ | ⟨e, _hG2⟩
  · letI : Fintype ι := Fintype.ofEquiv (Fin n) e
    obtain ⟨C, hC, hMe, -⟩ := S2MathFi1451.ggWeyl_exists_cartanTree hM0
    exact l6w2_entry_of_finiteType hC hMe hij
  · letI : Fintype ι := Fintype.ofEquiv (Fin n) e
    obtain ⟨C, hC, hMe, -⟩ := S2MathFi1451.ggWeyl_exists_cartanTree hM0
    exact l6w2_entry_of_finiteType hC hMe hij
  · letI : Fintype ι := Fintype.ofEquiv (Fin n) e
    obtain ⟨C, hC, hMe, -⟩ := S2MathFi1451.ggWeyl_exists_cartanTree hM0
    exact l6w2_entry_of_finiteType hC hMe hij
  · letI : Fintype ι := Fintype.ofEquiv (Fin 6) e
    obtain ⟨C, hC, hMe, -⟩ := S2MathFi1451.ggWeyl_exists_cartanTree hM0
    exact l6w2_entry_of_finiteType hC hMe hij
  · letI : Fintype ι := Fintype.ofEquiv (Fin 7) e
    obtain ⟨C, hC, hMe, -⟩ := S2MathFi1451.ggWeyl_exists_cartanTree hM0
    exact l6w2_entry_of_finiteType hC hMe hij
  · letI : Fintype ι := Fintype.ofEquiv (Fin 8) e
    obtain ⟨C, hC, hMe, -⟩ := S2MathFi1451.ggWeyl_exists_cartanTree hM0
    exact l6w2_entry_of_finiteType hC hMe hij
  · letI : Fintype ι := Fintype.ofEquiv (Fin 4) e
    obtain ⟨C, hC, hMe, -⟩ := S2MathFi1451.ggWeyl_exists_cartanTree hM0
    exact l6w2_entry_of_finiteType hC hMe hij
  · letI : Fintype ι := Fintype.ofEquiv (Fin 2) e
    obtain ⟨C, hC, hMe, -⟩ := S2MathFi1451.ggWeyl_exists_cartanTree hM0
    exact l6w2_entry_of_finiteType hC hMe hij

private theorem l6w2_bonds_of_finiteType {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ} (hC : TauCeti.IsFiniteType C)
    (hMe : CFSG.LieType.RootSystem.coxeterMatrix hC = M) :
    ∀ i j, i ≠ j → (C i j ≠ 0 ↔ 3 ≤ M.M i j) := by
  intro i j hij
  have hcoe : M.M i j = TauCeti.coxeterOrder (C i j * C j i) := by
    rw [← hMe]
    simp only [CFSG.LieType.RootSystem.coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  rw [hcoe]
  have hiff : C i j ≠ 0 ↔ C i j * C j i ≠ 0 := by
    constructor
    · intro hne
      have hge := hC.one_le_apply_mul_apply hne
      exact ne_of_gt (by omega)
    · intro hp h0
      exact hp (by rw [h0, zero_mul])
  have h3 : 3 ≤ TauCeti.coxeterOrder (C i j * C j i) ↔ C i j * C j i ≠ 0 := by
    have hp := hC.apply_mul_apply_mem_of_ne hij
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with h0 | h1 | h2 | h3
    · rw [h0]; simp [TauCeti.coxeterOrder_zero]
    · rw [h1]; simp [TauCeti.coxeterOrder_one]
    · rw [h2]; simp [TauCeti.coxeterOrder_two]
    · rw [h3]; simp [TauCeti.coxeterOrder_three]
  exact hiff.trans h3.symm

theorem ggFLW_cartanTree_bonds {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) :
    ∃ C : Matrix ι ι ℤ, CartanTree C ∧ ∀ i j, i ≠ j → (C i j ≠ 0 ↔ 3 ≤ M.M i j) := by
  obtain ⟨C, hC, hMe, hT⟩ := S2MathFi1451.ggWeyl_exists_cartanTree hM
  exact ⟨C, hT, l6w2_bonds_of_finiteType hC hMe⟩

private noncomputable def l6w2_d {K : Type*} [Field K] {ι : Type} [DecidableEq ι]
    (P : ι → ι → K) (par : ι → ι) (root : ι) (depth : ι → ℕ)
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i) : ι → K
  | i => if _ : i = root then 1
      else l6w2_d P par root depth hdepth (par i) * P (par i) i * (P i (par i))⁻¹
termination_by i => depth i
decreasing_by exact hdepth i ‹i ≠ root›

private theorem l6w2_d_of_ne_root {K : Type*} [Field K] {ι : Type} [DecidableEq ι]
    (P : ι → ι → K) (par : ι → ι) (root : ι) (depth : ι → ℕ)
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i) {i : ι} (hi : i ≠ root) :
    l6w2_d P par root depth hdepth i =
      l6w2_d P par root depth hdepth (par i) * P (par i) i * (P i (par i))⁻¹ := by
  rw [l6w2_d.eq_1, dif_neg hi]

theorem ggFLW_symmetrizer {K : Type*} [Field K] {ι : Type} [DecidableEq ι] (C : Matrix ι ι ℤ)
    (hT : CartanTree C) (P : ι → ι → K) (hP : ∀ i j, i ≠ j → (P i j ≠ 0 ↔ C i j ≠ 0)) :
    ∃ d : ι → K, (∀ i, d i ≠ 0) ∧ ∀ i j, d i * P i j = d j * P j i := by
  classical
  obtain ⟨par, root, depth, hpar, hdepth⟩ := hT
  set d : ι → K := l6w2_d P par root depth hdepth with hddef
  have hroot : d root = 1 := by rw [hddef, l6w2_d.eq_1, dif_pos rfl]
  have hstep : ∀ i, i ≠ root → d i = d (par i) * P (par i) i * (P i (par i))⁻¹ := by
    intro i hi
    rw [hddef, l6w2_d_of_ne_root P par root depth hdepth hi]
  have hparne : ∀ i, i ≠ root → i ≠ par i := by
    intro i hi heq
    have hlt := hdepth i hi
    rw [← heq] at hlt
    exact lt_irrefl _ hlt
  have hPi : ∀ i, i ≠ root → C i (par i) ≠ 0 := fun i hi =>
    (hpar i (par i) (hparne i hi)).mpr (Or.inl ⟨hi, rfl⟩)
  have hPpar : ∀ i, i ≠ root → C (par i) i ≠ 0 := fun i hi =>
    (hpar (par i) i (Ne.symm (hparne i hi))).mpr (Or.inr ⟨hi, rfl⟩)
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i
    induction hdn : depth i using Nat.strong_induction_on generalizing i with
    | _ n ih =>
      by_cases hi : i = root
      · subst hi
        rw [hroot]
        exact one_ne_zero
      · rw [hstep i hi]
        have hlt : depth (par i) < n := hdn ▸ hdepth i hi
        refine mul_ne_zero (mul_ne_zero (ih _ hlt (par i) rfl) ?_)
          (inv_ne_zero ?_)
        · exact (hP (par i) i (Ne.symm (hparne i hi))).mpr (hPpar i hi)
        · exact (hP i (par i) (hparne i hi)).mpr (hPi i hi)
  refine ⟨d, hd0, ?_⟩
  intro i j
  by_cases hij : i = j
  · subst hij
    rfl
  · by_cases hCij : C i j = 0
    · have hnot : ¬ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i)) :=
        fun h => ((hpar i j hij).mpr h) hCij
      have hCji : C j i = 0 := by
        by_contra h
        exact hnot (((hpar j i (Ne.symm hij)).mp h).elim Or.inr Or.inl)
      have hPij0 : P i j = 0 := by
        by_contra h
        exact ((hP i j hij).mp h) hCij
      have hPji0 : P j i = 0 := by
        by_contra h
        exact ((hP j i (Ne.symm hij)).mp h) hCji
      rw [hPij0, hPji0, mul_zero, mul_zero]
    · rcases (hpar i j hij).mp hCij with ⟨hir, hpi⟩ | ⟨hjr, hpj⟩
      · have hdi : d i = d j * P j i * (P i j)⁻¹ := by
          rw [hstep i hir, hpi]
        rw [hdi]
        have hPij : P i j ≠ 0 := (hP i j hij).mpr hCij
        field_simp
      · have hsym : C j i ≠ 0 :=
          (hpar j i (Ne.symm hij)).mpr (((hpar i j hij).mp hCij).elim Or.inr Or.inl)
        have hdj : d j = d i * P i j * (P j i)⁻¹ := by
          rw [hstep j hjr, hpj]
        rw [hdj]
        have hPji : P j i ≠ 0 := (hP j i (Ne.symm hij)).mpr hsym
        field_simp

theorem ggWeyl_exists_bond {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι] {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) (i : ι) : ∃ j, j ≠ i ∧ 3 ≤ M.M i j := by
  classical
  obtain ⟨C, ⟨par, root, depth, hbond, hdepth⟩, hC⟩ := ggFLW_cartanTree_bonds hM
  by_cases hi : i = root
  · subst hi
    obtain ⟨b, hb⟩ := exists_ne i
    have hne : (Finset.univ.filter fun k : ι => k ≠ i).Nonempty := ⟨b, by simpa using hb⟩
    obtain ⟨k, hkmem, hkmin⟩ := Finset.exists_min_image _ depth hne
    have hk : k ≠ i := by simpa using hkmem
    have hpar : par k = i := by
      by_contra hcon
      have hlt := hdepth k hk
      have hle := hkmin (par k) (by simpa using hcon)
      omega
    have hik : i ≠ k := fun h => hk h.symm
    refine ⟨k, hk, ?_⟩
    exact (hC i k hik).mp ((hbond i k hik).mpr (Or.inr ⟨hk, hpar⟩))
  · have hlt := hdepth i hi
    have hne : i ≠ par i := fun h => by rw [← h] at hlt; exact lt_irrefl _ hlt
    refine ⟨par i, hne.symm, ?_⟩
    exact (hC i (par i) hne).mp ((hbond i (par i) hne).mpr (Or.inl ⟨hi, rfl⟩))

theorem ggSimple_exists_not_commute {Γ : Type} [Fintype Γ] [DecidableEq Γ] [Nontrivial Γ]
    {M : CoxeterMatrix Γ} (hM : GGIsWeylMatrix M) (i : Γ) :
    ∃ j : Γ, M.simple i * M.simple j ≠ M.simple j * M.simple i := by
  obtain ⟨j, hji, hbond⟩ := ggWeyl_exists_bond hM i
  refine ⟨j, ?_⟩
  intro hcomm
  have hsq : (M.simple i * M.simple j) ^ 2 = 1 := by
    rw [pow_two]
    calc
      (M.simple i * M.simple j) * (M.simple i * M.simple j)
          = M.simple i * (M.simple j * M.simple i) * M.simple j := by group
      _ = M.simple i * (M.simple i * M.simple j) * M.simple j := by rw [hcomm]
      _ = (M.simple i * M.simple i) * (M.simple j * M.simple j) := by group
      _ = 1 := by
        have hii : M.simple i * M.simple i = 1 := by
          change M.toCoxeterSystem.simple i * M.toCoxeterSystem.simple i = 1
          exact M.toCoxeterSystem.simple_mul_simple_self i
        have hjj : M.simple j * M.simple j = 1 := by
          change M.toCoxeterSystem.simple j * M.toCoxeterSystem.simple j = 1
          exact M.toCoxeterSystem.simple_mul_simple_self j
        rw [hii, hjj, mul_one]
  have hdvd : orderOf (M.simple i * M.simple j) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one hsq
  have hord : orderOf (M.simple i * M.simple j) = M.M i j := by
    change orderOf (M.toCoxeterSystem.simple i * M.toCoxeterSystem.simple j) = M.M i j
    exact M.toCoxeterSystem.orderOf_simple_mul_simple i j
  rw [hord] at hdvd
  have hle : M.M i j ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem ggSimple_exists_not_commute_of_mulEquiv {G : Type} [Group G] {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} {Γ : Type} [Fintype Γ] [DecidableEq Γ] [Nontrivial Γ]
    {M : CoxeterMatrix Γ} (hM : GGIsWeylMatrix M) (e : M.Group ≃* ↥A)
    (φ : Γ → MulAut ↥Bs) (hφ : ∀ i, ((e (M.simple i) : ↥A) : MulAut ↥Bs) = φ i)
    (i : Γ) : ∃ j : Γ, φ i * φ j ≠ φ j * φ i := by
  obtain ⟨j, hnc⟩ := ggSimple_exists_not_commute hM i
  refine ⟨j, ?_⟩
  intro hcomm
  apply hnc
  apply e.injective
  rw [map_mul, map_mul]
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [hφ i, hφ j]
  exact hcomm

theorem ggSimple_all_mem_of_choice {G : Type} [Group G] {Bs : Subgroup G}
    {AL AK : Subgroup (MulAut ↥Bs)} {Γ : Type} [Fintype Γ] [DecidableEq Γ] [Nontrivial Γ]
    {M : CoxeterMatrix Γ} (hM : GGIsWeylMatrix M) (e : M.Group ≃* ↥AK)
    (φ : Γ → MulAut ↥Bs) (hφ : ∀ i, ((e (M.simple i) : ↥AK) : MulAut ↥Bs) = φ i)
    (hgen : AK = Subgroup.closure (Set.range φ)) (r : MulAut ↥Bs)
    (hrAL : ∀ a ∈ AL, r * a = a * r) (hchoice : ∀ i, φ i ∈ AL ∨ φ i = r) :
    AK ≤ AL := by
  have hmem : ∀ i : Γ, φ i ∈ AL := by
    intro i
    rcases hchoice i with hi | hi
    · exact hi
    · exfalso
      obtain ⟨j, hnc⟩ := ggSimple_exists_not_commute_of_mulEquiv hM e φ hφ i
      rcases hchoice j with hj | hj
      · rw [hi] at hnc
        exact hnc (hrAL (φ j) hj)
      · rw [hi, hj] at hnc
        exact hnc rfl
  rw [hgen]
  exact (Subgroup.closure_le AL).mpr (by rintro _ ⟨i, rfl⟩; exact hmem i)

end CFSG.StandardType

end
