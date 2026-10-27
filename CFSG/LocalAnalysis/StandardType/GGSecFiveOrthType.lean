module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSetup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthCount
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthTyBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthTyDim
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import Certificates.Certificate7233Base

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.OrthF3

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  TauCeti

private def ct_tyd_embD (n : ℕ) (hn : 5 ≤ n) : Fin 5 → Fin n :=
  fun i => ⟨n - 5 + i.val, by omega⟩

private def ct_tyd_embA (m : ℕ) (hm : 6 ≤ m) : Fin 5 → Fin m :=
  fun i => ⟨if i.val < 4 then i.val else 5, by split_ifs <;> omega⟩

private def ct_tyd_embE6 : Fin 5 → Fin 6 := ![1, 3, 4, 5, 0]
private def ct_tyd_embE7 : Fin 5 → Fin 7 := ![1, 3, 4, 5, 0]
private def ct_tyd_embE8 : Fin 5 → Fin 8 := ![1, 3, 4, 5, 0]

private theorem ct_tyd_A_three (m : ℕ) (i j : Fin m) (hij : i ≠ j) :
    (CoxeterMatrix.A m) i j = 3 ↔ (SimpleGraph.pathGraph m).Adj i j := by
  rw [CoxeterMatrix.A]
  simp only [Matrix.of_apply, if_neg hij, SimpleGraph.pathGraph_adj]
  split_ifs <;> omega

private theorem ct_tyd_A_two (m : ℕ) (i j : Fin m) (hij : i ≠ j) :
    (CoxeterMatrix.A m) i j = 2 ↔ ¬ (SimpleGraph.pathGraph m).Adj i j := by
  have h23 : (CoxeterMatrix.A m) i j = 2 ∨ (CoxeterMatrix.A m) i j = 3 := by
    rw [CoxeterMatrix.A]
    simp only [Matrix.of_apply, if_neg hij]
    split_ifs <;> omega
  rw [← ct_tyd_A_three m i j hij]
  constructor
  · intro h h3; rw [h] at h3; omega
  · intro h3
    rcases h23 with h | h
    · exact h
    · exact absurd h h3

private theorem ct_tyd_D_ne (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    CartanMatrix.D n i j ≠ 0 ↔ ggOrthAdjFork n i j := by
  rw [CartanMatrix.D]
  simp only [Matrix.of_apply, if_neg hij]
  rw [ggOrthAdjFork]
  split_ifs <;> omega

private theorem ct_tyd_D_three (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (ggCoxeterMatrixD n) i j = 3 ↔ ggOrthAdjFork n i j := by
  rw [ggCoxeterMatrixD_apply, if_neg hij]
  by_cases hD : CartanMatrix.D n i j = 0
  · rw [if_pos hD]
    have hne : ¬ ggOrthAdjFork n i j := by rw [← ct_tyd_D_ne n i j hij]; exact fun h => h hD
    simp [hne]
  · rw [if_neg hD]
    have hne : ggOrthAdjFork n i j := (ct_tyd_D_ne n i j hij).mp hD
    simp [hne]

private theorem ct_tyd_D_two (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (ggCoxeterMatrixD n) i j = 2 ↔ ¬ ggOrthAdjFork n i j := by
  rw [ggCoxeterMatrixD_apply, if_neg hij]
  by_cases hD : CartanMatrix.D n i j = 0
  · rw [if_pos hD]
    have hne : ¬ ggOrthAdjFork n i j := by rw [← ct_tyd_D_ne n i j hij]; exact fun h => h hD
    simp [hne]
  · rw [if_neg hD]
    have hne : ggOrthAdjFork n i j := (ct_tyd_D_ne n i j hij).mp hD
    simp [hne]

private theorem ct_tyd_D_emb_three (n : ℕ) (hn : 5 ≤ n) (i j : Fin 5) (hij : i ≠ j) :
    (ggCoxeterMatrixD n) (ct_tyd_embD n hn i) (ct_tyd_embD n hn j) = 3 ↔ ggOrthAdjFork 5 i j := by
  rw [ct_tyd_D_three n _ _ (fun h => hij (by
    have := congrArg Fin.val h
    simp only [ct_tyd_embD] at this
    omega))]
  rw [ggOrthAdjFork]
  fin_cases i <;> fin_cases j <;> simp_all [ct_tyd_embD, ggOrthAdjFork] <;> omega

private theorem ct_tyd_D_emb_two (n : ℕ) (hn : 5 ≤ n) (i j : Fin 5) (hij : i ≠ j) :
    (ggCoxeterMatrixD n) (ct_tyd_embD n hn i) (ct_tyd_embD n hn j) = 2 ↔ ¬ ggOrthAdjFork 5 i j := by
  rw [ct_tyd_D_two n _ _ (fun h => hij (by
    have := congrArg Fin.val h
    simp only [ct_tyd_embD] at this
    omega))]
  rw [ggOrthAdjFork]
  fin_cases i <;> fin_cases j <;> simp_all [ct_tyd_embD, ggOrthAdjFork] <;> omega
private theorem ct_tyd_A_emb_three (m : ℕ) (hm : 6 ≤ m) (i j : Fin 5) (hij : i ≠ j) :
    (CoxeterMatrix.A m) (ct_tyd_embA m hm i) (ct_tyd_embA m hm j) = 3 ↔ ggOrthAdjPathIso i j := by
  rw [ct_tyd_A_three m _ _ (fun h => hij (by
    have := congrArg Fin.val h
    simp only [ct_tyd_embA] at this
    split_ifs at this <;> omega))]
  rw [ggOrthAdjPathIso]
  fin_cases i <;> fin_cases j <;> simp_all [ct_tyd_embA, SimpleGraph.pathGraph_adj]
private theorem ct_tyd_A_emb_two (m : ℕ) (hm : 6 ≤ m) (i j : Fin 5) (hij : i ≠ j) :
    (CoxeterMatrix.A m) (ct_tyd_embA m hm i) (ct_tyd_embA m hm j) = 2 ↔ ¬ ggOrthAdjPathIso i j := by
  rw [ct_tyd_A_two m _ _ (fun h => hij (by
    have := congrArg Fin.val h
    simp only [ct_tyd_embA] at this
    split_ifs at this <;> omega))]
  rw [ggOrthAdjPathIso]
  fin_cases i <;> fin_cases j <;> simp_all [ct_tyd_embA, SimpleGraph.pathGraph_adj]
private theorem ct_tyd_E6_three (i j : Fin 5) :
    CoxeterMatrix.E₆ (ct_tyd_embE6 i) (ct_tyd_embE6 j) = 3 ↔ ggOrthAdjPathIso i j := by
  fin_cases i <;> fin_cases j <;>
   simp [CoxeterMatrix.E₆, ct_tyd_embE6, ggOrthAdjPathIso, Matrix.of_apply, Matrix.cons_val']

private theorem ct_tyd_E6_two (i j : Fin 5) (hij : i ≠ j) :
    CoxeterMatrix.E₆ (ct_tyd_embE6 i) (ct_tyd_embE6 j) = 2 ↔ ¬ ggOrthAdjPathIso i j := by
  fin_cases i <;> fin_cases j <;>
   simp_all [CoxeterMatrix.E₆, ct_tyd_embE6, ggOrthAdjPathIso, Matrix.of_apply,
    Matrix.cons_val']
private theorem ct_tyd_E7_three (i j : Fin 5) :
    CoxeterMatrix.E₇ (ct_tyd_embE7 i) (ct_tyd_embE7 j) = 3 ↔ ggOrthAdjPathIso i j := by
  fin_cases i <;> fin_cases j <;>
   simp [CoxeterMatrix.E₇, ct_tyd_embE7, ggOrthAdjPathIso, Matrix.of_apply, Matrix.cons_val']

private theorem ct_tyd_E7_two (i j : Fin 5) (hij : i ≠ j) :
    CoxeterMatrix.E₇ (ct_tyd_embE7 i) (ct_tyd_embE7 j) = 2 ↔ ¬ ggOrthAdjPathIso i j := by
  fin_cases i <;> fin_cases j <;>
   simp_all [CoxeterMatrix.E₇, ct_tyd_embE7, ggOrthAdjPathIso, Matrix.of_apply,
    Matrix.cons_val']
private theorem ct_tyd_E8_three (i j : Fin 5) :
    CoxeterMatrix.E₈ (ct_tyd_embE8 i) (ct_tyd_embE8 j) = 3 ↔ ggOrthAdjPathIso i j := by
  fin_cases i <;> fin_cases j <;>
   simp [CoxeterMatrix.E₈, ct_tyd_embE8, ggOrthAdjPathIso, Matrix.of_apply, Matrix.cons_val']

private theorem ct_tyd_E8_two (i j : Fin 5) (hij : i ≠ j) :
    CoxeterMatrix.E₈ (ct_tyd_embE8 i) (ct_tyd_embE8 j) = 2 ↔ ¬ ggOrthAdjPathIso i j := by
  fin_cases i <;> fin_cases j <;>
   simp_all [CoxeterMatrix.E₈, ct_tyd_embE8, ggOrthAdjPathIso, Matrix.of_apply,
    Matrix.cons_val']
private theorem ct_tyd_embD_injective (n : ℕ) (hn : 5 ≤ n) :
    Function.Injective (ct_tyd_embD n hn) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [ct_tyd_embD] at hv
  omega
private theorem ct_tyd_embA_injective (m : ℕ) (hm : 6 ≤ m) :
    Function.Injective (ct_tyd_embA m hm) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [ct_tyd_embA] at hv
  split_ifs at hv <;> omega

private theorem ct_tyd_embE6_injective : Function.Injective ct_tyd_embE6 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [ct_tyd_embE6]

private theorem ct_tyd_embE7_injective : Function.Injective ct_tyd_embE7 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [ct_tyd_embE7]

private theorem ct_tyd_embE8_injective : Function.Injective ct_tyd_embE8 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [ct_tyd_embE8]

private theorem ct_tyd_finrank_le_of_independent {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [finV : FiniteDimensional (ZMod 3) V]
    {k : ℕ} {w : Fin k → V} {U : Submodule (ZMod 3) V} (hw : ∀ i, w i ∈ U)
    (hind : LinearIndependent (ZMod 3) w) :
    k ≤ Module.finrank (ZMod 3) U := by
  have hspan : Submodule.span (ZMod 3) (Set.range w) ≤ U :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hw i)
  have hfin : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range w)) = k := by
    simpa using finrank_span_eq_card hind
  rw [← hfin]
  exact Submodule.finrank_mono hspan


private theorem ct_tyd_polar_zero_on_span
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {κ : Type} {x : κ → V} {y : V}
    (h : ∀ i, QuadraticMap.polar Q (x i) y = 0) :
    ∀ u ∈ Submodule.span (ZMod 3) (Set.range x), QuadraticMap.polar Q u y = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem z hz => rcases hz with ⟨i, rfl⟩; exact h i
  | zero => exact QuadraticMap.polar_zero_left Q y
  | add a b _ _ ha hb =>
      simp only [QuadraticMap.polar_add_left, ha, hb, add_zero]
  | smul c a _ ha =>
      simp only [QuadraticMap.polar_smul_left, ha, smul_zero]

private theorem ct_tyd_aniso_of_hyperplane
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [finV : FiniteDimensional (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} (hQ : PolarNondeg3 Q)
    {U : Submodule (ZMod 3) V} {y : V}
    (hUfin : Module.finrank (ZMod 3) U + 1 = Module.finrank (ZMod 3) V)
    (hyU : y ∉ U)
    (hperp : ∀ u ∈ U, QuadraticMap.polar Q u y = 0) :
    Q y ≠ 0 := by
  intro hQy
  have hyne : y ≠ 0 := by
    intro h0
    apply hyU
    rw [h0]
    exact Submodule.zero_mem _
  have htop : U ⊔ Submodule.span (ZMod 3) {y} = ⊤ := by
    apply Submodule.eq_top_of_disjoint
    · rw [finrank_span_singleton hyne]
      omega
    · exact Submodule.disjoint_span_singleton_of_notMem hyU
  have hall : ∀ z, QuadraticMap.polar Q z y = 0 := by
    intro z
    have hz : z ∈ U ⊔ Submodule.span (ZMod 3) {y} := by
      rw [htop]
      trivial
    rcases Submodule.mem_sup.mp hz with ⟨u, hu, c, hc, rfl⟩
    rcases Submodule.mem_span_singleton.mp hc with ⟨a, rfl⟩
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hperp u hu,
      zero_add, QuadraticMap.polar_self, hQy, smul_zero]
  have hy0 : y = 0 := hQ.2 y (fun z => by simpa using hall z)
  exact hyne hy0

private theorem ct_tyd_path_four_data
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [finV : FiniteDimensional (ZMod 3) V]
    {κ : Type} {M : CoxeterMatrix κ}
    {Q : QuadraticForm (ZMod 3) V} {v : κ → V} {U : Submodule (ZMod 3) V}
    {w : Fin 4 → κ} (hwinj : Function.Injective w)
    (hQ : ∀ i, Q (v i) ≠ 0)
    (h2 : ∀ i j, i ≠ j → M.M i j = 2 → QuadraticMap.polar Q (v i) (v j) = 0)
    (h3 : ∀ i j, i ≠ j → M.M i j = 3 →
      QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
        QuadraticMap.polar Q (v i) (v j) ≠ 0)
    (hM2 : ∀ i j : Fin 4, i ≠ j → ¬ (SimpleGraph.pathGraph 4).Adj i j →
      M.M (w i) (w j) = 2)
    (hM3 : ∀ i j : Fin 4, i ≠ j → (SimpleGraph.pathGraph 4).Adj i j →
      M.M (w i) (w j) = 3)
    (hU : ∀ i, v (w i) ∈ U) :
    LinearIndependent (ZMod 3) (fun i => v (w i)) ∧
      (∀ u ∈ Submodule.span (ZMod 3) (Set.range (fun i => v (w i))),
        (∀ i, QuadraticMap.polar Q (v (w i)) u = 0) → u = 0) ∧
      4 ≤ Module.finrank (ZMod 3) U := by
  have hQ' : ∀ i : Fin 4, Q (v (w i)) ≠ 0 := fun i => hQ (w i)
  have h2' : ∀ i j : Fin 4, i ≠ j → ¬ (SimpleGraph.pathGraph 4).Adj i j →
      QuadraticMap.polar Q (v (w i)) (v (w j)) = 0 := by
    intro i j hij h
    exact h2 (w i) (w j) (fun hh => hij (hwinj hh)) (hM2 i j hij h)
  have h3' : ∀ i j : Fin 4, i ≠ j → (SimpleGraph.pathGraph 4).Adj i j →
      QuadraticMap.polar Q (v (w i)) (v (w j)) ^ 2 =
          Q (v (w i)) * Q (v (w j)) ∧
        QuadraticMap.polar Q (v (w i)) (v (w j)) ≠ 0 := by
    intro i j hij h
    exact h3 (w i) (w j) (fun hh => hij (hwinj hh)) (hM3 i j hij h)
  obtain ⟨hind, horth⟩ :=
    ggOrthGram_path_four Q (fun i => v (w i)) hQ' h2' h3'
  exact ⟨hind, horth,
    ct_tyd_finrank_le_of_independent (finV := finV) (fun i => hU i) hind⟩

private theorem ct_tyd_path_iso_le_finrank
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [finV : FiniteDimensional (ZMod 3) V]
    {κ : Type} {M : CoxeterMatrix κ}
    {Q : QuadraticForm (ZMod 3) V} {v : κ → V} {U : Submodule (ZMod 3) V}
    {w : Fin 5 → κ} (hwinj : Function.Injective w)
    (hQ : ∀ i, Q (v i) ≠ 0)
    (h2 : ∀ i j, i ≠ j → M.M i j = 2 → QuadraticMap.polar Q (v i) (v j) = 0)
    (h3 : ∀ i j, i ≠ j → M.M i j = 3 →
      QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
        QuadraticMap.polar Q (v i) (v j) ≠ 0)
    (hM2 : ∀ i j : Fin 5, i ≠ j → ¬ ggOrthAdjPathIso i j → M.M (w i) (w j) = 2)
    (hM3 : ∀ i j : Fin 5, i ≠ j → ggOrthAdjPathIso i j → M.M (w i) (w j) = 3)
    (hU : ∀ i, v (w i) ∈ U) :
    5 ≤ Module.finrank (ZMod 3) U := by
  have hQ' : ∀ i : Fin 5, Q (v (w i)) ≠ 0 := fun i => hQ (w i)
  have h2' : ∀ i j : Fin 5, i ≠ j → ¬ ggOrthAdjPathIso i j →
      QuadraticMap.polar Q (v (w i)) (v (w j)) = 0 := by
    intro i j hij h
    exact h2 (w i) (w j) (fun hh => hij (hwinj hh)) (hM2 i j hij h)
  have h3' : ∀ i j : Fin 5, i ≠ j → ggOrthAdjPathIso i j →
      QuadraticMap.polar Q (v (w i)) (v (w j)) ^ 2 =
          Q (v (w i)) * Q (v (w j)) ∧
        QuadraticMap.polar Q (v (w i)) (v (w j)) ≠ 0 := by
    intro i j hij h
    exact h3 (w i) (w j) (fun hh => hij (hwinj hh)) (hM3 i j hij h)
  obtain ⟨hind, -⟩ := ggOrthGram_path_iso Q (fun i => v (w i)) hQ' h2' h3'
  exact ct_tyd_finrank_le_of_independent (finV := finV) (fun i => hU i) hind

private theorem ct_tyd_fork_four_le_finrank
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [finV : FiniteDimensional (ZMod 3) V]
    {κ : Type} {M : CoxeterMatrix κ}
    {Q : QuadraticForm (ZMod 3) V} {v : κ → V} {U : Submodule (ZMod 3) V}
    {w : Fin 4 → κ} (hwinj : Function.Injective w)
    (hQ : ∀ i, Q (v i) ≠ 0)
    (h2 : ∀ i j, i ≠ j → M.M i j = 2 → QuadraticMap.polar Q (v i) (v j) = 0)
    (h3 : ∀ i j, i ≠ j → M.M i j = 3 →
      QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
        QuadraticMap.polar Q (v i) (v j) ≠ 0)
    (hM2 : ∀ i j : Fin 4, i ≠ j → ¬ ggOrthAdjFork 4 i j → M.M (w i) (w j) = 2)
    (hM3 : ∀ i j : Fin 4, i ≠ j → ggOrthAdjFork 4 i j → M.M (w i) (w j) = 3)
    (hU : ∀ i, v (w i) ∈ U) :
    4 ≤ Module.finrank (ZMod 3) U := by
  have hQ' : ∀ i : Fin 4, Q (v (w i)) ≠ 0 := fun i => hQ (w i)
  have h2' : ∀ i j : Fin 4, i ≠ j → ¬ ggOrthAdjFork 4 i j →
      QuadraticMap.polar Q (v (w i)) (v (w j)) = 0 := by
    intro i j hij h
    exact h2 (w i) (w j) (fun hh => hij (hwinj hh)) (hM2 i j hij h)
  have h3' : ∀ i j : Fin 4, i ≠ j → ggOrthAdjFork 4 i j →
      QuadraticMap.polar Q (v (w i)) (v (w j)) ^ 2 =
          Q (v (w i)) * Q (v (w j)) ∧
        QuadraticMap.polar Q (v (w i)) (v (w j)) ≠ 0 := by
    intro i j hij h
    exact h3 (w i) (w j) (fun hh => hij (hwinj hh)) (hM3 i j hij h)
  obtain ⟨hind, -⟩ := ggOrthGram_fork_four Q (fun i => v (w i)) hQ' h2' h3'
  exact ct_tyd_finrank_le_of_independent (finV := finV) (fun i => hU i) hind

private theorem ct_tyd_fork_five_le_finrank
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [finV : FiniteDimensional (ZMod 3) V]
    {κ : Type} {M : CoxeterMatrix κ}
    {Q : QuadraticForm (ZMod 3) V} {v : κ → V} {U : Submodule (ZMod 3) V}
    {w : Fin 5 → κ} (hwinj : Function.Injective w)
    (hQ : ∀ i, Q (v i) ≠ 0)
    (h2 : ∀ i j, i ≠ j → M.M i j = 2 → QuadraticMap.polar Q (v i) (v j) = 0)
    (h3 : ∀ i j, i ≠ j → M.M i j = 3 →
      QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
        QuadraticMap.polar Q (v i) (v j) ≠ 0)
    (hM2 : ∀ i j : Fin 5, i ≠ j → ¬ ggOrthAdjFork 5 i j → M.M (w i) (w j) = 2)
    (hM3 : ∀ i j : Fin 5, i ≠ j → ggOrthAdjFork 5 i j → M.M (w i) (w j) = 3)
    (hU : ∀ i, v (w i) ∈ U) :
    5 ≤ Module.finrank (ZMod 3) U := by
  have hQ' : ∀ i : Fin 5, Q (v (w i)) ≠ 0 := fun i => hQ (w i)
  have h2' : ∀ i j : Fin 5, i ≠ j → ¬ ggOrthAdjFork 5 i j →
      QuadraticMap.polar Q (v (w i)) (v (w j)) = 0 := by
    intro i j hij h
    exact h2 (w i) (w j) (fun hh => hij (hwinj hh)) (hM2 i j hij h)
  have h3' : ∀ i j : Fin 5, i ≠ j → ggOrthAdjFork 5 i j →
      QuadraticMap.polar Q (v (w i)) (v (w j)) ^ 2 =
          Q (v (w i)) * Q (v (w j)) ∧
        QuadraticMap.polar Q (v (w i)) (v (w j)) ≠ 0 := by
    intro i j hij h
    exact h3 (w i) (w j) (fun hh => hij (hwinj hh)) (hM3 i j hij h)
  obtain ⟨hind, -⟩ := ggOrthGram_fork_five Q (fun i => v (w i)) hQ' h2' h3'
  exact ct_tyd_finrank_le_of_independent (finV := finV) (fun i => hU i) hind



section CaseHelpers


variable {G : Type} [Group G]
variable {Bs L : Subgroup G} {x : G}
variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
variable {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V}

private theorem ct_tyd_PSL_A3
    {n f : ℕ}
    (hWeyl : GGWeylOfType 3 (CoxeterMatrix.A (n - 1)) (ggAutomizer L Bs))
    {U : Submodule (ZMod 3) V}
    (hUfin : Module.finrank (ZMod 3) U + 1 = Module.finrank (ZMod 3) V)
    (hUle : Module.finrank (ZMod 3) U ≤ (ggU .PSL n f).D.rank)
    (hr : (ggU .PSL n f).D.rank = n - 1)
    (hm : n - 1 = 3)
    (hdim : Module.finrank (ZMod 3) V = 4 ∨ Module.finrank (ZMod 3) V = 5) :
    Module.finrank (ZMod 3) V = 4 ∧
      GGWeylOfType 3 (CoxeterMatrix.A 3) (ggAutomizer L Bs) := by
  have hUle3 : Module.finrank (ZMod 3) U ≤ 3 := by
    rw [hr, hm] at hUle
    exact hUle
  have hV4 : Module.finrank (ZMod 3) V = 4 := by
    rcases hdim with h | h
    · exact h
    · exfalso
      omega
  refine ⟨hV4, ?_⟩
  rw [hm] at hWeyl
  exact hWeyl

private theorem ct_tyd_PSL_A4_roots
    (hV : FiniteDimensional (ZMod 3) V)
    {n f : ℕ}
    {e : Fin (n - 1) ≃ Fin (ggU .PSL n f).D.rank}
    (he : coxeterMatrix (ggU .PSL n f).D.isFiniteType =
      (CoxeterMatrix.A (n - 1)).reindex e)
    {v : Fin (ggU .PSL n f).D.rank → V}
    (hvQ : ∀ i, Q (v i) ≠ 0)
    (hv2 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .PSL n f).D.isFiniteType).M i j = 2 →
      QuadraticMap.polar Q (v i) (v j) = 0)
    (hv3 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .PSL n f).D.isFiniteType).M i j = 3 →
      QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
        QuadraticMap.polar Q (v i) (v j) ≠ 0)
    {U : Submodule (ZMod 3) V}
    (hU : ∀ i, v i ∈ U)
    (hUle : Module.finrank (ZMod 3) U ≤ (ggU .PSL n f).D.rank)
    (hr : (ggU .PSL n f).D.rank = n - 1)
    (hm : n - 1 = 4) :
    ∃ w : Fin 4 → Fin (ggU .PSL n f).D.rank,
      Function.Injective w ∧
      LinearIndependent (ZMod 3) (fun i => v (w i)) ∧
      (∀ u ∈ Submodule.span (ZMod 3) (Set.range (fun i => v (w i))),
        (∀ i, QuadraticMap.polar Q (v (w i)) u = 0) → u = 0) ∧
      Module.finrank (ZMod 3) U = 4 := by
  let w : Fin 4 → Fin (ggU .PSL n f).D.rank := fun i => e (Fin.cast hm.symm i)
  have hwinj : Function.Injective w := by
    intro i j h
    exact Fin.cast_injective hm.symm (e.injective h)
  have hM2 : ∀ i j : Fin 4, i ≠ j → ¬ (SimpleGraph.pathGraph 4).Adj i j →
      (coxeterMatrix (ggU .PSL n f).D.isFiniteType).M (w i) (w j) = 2 := by
    intro i j hij h
    simp only [w, he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
    rw [ct_tyd_A_two (n - 1) (Fin.cast hm.symm i) (Fin.cast hm.symm j)
      (fun hh => hij (Fin.cast_injective hm.symm hh))]
    simpa [SimpleGraph.pathGraph_adj] using h
  have hM3 : ∀ i j : Fin 4, i ≠ j → (SimpleGraph.pathGraph 4).Adj i j →
      (coxeterMatrix (ggU .PSL n f).D.isFiniteType).M (w i) (w j) = 3 := by
    intro i j hij h
    simp only [w, he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
    rw [ct_tyd_A_three (n - 1) (Fin.cast hm.symm i) (Fin.cast hm.symm j)
      (fun hh => hij (Fin.cast_injective hm.symm hh))]
    simpa [SimpleGraph.pathGraph_adj] using h
  have hUw : ∀ i, v (w i) ∈ U := fun i => hU (w i)
  obtain ⟨hind, horth, hUge4⟩ :=
    ct_tyd_path_four_data (finV := hV) hwinj hvQ hv2 hv3 hM2 hM3 hUw
  have hUle4 : Module.finrank (ZMod 3) U ≤ 4 := by
    rw [hr, hm] at hUle
    exact hUle
  have hUeq : Module.finrank (ZMod 3) U = 4 := le_antisymm hUle4 hUge4
  exact ⟨w, hwinj, hind, horth, hUeq⟩

private theorem ct_tyd_PSL_A4
    (hV : FiniteDimensional (ZMod 3) V)
    (hnondeg : PolarNondeg3 Q)
    {n f : ℕ}
    {e : Fin (n - 1) ≃ Fin (ggU .PSL n f).D.rank}
    (he : coxeterMatrix (ggU .PSL n f).D.isFiniteType =
      (CoxeterMatrix.A (n - 1)).reindex e)
    {v : Fin (ggU .PSL n f).D.rank → V}
    (hvQ : ∀ i, Q (v i) ≠ 0)
    (hv2 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .PSL n f).D.isFiniteType).M i j = 2 →
      QuadraticMap.polar Q (v i) (v j) = 0)
    (hv3 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .PSL n f).D.isFiniteType).M i j = 3 →
      QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
        QuadraticMap.polar Q (v i) (v j) ≠ 0)
    {U : Submodule (ZMod 3) V}
    (hU : ∀ i, v i ∈ U)
    (hUfin : Module.finrank (ZMod 3) U + 1 = Module.finrank (ZMod 3) V)
    (hUle : Module.finrank (ZMod 3) U ≤ (ggU .PSL n f).D.rank)
    (hr : (ggU .PSL n f).D.rank = n - 1)
    (hm : n - 1 = 4)
    (hWeyl : GGWeylOfType 3 (CoxeterMatrix.A 4) (ggAutomizer L Bs))
    (hx : x ∈ Bs) (hxne : ι (Additive.ofMul ⟨x, hx⟩) ≠ 0)
    (hxperp : ∀ i, QuadraticMap.polar Q (v i)
      (ι (Additive.ofMul ⟨x, hx⟩)) = 0) :
    Module.finrank (ZMod 3) V = 5 ∧
      GGWeylOfType 3 (CoxeterMatrix.A 4) (ggAutomizer L Bs) ∧
      ∃ hx : x ∈ Bs, Q (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0 := by
  obtain ⟨w, -, hind, horth, hUeq⟩ :=
    ct_tyd_PSL_A4_roots hV he hvQ hv2 hv3 hU hUle hr hm
  have hUw : ∀ i, v (w i) ∈ U := fun i => hU (w i)
  have hspanw : Submodule.span (ZMod 3) (Set.range (fun i => v (w i))) = U := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hUw i)
    · rw [finrank_span_eq_card hind, hUeq, Fintype.card_fin]
  have hd5 : Module.finrank (ZMod 3) V = 5 := by omega
  set y : V := ι (Additive.ofMul ⟨x, hx⟩) with hydef
  have hyne : y ≠ 0 := by rw [hydef]; exact hxne
  have hperp : ∀ i, QuadraticMap.polar Q (v (w i)) y = 0 := by
    intro i
    rw [hydef]
    exact hxperp (w i)
  have hyUnot : y ∉ U := by
    intro hy
    have h0 : y = 0 := horth y (by rw [hspanw]; exact hy) hperp
    exact hyne h0
  have hyaniso : Q y ≠ 0 :=
    ct_tyd_aniso_of_hyperplane (finV := hV) hnondeg hUfin hyUnot (by
      rw [← hspanw]
      exact ct_tyd_polar_zero_on_span hperp)
  refine ⟨hd5, hWeyl, hx, ?_⟩
  rw [← hydef]
  exact hyaniso

private theorem ct_tyd_PSL_A5
    (hV : FiniteDimensional (ZMod 3) V)
    {n f : ℕ}
    {e : Fin (n - 1) ≃ Fin (ggU .PSL n f).D.rank}
    (he : coxeterMatrix (ggU .PSL n f).D.isFiniteType =
      (CoxeterMatrix.A (n - 1)).reindex e)
    {v : Fin (ggU .PSL n f).D.rank → V}
    (hvQ : ∀ i, Q (v i) ≠ 0)
    (hv2 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .PSL n f).D.isFiniteType).M i j = 2 →
      QuadraticMap.polar Q (v i) (v j) = 0)
    (hv3 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .PSL n f).D.isFiniteType).M i j = 3 →
      QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
        QuadraticMap.polar Q (v i) (v j) ≠ 0)
    {U : Submodule (ZMod 3) V}
    (hU : ∀ i, v i ∈ U)
    (hUfin : Module.finrank (ZMod 3) U + 1 = Module.finrank (ZMod 3) V)
    (hdim : Module.finrank (ZMod 3) V = 4 ∨ Module.finrank (ZMod 3) V = 5)
    (hm : n - 1 = 5)
    (hWeyl : GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer L Bs)) :
    Module.finrank (ZMod 3) V = 5 ∧
      GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer L Bs) := by
  let w : Fin 4 → Fin (ggU .PSL n f).D.rank :=
    fun i => e (Fin.cast hm.symm (Fin.castSucc i))
  have hwinj : Function.Injective w := by
    intro i j h
    exact Fin.ext (by simpa using congrArg Fin.val (e.injective h))
  have hM2 : ∀ i j : Fin 4, i ≠ j → ¬ (SimpleGraph.pathGraph 4).Adj i j →
      (coxeterMatrix (ggU .PSL n f).D.isFiniteType).M (w i) (w j) = 2 := by
    intro i j hij h
    simp only [w, he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
    rw [ct_tyd_A_two (n - 1) (Fin.cast hm.symm (Fin.castSucc i))
      (Fin.cast hm.symm (Fin.castSucc j))
      (fun hh => hij (Fin.ext (by simpa using congrArg Fin.val hh)))]
    simpa [SimpleGraph.pathGraph_adj] using h
  have hM3 : ∀ i j : Fin 4, i ≠ j → (SimpleGraph.pathGraph 4).Adj i j →
      (coxeterMatrix (ggU .PSL n f).D.isFiniteType).M (w i) (w j) = 3 := by
    intro i j hij h
    simp only [w, he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
    rw [ct_tyd_A_three (n - 1) (Fin.cast hm.symm (Fin.castSucc i))
      (Fin.cast hm.symm (Fin.castSucc j))
      (fun hh => hij (Fin.ext (by simpa using congrArg Fin.val hh)))]
    simpa [SimpleGraph.pathGraph_adj] using h
  have hUw : ∀ i, v (w i) ∈ U := fun i => hU (w i)
  obtain ⟨-, -, hUge4⟩ :=
    ct_tyd_path_four_data (finV := hV) hwinj hvQ hv2 hv3 hM2 hM3 hUw
  have hd5 : Module.finrank (ZMod 3) V = 5 := by
    rcases hdim with h | h <;> omega
  exact ⟨hd5, hWeyl⟩

private theorem ct_tyd_PSL_high
    (hV : FiniteDimensional (ZMod 3) V)
    {n f : ℕ}
    {e : Fin (n - 1) ≃ Fin (ggU .PSL n f).D.rank}
    (he : coxeterMatrix (ggU .PSL n f).D.isFiniteType =
      (CoxeterMatrix.A (n - 1)).reindex e)
    {v : Fin (ggU .PSL n f).D.rank → V}
    (hvQ : ∀ i, Q (v i) ≠ 0)
    (hv2 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .PSL n f).D.isFiniteType).M i j = 2 →
      QuadraticMap.polar Q (v i) (v j) = 0)
    (hv3 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .PSL n f).D.isFiniteType).M i j = 3 →
      QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
        QuadraticMap.polar Q (v i) (v j) ≠ 0)
    {U : Submodule (ZMod 3) V}
    (hU : ∀ i, v i ∈ U)
    (hUfin : Module.finrank (ZMod 3) U + 1 = Module.finrank (ZMod 3) V)
    (hdim : Module.finrank (ZMod 3) V = 4 ∨ Module.finrank (ZMod 3) V = 5)
    (h6 : 6 ≤ n - 1) :
    False := by
  let w : Fin 5 → Fin (ggU .PSL n f).D.rank :=
    fun i => e (ct_tyd_embA (n - 1) h6 i)
  have hwinj : Function.Injective w := by
    intro i j h
    exact ct_tyd_embA_injective (n - 1) h6 (e.injective h)
  have hM2 : ∀ i j : Fin 5, i ≠ j → ¬ ggOrthAdjPathIso i j →
      (coxeterMatrix (ggU .PSL n f).D.isFiniteType).M (w i) (w j) = 2 := by
    intro i j hij h
    simpa only [w, he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply] using
      (ct_tyd_A_emb_two (n - 1) h6 i j hij).mpr h
  have hM3 : ∀ i j : Fin 5, i ≠ j → ggOrthAdjPathIso i j →
      (coxeterMatrix (ggU .PSL n f).D.isFiniteType).M (w i) (w j) = 3 := by
    intro i j hij h
    simpa only [w, he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply] using
      (ct_tyd_A_emb_three (n - 1) h6 i j hij).mpr h
  have hUw : ∀ i, v (w i) ∈ U := fun i => hU (w i)
  have hUge5 :=
    ct_tyd_path_iso_le_finrank (finV := hV) hwinj hvQ hv2 hv3 hM2 hM3 hUw
  rcases hdim with h | h <;> omega

private theorem ct_tyd_POmegaPlus_four
    (hV : FiniteDimensional (ZMod 3) V)
    {n f : ℕ} (hn4 : n = 4)
    {e : Fin n ≃ Fin (ggU .POmegaPlus n f).D.rank}
    (he : coxeterMatrix (ggU .POmegaPlus n f).D.isFiniteType =
      (ggCoxeterMatrixD n).reindex e)
    {v : Fin (ggU .POmegaPlus n f).D.rank → V}
    (hvQ : ∀ i, Q (v i) ≠ 0)
    (hv2 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .POmegaPlus n f).D.isFiniteType).M i j = 2 →
      QuadraticMap.polar Q (v i) (v j) = 0)
    (hv3 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .POmegaPlus n f).D.isFiniteType).M i j = 3 →
      QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
        QuadraticMap.polar Q (v i) (v j) ≠ 0)
    {U : Submodule (ZMod 3) V}
    (hU : ∀ i, v i ∈ U)
    (hUfin : Module.finrank (ZMod 3) U + 1 = Module.finrank (ZMod 3) V)
    (hdim : Module.finrank (ZMod 3) V = 4 ∨ Module.finrank (ZMod 3) V = 5)
    (hWeyl : GGWeylOfType 3 (ggCoxeterMatrixD 4) (ggAutomizer L Bs)) :
    Module.finrank (ZMod 3) V = 5 ∧
      GGWeylOfType 3 (ggCoxeterMatrixD 4) (ggAutomizer L Bs) := by
  subst n
  let w : Fin 4 → Fin (ggU .POmegaPlus 4 f).D.rank := e
  have hwinj : Function.Injective w := by simpa [w] using e.injective
  have hM2 : ∀ i j : Fin 4, i ≠ j → ¬ ggOrthAdjFork 4 i j →
      (coxeterMatrix (ggU .POmegaPlus 4 f).D.isFiniteType).M (w i) (w j) = 2 := by
    intro i j hij h
    simp only [w, he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
    exact (ct_tyd_D_two 4 i j hij).mpr h
  have hM3 : ∀ i j : Fin 4, i ≠ j → ggOrthAdjFork 4 i j →
      (coxeterMatrix (ggU .POmegaPlus 4 f).D.isFiniteType).M (w i) (w j) = 3 := by
    intro i j hij h
    simp only [w, he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
    exact (ct_tyd_D_three 4 i j hij).mpr h
  have hUw : ∀ i, v (w i) ∈ U := fun i => hU (w i)
  have hUge4 :=
    ct_tyd_fork_four_le_finrank (finV := hV) hwinj hvQ hv2 hv3 hM2 hM3 hUw
  have hd5 : Module.finrank (ZMod 3) V = 5 := by
    rcases hdim with h | h
    · exfalso
      omega
    · exact h
  exact ⟨hd5, hWeyl⟩

private theorem ct_tyd_POmegaPlus_five
    (hV : FiniteDimensional (ZMod 3) V)
    {n f : ℕ} (hn5 : n = 5)
    {e : Fin n ≃ Fin (ggU .POmegaPlus n f).D.rank}
    (he : coxeterMatrix (ggU .POmegaPlus n f).D.isFiniteType =
      (ggCoxeterMatrixD n).reindex e)
    {v : Fin (ggU .POmegaPlus n f).D.rank → V}
    (hvQ : ∀ i, Q (v i) ≠ 0)
    (hv2 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .POmegaPlus n f).D.isFiniteType).M i j = 2 →
      QuadraticMap.polar Q (v i) (v j) = 0)
    (hv3 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .POmegaPlus n f).D.isFiniteType).M i j = 3 →
      QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
        QuadraticMap.polar Q (v i) (v j) ≠ 0)
    {U : Submodule (ZMod 3) V}
    (hU : ∀ i, v i ∈ U)
    (hUfin : Module.finrank (ZMod 3) U + 1 = Module.finrank (ZMod 3) V)
    (hdim : Module.finrank (ZMod 3) V = 4 ∨ Module.finrank (ZMod 3) V = 5) :
    False := by
  subst n
  let w : Fin 5 → Fin (ggU .POmegaPlus 5 f).D.rank := e
  have hwinj : Function.Injective w := by simpa [w] using e.injective
  have hM2 : ∀ i j : Fin 5, i ≠ j → ¬ ggOrthAdjFork 5 i j →
      (coxeterMatrix (ggU .POmegaPlus 5 f).D.isFiniteType).M (w i) (w j) = 2 := by
    intro i j hij h
    simp only [w, he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
    exact (ct_tyd_D_two 5 i j hij).mpr h
  have hM3 : ∀ i j : Fin 5, i ≠ j → ggOrthAdjFork 5 i j →
      (coxeterMatrix (ggU .POmegaPlus 5 f).D.isFiniteType).M (w i) (w j) = 3 := by
    intro i j hij h
    simp only [w, he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
    exact (ct_tyd_D_three 5 i j hij).mpr h
  have hUw : ∀ i, v (w i) ∈ U := fun i => hU (w i)
  have hUge5 :=
    ct_tyd_fork_five_le_finrank (finV := hV) hwinj hvQ hv2 hv3 hM2 hM3 hUw
  rcases hdim with h | h <;> omega

private theorem ct_tyd_POmegaPlus_high
    (hV : FiniteDimensional (ZMod 3) V)
    {n f : ℕ} (h5 : 5 ≤ n)
    {e : Fin n ≃ Fin (ggU .POmegaPlus n f).D.rank}
    (he : coxeterMatrix (ggU .POmegaPlus n f).D.isFiniteType =
      (ggCoxeterMatrixD n).reindex e)
    {v : Fin (ggU .POmegaPlus n f).D.rank → V}
    (hvQ : ∀ i, Q (v i) ≠ 0)
    (hv2 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .POmegaPlus n f).D.isFiniteType).M i j = 2 →
      QuadraticMap.polar Q (v i) (v j) = 0)
    (hv3 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .POmegaPlus n f).D.isFiniteType).M i j = 3 →
      QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
        QuadraticMap.polar Q (v i) (v j) ≠ 0)
    {U : Submodule (ZMod 3) V}
    (hU : ∀ i, v i ∈ U)
    (hUfin : Module.finrank (ZMod 3) U + 1 = Module.finrank (ZMod 3) V)
    (hdim : Module.finrank (ZMod 3) V = 4 ∨ Module.finrank (ZMod 3) V = 5) :
    False := by
  let w : Fin 5 → Fin (ggU .POmegaPlus n f).D.rank :=
    fun i => e (ct_tyd_embD n h5 i)
  have hwinj : Function.Injective w := by
    intro i j h
    exact ct_tyd_embD_injective n h5 (e.injective h)
  have hM2 : ∀ i j : Fin 5, i ≠ j → ¬ ggOrthAdjFork 5 i j →
      (coxeterMatrix (ggU .POmegaPlus n f).D.isFiniteType).M (w i) (w j) = 2 := by
    intro i j hij h
    simpa only [w, he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply] using
      (ct_tyd_D_emb_two n h5 i j hij).mpr h
  have hM3 : ∀ i j : Fin 5, i ≠ j → ggOrthAdjFork 5 i j →
      (coxeterMatrix (ggU .POmegaPlus n f).D.isFiniteType).M (w i) (w j) = 3 := by
    intro i j hij h
    simpa only [w, he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply] using
      (ct_tyd_D_emb_three n h5 i j hij).mpr h
  have hUw : ∀ i, v (w i) ∈ U := fun i => hU (w i)
  have hUge5 :=
    ct_tyd_fork_five_le_finrank (finV := hV) hwinj hvQ hv2 hv3 hM2 hM3 hUw
  rcases hdim with h | h <;> omega

private theorem ct_tyd_E6_case
    (hV : FiniteDimensional (ZMod 3) V)
    {n f : ℕ}
    {e : Fin 6 ≃ Fin (ggU .E6 n f).D.rank}
    (he : coxeterMatrix (ggU .E6 n f).D.isFiniteType = CoxeterMatrix.E₆.reindex e)
    {v : Fin (ggU .E6 n f).D.rank → V}
    (hvQ : ∀ i, Q (v i) ≠ 0)
    (hv2 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .E6 n f).D.isFiniteType).M i j = 2 →
      QuadraticMap.polar Q (v i) (v j) = 0)
    (hv3 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .E6 n f).D.isFiniteType).M i j = 3 →
      QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
        QuadraticMap.polar Q (v i) (v j) ≠ 0)
    {U : Submodule (ZMod 3) V}
    (hU : ∀ i, v i ∈ U)
    (hUfin : Module.finrank (ZMod 3) U + 1 = Module.finrank (ZMod 3) V)
    (hdim : Module.finrank (ZMod 3) V = 4 ∨ Module.finrank (ZMod 3) V = 5) :
    False := by
  let w : Fin 5 → Fin (ggU .E6 n f).D.rank := fun i => e (ct_tyd_embE6 i)
  have hwinj : Function.Injective w := by
    intro i j h
    exact ct_tyd_embE6_injective (e.injective h)
  have hM2 : ∀ i j : Fin 5, i ≠ j → ¬ ggOrthAdjPathIso i j →
      (coxeterMatrix (ggU .E6 n f).D.isFiniteType).M (w i) (w j) = 2 := by
    intro i j hij h
    simp only [w, he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
    exact (ct_tyd_E6_two i j hij).mpr h
  have hM3 : ∀ i j : Fin 5, i ≠ j → ggOrthAdjPathIso i j →
      (coxeterMatrix (ggU .E6 n f).D.isFiniteType).M (w i) (w j) = 3 := by
    intro i j hij h
    simp only [w, he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
    exact (ct_tyd_E6_three i j).mpr h
  have hUw : ∀ i, v (w i) ∈ U := fun i => hU (w i)
  have hUge5 :=
    ct_tyd_path_iso_le_finrank (finV := hV) hwinj hvQ hv2 hv3 hM2 hM3 hUw
  rcases hdim with h | h <;> omega

private theorem ct_tyd_E7_case
    (hV : FiniteDimensional (ZMod 3) V)
    {n f : ℕ}
    {e : Fin 7 ≃ Fin (ggU .E7 n f).D.rank}
    (he : coxeterMatrix (ggU .E7 n f).D.isFiniteType = CoxeterMatrix.E₇.reindex e)
    {v : Fin (ggU .E7 n f).D.rank → V}
    (hvQ : ∀ i, Q (v i) ≠ 0)
    (hv2 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .E7 n f).D.isFiniteType).M i j = 2 →
      QuadraticMap.polar Q (v i) (v j) = 0)
    (hv3 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .E7 n f).D.isFiniteType).M i j = 3 →
      QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
        QuadraticMap.polar Q (v i) (v j) ≠ 0)
    {U : Submodule (ZMod 3) V}
    (hU : ∀ i, v i ∈ U)
    (hUfin : Module.finrank (ZMod 3) U + 1 = Module.finrank (ZMod 3) V)
    (hdim : Module.finrank (ZMod 3) V = 4 ∨ Module.finrank (ZMod 3) V = 5) :
    False := by
  let w : Fin 5 → Fin (ggU .E7 n f).D.rank := fun i => e (ct_tyd_embE7 i)
  have hwinj : Function.Injective w := by
    intro i j h
    exact ct_tyd_embE7_injective (e.injective h)
  have hM2 : ∀ i j : Fin 5, i ≠ j → ¬ ggOrthAdjPathIso i j →
      (coxeterMatrix (ggU .E7 n f).D.isFiniteType).M (w i) (w j) = 2 := by
    intro i j hij h
    simp only [w, he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
    exact (ct_tyd_E7_two i j hij).mpr h
  have hM3 : ∀ i j : Fin 5, i ≠ j → ggOrthAdjPathIso i j →
      (coxeterMatrix (ggU .E7 n f).D.isFiniteType).M (w i) (w j) = 3 := by
    intro i j hij h
    simp only [w, he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
    exact (ct_tyd_E7_three i j).mpr h
  have hUw : ∀ i, v (w i) ∈ U := fun i => hU (w i)
  have hUge5 :=
    ct_tyd_path_iso_le_finrank (finV := hV) hwinj hvQ hv2 hv3 hM2 hM3 hUw
  rcases hdim with h | h <;> omega

private theorem ct_tyd_E8_case
    (hV : FiniteDimensional (ZMod 3) V)
    {n f : ℕ}
    {e : Fin 8 ≃ Fin (ggU .E8 n f).D.rank}
    (he : coxeterMatrix (ggU .E8 n f).D.isFiniteType = CoxeterMatrix.E₈.reindex e)
    {v : Fin (ggU .E8 n f).D.rank → V}
    (hvQ : ∀ i, Q (v i) ≠ 0)
    (hv2 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .E8 n f).D.isFiniteType).M i j = 2 →
      QuadraticMap.polar Q (v i) (v j) = 0)
    (hv3 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .E8 n f).D.isFiniteType).M i j = 3 →
      QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
        QuadraticMap.polar Q (v i) (v j) ≠ 0)
    {U : Submodule (ZMod 3) V}
    (hU : ∀ i, v i ∈ U)
    (hUfin : Module.finrank (ZMod 3) U + 1 = Module.finrank (ZMod 3) V)
    (hdim : Module.finrank (ZMod 3) V = 4 ∨ Module.finrank (ZMod 3) V = 5) :
    False := by
  let w : Fin 5 → Fin (ggU .E8 n f).D.rank := fun i => e (ct_tyd_embE8 i)
  have hwinj : Function.Injective w := by
    intro i j h
    exact ct_tyd_embE8_injective (e.injective h)
  have hM2 : ∀ i j : Fin 5, i ≠ j → ¬ ggOrthAdjPathIso i j →
      (coxeterMatrix (ggU .E8 n f).D.isFiniteType).M (w i) (w j) = 2 := by
    intro i j hij h
    simp only [w, he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
    exact (ct_tyd_E8_two i j hij).mpr h
  have hM3 : ∀ i j : Fin 5, i ≠ j → ggOrthAdjPathIso i j →
      (coxeterMatrix (ggU .E8 n f).D.isFiniteType).M (w i) (w j) = 3 := by
    intro i j hij h
    simp only [w, he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
    exact (ct_tyd_E8_three i j).mpr h
  have hUw : ∀ i, v (w i) ∈ U := fun i => hU (w i)
  have hUge5 :=
    ct_tyd_path_iso_le_finrank (finV := hV) hwinj hvQ hv2 hv3 hM2 hM3 hUw
  rcases hdim with h | h <;> omega

private theorem ct_tyd_PSL_case
    (hV : FiniteDimensional (ZMod 3) V)
    (hnondeg : PolarNondeg3 Q)
    {n f : ℕ} {ψ : (ggU .PSL n f).K →* G}
    (hadm : StatedLieAdmissible .PSL n 2 f) (hrank3 : 3 ≤ bnRank .PSL n)
    (hker : ψ.ker ≤ Subgroup.center (ggU .PSL n f).K)
    (hrange : ψ.range = L) (h3dvd : 3 ∣ 2 ^ f - 1)
    {ε : (coxeterMatrix (ggU .PSL n f).D.isFiniteType).Group ≃*
      ↥(ggAutomizer L Bs)}
    (hε : ∀ i, GGIsReflection 3
      ((ε ((coxeterMatrix (ggU .PSL n f).D.isFiniteType).simple i) :
          ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
    {v : Fin (ggU .PSL n f).D.rank → V}
    (hvQ : ∀ i, Q (v i) ≠ 0)
    (hv2 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .PSL n f).D.isFiniteType).M i j = 2 →
      QuadraticMap.polar Q (v i) (v j) = 0)
    (hv3 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .PSL n f).D.isFiniteType).M i j = 3 →
      QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
        QuadraticMap.polar Q (v i) (v j) ≠ 0)
    {U : Submodule (ZMod 3) V}
    (hU : ∀ i, v i ∈ U)
    (hUfin : Module.finrank (ZMod 3) U + 1 = Module.finrank (ZMod 3) V)
    (hUle : Module.finrank (ZMod 3) U ≤ (ggU .PSL n f).D.rank)
    (hdim : Module.finrank (ZMod 3) V = 4 ∨ Module.finrank (ZMod 3) V = 5)
    (hx : x ∈ Bs) (hxne : ι (Additive.ofMul ⟨x, hx⟩) ≠ 0)
    (hxperp : ∀ i, QuadraticMap.polar Q (v i)
      (ι (Additive.ofMul ⟨x, hx⟩)) = 0) :
    (Module.finrank (ZMod 3) V = 4 ∧
        GGWeylOfType 3 (CoxeterMatrix.A 3) (ggAutomizer L Bs)) ∨
      (Module.finrank (ZMod 3) V = 5 ∧
        GGWeylOfType 3 (CoxeterMatrix.A 4) (ggAutomizer L Bs) ∧
        GGOrthPres L .PSL 5 ∧
        ∃ hx : x ∈ Bs, Q (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0) ∨
      (Module.finrank (ZMod 3) V = 5 ∧
        GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer L Bs)) ∨
      (Module.finrank (ZMod 3) V = 5 ∧
        GGWeylOfType 3 (ggCoxeterMatrixD 4) (ggAutomizer L Bs) ∧
        GGOrthPres L .POmegaPlus 4) := by
  obtain ⟨e, he⟩ := ggOrthTy_cox_psl hadm
  have hr : (ggU .PSL n f).D.rank = n - 1 := by
    simpa using (Fintype.card_congr e).symm
  have hWeyl : GGWeylOfType 3 (CoxeterMatrix.A (n - 1)) (ggAutomizer L Bs) := by
    have h0 : GGWeylOfType 3 (coxeterMatrix (ggU .PSL n f).D.isFiniteType)
        (ggAutomizer L Bs) := ⟨ε, hε⟩
    rw [he] at h0
    exact GGWeylOfType.of_reindex h0
  have h3le : 3 ≤ n - 1 := hrank3
  rcases lt_or_ge (n - 1) 4 with h4 | h4
  · have hm : n - 1 = 3 := by omega
    exact Or.inl (ct_tyd_PSL_A3 hWeyl hUfin hUle hr hm hdim)
  · rcases lt_or_ge (n - 1) 5 with h5 | h5
    · have hm : n - 1 = 4 := by omega
      have hW4 : GGWeylOfType 3 (CoxeterMatrix.A 4) (ggAutomizer L Bs) := by
        rw [hm] at hWeyl
        exact hWeyl
      have hA4 := ct_tyd_PSL_A4 hV hnondeg he hvQ hv2 hv3 hU hUfin hUle hr hm hW4
        hx hxne hxperp
      have hn5 : n = 5 := by omega
      have hpres : GGOrthPres L .PSL n := ⟨f, ψ, hadm, hrank3, hker, hrange, h3dvd⟩
      exact Or.inr (Or.inl ⟨hA4.1, hA4.2.1, hn5 ▸ hpres, hA4.2.2⟩)
    · rcases lt_or_ge (n - 1) 6 with h6 | h6
      · have hm : n - 1 = 5 := by omega
        have hW5 : GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer L Bs) := by
          rw [hm] at hWeyl
          exact hWeyl
        exact Or.inr (Or.inr (Or.inl (ct_tyd_PSL_A5 hV he hvQ hv2 hv3 hU hUfin hdim hm hW5)))
      · exact (ct_tyd_PSL_high hV he hvQ hv2 hv3 hU hUfin hdim h6).elim

private theorem ct_tyd_POmegaPlus_case
    (hV : FiniteDimensional (ZMod 3) V)
    {n f : ℕ} {ψ : (ggU .POmegaPlus n f).K →* G}
    (hadm : StatedLieAdmissible .POmegaPlus n 2 f)
    (hrank3 : 3 ≤ bnRank .POmegaPlus n)
    (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus n f).K)
    (hrange : ψ.range = L) (h3dvd : 3 ∣ 2 ^ f - 1)
    {ε : (coxeterMatrix (ggU .POmegaPlus n f).D.isFiniteType).Group ≃*
      ↥(ggAutomizer L Bs)}
    (hε : ∀ i, GGIsReflection 3
      ((ε ((coxeterMatrix (ggU .POmegaPlus n f).D.isFiniteType).simple i) :
          ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
    {v : Fin (ggU .POmegaPlus n f).D.rank → V}
    (hvQ : ∀ i, Q (v i) ≠ 0)
    (hv2 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .POmegaPlus n f).D.isFiniteType).M i j = 2 →
      QuadraticMap.polar Q (v i) (v j) = 0)
    (hv3 : ∀ i j, i ≠ j →
      (coxeterMatrix (ggU .POmegaPlus n f).D.isFiniteType).M i j = 3 →
      QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
        QuadraticMap.polar Q (v i) (v j) ≠ 0)
    {U : Submodule (ZMod 3) V}
    (hU : ∀ i, v i ∈ U)
    (hUfin : Module.finrank (ZMod 3) U + 1 = Module.finrank (ZMod 3) V)
    (hdim : Module.finrank (ZMod 3) V = 4 ∨ Module.finrank (ZMod 3) V = 5) :
    Module.finrank (ZMod 3) V = 5 ∧
      GGWeylOfType 3 (ggCoxeterMatrixD 4) (ggAutomizer L Bs) ∧
      GGOrthPres L .POmegaPlus 4 := by
  obtain ⟨e, he⟩ := ggOrthTy_cox_D hadm
  have hWeyl : GGWeylOfType 3 (ggCoxeterMatrixD n) (ggAutomizer L Bs) := by
    have h0 : GGWeylOfType 3 (coxeterMatrix (ggU .POmegaPlus n f).D.isFiniteType)
        (ggAutomizer L Bs) := ⟨ε, hε⟩
    rw [he] at h0
    exact GGWeylOfType.of_reindex h0
  have h4n : 4 ≤ n := hadm.2.2
  rcases lt_or_ge n 5 with h5 | h5
  · have hn4 : n = 4 := by omega
    have hW4 : GGWeylOfType 3 (ggCoxeterMatrixD 4) (ggAutomizer L Bs) := by
      rw [hn4] at hWeyl
      exact hWeyl
    obtain ⟨hd5, hW⟩ :=
      ct_tyd_POmegaPlus_four hV hn4 he hvQ hv2 hv3 hU hUfin hdim hW4
    have hpres : GGOrthPres L .POmegaPlus n :=
      ⟨f, ψ, hadm, hrank3, hker, hrange, h3dvd⟩
    exact ⟨hd5, hW, hn4 ▸ hpres⟩
  · rcases lt_or_ge n 6 with h6 | h6
    · have hn5 : n = 5 := by omega
      exact (ct_tyd_POmegaPlus_five hV hn5 he hvQ hv2 hv3 hU hUfin hdim).elim
    · have h5' : 5 ≤ n := by omega
      exact (ct_tyd_POmegaPlus_high hV h5' he hvQ hv2 hv3 hU hUfin hdim).elim
end CaseHelpers

theorem GGOrthSetup.typeAL
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V}
    {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι)
    (hFix : GGSecFiveFixInput) :
    (Module.finrank (ZMod 3) V = 4 ∧ GGWeylOfType 3 (CoxeterMatrix.A 3) (ggAutomizer L Bs)) ∨
    (Module.finrank (ZMod 3) V = 5 ∧ GGWeylOfType 3 (CoxeterMatrix.A 4) (ggAutomizer L Bs) ∧
      GGOrthPres L .PSL 5 ∧ ∃ hx : x ∈ Bs, Q (ι (Additive.ofMul ⟨x, hx⟩)) ≠ 0) ∨
    (Module.finrank (ZMod 3) V = 5 ∧ GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer L Bs)) ∨
    (Module.finrank (ZMod 3) V = 5 ∧ GGWeylOfType 3 (ggCoxeterMatrixD 4) (ggAutomizer L Bs) ∧
      GGOrthPres L .POmegaPlus 4) := by
  obtain ⟨t, n, f, ψ, hadm, hrank3, hker, hrange, htags, h3dvd, hTB⟩ := ggOrthTy_frame S
  obtain ⟨ε, hε, -, -⟩ := hTB
  obtain ⟨v, hvQ, -, hv2, hv3, hvfin, hx, hxne, hxperp⟩ :=
    ggOrthTy_roots S hFix (coxeterMatrix (ggU t n f).D.isFiniteType) ε hε
  set U : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range v) with hUdef
  have hUfin : Module.finrank (ZMod 3) U + 1 = Module.finrank (ZMod 3) V := by
    rw [hUdef]; exact hvfin
  have hUle : Module.finrank (ZMod 3) U ≤ (ggU t n f).D.rank := by
    rw [hUdef]
    have h := finrank_range_le_card (R := ZMod 3) v
    simp only [Set.finrank, Fintype.card_fin] at h
    exact h
  have hV : FiniteDimensional (ZMod 3) V := by
    rcases S.dim with h | h
    · exact Module.finite_of_finrank_pos (by rw [h]; norm_num)
    · exact Module.finite_of_finrank_pos (by rw [h]; norm_num)
  have hUall : ∀ i, v i ∈ U := fun i => by
    rw [hUdef]
    exact Submodule.subset_span ⟨i, rfl⟩
  rcases htags with rfl | rfl | rfl | rfl | rfl
  ·
    exact ct_tyd_PSL_case hV S.nondeg hadm hrank3 hker hrange h3dvd hε
      hvQ hv2 hv3 hUall hUfin hUle S.dim hx hxne hxperp
  ·
    exact Or.inr (Or.inr (Or.inr (ct_tyd_POmegaPlus_case hV hadm hrank3 hker
      hrange h3dvd hε hvQ hv2 hv3 hUall hUfin S.dim)))
  ·
    obtain ⟨e, he⟩ := ggOrthTy_cox_E (n := n) (f := f)
    exact (ct_tyd_E6_case hV he hvQ hv2 hv3 hUall hUfin S.dim).elim
  ·
    obtain ⟨e, he⟩ := ggOrthTy_cox_E7 (n := n) (f := f)
    exact (ct_tyd_E7_case hV he hvQ hv2 hv3 hUall hUfin S.dim).elim
  ·
    obtain ⟨e, he⟩ := ggOrthTy_cox_E8 (n := n) (f := f)
    exact (ct_tyd_E8_case hV he hvQ hv2 hv3 hUall hUfin S.dim).elim

end CFSG.StandardType.OrthF3

end
