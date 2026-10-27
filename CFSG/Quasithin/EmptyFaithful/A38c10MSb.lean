module

public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.A38c10.MS

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem fixed_vec_zero {F : Type} [Field F] (dual : Bool) {v : Fin 3 → F}
    (h : ∀ s : Matrix.SpecialLinearGroup (Fin 3) F,
      (moduleAct dual (((specialLinearGroupEquivStatedSL 3 F s : ↥(StatedSL 3 F)) :
        Matrix.GeneralLinearGroup (Fin 3) F))).mulVec v = v) :
    v = 0 := by
  funext j
  obtain ⟨i, hij⟩ := exists_ne j
  cases dual
  · let t : Matrix.TransvectionStruct (Fin 3) F := ⟨i, j, hij, 1⟩
    let s : Matrix.SpecialLinearGroup (Fin 3) F := ⟨t.toMatrix, t.det⟩
    have h1 := h s
    have h2 := congrFun h1 i
    simp only [moduleAct, Bool.false_eq_true, ↓reduceIte] at h2
    rw [specialLinearGroupEquivStatedSL_coe] at h2
    have h3 : (s : Matrix (Fin 3) (Fin 3) F) = Matrix.transvection i j 1 := rfl
    rw [h3] at h2
    simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec] at h2
    simpa using h2
  · let t : Matrix.TransvectionStruct (Fin 3) F := ⟨j, i, hij.symm, 1⟩
    let s : Matrix.SpecialLinearGroup (Fin 3) F := ⟨t.toMatrix, t.det⟩
    have h1 := h s⁻¹
    have h2 := congrFun h1 i
    simp only [moduleAct, ↓reduceIte] at h2
    simp only [← Subgroup.coe_inv, ← map_inv, inv_inv, specialLinearGroupEquivStatedSL_coe] at h2
    have h3 : (s : Matrix (Fin 3) (Fin 3) F) = Matrix.transvection j i 1 := rfl
    rw [h3] at h2
    simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec] at h2
    simpa using h2

theorem mem_of_fixed {G : Type} [Group G] {K V Z : Subgroup G} {F : Type} [Field F]
    {α : ↥K →* ↥(StatedSL 3 F)} (hα : Function.Surjective α) {dual : Bool} {k : ℕ}
    (hmod : IsSumOfNaturalModulesVia K V Z α dual k) {v : G} (hv : v ∈ V)
    (hfix : ∀ a ∈ K, a * v * a⁻¹ = v) : v ∈ Z := by
  obtain ⟨-, -, β, -, hβk, hβe⟩ := hmod
  have hu : ∀ i : Fin k, Multiplicative.toAdd (β ⟨v, hv⟩) i = 0 := by
    intro i
    apply fixed_vec_zero dual
    intro s
    obtain ⟨a, ha⟩ := hα (specialLinearGroupEquivStatedSL 3 F s)
    have h1 := hβe a ⟨v, hv⟩ ⟨v, hv⟩ (hfix a a.2).symm i
    rw [ha] at h1
    exact h1.symm
  have h1 : β ⟨v, hv⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    simpa using hu i
  have h2 : (⟨v, hv⟩ : ↥V) ∈ β.ker := h1
  rw [hβk, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem false_of_case_one_two_three {G : Type} [Group G] {G₀ R K : Subgroup G} {i : ℕ}
    (hi : IsC134Case i G₀ R K) (hi123 : i = 1 ∨ i = 2 ∨ i = 3) {q : G} (hq : q ∈ c134Q G₀ K)
    (hq1 : q ≠ 1) (hfix : ∀ a ∈ K, a * q * a⁻¹ = q) : False := by
  rcases hi123 with rfl | rfl | rfl
  · obtain ⟨-, n, F, _, _, hFc, hNS⟩ := hi
    obtain ⟨α, hαs, hαk, hZ⟩ :=
      (isNaturalSection_iff_isSumOfNaturalModules_one (CFSG.pCore 2 ↥K) (StatedSL 3 F) bot_le).mp hNS
    exact hq1 (Subgroup.mem_bot.mp (mem_of_fixed hαs hZ hq hfix))
  · obtain ⟨⟨n, F, _, _, α, hFc, hα, hZ⟩, -⟩ := hi
    exact hq1 (Subgroup.mem_bot.mp (mem_of_fixed hα.1 hZ hq hfix))
  · obtain ⟨⟨n, F, _, _, α, hFc, hα, hZ1, hZ2⟩, -⟩ := hi
    have hqZ : q ∈ centerOf (c134Q G₀ K) := mem_of_fixed hα.1 hZ2 hq hfix
    exact hq1 (Subgroup.mem_bot.mp (mem_of_fixed hα.1 hZ1 hqZ hfix))

end CFSG.Quasithin.A38c10.MS
