module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigCls

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

open scoped CharTwo

theorem s16c11_big_fix_sum_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) {x : Fin n → ZMod 2}
    (hx : ∑ i, x i = 0) : ∑ i, x (σ⁻¹ i) = 0 := by
  rw [Equiv.sum_comp σ⁻¹ x, hx]

theorem s16c11_big_fix_class_fixed_iff {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : σ ^ 3 = 1)
    (i₀ : Fin n) {x : Fin n → ZMod 2} (hx : ∑ i, x i = 0)
    (hx' : ∑ i, x (σ⁻¹ i) = 0) :
    (FFModel.symDn_isActionModel n).modAct σ (s16c11BigCls n x hx) =
        s16c11BigCls n x hx ↔
      ∀ i, x (σ⁻¹ i) = x i := by
  have hshift : (∀ i, x i = x (σ⁻¹ i) + 1) → False := by
    intro h
    have h1 : x (σ⁻¹ i₀) = x (σ⁻¹ (σ⁻¹ i₀)) + 1 := h (σ⁻¹ i₀)
    have h2 : x (σ⁻¹ (σ⁻¹ i₀)) = x (σ⁻¹ (σ⁻¹ (σ⁻¹ i₀))) + 1 := h (σ⁻¹ (σ⁻¹ i₀))
    have hσi : σ⁻¹ (σ⁻¹ (σ⁻¹ i₀)) = i₀ := by
      have hσinv : σ⁻¹ ^ 3 = 1 := by rw [inv_pow, hσ, inv_one]
      have := congrFun (congrArg (fun f : Equiv.Perm (Fin n) => (f : Fin n → Fin n)) hσinv) i₀
      simpa [pow_succ, pow_two, Equiv.Perm.mul_apply] using this
    have hbad : x i₀ = x i₀ + 1 := by
      calc x i₀ = x (σ⁻¹ i₀) + 1 := h i₀
        _ = (x (σ⁻¹ (σ⁻¹ i₀)) + 1) + 1 := by rw [h1]
        _ = x (σ⁻¹ (σ⁻¹ i₀)) := by rw [CharTwo.add_cancel_right]
        _ = x (σ⁻¹ (σ⁻¹ (σ⁻¹ i₀))) + 1 := h2
        _ = x i₀ + 1 := by rw [hσi]
    have : (0 : ZMod 2) = 1 := by
      have hrhs : (x i₀ + 1) - x i₀ = (1 : ZMod 2) := by ring
      have := congrArg (fun t => t - x i₀) hbad
      rw [sub_self, hrhs] at this
      exact this
    exact zero_ne_one this
  rw [s16c11BigCls_modAct n σ (hx := hx) (hx' := hx'), s16c11BigCls_eq_iff]
  constructor
  · rintro (h | h)
    · intro i
      exact (congrFun h i).symm
    · exact (hshift (fun j => congrFun h j)).elim
  · intro h
    left
    funext i
    exact (h i).symm

theorem s16c11_big_fix_fixed_iff_closure {n : ℕ} {c₁ c₂ : Equiv.Perm (Fin n)}
    (q : (FFModel.symDn n).Mod) :
    (∀ σ ∈ Subgroup.closure ({c₁, c₂} : Set (Equiv.Perm (Fin n))),
        (FFModel.symDn_isActionModel n).modAct σ q = q) ↔
      ((FFModel.symDn_isActionModel n).modAct c₁ q = q ∧
        (FFModel.symDn_isActionModel n).modAct c₂ q = q) := by
  let S : Subgroup (Equiv.Perm (Fin n)) :=
    { carrier := {σ | (FFModel.symDn_isActionModel n).modAct σ q = q}
      one_mem' := by
        change (FFModel.symDn_isActionModel n).modAct (1 : Equiv.Perm (Fin n)) q = q
        erw [map_one]
        rfl
      mul_mem' := by
        intro σ τ hσ hτ
        change (FFModel.symDn_isActionModel n).modAct (σ * τ) q = q
        erw [map_mul, MulAut.mul_apply, hτ, hσ]
      inv_mem' := by
        intro σ hσ
        change (FFModel.symDn_isActionModel n).modAct σ⁻¹ q = q
        have h := congrArg (fun r => (FFModel.symDn_isActionModel n).modAct σ⁻¹ r) hσ
        erw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h
        exact h.symm }
  constructor
  · intro h
    exact ⟨h c₁ (Subgroup.subset_closure (by simp)),
      h c₂ (Subgroup.subset_closure (by simp))⟩
  · rintro ⟨h1, h2⟩
    have hle : Subgroup.closure ({c₁, c₂} : Set (Equiv.Perm (Fin n))) ≤ S := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact h1
      · exact h2
    intro σ hσ
    exact hle hσ

theorem s16c11_big_fix_pow_three_closure {G : Type*} [Group G] {c₁ c₂ : G}
    (hcomm : c₁ * c₂ = c₂ * c₁) (h1 : c₁ ^ 3 = 1) (h2 : c₂ ^ 3 = 1) :
    ∀ x ∈ Subgroup.closure ({c₁, c₂} : Set G), x ^ 3 = 1 := by
  set B : Subgroup G := Subgroup.closure ({c₁, c₂} : Set G) with hB
  have hle : B ≤ Subgroup.centralizer (B : Set G) := by
    rw [hB, Subgroup.centralizer_closure, Subgroup.closure_le]
    intro x hx
    change x ∈ Subgroup.centralizer ({c₁, c₂} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hcomm.symm
    · exact hcomm
    · rfl
  have hcommB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    exact ((Subgroup.mem_centralizer_iff.mp (hle hx)) y hy).symm
  intro x hx
  rw [hB] at hx
  refine Subgroup.closure_induction (k := ({c₁, c₂} : Set G)) ?_ ?_ ?_ ?_ hx
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h1
    · exact h2
  · simp
  · intro x y hx hy hpx hpy
    have hxy : Commute x y := hcommB x (by rw [hB]; exact hx) y (by rw [hB]; exact hy)
    rw [hxy.mul_pow 3, hpx, hpy, mul_one]
  · intro x hx hpx
    rw [inv_pow, hpx, inv_one]

theorem s16c11_big_fix_isPGroup_closure {G : Type*} [Group G] {c₁ c₂ : G}
    (hcomm : c₁ * c₂ = c₂ * c₁) (h1 : c₁ ^ 3 = 1) (h2 : c₂ ^ 3 = 1) :
    IsPGroup 3 ↥(Subgroup.closure ({c₁, c₂} : Set G)) := by
  refine fun x => ⟨1, ?_⟩
  apply Subtype.ext
  simpa using s16c11_big_fix_pow_three_closure hcomm h1 h2 x x.2

theorem s16c11_big_fix_closure_le_alternating {α : Type*} [Fintype α] [DecidableEq α]
    {c₁ c₂ : Equiv.Perm α} (h1 : c₁.IsThreeCycle) (h2 : c₂.IsThreeCycle) :
    Subgroup.closure ({c₁, c₂} : Set (Equiv.Perm α)) ≤ alternatingGroup α := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact h1.mem_alternatingGroup
  · exact h2.mem_alternatingGroup

theorem s16c11_big_fix_not_isCyclic_closure {G : Type*} [Group G] [Finite G]
    {c₁ c₂ : G} (hcomm : c₁ * c₂ = c₂ * c₁) (h1 : c₁ ^ 3 = 1) (h2 : c₂ ^ 3 = 1)
    (hc₁1 : c₁ ≠ 1) (hc₁2 : c₁ ^ 2 ≠ 1) (hc₁3 : c₁ ^ 2 ≠ c₁)
    (hc₂1 : c₂ ≠ 1) (hc₂2 : c₂ ≠ c₁) (hc₂3 : c₂ ≠ c₁ ^ 2) :
    ¬ IsCyclic ↥(Subgroup.closure ({c₁, c₂} : Set G)) := by
  intro hcyc
  classical
  set B : Subgroup G := Subgroup.closure ({c₁, c₂} : Set G) with hB
  have hmem₁ : c₁ ∈ B := Subgroup.subset_closure (by simp)
  have hmem₂ : c₂ ∈ B := Subgroup.subset_closure (by simp)
  have h4 : 4 ≤ Nat.card ↥B := by
    have e0 : (⟨1, B.one_mem⟩ : ↥B) ≠ ⟨c₁, hmem₁⟩ :=
      fun h => hc₁1 (Subtype.ext_iff.mp h).symm
    have e0' : (⟨1, B.one_mem⟩ : ↥B) ≠ ⟨c₁ ^ 2, B.pow_mem hmem₁ 2⟩ :=
      fun h => hc₁2 (Subtype.ext_iff.mp h).symm
    have e0'' : (⟨1, B.one_mem⟩ : ↥B) ≠ ⟨c₂, hmem₂⟩ :=
      fun h => hc₂1 (Subtype.ext_iff.mp h).symm
    have e1 : (⟨c₁, hmem₁⟩ : ↥B) ≠ ⟨c₁ ^ 2, B.pow_mem hmem₁ 2⟩ :=
      fun h => hc₁3 (Subtype.ext_iff.mp h).symm
    have e2 : (⟨c₁, hmem₁⟩ : ↥B) ≠ ⟨c₂, hmem₂⟩ :=
      fun h => hc₂2 (Subtype.ext_iff.mp h).symm
    have e3 : (⟨c₁ ^ 2, B.pow_mem hmem₁ 2⟩ : ↥B) ≠ ⟨c₂, hmem₂⟩ :=
      fun h => hc₂3 (Subtype.ext_iff.mp h).symm
    let f : Fin 4 → ↥B :=
      ![⟨1, B.one_mem⟩, ⟨c₁, hmem₁⟩, ⟨c₁ ^ 2, B.pow_mem hmem₁ 2⟩, ⟨c₂, hmem₂⟩]
    have hfinj : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [f, Subtype.ext_iff, Ne.symm e0, Ne.symm e0', Ne.symm e0'',
          Ne.symm e1, Ne.symm e2, Ne.symm e3]
    have := Finite.card_le_of_embedding (Function.Embedding.mk f hfinj)
    simpa using this
  have hle3 : Nat.card ↥B ≤ 3 := by
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyc
    have hg3 : g ^ 3 = 1 := by
      apply Subtype.ext
      simpa using s16c11_big_fix_pow_three_closure hcomm h1 h2 g g.2
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hg3
    rw [← hg]
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h <;> omega
  omega

theorem s16c11_big_fix_zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  decide +revert

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
