module

public import CFSG.Quasithin.EmptyFaithful.S152He5AutBase
public import CFSG.Quasithin.EmptyFaithful.S152He5Lift

public section

namespace CFSG.Quasithin.He5

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin

variable {n : ℕ}

theorem conj_apply_aut (τ : MulAut (projectiveSL n K2)) (g : projectiveSL n K2) :
    (MulAut.conj (τ g) : MulAut (projectiveSL n K2)) = τ * MulAut.conj g * τ⁻¹ := by
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_def]

theorem map_projStabilizer_flag (hn : 3 ≤ n) (τ : MulAut (projectiveSL n K2)) (hτ : τ ∉ InnP n)
    (hU : ∀ g, g ∈ projUpperTriangular n K2 ↔ τ g ∈ projUpperTriangular n K2)
    {d : ℕ} (hd : 1 ≤ d) (hdn : d < n) :
    (projStabilizer (flagSpace n K2 d)).map (τ : projectiveSL n K2 →* projectiveSL n K2) =
      projStabilizer (flagSpace n K2 (n - d)) := by
  obtain ⟨A, hA⟩ : ∃ A : GL (Fin n) K2, τ = LinearFlag.conjAut n K2 A * LinearFlag.dualAut n K2 := by
    rcases mem_inn_or_eq_conj_dual hn τ with h | h
    · exact absurd h hτ
    · exact h
  obtain ⟨g, rfl⟩ := exists_toGL_eq n A
  have htrans := standard_automorphism_transport (K := K2) (n := n)
  set W' : Submodule K2 (Fin n → K2) :=
    (dotOrth (flagSpace n K2 d)).map (mulVecLin ((SpecialLinearGroup.toGL g : GL (Fin n) K2) :
      Matrix (Fin n) (Fin n) K2)) with hW'
  have hmap : (projStabilizer (flagSpace n K2 d)).map
      (τ : projectiveSL n K2 →* projectiveSL n K2) = projStabilizer W' := by
    have e1 : (τ : projectiveSL n K2 →* projectiveSL n K2) =
        (LinearFlag.conjAut n K2 (SpecialLinearGroup.toGL g) : projectiveSL n K2 →* projectiveSL n K2).comp
          (LinearFlag.dualAut n K2 : projectiveSL n K2 →* projectiveSL n K2) := by
      rw [hA]; rfl
    rw [e1, ← Subgroup.map_map, htrans.2.2.2.2.2.2.2.2.1 (flagSpace n K2 d),
      htrans.2.2.2.2.2.2.1 (SpecialLinearGroup.toGL g) (dotOrth (flagSpace n K2 d))]
  have hdim : finrank K2 W' = n - d := by
    have h1 : finrank K2 W' = finrank K2 (dotOrth (flagSpace n K2 d)) :=
      LinearEquiv.finrank_map_eq (SpecialLinearGroup.toLin' g) _
    rw [h1, finrank_dotOrth, finrank_flagSpace hdn.le]
  have hUW : projUpperTriangular n K2 ≤ projStabilizer W' := by
    intro x hx
    have hx' : τ.symm x ∈ projUpperTriangular n K2 := by
      have := (hU (τ.symm x)).mpr (by simpa using hx)
      exact this
    have hx'' : τ.symm x ∈ projStabilizer (flagSpace n K2 d) :=
      projUpperTriangular_le_projStabilizer d hx'
    rw [← hmap]
    exact ⟨τ.symm x, hx'', by simp⟩
  have hB : upperTriangular n K2 ≤ stabilizer W' := by
    have := hUW
    rw [projUpperTriangular, projStabilizer,
      Subgroup.map_le_map_iff_of_injective (proj_injective n)] at this
    exact this
  have hinv : ∀ b ∈ flagStabilizer n K2 (fullCuts n), ∀ v ∈ W',
      (b : Matrix (Fin n) (Fin n) K2) *ᵥ v ∈ W' := by
    intro b hb v hv
    rw [flagStabilizer_full] at hb
    have h := mem_stabilizer.mp (hB hb)
    rw [← h]
    exact ⟨v, hv, rfl⟩
  have hW'eq : W' = flagSpace n K2 (n - d) := by
    rcases ((subflag_stabilizer_generation (K := K2) (n := n) (fullCuts n)).2.1 W').mp hinv with
      h | h | ⟨i, hi, h⟩
    · rw [h, finrank_bot] at hdim
      omega
    · rw [h, finrank_top, finrank_fin_fun] at hdim
      omega
    · rw [h, finrank_flagSpace hi.2.le] at hdim
      rw [h, hdim]
  rw [hmap, hW'eq]

theorem mem_PI {I : Set ℕ} {x : projectiveSL n K2} :
    x ∈ PI n I ↔ ∀ i ∈ I, x ∈ projStabilizer (flagSpace n K2 i) := by
  constructor
  · rintro ⟨y, hy, rfl⟩ i hi
    exact ⟨y, mem_flagStabilizer.mp hy i hi, rfl⟩
  · intro h
    obtain ⟨y, rfl⟩ := proj_surjective n K2 x
    refine ⟨y, mem_flagStabilizer.mpr fun i hi => ?_, rfl⟩
    obtain ⟨y', hy', hyy⟩ := h i hi
    have := proj_injective n hyy
    rw [← this]
    exact hy'

@[expose] def swapCuts (n : ℕ) (I : Set ℕ) : Set ℕ := (fun i => n - i) '' I

theorem map_PI (hn : 3 ≤ n) (τ : MulAut (projectiveSL n K2)) (hτ : τ ∉ InnP n)
    (hU : ∀ g, g ∈ projUpperTriangular n K2 ↔ τ g ∈ projUpperTriangular n K2) {I : Set ℕ}
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) :
    (PI n I).map (τ : projectiveSL n K2 →* projectiveSL n K2) = PI n (swapCuts n I) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_PI] at hy ⊢
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨hi1, hin⟩ := hI i hi
    have := map_projStabilizer_flag hn τ hτ hU hi1 hin
    rw [← this]
    exact ⟨y, hy i hi, rfl⟩
  · intro hx
    rw [mem_PI] at hx
    refine ⟨τ.symm x, ?_, by simp⟩
    rw [mem_PI]
    intro i hi
    obtain ⟨hi1, hin⟩ := hI i hi
    have h1 := hx (n - i) ⟨i, hi, rfl⟩
    rw [← map_projStabilizer_flag hn τ hτ hU hi1 hin] at h1
    obtain ⟨z, hz, hzx⟩ := h1
    have : z = τ.symm x := by
      rw [← hzx]
      simp
    rw [← this]
    exact hz

theorem swapCuts_sub {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) : ∀ j ∈ swapCuts n I, 1 ≤ j ∧ j < n := by
  rintro _ ⟨i, hi, rfl⟩
  have := hI i hi
  show 1 ≤ n - i ∧ n - i < n
  omega

theorem swapCuts_eq_of_inv (hn : 3 ≤ n) (τ : MulAut (projectiveSL n K2)) (hτ : τ ∉ InnP n)
    (hU : ∀ g, g ∈ projUpperTriangular n K2 ↔ τ g ∈ projUpperTriangular n K2) {I : Set ℕ}
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (hinv : ∀ g, g ∈ PI n I ↔ τ g ∈ PI n I) :
    swapCuts n I = I := by
  have hmap : (PI n I).map (τ : projectiveSL n K2 →* projectiveSL n K2) = PI n I := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hinv y).mp hy
    · intro hx
      refine ⟨τ.symm x, (hinv _).mpr (by simpa using hx), by simp⟩
  rw [map_PI hn τ hτ hU hI] at hmap
  exact Set.Subset.antisymm ((PI_le_PI_iff (swapCuts_sub hI)).mp hmap.ge)
    ((PI_le_PI_iff hI).mp hmap.le)

theorem finite_mulAut (n : ℕ) : Finite (MulAut (projectiveSL n K2)) :=
  Finite.of_injective (fun f : MulAut (projectiveSL n K2) => (f : projectiveSL n K2 → projectiveSL n K2))
    DFunLike.coe_injective

theorem overBool2_mulAut_of_orbits (hn : 3 ≤ n) {O₁ O₂ : Set ℕ}
    (hO₁ : ∀ i ∈ O₁, 1 ≤ i ∧ i < n) (hO₂ : ∀ i ∈ O₂, 1 ≤ i ∧ i < n)
    (hsw₁ : swapCuts n O₁ = O₁) (hsw₂ : swapCuts n O₂ = O₂)
    (hne₁ : ¬ fullCuts n ⊆ O₁) (hne₂ : ¬ fullCuts n ⊆ O₂) (h12 : ¬ O₂ ⊆ O₁) (h21 : ¬ O₁ ⊆ O₂)
    (hcl : ∀ I : Set ℕ, (∀ i ∈ I, 1 ≤ i ∧ i < n) → swapCuts n I = I →
      I = ∅ ∨ I = O₁ ∨ I = O₂ ∨ I = fullCuts n)
    {T : Subgroup (MulAut (projectiveSL n K2))} (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) :
    OverBool2 T := by
  have : Finite (MulAut (projectiveSL n K2)) := finite_mulAut n
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨SU, hSU⟩ := exists_sylow_projUnitriangular (K := K2) 2 (show 1 ≤ n by omega)
  rw [← projUpperTriangular_eq_projUnitriangular] at hSU
  obtain ⟨Q, hQ⟩ := Sylow.exists_comap_eq_of_injective SU (conj_injective n)
  have hQU : (Q : Subgroup (MulAut (projectiveSL n K2))).comap
      (MulAut.conj : projectiveSL n K2 →* MulAut (projectiveSL n K2)) =
      projUpperTriangular n K2 := by rw [hQ, hSU]
  have hQnle : ¬ (Q : Subgroup (MulAut (projectiveSL n K2))) ≤ InnP n := by
    intro hle
    have h1 := Subgroup.relIndex_mul_index hle
    rw [index_inn_eq_two hn] at h1
    exact Q.not_dvd_index (h1 ▸ dvd_mul_left 2 _)
  obtain ⟨τ, hτQ, hτ⟩ := IsConcreteLE.not_le_iff_exists.mp hQnle
  have hφ : ∀ g, (MulAut.conj : projectiveSL n K2 →* MulAut (projectiveSL n K2)) (τ g) =
      τ * (MulAut.conj : projectiveSL n K2 →* MulAut (projectiveSL n K2)) g * τ⁻¹ :=
    fun g => conj_apply_aut τ g
  have hUinv : ∀ g, g ∈ projUpperTriangular n K2 ↔ τ g ∈ projUpperTriangular n K2 := by
    intro g
    rw [← hQU]
    change (MulAut.conj : projectiveSL n K2 →* MulAut (projectiveSL n K2)) g ∈
        (Q : Subgroup (MulAut (projectiveSL n K2))) ↔
      (MulAut.conj : projectiveSL n K2 →* MulAut (projectiveSL n K2)) (τ g) ∈
        (Q : Subgroup (MulAut (projectiveSL n K2)))
    rw [hφ g]
    constructor
    · intro h
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hτQ h) (Subgroup.inv_mem _ hτQ)
    · intro h
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hτQ) h) hτQ
      simpa [mul_assoc] using this
  have hinvO : ∀ O : Set ℕ, (∀ i ∈ O, 1 ≤ i ∧ i < n) → swapCuts n O = O →
      ∀ g, g ∈ PI n O ↔ τ g ∈ PI n O := by
    intro O hO hsw g
    have hmap := map_PI hn τ hτ hUinv hO
    rw [hsw] at hmap
    constructor
    · intro hg
      rw [← hmap]
      exact ⟨g, hg, rfl⟩
    · intro hg
      rw [← hmap] at hg
      obtain ⟨y, hy, hyg⟩ := hg
      have : y = g := τ.injective hyg
      rw [← this]
      exact hy
  have hOQ : OverBool2 (Q : Subgroup (MulAut (projectiveSL n K2))) := by
    refine OverBool2.of_index_two (MulAut.conj : projectiveSL n K2 →* MulAut (projectiveSL n K2))
      (conj_injective n) τ τ hφ hτ (fun y => ?_) hτQ hQU
      (R₁ := PI n O₁) (R₂ := PI n O₂) ?_ ?_ ?_ ?_ (hinvO O₁ hO₁ hsw₁) (hinvO O₂ hO₂ hsw₂) ?_
    · by_cases hy : y ∈ InnP n
      · exact Or.inl hy
      · exact Or.inr (mul_inv_mem_inn hn hy hτ)
    · rw [← PI_full]
      refine lt_of_le_of_ne ((PI_le_PI_iff hO₁).mpr (fun i hi => hO₁ i hi)) fun h => ?_
      exact hne₁ ((PI_le_PI_iff fullCuts_sub).mp h.ge)
    · rw [← PI_full]
      refine lt_of_le_of_ne ((PI_le_PI_iff hO₂).mpr (fun i hi => hO₂ i hi)) fun h => ?_
      exact hne₂ ((PI_le_PI_iff fullCuts_sub).mp h.ge)
    · exact fun h => h12 ((PI_le_PI_iff hO₂).mp h)
    · exact fun h => h21 ((PI_le_PI_iff hO₁).mp h)
    · intro R hUR hRinv
      obtain ⟨I, hI, rfl⟩ := exists_PI_of_ge hUR
      have hsw := swapCuts_eq_of_inv hn τ hτ hUinv hI hRinv
      rcases hcl I hI hsw with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (PI_empty n)))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inl (PI_full n)
  exact OverBool2.of_sylow Q.isPGroup' Q.not_dvd_index hT hTi hOQ

theorem cl4 {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < 4) (hsw : swapCuts 4 I = I) :
    I = ∅ ∨ I = {2} ∨ I = {1, 3} ∨ I = fullCuts 4 := by
  have hs : ∀ i ∈ I, 4 - i ∈ I := fun i hi => hsw ▸ ⟨i, hi, rfl⟩
  have h31 : 3 ∈ I ↔ 1 ∈ I := ⟨fun h => by simpa using hs 3 h, fun h => by simpa using hs 1 h⟩
  have key : ∀ i, i ∈ I ↔ (i = 1 ∧ 1 ∈ I) ∨ (i = 2 ∧ 2 ∈ I) ∨ (i = 3 ∧ 1 ∈ I) := by
    intro i
    constructor
    · intro hi
      have := hI i hi
      rcases (show i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl
      · exact Or.inl ⟨rfl, hi⟩
      · exact Or.inr (Or.inl ⟨rfl, hi⟩)
      · exact Or.inr (Or.inr ⟨rfl, h31.mp hi⟩)
    · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
      · exact h
      · exact h
      · exact h31.mpr h
  by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I
  · right; right; right
    ext i
    rw [key i]
    change _ ↔ (1 ≤ i ∧ i < 4)
    constructor
    · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩) <;> omega
    · intro hi
      rcases (show i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl
      · exact Or.inl ⟨rfl, h1⟩
      · exact Or.inr (Or.inl ⟨rfl, h2⟩)
      · exact Or.inr (Or.inr ⟨rfl, h1⟩)
  · right; right; left
    ext i
    rw [key i]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (⟨rfl, -⟩ | ⟨rfl, h⟩ | ⟨rfl, -⟩)
      · exact Or.inl rfl
      · exact absurd h h2
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, h1⟩
      · exact Or.inr (Or.inr ⟨rfl, h1⟩)
  · right; left
    ext i
    rw [key i]
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro (⟨rfl, h⟩ | ⟨rfl, -⟩ | ⟨rfl, h⟩)
      · exact absurd h h1
      · rfl
      · exact absurd h h1
    · rintro rfl
      exact Or.inr (Or.inl ⟨rfl, h2⟩)
  · left
    ext i
    rw [key i]
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact h1 h
    · exact h2 h
    · exact h1 h

theorem cl5 {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < 5) (hsw : swapCuts 5 I = I) :
    I = ∅ ∨ I = {2, 3} ∨ I = {1, 4} ∨ I = fullCuts 5 := by
  have hs : ∀ i ∈ I, 5 - i ∈ I := fun i hi => hsw ▸ ⟨i, hi, rfl⟩
  have h41 : 4 ∈ I ↔ 1 ∈ I := ⟨fun h => by simpa using hs 4 h, fun h => by simpa using hs 1 h⟩
  have h32 : 3 ∈ I ↔ 2 ∈ I := ⟨fun h => by simpa using hs 3 h, fun h => by simpa using hs 2 h⟩
  have key : ∀ i, i ∈ I ↔
      (i = 1 ∧ 1 ∈ I) ∨ (i = 2 ∧ 2 ∈ I) ∨ (i = 3 ∧ 2 ∈ I) ∨ (i = 4 ∧ 1 ∈ I) := by
    intro i
    constructor
    · intro hi
      have := hI i hi
      rcases (show i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl
      · exact Or.inl ⟨rfl, hi⟩
      · exact Or.inr (Or.inl ⟨rfl, hi⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, h32.mp hi⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, h41.mp hi⟩))
    · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
      · exact h
      · exact h
      · exact h32.mpr h
      · exact h41.mpr h
  by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I
  · right; right; right
    ext i
    rw [key i]
    change _ ↔ (1 ≤ i ∧ i < 5)
    constructor
    · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩) <;> omega
    · intro hi
      rcases (show i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl
      · exact Or.inl ⟨rfl, h1⟩
      · exact Or.inr (Or.inl ⟨rfl, h2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, h2⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, h1⟩))
  · right; right; left
    ext i
    rw [key i]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (⟨rfl, -⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, -⟩)
      · exact Or.inl rfl
      · exact absurd h h2
      · exact absurd h h2
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, h1⟩
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, h1⟩))
  · right; left
    ext i
    rw [key i]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (⟨rfl, h⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, h⟩)
      · exact absurd h h1
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd h h1
    · rintro (rfl | rfl)
      · exact Or.inr (Or.inl ⟨rfl, h2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, h2⟩))
  · left
    ext i
    rw [key i]
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact h1 h
    · exact h2 h
    · exact h2 h
    · exact h1 h

theorem overBool2_mulAut_four {T : Subgroup (MulAut (projectiveSL 4 K2))} (hT : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.index) : OverBool2 T := by
  refine overBool2_mulAut_of_orbits (n := 4) (by norm_num) (O₁ := {2}) (O₂ := {1, 3}) ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ hT hTi
  · intro i hi; rw [Set.mem_singleton_iff] at hi; subst hi; omega
  · intro i hi
    rcases hi with rfl | hi
    · omega
    · rw [Set.mem_singleton_iff] at hi; subst hi; omega
  · simp [swapCuts]
  · simp [swapCuts, Set.pair_comm]
  · intro h
    have := h (show 1 ∈ fullCuts 4 by simp [fullCuts])
    simp at this
  · intro h
    have := h (show 2 ∈ fullCuts 4 by simp [fullCuts])
    simp at this
  · intro h
    have := h (show 1 ∈ ({1, 3} : Set ℕ) by simp)
    simp at this
  · intro h
    have := h (show 2 ∈ ({2} : Set ℕ) by simp)
    simp at this
  · exact fun I hI hsw => cl4 hI hsw

theorem overBool2_mulAut_five {T : Subgroup (MulAut (projectiveSL 5 K2))} (hT : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.index) : OverBool2 T := by
  refine overBool2_mulAut_of_orbits (n := 5) (by norm_num) (O₁ := {2, 3}) (O₂ := {1, 4}) ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ hT hTi
  · intro i hi
    rcases hi with rfl | hi
    · omega
    · rw [Set.mem_singleton_iff] at hi; subst hi; omega
  · intro i hi
    rcases hi with rfl | hi
    · omega
    · rw [Set.mem_singleton_iff] at hi; subst hi; omega
  · simp [swapCuts, Set.pair_comm]
  · simp [swapCuts, Set.pair_comm]
  · intro h
    have := h (show 1 ∈ fullCuts 5 by simp [fullCuts])
    simp at this
  · intro h
    have := h (show 2 ∈ fullCuts 5 by simp [fullCuts])
    simp at this
  · intro h
    have := h (show 1 ∈ ({1, 4} : Set ℕ) by simp)
    simp at this
  · intro h
    have := h (show 2 ∈ ({2, 3} : Set ℕ) by simp)
    simp at this
  · exact fun I hI hsw => cl5 hI hsw

end CFSG.Quasithin.He5
