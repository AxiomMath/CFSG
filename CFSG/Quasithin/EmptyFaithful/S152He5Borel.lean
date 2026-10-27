module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LieType.SteinbergBRBinaryLinearSylow
public import CFSG.Quasithin.EmptyFaithful.S152He5Wr
public import CFSG.Quasithin.EmptyFaithful.S152He5Defs

public section

namespace CFSG.Quasithin.He5

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin

abbrev K2 : Type := ZMod 2

theorem card_K2 : Nat.card K2 = 2 := by simp

theorem proj_injective (n : ℕ) : Function.Injective (proj n K2) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj]
  exact CFSG.LieType.SteinbergBR.BinaryLinear.scalars_eq_bot card_K2

@[expose] def fullCuts (n : ℕ) : Set ℕ := {i | 1 ≤ i ∧ i < n}

@[expose] noncomputable def PI (n : ℕ) (I : Set ℕ) : Subgroup (projectiveSL n K2) :=
  (flagStabilizer n K2 I).map (proj n K2)

theorem exists_PI_of_ge {n : ℕ} {R : Subgroup (projectiveSL n K2)}
    (h : projUpperTriangular n K2 ≤ R) : ∃ I : Set ℕ, (∀ i ∈ I, 1 ≤ i ∧ i < n) ∧ R = PI n I := by
  set A := R.comap (proj n K2) with hA
  have hBA : upperTriangular n K2 ≤ A := by
    rw [hA, ← Subgroup.map_le_iff_le_comap]
    exact h
  obtain ⟨hAI, -⟩ := borel_overgroups A hBA
  refine ⟨borelOvergroupCuts A, ?_, ?_⟩
  · rintro i ⟨hi, hin, -⟩
    exact ⟨hi, hin⟩
  · rw [PI, ← hAI]
    exact (Subgroup.map_comap_eq_self_of_surjective (proj_surjective n K2) R).symm

theorem PI_le_PI_iff {n : ℕ} {I J : Set ℕ} (hJ : ∀ i ∈ J, 1 ≤ i ∧ i < n) :
    PI n I ≤ PI n J ↔ J ⊆ I := by
  rw [PI, PI, Subgroup.map_le_map_iff_of_injective (proj_injective n)]
  constructor
  · intro h j hj
    obtain ⟨hj1, hjn⟩ := hJ j hj
    by_contra hjI
    have h1 : reflection n K2 j hj1 hjn ∈ flagStabilizer n K2 I :=
      ((subflag_stabilizer_generation (K := K2) (n := n) I).2.2 j hj1 hjn).mpr hjI
    exact (((subflag_stabilizer_generation (K := K2) (n := n) J).2.2 j hj1 hjn).mp (h h1)) hj
  · intro hJI g hg
    exact mem_flagStabilizer.mpr fun i hi => mem_flagStabilizer.mp hg i (hJI hi)

theorem PI_empty (n : ℕ) : PI n ∅ = ⊤ := by
  rw [PI, flagStabilizer_empty, Subgroup.map_top_of_surjective _ (proj_surjective n K2)]

theorem flagStabilizer_full (n : ℕ) : flagStabilizer n K2 (fullCuts n) = upperTriangular n K2 := by
  have h := (borel_overgroups (upperTriangular n K2) le_rfl).1
  have hc : borelOvergroupCuts (upperTriangular n K2) = fullCuts n := by
    ext i
    constructor
    · rintro ⟨hi, hin, -⟩
      exact ⟨hi, hin⟩
    · rintro ⟨hi, hin⟩
      exact ⟨hi, hin, fun hB =>
        reflection_notMem_stabilizer hi hin (upperTriangular_le_stabilizer_flagSpace i hB)⟩
  rw [hc] at h
  exact h.symm

theorem PI_full (n : ℕ) : PI n (fullCuts n) = projUpperTriangular n K2 := by
  rw [PI, flagStabilizer_full]
  rfl

theorem fullCuts_sub {n : ℕ} : ∀ i ∈ fullCuts n, 1 ≤ i ∧ i < n := fun _ h => h

theorem cut3 {I : Set ℕ} (h : ∀ i ∈ I, 1 ≤ i ∧ i < 3) :
    I = ∅ ∨ I = {1} ∨ I = {2} ∨ I = fullCuts 3 := by
  have key : ∀ i, i ∈ I ↔ (i = 1 ∧ 1 ∈ I) ∨ (i = 2 ∧ 2 ∈ I) := by
    intro i
    constructor
    · intro hi
      have := h i hi
      rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
      · exact Or.inl ⟨rfl, hi⟩
      · exact Or.inr ⟨rfl, hi⟩
    · rintro (⟨rfl, hi⟩ | ⟨rfl, hi⟩) <;> exact hi
  by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I
  · right; right; right
    ext i
    rw [key i]
    change (i = 1 ∧ 1 ∈ I ∨ i = 2 ∧ 2 ∈ I) ↔ (1 ≤ i ∧ i < 3)
    constructor
    · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩) <;> omega
    · intro hi
      rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
      · exact Or.inl ⟨rfl, h1⟩
      · exact Or.inr ⟨rfl, h2⟩
  · right; left
    ext i
    rw [key i]
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro (⟨rfl, -⟩ | ⟨rfl, hi⟩)
      · rfl
      · exact absurd hi h2
    · rintro rfl; exact Or.inl ⟨rfl, h1⟩
  · right; right; left
    ext i
    rw [key i]
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro (⟨rfl, hi⟩ | ⟨rfl, -⟩)
      · exact absurd hi h1
      · rfl
    · rintro rfl; exact Or.inr ⟨rfl, h2⟩
  · left
    ext i
    rw [key i]
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro (⟨rfl, hi⟩ | ⟨rfl, hi⟩)
    · exact h1 hi
    · exact h2 hi

theorem overBool2_projUpperTriangular_three : OverBool2 (projUpperTriangular 3 K2) := by
  rw [← PI_full]
  have h1 : (1 : ℕ) ∈ fullCuts 3 := by simp [fullCuts]
  have h2 : (2 : ℕ) ∈ fullCuts 3 := by simp [fullCuts]
  have hs1 : ∀ i ∈ ({1} : Set ℕ), 1 ≤ i ∧ i < 3 := by
    intro i hi; rw [Set.mem_singleton_iff] at hi; subst hi; omega
  have hs2 : ∀ i ∈ ({2} : Set ℕ), 1 ≤ i ∧ i < 3 := by
    intro i hi; rw [Set.mem_singleton_iff] at hi; subst hi; omega
  have hsub1 : ({1} : Set ℕ) ⊆ fullCuts 3 := fun i hi => by
    rw [Set.mem_singleton_iff] at hi; subst hi; exact h1
  have hsub2 : ({2} : Set ℕ) ⊆ fullCuts 3 := fun i hi => by
    rw [Set.mem_singleton_iff] at hi; subst hi; exact h2
  refine ⟨PI 3 {1}, PI 3 {2}, ?_, ?_, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne ((PI_le_PI_iff hs1).mpr hsub1) fun h => ?_
    have := (PI_le_PI_iff fullCuts_sub).mp h.ge
    have h2' := this h2
    rw [Set.mem_singleton_iff] at h2'
    omega
  · refine lt_of_le_of_ne ((PI_le_PI_iff hs2).mpr hsub2) fun h => ?_
    have := (PI_le_PI_iff fullCuts_sub).mp h.ge
    have h1' := this h1
    rw [Set.mem_singleton_iff] at h1'
    omega
  · intro h
    have := (PI_le_PI_iff hs2).mp h
    have h2' := this (Set.mem_singleton 2)
    rw [Set.mem_singleton_iff] at h2'
    omega
  · intro h
    have := (PI_le_PI_iff hs1).mp h
    have h1' := this (Set.mem_singleton 1)
    rw [Set.mem_singleton_iff] at h1'
    omega
  · intro S hS
    rw [PI_full] at hS
    obtain ⟨I, hI, rfl⟩ := exists_PI_of_ge hS
    rcases cut3 hI with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (PI_empty 3)))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl rfl

theorem projUpperTriangular_eq_projUnitriangular (n : ℕ) :
    projUpperTriangular n K2 = projUnitriangular n K2 := by
  rw [projUpperTriangular, projUnitriangular,
    CFSG.LieType.SteinbergBR.BinaryLinear.upperTriangular_eq_unitriangular card_K2]

theorem normalizer_projUpperTriangular (n : ℕ) :
    Subgroup.normalizer (projUpperTriangular n K2 : Set (projectiveSL n K2)) =
      projUpperTriangular n K2 := by
  have h := normalizer_projUnitriangular (K := K2) (n := n) 2
  rw [projUpperTriangular_eq_projUnitriangular]
  exact h.trans (projUpperTriangular_eq_projUnitriangular n)

theorem projUpperTriangular_sylow (n : ℕ) (hn : 1 ≤ n) :
    IsPGroup 2 (projUpperTriangular n K2) ∧ ¬ 2 ∣ (projUpperTriangular n K2).index := by
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K2) 2 hn
  rw [projUpperTriangular_eq_projUnitriangular, ← hP]
  exact ⟨P.isPGroup', P.not_dvd_index⟩

theorem projUpperTriangular_ne_bot (n : ℕ) (hn : 2 ≤ n) : projUpperTriangular n K2 ≠ ⊥ := by
  intro h
  have h1 := card_projUnitriangular (K := K2) n
  rw [← projUpperTriangular_eq_projUnitriangular, h, Subgroup.card_bot, card_K2] at h1
  have : 1 ≤ n * (n - 1) / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 (by
      have := Nat.mul_le_mul hn (show 1 ≤ n - 1 by omega)
      omega)
  have h2 : 2 ≤ 2 ^ (n * (n - 1) / 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n * (n - 1) / 2) := Nat.pow_le_pow_right (by norm_num) this
  omega

theorem wrCollapse_three : WrZ2.WrCollapse (projUpperTriangular 3 K2) := by
  intro R P hDR hRP hnorm
  obtain ⟨C₁, C₂, h1, h2, h12, h21, hall⟩ := overBool2_projUpperTriangular_three
  obtain ⟨-, hs, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K2) (n := 3)
    (by norm_num) (Or.inl le_rfl)
  have : IsSimpleGroup (projectiveSL 3 K2) :=
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K2).symm.isSimpleGroup
  have hDnorm := normalizer_projUpperTriangular 3
  have hnotnormal : ∀ C : Subgroup (projectiveSL 3 K2), projUpperTriangular 3 K2 < C →
      R = projUpperTriangular 3 K2 → (∀ p ∈ C, ∀ r ∈ R, p * r * p⁻¹ ∈ R) → False := by
    intro C hDC hRD hn
    rw [hRD] at hn
    apply hDC.ne
    refine le_antisymm hDC.le (fun p hp => ?_)
    have : p ∈ Subgroup.normalizer (projUpperTriangular 3 K2 : Set (projectiveSL 3 K2)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => hn p hp x hx, fun hx => ?_⟩
      have := hn p⁻¹ (C.inv_mem hp) _ hx
      simpa [mul_assoc] using this
    rw [hDnorm] at this
    exact this
  have hRcases := hall R hDR
  rcases hall P (hDR.trans hRP) with hP | hP | hP | hP
  · rw [hP] at hRP ⊢
    exact le_antisymm hRP hDR
  · rw [hP] at hRP hnorm ⊢
    rcases hRcases with hR | hR | hR | hR
    · exact (hnotnormal C₁ h1 hR hnorm).elim
    · exact hR
    · exact (h21 (hR ▸ hRP)).elim
    · exact (h21 (le_top.trans (hR ▸ hRP))).elim
  · rw [hP] at hRP hnorm ⊢
    rcases hRcases with hR | hR | hR | hR
    · exact (hnotnormal C₂ h2 hR hnorm).elim
    · exact (h12 (hR ▸ hRP)).elim
    · exact hR
    · exact (h12 (le_top.trans (hR ▸ hRP))).elim
  · rw [hP] at hRP hnorm ⊢
    have : R.Normal := ⟨fun r hr p => hnorm p trivial r hr⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with hR | hR
    · exact (projUpperTriangular_ne_bot 3 (by norm_num) (le_bot_iff.mp (hR ▸ hDR))).elim
    · exact hR

theorem overBool2_l32WrZ2 {T : Subgroup L32WrZ2} (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) :
    OverBool2 T := by
  have hg : WrZ2.IsTwo (Multiplicative.ofAdd (1 : ZMod 2)) := ⟨by decide, by decide⟩
  have hQ2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp
  have hO : OverBool2 (WrZ2.wrSub (Multiplicative (ZMod 2)) (projUpperTriangular 3 K2)) :=
    WrZ2.overBool2_wrSub hg overBool2_projUpperTriangular_three wrCollapse_three
  obtain ⟨hDp, hDi⟩ := projUpperTriangular_sylow 3 (by norm_num)
  let e : (projectiveSL 3 K2) ≀ᵣ Multiplicative (ZMod 2) ≃* L32WrZ2 :=
    RegularWreathProduct.congr
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K2).symm (MulEquiv.refl _)
  exact OverBool2.sylow_of_mulEquiv e (WrZ2.isPGroup_wrSub hQ2 hDp) (WrZ2.index_wrSub hQ2 hDi) hO
    hT hTi

end CFSG.Quasithin.He5
