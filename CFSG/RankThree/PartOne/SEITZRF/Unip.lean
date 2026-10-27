module

public import CFSG.RankThree.PartOne.SEITZRF.Defs

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZRF

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

namespace Unip

section Blocks

variable {K : Type} [Field K] {a : ℕ}

theorem sylowB_eq_sylowV (b c : K) :
    sylowB a K b c = sylowV a K 0 b c 0 0 0 0 0 0 0 0 0 := by
  simp [sylowV, sylowA, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowL, sylowX,
    largeReeSigma_zero, pinnedX_zero]

theorem sylowD_eq_sylowV (d e : K) :
    sylowD a K d e = sylowV a K 0 0 0 d e 0 0 0 0 0 0 0 := by
  simp [sylowV, sylowA, sylowB, sylowF, sylowH, sylowJ, sylowK, sylowL, sylowX,
    largeReeSigma_zero, pinnedX_zero]

theorem sylowF_eq_sylowV (f g : K) :
    sylowF a K f g = sylowV a K 0 0 0 0 0 f g 0 0 0 0 0 := by
  simp [sylowV, sylowA, sylowB, sylowD, sylowH, sylowJ, sylowK, sylowL, sylowX,
    largeReeSigma_zero, pinnedX_zero]

theorem sylowH_eq_sylowV (h i : K) :
    sylowH a K h i = sylowV a K 0 0 0 0 0 0 0 h i 0 0 0 := by
  simp [sylowV, sylowA, sylowB, sylowD, sylowF, sylowJ, sylowK, sylowL, sylowX,
    largeReeSigma_zero, pinnedX_zero]

theorem sylowJ_eq_sylowV (j : K) :
    sylowJ a K j = sylowV a K 0 0 0 0 0 0 0 0 0 j 0 0 := by
  simp [sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowK, sylowL, sylowX,
    largeReeSigma_zero, pinnedX_zero]

theorem sylowK_eq_sylowV (k : K) :
    sylowK a K k = sylowV a K 0 0 0 0 0 0 0 0 0 0 k 0 := by
  simp [sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowL, sylowX,
    largeReeSigma_zero, pinnedX_zero]

theorem sylowL_eq_sylowV (l : K) :
    sylowL a K l = sylowV a K 0 0 0 0 0 0 0 0 0 0 0 l := by
  simp [sylowV, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowX,
    largeReeSigma_zero, pinnedX_zero]

end Blocks

section Membership

variable {K : Type} [Field K] [Finite K]
  [CharP K F4.prime] {a : ℕ}

theorem sylowV_rest_mem_complement_one (hK : Nat.card K = 2 ^ (2 * a + 1))
    (d e f g h i j k l : K) :
    sylowV a K 0 0 0 d e f g h i j k l ∈
      F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ :=
  Subgroup.mem_inf.2 ⟨sylowV_rest_mem_rootSpan_one _ _ _ _ _ _ _ _ _,
    (Subgroup.mem_inf.1 (sylowV_mem hK _ _ _ _ _ _ _ _ _ _ _ _)).2⟩

theorem sylowB_mem_complement_zero (hK : Nat.card K = 2 ^ (2 * a + 1)) (b c : K) :
    sylowB a K b c ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ := by
  rw [sylowB_eq_sylowV]
  exact sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _

theorem sylowD_mem_complement_zero (hK : Nat.card K = 2 ^ (2 * a + 1)) (d e : K) :
    sylowD a K d e ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ := by
  rw [sylowD_eq_sylowV]
  exact sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _

theorem sylowF_mem_complement_zero (hK : Nat.card K = 2 ^ (2 * a + 1)) (f g : K) :
    sylowF a K f g ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ := by
  rw [sylowF_eq_sylowV]
  exact sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _

theorem sylowH_mem_complement_zero (hK : Nat.card K = 2 ^ (2 * a + 1)) (h i : K) :
    sylowH a K h i ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ := by
  rw [sylowH_eq_sylowV]
  exact sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _

theorem sylowJ_mem_complement_zero (hK : Nat.card K = 2 ^ (2 * a + 1)) (j : K) :
    sylowJ a K j ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ := by
  rw [sylowJ_eq_sylowV]
  exact sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _

theorem sylowK_mem_complement_zero (hK : Nat.card K = 2 ^ (2 * a + 1)) (k : K) :
    sylowK a K k ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ := by
  rw [sylowK_eq_sylowV]
  exact sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _

theorem sylowL_mem_complement_zero (hK : Nat.card K = 2 ^ (2 * a + 1)) (l : K) :
    sylowL a K l ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ := by
  rw [sylowL_eq_sylowV]
  exact sylowV_zero_mem_complement hK _ _ _ _ _ _ _ _ _ _ _

theorem sylowD_mem_complement_one (hK : Nat.card K = 2 ^ (2 * a + 1)) (d e : K) :
    sylowD a K d e ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ := by
  rw [sylowD_eq_sylowV]
  exact sylowV_rest_mem_complement_one hK _ _ _ _ _ _ _ _ _

theorem sylowF_mem_complement_one (hK : Nat.card K = 2 ^ (2 * a + 1)) (f g : K) :
    sylowF a K f g ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ := by
  rw [sylowF_eq_sylowV]
  exact sylowV_rest_mem_complement_one hK _ _ _ _ _ _ _ _ _

theorem sylowH_mem_complement_one (hK : Nat.card K = 2 ^ (2 * a + 1)) (h i : K) :
    sylowH a K h i ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ := by
  rw [sylowH_eq_sylowV]
  exact sylowV_rest_mem_complement_one hK _ _ _ _ _ _ _ _ _

theorem sylowJ_mem_complement_one (hK : Nat.card K = 2 ^ (2 * a + 1)) (j : K) :
    sylowJ a K j ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ := by
  rw [sylowJ_eq_sylowV]
  exact sylowV_rest_mem_complement_one hK _ _ _ _ _ _ _ _ _

theorem sylowK_mem_complement_one (hK : Nat.card K = 2 ^ (2 * a + 1)) (k : K) :
    sylowK a K k ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ := by
  rw [sylowK_eq_sylowV]
  exact sylowV_rest_mem_complement_one hK _ _ _ _ _ _ _ _ _

theorem sylowL_mem_complement_one (hK : Nat.card K = 2 ^ (2 * a + 1)) (l : K) :
    sylowL a K l ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ := by
  rw [sylowL_eq_sylowV]
  exact sylowV_rest_mem_complement_one hK _ _ _ _ _ _ _ _ _

end Membership

section Levi

variable {K : Type} [Field K]

theorem mem_leviImage_of_mul_mul_mem {R V H : Subgroup (ModGL F4.tag K)}
    {hRV : R ≤ Subgroup.normalizer (V : Set (ModGL F4.tag K))} {r w₁ w₂ : ModGL F4.tag K}
    (hr : r ∈ R) (hw₁ : w₁ ∈ V) (hw₂ : w₂ ∈ V) (h : w₁ * r * w₂ ∈ H) :
    r ∈ leviImage R V H hRV := by
  refine ⟨hr, w₁ * (r * w₂ * r⁻¹),
    V.mul_mem hw₁ ((Subgroup.mem_normalizer_iff.1 (hRV hr) w₂).1 hw₂), ?_⟩
  have e : w₁ * (r * w₂ * r⁻¹) * r = w₁ * r * w₂ := by group
  rw [e]
  exact h

end Levi

section Rank

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem sylowA_mem_rankOneGroupOne (hK : Nat.card K = 2 ^ (2 * a + 1)) (s : K) :
    sylowA a K s ∈ rankOneGroupOne K a :=
  Subgroup.subset_closure (Or.inl (Or.inl (sylowA_mem_U1 hK s)))

theorem sylowB_mem_rankOneGroupTwo (hK : Nat.card K = 2 ^ (2 * a + 1)) (b c : K) :
    sylowB a K b c ∈ rankOneGroupTwo K a :=
  Subgroup.subset_closure (Or.inl (Or.inl (sylowB_mem_U2 hK b c)))

theorem sylowA_mem_Y1 (hK : Nat.card K = 2 ^ (2 * a + 1))
    {H : Subgroup (ModGL F4.tag K)} {s : K} {w₁ w₂ : ModGL F4.tag K}
    (hw₁ : w₁ ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩)
    (hw₂ : w₂ ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩)
    (h : w₁ * sylowA a K s * w₂ ∈ H) : sylowA a K s ∈ Y1 K a hK H :=
  mem_leviImage_of_mul_mul_mem (sylowA_mem_rankOneGroupOne hK s) hw₁ hw₂ h

theorem sylowB_mem_Y2 (hK : Nat.card K = 2 ^ (2 * a + 1))
    {H : Subgroup (ModGL F4.tag K)} {b c : K} {w₁ w₂ : ModGL F4.tag K}
    (hw₁ : w₁ ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩)
    (hw₂ : w₂ ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩)
    (h : w₁ * sylowB a K b c * w₂ ∈ H) : sylowB a K b c ∈ Y2 K a hK H :=
  mem_leviImage_of_mul_mul_mem (sylowB_mem_rankOneGroupTwo hK b c) hw₁ hw₂ h

end Rank

section RfBlocks

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem sylowV_mem_Rf_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    (x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ : K) :
    sylowV a K x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ ∈ Rf K a β ↔
      β x₀ = x₀ ∧ β x₁ = x₁ ∧ β x₂ = x₂ ∧ β x₃ = x₃ ∧ β x₄ = x₄ ∧ β x₅ = x₅ ∧ β x₆ = x₆ ∧
        β x₇ = x₇ ∧ β x₈ = x₈ ∧ β x₉ = x₉ ∧ β x₁₀ = x₁₀ ∧ β x₁₁ = x₁₁ := by
  have e : sylowV a K x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ =
      sylowVec a K ![x₀, x₁, x₂, x₃, x₄, x₅, x₆, x₇, x₈, x₉, x₁₀, x₁₁] := rfl
  rw [e, sylowVec_mem_Rf_iff hK β]
  refine ⟨fun h => ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7, h 8, h 9, h 10, h 11⟩, ?_⟩
  rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ i
  fin_cases i
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

theorem sylowA_mem_Rf_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) (s : K) :
    sylowA a K s ∈ Rf K a β ↔ β s = s := by
  rw [← sylowV_eq_sylowA (m := a), sylowV_mem_Rf_iff hK β]
  simp

theorem sylowB_mem_Rf_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) (b c : K) :
    sylowB a K b c ∈ Rf K a β ↔ β b = b ∧ β c = c := by
  rw [sylowB_eq_sylowV, sylowV_mem_Rf_iff hK β]
  simp

theorem sylowD_mem_Rf_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) (d e : K) :
    sylowD a K d e ∈ Rf K a β ↔ β d = d ∧ β e = e := by
  rw [sylowD_eq_sylowV, sylowV_mem_Rf_iff hK β]
  simp

theorem sylowF_mem_Rf_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) (f g : K) :
    sylowF a K f g ∈ Rf K a β ↔ β f = f ∧ β g = g := by
  rw [sylowF_eq_sylowV, sylowV_mem_Rf_iff hK β]
  simp

theorem sylowH_mem_Rf_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) (h i : K) :
    sylowH a K h i ∈ Rf K a β ↔ β h = h ∧ β i = i := by
  rw [sylowH_eq_sylowV, sylowV_mem_Rf_iff hK β]
  simp

theorem sylowJ_mem_Rf_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) (j : K) :
    sylowJ a K j ∈ Rf K a β ↔ β j = j := by
  rw [sylowJ_eq_sylowV, sylowV_mem_Rf_iff hK β]
  simp

theorem sylowK_mem_Rf_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) (k : K) :
    sylowK a K k ∈ Rf K a β ↔ β k = k := by
  rw [sylowK_eq_sylowV, sylowV_mem_Rf_iff hK β]
  simp

theorem sylowL_mem_Rf_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K) (l : K) :
    sylowL a K l ∈ Rf K a β ↔ β l = l := by
  rw [sylowL_eq_sylowV, sylowV_mem_Rf_iff hK β]
  simp

end RfBlocks

section Weyl

variable {K : Type} [Field K] [CharP K F4.prime]
  {a : ℕ}

theorem weylOne_conj_sylowB_full (b c : K) :
    weylOne K * sylowB a K b c * (weylOne K)⁻¹ = sylowD a K b c := by
  simp only [sylowB, sylowD, weyl_conj_mul]
  rw [weylOne_conj_sylowX (r := 25) (r' := 26) (by decide),
    weylOne_conj_sylowX (r := 27) (r' := 34) (by decide),
    weylOne_conj_sylowX (r := 28) (r' := 36) (by decide),
    weylOne_conj_sylowX (r := 30) (r' := 39) (by decide)]

theorem weylOne_conj_sylowD_full (d e : K) :
    weylOne K * sylowD a K d e * (weylOne K)⁻¹ = sylowB a K d e := by
  simp only [sylowB, sylowD, weyl_conj_mul]
  rw [weylOne_conj_sylowX (r := 26) (r' := 25) (by decide),
    weylOne_conj_sylowX (r := 34) (r' := 27) (by decide),
    weylOne_conj_sylowX (r := 36) (r' := 28) (by decide),
    weylOne_conj_sylowX (r := 39) (r' := 30) (by decide)]

theorem weylOne_conj_sylowF_full (f g : K) :
    weylOne K * sylowF a K f g * (weylOne K)⁻¹ = sylowH a K f g := by
  simp only [sylowF, sylowH, weyl_conj_mul]
  rw [weylOne_conj_sylowX (r := 29) (r' := 35) (by decide),
    weylOne_conj_sylowX (r := 37) (r' := 32) (by decide),
    weylOne_conj_sylowX (r := 43) (r' := 44) (by decide),
    weylOne_conj_sylowX (r := 46) (r' := 47) (by decide)]

theorem weylOne_conj_sylowH_full (h i : K) :
    weylOne K * sylowH a K h i * (weylOne K)⁻¹ = sylowF a K h i := by
  simp only [sylowF, sylowH, weyl_conj_mul]
  rw [weylOne_conj_sylowX (r := 35) (r' := 29) (by decide),
    weylOne_conj_sylowX (r := 32) (r' := 37) (by decide),
    weylOne_conj_sylowX (r := 44) (r' := 43) (by decide),
    weylOne_conj_sylowX (r := 47) (r' := 46) (by decide)]

theorem weylTwo_conj_sylowD_full (d e : K) :
    weylTwo K * sylowD a K d e * (weylTwo K)⁻¹ = sylowF a K d e := by
  simp only [sylowD, sylowF, weyl_conj_mul]
  rw [weylTwo_conj_sylowX (r := 26) (r' := 29) (by decide),
    weylTwo_conj_sylowX (r := 34) (r' := 37) (by decide),
    weylTwo_conj_sylowX (r := 36) (r' := 43) (by decide),
    weylTwo_conj_sylowX (r := 39) (r' := 46) (by decide)]

theorem weylTwo_conj_sylowF_full (f g : K) :
    weylTwo K * sylowF a K f g * (weylTwo K)⁻¹ = sylowD a K f g := by
  simp only [sylowD, sylowF, weyl_conj_mul]
  rw [weylTwo_conj_sylowX (r := 29) (r' := 26) (by decide),
    weylTwo_conj_sylowX (r := 37) (r' := 34) (by decide),
    weylTwo_conj_sylowX (r := 43) (r' := 36) (by decide),
    weylTwo_conj_sylowX (r := 46) (r' := 39) (by decide)]

theorem weylTwo_conj_sylowH_full (h i : K) :
    weylTwo K * sylowH a K h i * (weylTwo K)⁻¹ = sylowH a K h i := by
  simp only [sylowH, weyl_conj_mul]
  rw [weylTwo_conj_sylowX (r := 35) (r' := 35) (by decide),
    weylTwo_conj_sylowX (r := 32) (r' := 32) (by decide),
    weylTwo_conj_sylowX (r := 44) (r' := 44) (by decide),
    weylTwo_conj_sylowX (r := 47) (r' := 47) (by decide)]

theorem sylowJ_commute_sylowK (j k : K) : Commute (sylowJ a K j) (sylowK a K k) := by
  rw [sylowJ, sylowK]
  refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_) <;>
    exact sylowX_commute_of_commFactors (by norm_num) (by norm_num) (by norm_num) (by decide) _ _

theorem sylowJ_commute_sylowL (j l : K) : Commute (sylowJ a K j) (sylowL a K l) := by
  rw [sylowJ, sylowL]
  refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_) <;>
    exact sylowX_commute_of_commFactors (by norm_num) (by norm_num) (by norm_num) (by decide) _ _

end Weyl

section Main

variable {K : Type} [Field K] [Finite K]
  [CharP K F4.prime] {a : ℕ}

theorem map_eq_self_of_mul_sylowA_mul_mem' (hK : Nat.card K = 2 ^ (2 * a + 1)) {β : K ≃+* K}
    {H : Subgroup (ModGL F4.tag K)} (hA : ∀ s, sylowA a K s ∈ Y1 K a hK H → β s = s) {s : K}
    {w₁ w₂ : ModGL F4.tag K}
    (hw₁ : w₁ ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩)
    (hw₂ : w₂ ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩)
    (h : w₁ * sylowA a K s * w₂ ∈ H) : β s = s :=
  hA s (sylowA_mem_Y1 hK hw₁ hw₂ h)

theorem map_eq_self_of_mul_sylowB_mul_mem' (hK : Nat.card K = 2 ^ (2 * a + 1)) {β : K ≃+* K}
    {H : Subgroup (ModGL F4.tag K)}
    (hB : ∀ b c, sylowB a K b c ∈ Y2 K a hK H → β b = b ∧ β c = c) {b c : K}
    {w₁ w₂ : ModGL F4.tag K}
    (hw₁ : w₁ ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩)
    (hw₂ : w₂ ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩)
    (h : w₁ * sylowB a K b c * w₂ ∈ H) : β b = b ∧ β c = c :=
  hB b c (sylowB_mem_Y2 hK hw₁ hw₂ h)

theorem map_coords_eq_self_of_sylowV_mem' (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    {H : Subgroup (ModGL F4.tag K)} (hRH : Rf K a β ≤ H) (hA : ∀ s, sylowA a K s ∈ Y1 K a hK H → β s = s)
    (hB : ∀ b c, sylowB a K b c ∈ Y2 K a hK H → β b = b ∧ β c = c) {x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ : K}
    (hx : sylowV a K x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ ∈ H) :
    β x₀ = x₀ ∧ β x₁ = x₁ ∧ β x₂ = x₂ ∧ β x₃ = x₃ ∧ β x₄ = x₄ ∧ β x₅ = x₅ ∧ β x₆ = x₆ ∧
      β x₇ = x₇ ∧ β x₈ = x₈ ∧ β x₉ = x₉ ∧ β x₁₀ = x₁₀ ∧ β x₁₁ = x₁₁ := by
  have hn₁ : weylOne K ∈ H := hRH (weylOne_mem_Rf β)
  have hn₂ : weylTwo K ∈ H := hRH (weylTwo_mem_Rf β)
  have conj₁ : ∀ {y : ModGL F4.tag K}, y ∈ H → weylOne K * y * (weylOne K)⁻¹ ∈ H :=
    fun hy => H.mul_mem (H.mul_mem hn₁ hy) (H.inv_mem hn₁)
  have conj₂ : ∀ {y : ModGL F4.tag K}, y ∈ H → weylTwo K * y * (weylTwo K)⁻¹ ∈ H :=
    fun hy => H.mul_mem (H.mul_mem hn₂ hy) (H.inv_mem hn₂)
  have hx' : sylowA a K x₀ * (sylowB a K x₁ x₂ * (sylowD a K x₃ x₄ * (sylowF a K x₅ x₆ *
      (sylowH a K x₇ x₈ * (sylowJ a K x₉ * (sylowK a K x₁₀ * sylowL a K x₁₁)))))) ∈ H := by
    simpa only [sylowV, mul_assoc] using hx
  have h0 : β x₀ = x₀ := by
    refine map_eq_self_of_mul_sylowA_mul_mem' hK hA (one_mem _)
      (mul_mem (sylowB_mem_complement_zero hK x₁ x₂)
        (mul_mem (sylowD_mem_complement_zero hK x₃ x₄)
          (mul_mem (sylowF_mem_complement_zero hK x₅ x₆)
            (mul_mem (sylowH_mem_complement_zero hK x₇ x₈)
              (mul_mem (sylowJ_mem_complement_zero hK x₉)
                (mul_mem (sylowK_mem_complement_zero hK x₁₀)
                  (sylowL_mem_complement_zero hK x₁₁))))))) ?_
    simpa only [one_mul] using hx'
  have hA₀ : sylowA a K x₀ ∈ H := hRH ((sylowA_mem_Rf_iff hK β x₀).2 h0)
  have hx₁ := (H.mul_mem_cancel_left hA₀).1 hx'
  obtain ⟨h1, h2⟩ : β x₁ = x₁ ∧ β x₂ = x₂ := by
    refine map_eq_self_of_mul_sylowB_mul_mem' hK hB (one_mem _)
      (mul_mem (sylowD_mem_complement_one hK x₃ x₄)
        (mul_mem (sylowF_mem_complement_one hK x₅ x₆)
          (mul_mem (sylowH_mem_complement_one hK x₇ x₈)
            (mul_mem (sylowJ_mem_complement_one hK x₉)
              (mul_mem (sylowK_mem_complement_one hK x₁₀)
                (sylowL_mem_complement_one hK x₁₁)))))) ?_
    simpa only [one_mul] using hx₁
  have hB₀ : sylowB a K x₁ x₂ ∈ H := hRH ((sylowB_mem_Rf_iff hK β x₁ x₂).2 ⟨h1, h2⟩)
  have hx₂ := (H.mul_mem_cancel_left hB₀).1 hx₁
  have h₄ := conj₁ hx₂
  simp only [weyl_conj_mul, weylOne_conj_sylowD_full, weylOne_conj_sylowF_full,
    weylOne_conj_sylowH_full, weylOne_conj_sylowJ, weylOne_conj_sylowK,
    weylOne_conj_sylowL] at h₄
  obtain ⟨h3, h4⟩ : β x₃ = x₃ ∧ β x₄ = x₄ := by
    refine map_eq_self_of_mul_sylowB_mul_mem' hK hB (one_mem _)
      (mul_mem (sylowH_mem_complement_one hK x₅ x₆)
        (mul_mem (sylowF_mem_complement_one hK x₇ x₈)
          (mul_mem (sylowK_mem_complement_one hK x₉)
            (mul_mem (sylowJ_mem_complement_one hK x₁₀)
              (sylowL_mem_complement_one hK x₁₁))))) ?_
    simpa only [one_mul] using h₄
  have hD₀ : sylowD a K x₃ x₄ ∈ H := hRH ((sylowD_mem_Rf_iff hK β x₃ x₄).2 ⟨h3, h4⟩)
  have hx₃ := (H.mul_mem_cancel_left hD₀).1 hx₂
  have h₆ := conj₂ hx₃
  simp only [weyl_conj_mul, weylTwo_conj_sylowF_full, weylTwo_conj_sylowH_full,
    weylTwo_conj_sylowJ, weylTwo_conj_sylowK, weylTwo_conj_sylowL] at h₆
  have h9 : β x₉ = x₉ := by
    refine map_eq_self_of_mul_sylowA_mul_mem' hK hA
      (mul_mem (sylowD_mem_complement_zero hK x₅ x₆) (sylowH_mem_complement_zero hK x₇ x₈))
      (mul_mem (sylowL_mem_complement_zero hK x₁₀) (sylowK_mem_complement_zero hK x₁₁)) ?_
    simpa only [mul_assoc] using h₆
  have hJ₀ : sylowJ a K x₉ ∈ H := hRH ((sylowJ_mem_Rf_iff hK β x₉).2 h9)
  have hx₄ : sylowF a K x₅ x₆ * (sylowH a K x₇ x₈ * (sylowK a K x₁₀ * sylowL a K x₁₁)) ∈ H := by
    have hc : sylowJ a K x₉ * (sylowK a K x₁₀ * sylowL a K x₁₁) =
        (sylowK a K x₁₀ * sylowL a K x₁₁) * sylowJ a K x₉ :=
      ((sylowJ_commute_sylowK (a := a) x₉ x₁₀).mul_right
        (sylowJ_commute_sylowL (a := a) x₉ x₁₁)).eq
    have e : sylowF a K x₅ x₆ * (sylowH a K x₇ x₈ * (sylowJ a K x₉ * (sylowK a K x₁₀ *
        sylowL a K x₁₁))) = (sylowF a K x₅ x₆ * (sylowH a K x₇ x₈ * (sylowK a K x₁₀ *
        sylowL a K x₁₁))) * sylowJ a K x₉ := by
      rw [hc]
      simp only [mul_assoc]
    rw [e] at hx₃
    exact (H.mul_mem_cancel_right hJ₀).1 hx₃
  have h₈a := conj₂ (conj₁ hx₄)
  simp only [weyl_conj_mul, weylOne_conj_sylowF_full, weylOne_conj_sylowH_full,
    weylOne_conj_sylowK, weylOne_conj_sylowL, weylTwo_conj_sylowF_full,
    weylTwo_conj_sylowH_full, weylTwo_conj_sylowJ, weylTwo_conj_sylowL] at h₈a
  have h10 : β x₁₀ = x₁₀ := by
    refine map_eq_self_of_mul_sylowA_mul_mem' hK hA
      (mul_mem (sylowH_mem_complement_zero hK x₅ x₆) (sylowD_mem_complement_zero hK x₇ x₈))
      (sylowK_mem_complement_zero hK x₁₁) ?_
    simpa only [mul_assoc] using h₈a
  have h₈b := conj₁ (conj₂ hx₄)
  simp only [weyl_conj_mul, weylTwo_conj_sylowF_full, weylTwo_conj_sylowH_full,
    weylTwo_conj_sylowK, weylTwo_conj_sylowL, weylOne_conj_sylowD_full,
    weylOne_conj_sylowH_full, weylOne_conj_sylowK, weylOne_conj_sylowL] at h₈b
  obtain ⟨h5, h6⟩ : β x₅ = x₅ ∧ β x₆ = x₆ := by
    refine map_eq_self_of_mul_sylowB_mul_mem' hK hB (one_mem _)
      (mul_mem (sylowF_mem_complement_one hK x₇ x₈)
        (mul_mem (sylowL_mem_complement_one hK x₁₀)
          (sylowJ_mem_complement_one hK x₁₁))) ?_
    simpa only [one_mul] using h₈b
  have hF₀ : sylowF a K x₅ x₆ ∈ H := hRH ((sylowF_mem_Rf_iff hK β x₅ x₆).2 ⟨h5, h6⟩)
  have hx₅ := (H.mul_mem_cancel_left hF₀).1 hx₄
  have h₉ := conj₂ (conj₁ (conj₂ hx₅))
  simp only [weyl_conj_mul, weylTwo_conj_sylowH_full, weylTwo_conj_sylowK,
    weylTwo_conj_sylowL, weylOne_conj_sylowH_full, weylOne_conj_sylowK, weylOne_conj_sylowL,
    weylTwo_conj_sylowF_full, weylTwo_conj_sylowJ] at h₉
  have h11 : β x₁₁ = x₁₁ := by
    refine map_eq_self_of_mul_sylowA_mul_mem' hK hA
      (mul_mem (sylowD_mem_complement_zero hK x₇ x₈) (sylowK_mem_complement_zero hK x₁₀))
      (one_mem _) ?_
    simpa only [mul_assoc, mul_one] using h₉
  have hK₀ : sylowK a K x₁₀ ∈ H := hRH ((sylowK_mem_Rf_iff hK β x₁₀).2 h10)
  have hL₀ : sylowL a K x₁₁ ∈ H := hRH ((sylowL_mem_Rf_iff hK β x₁₁).2 h11)
  have hx₆ : sylowH a K x₇ x₈ ∈ H := (H.mul_mem_cancel_right (H.mul_mem hK₀ hL₀)).1 hx₅
  have h₁₀ := conj₁ (conj₂ (conj₁ hx₆))
  simp only [weylOne_conj_sylowH_full, weylTwo_conj_sylowF_full,
    weylOne_conj_sylowD_full] at h₁₀
  obtain ⟨h7, h8⟩ : β x₇ = x₇ ∧ β x₈ = x₈ := by
    refine map_eq_self_of_mul_sylowB_mul_mem' hK hB (one_mem _) (one_mem _) ?_
    simpa only [one_mul, mul_one] using h₁₀
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

end Main

end Unip

section Final

variable {K : Type}
  [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem inf_reeFixedPosUnipotent_le_Rf_of_roots (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : K ≃+* K) {H : Subgroup (ModGL F4.tag K)} (hRH : Rf K a β ≤ H)
    (hA : ∀ s, sylowA a K s ∈ Y1 K a hK H → β s = s)
    (hB : ∀ b c, sylowB a K b c ∈ Y2 K a hK H → β b = b ∧ β c = c) :
    H ⊓ F4.reeFixedPosUnipotent K a ≤ Rf K a β := by
  intro x hx
  obtain ⟨hxH, hxU⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨z, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hxU
  exact (Unip.sylowV_mem_Rf_iff hK β _ _ _ _ _ _ _ _ _ _ _ _).2
    (Unip.map_coords_eq_self_of_sylowV_mem' hK β hRH hA hB hxH)

theorem inf_reeFixedPosUnipotent_le_Rf (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    {H : Subgroup (ModGL F4.tag K)} (hRH : Rf K a β ≤ H) (hY1 : Y1 K a hK H ≤ Rf K a β)
    (hY2 : Y2 K a hK H ≤ Rf K a β) :
    H ⊓ F4.reeFixedPosUnipotent K a ≤ Rf K a β :=
  inf_reeFixedPosUnipotent_le_Rf_of_roots hK β hRH
    (fun s hs => (Unip.sylowA_mem_Rf_iff hK β s).1 (hY1 hs))
    (fun b c hbc => (Unip.sylowB_mem_Rf_iff hK β b c).1 (hY2 hbc))

end Final

end CFSG.RankThree.PartOne.SEITZRF
