module

public import CFSG.Quasithin.H13.KGLieTwDet

public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin Subgroup
open scoped Matrix

section Rank

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [CharP F 2]

theorem rank_one_of_socle [Finite F] (hF : Nat.card F = 2 ^ (2 * 1))
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {U : Subgroup ↥Γ} (hU2 : IsPGroup 2 U)
    {hi : ι}
    (hRC : ∀ X, IsHerm 1 X → (∀ u ∈ U,
      twist 1 (((u : ↥Γ) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) X = X) →
      X = X hi hi • unitM hi)
    (S₂ : Set (Matrix ι ι F)) (hS₂add : ∀ Y Y', Y ∈ S₂ → Y' ∈ S₂ → Y + Y' ∈ S₂)
    (hsoc : ∀ Y, IsHerm 1 Y → (∀ u ∈ U,
      twist 1 (((u : ↥Γ) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) Y - Y = 0 ∨
      twist 1 (((u : ↥Γ) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) Y - Y = unitM hi) →
      Y ∈ S₂)
    (hsupp : ∀ γ : ↥Γ, (∀ X, IsHerm 1 X →
      twist 1 ((γ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) X - X ∈ S₂) →
      ∀ X, IsHerm 1 X → twist 1 ((γ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) X = X)
    (h : ↥Γ) (hhS : ∀ Y ∈ S₂, twist 1 ((h : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) Y ∈ S₂)
    (hhE : twist 1 ((h : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) (unitM hi) = unitM hi)
    (hhmove : ∀ Y ∈ S₂, (twist 1 ((h : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) Y = Y ∨
      twist 1 ((h : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) Y = Y + unitM hi) →
      Y = 0 ∨ Y = unitM hi)
    {T : Matrix ι ι F → Matrix ι ι F} (hT : TwData 1 Γ U T) :
    ∀ X, IsHerm 1 X → T X - X = 0 ∨ T X - X = unitM hi := by
  classical
  have h2M : ∀ M : Matrix ι ι F, M + M = 0 := fun M => by
    rw [← two_smul F M, CharTwo.two_eq_zero, zero_smul]
  have hT0 : T 0 = 0 := by
    have h1 := hT.add 0 0 (isHerm_zero 1) (isHerm_zero 1)
    rw [add_zero] at h1
    exact add_eq_left.mp h1.symm
  have hinj : ∀ (g : Matrix.GeneralLinearGroup ι F) (Y Y' : Matrix ι ι F),
      twist 1 (g : Matrix ι ι F) Y = twist 1 (g : Matrix ι ι F) Y' → Y = Y' := by
    intro g Y Y' hYY
    have := congrArg (twist 1 (((g⁻¹ : Matrix.GeneralLinearGroup ι F)) : Matrix ι ι F)) hYY
    rwa [twist_inv_twist, twist_inv_twist] at this
  set imN : Set (Matrix ι ι F) := {Y | ∃ X, IsHerm 1 X ∧ T X - X = Y} with himN
  have hcard : imN.ncard ≤ 4 := hT.card
  have hNherm : ∀ X, IsHerm 1 X → IsHerm 1 (T X - X) := fun X hX =>
    isHerm_sub (hT.herm X hX) hX
  have hadd : ∀ Y Y', Y ∈ imN → Y' ∈ imN → Y + Y' ∈ imN := by
    rintro _ _ ⟨X, hX, rfl⟩ ⟨X', hX', rfl⟩
    refine ⟨X + X', isHerm_add hX hX', ?_⟩
    rw [hT.add X X' hX hX']
    abel
  have hmemU : ∀ u ∈ U, ∀ Y ∈ imN,
      twist 1 (((u : ↥Γ) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) Y ∈ imN := by
    rintro u hu _ ⟨X, hX, rfl⟩
    exact ⟨_, isHerm_twist hF _ hX, by rw [twist_sub, hT.comm u hu X hX]⟩
  obtain ⟨X₀, hX₀, hY0, hYfix⟩ := exists_fixed_of_twData hF hU2 hT
  have hY₀E := hRC _ (hNherm X₀ hX₀) hYfix
  have hc₀ : (T X₀ - X₀) hi hi = 1 := by
    have hf := isHerm_diag (hNherm X₀ hX₀) hi
    have hne : (T X₀ - X₀) hi hi ≠ 0 := by
      intro h0
      apply hY0
      rw [hY₀E, h0, zero_smul]
    have : (T X₀ - X₀) hi hi * ((T X₀ - X₀) hi hi - 1) = 0 := by
      linear_combination hf
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hne)
  rw [hc₀, one_smul] at hY₀E
  have hPm : unitM hi ∈ imN := ⟨X₀, hX₀, hY₀E⟩
  have hPfix : ∀ u ∈ U,
      twist 1 (((u : ↥Γ) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) (unitM hi) =
        unitM hi := fun u hu => by
    rw [← hY₀E]
    exact hYfix u hu
  by_contra hcon
  push Not at hcon
  obtain ⟨X₁, hX₁, hY₁0, hY₁P⟩ := hcon
  set Y₁ := T X₁ - X₁ with hY₁
  have hY₁m : Y₁ ∈ imN := ⟨X₁, hX₁, rfl⟩
  have hY₂m : Y₁ + unitM hi ∈ imN := hadd _ _ hY₁m hPm
  have hP0 : (unitM hi : Matrix ι ι F) ≠ 0 := by
    intro h0
    have := congrFun (congrFun h0 hi) hi
    simp [unitM] at this
  have hY₂0 : Y₁ + unitM hi ≠ 0 := by
    intro h0
    apply hY₁P
    have := congrArg (· + unitM hi) h0
    simpa only [zero_add, add_assoc, h2M, add_zero] using this
  have hY₂1 : Y₁ + unitM hi ≠ Y₁ := by
    intro h0
    apply hP0
    have := congrArg (Y₁ + ·) h0
    simpa only [← add_assoc, h2M, zero_add] using this
  have hY₂2 : Y₁ + unitM hi ≠ unitM hi := by
    intro h0
    apply hY₁0
    have := congrArg (· + unitM hi) h0
    simpa only [add_assoc, h2M, add_zero] using this
  have hsub : ({0, unitM hi, Y₁, Y₁ + unitM hi} : Set (Matrix ι ι F)) ⊆ imN := by
    intro Y hY
    rcases hY with rfl | rfl | rfl | rfl
    · exact ⟨0, isHerm_zero 1, by rw [hT0, sub_zero]⟩
    · exact hPm
    · exact hY₁m
    · exact hY₂m
  have hc4 : ({0, unitM hi, Y₁, Y₁ + unitM hi} : Set (Matrix ι ι F)).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_eq_three.mpr ⟨_, _, _, fun h => hY₁P h.symm,
      hY₂2.symm, hY₂1.symm, rfl⟩]
    rintro (h | h | h)
    · exact hP0 h.symm
    · exact hY₁0 h.symm
    · exact hY₂0 h.symm
  have heq : ({0, unitM hi, Y₁, Y₁ + unitM hi} : Set (Matrix ι ι F)) = imN :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hc4]; exact hcard) (Set.toFinite _)
  have hmemN : ∀ Y ∈ imN, Y = 0 ∨ Y = unitM hi ∨ Y = Y₁ ∨ Y = Y₁ + unitM hi := by
    intro Y hY
    rw [← heq] at hY
    rcases hY with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hmove : ∀ (g : Matrix.GeneralLinearGroup ι F),
      twist 1 (g : Matrix ι ι F) (unitM hi) = unitM hi →
      twist 1 (g : Matrix ι ι F) Y₁ ∈ imN →
      twist 1 (g : Matrix ι ι F) Y₁ = Y₁ ∨ twist 1 (g : Matrix ι ι F) Y₁ = Y₁ + unitM hi := by
    intro g hgP hgm
    rcases hmemN _ hgm with h0 | hP | h1 | h1
    · exact absurd (hinj g Y₁ 0 (by rw [h0, twist_zero])) hY₁0
    · exact absurd (hinj g Y₁ (unitM hi) (by rw [hP, hgP])) hY₁P
    · exact Or.inl h1
    · exact Or.inr h1
  have hNS : ∀ Y ∈ imN, Y ∈ S₂ := by
    intro Y hY
    obtain ⟨X, hX, rfl⟩ := hY
    refine hsoc _ (hNherm X hX) fun u hu => ?_
    have hu1 := hmove _ (hPfix u hu) (hmemU u hu Y₁ hY₁m)
    rcases hmemN _ ⟨X, hX, rfl⟩ with h | h | h | h <;> rw [h]
    · left
      rw [twist_zero, sub_zero]
    · left
      rw [hPfix u hu, sub_self]
    · rcases hu1 with h1 | h1 <;> rw [h1]
      · left
        exact sub_self _
      · right
        abel
    · rw [twist_add, hPfix u hu]
      rcases hu1 with h1 | h1 <;> rw [h1]
      · left
        exact sub_self _
      · right
        rw [show Y₁ + unitM hi + unitM hi - (Y₁ + unitM hi) = unitM hi by abel]
  obtain ⟨h', hh'⟩ := hT.norm h
  set x : ↥Γ := h' * h⁻¹ with hx
  have hxtw : ∀ X, twist 1 ((x : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) X =
      twist 1 ((h' : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F)
        (twist 1 (((h⁻¹ : ↥Γ) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) X) := by
    intro X
    rw [hx, Subgroup.coe_mul, Units.val_mul, twist_mul]
  have hsupp' := hsupp x (fun X hX => by
    set Z := twist 1 (((h⁻¹ : ↥Γ) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) X with hZ
    have hZh : IsHerm 1 Z := isHerm_twist hF _ hX
    have hXZ : X = twist 1 ((h : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) Z := by
      rw [hZ, ← twist_mul, Subgroup.coe_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        twist_one]
    rw [hxtw, ← hZ, ← hh' Z hZh]
    set W := twist 1 ((h : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) (T Z) with hW
    have hWh : IsHerm 1 W := isHerm_twist hF _ (hT.herm Z hZh)
    have e : T W - X = (T W - W) + twist 1 ((h : Matrix.GeneralLinearGroup ι F) :
        Matrix ι ι F) (T Z - Z) := by
      rw [twist_sub, ← hW, hXZ]
      abel
    rw [e]
    exact hS₂add _ _ (hNS _ ⟨W, hWh, rfl⟩) (hhS _ (hNS _ ⟨Z, hZh, rfl⟩)))
  have hTh : ∀ Z, IsHerm 1 Z →
      T (twist 1 ((h : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) (T Z)) =
        twist 1 ((h : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) Z := by
    intro Z hZ
    have h1 := hsupp' (twist 1 ((h : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) Z)
      (isHerm_twist hF _ hZ)
    rw [hxtw, Subgroup.coe_inv, twist_inv_twist, ← hh' Z hZ] at h1
    exact h1
  have hNh : ∀ Y, IsHerm 1 Y →
      T (twist 1 ((h : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) Y) -
        twist 1 ((h : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) Y =
      twist 1 ((h : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) (T Y - Y) := by
    intro Y hY
    have h1 := hTh (T Y) (hT.herm Y hY)
    rw [hT.invol Y hY] at h1
    rw [h1, twist_sub]
  have hhY : twist 1 ((h : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) Y₁ ∈ imN :=
    ⟨_, isHerm_twist hF _ hX₁, hNh X₁ hX₁⟩
  rcases hhmove Y₁ (hNS _ hY₁m) (hmove _ hhE hhY) with h0 | h0
  · exact hY₁0 h0
  · exact hY₁P h0

end Rank

end CFSG.Quasithin.H13.KGLie
