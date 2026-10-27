module

public import CFSG.RankThree.PartTwo.Sec21.Item228Insp2ProofStar

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228Insp2Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.RankThree.PartTwo.Sec4 (diagUnits coe_diagUnits diagUnits_mul)
open Matrix

section Roots

variable {K : Type} [Field K]

theorem cube_root_cases' {τ c : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hc : c ^ 3 = 1) :
    c = 1 ∨ c = τ ∨ c = τ ^ 2 := by
  have hs : 1 + τ + τ ^ 2 = 0 := by
    have h : (τ - 1) * (1 + τ + τ ^ 2) = 0 := by linear_combination hτ
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hτ1)
  have h : (c - 1) * (c - τ) * (c - τ ^ 2) = 0 := by
    linear_combination hc - c ^ 2 * hs + c * τ * hs - hτ
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

theorem units_cube_root_cases {s₁ s₂ : Kˣ} (h₁ : s₁ ^ 3 = 1) (h₁1 : s₁ ≠ 1) (h₂ : s₂ ^ 3 = 1)
    (h₂1 : s₂ ≠ 1) : s₂ = s₁ ∨ s₂ = s₁ ^ 2 := by
  have h₁' : (s₁ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h₁, Units.val_one]
  have h₂' : (s₂ : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h₂, Units.val_one]
  have h₁1' : (s₁ : K) ≠ 1 := fun h => h₁1 (Units.ext h)
  rcases cube_root_cases' h₁' h₁1' h₂' with h | h | h
  · exact absurd (Units.ext h) h₂1
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by rw [h, Units.val_pow_eq_pow_val]))

@[expose] def IsOddCoord (s t : Kˣ) (k : Fin 3) : Prop :=
  (∀ l, l ≠ k → (![1, (s : K), (t : K)] : Fin 3 → K) l ≠ (![1, (s : K), (t : K)] : Fin 3 → K) k) ∧
    ∀ i j, i ≠ k → j ≠ k →
      (![1, (s : K), (t : K)] : Fin 3 → K) i = (![1, (s : K), (t : K)] : Fin 3 → K) j

theorem exists_isOddCoord {s t : Kˣ} (hst : ¬ (s = 1 ∧ t = 1))
    (hreg : ¬ Function.Injective (![1, (s : K), (t : K)] : Fin 3 → K)) :
    ∃ k, IsOddCoord s t k := by
  rw [Function.not_injective_iff] at hreg
  obtain ⟨i, j, hij, hne⟩ := hreg
  have hs1 : (s : K) = 1 ↔ s = 1 := ⟨fun h => Units.ext h, fun h => by rw [h, Units.val_one]⟩
  have ht1 : (t : K) = 1 ↔ t = 1 := ⟨fun h => Units.ext h, fun h => by rw [h, Units.val_one]⟩
  have hcases : (s : K) = 1 ∨ (t : K) = 1 ∨ (s : K) = t := by
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hne
      | exact Or.inl hij.symm
      | exact Or.inl hij
      | exact Or.inr (Or.inl hij.symm)
      | exact Or.inr (Or.inl hij)
      | exact Or.inr (Or.inr hij)
      | exact Or.inr (Or.inr hij.symm)
  rcases hcases with h | h | h
  ·
    have ht : (t : K) ≠ 1 := fun ht => hst ⟨hs1.mp h, ht1.mp ht⟩
    refine ⟨2, fun l hl => ?_, fun a b ha hb => ?_⟩
    · fin_cases l
      · exact fun e => ht e.symm
      · exact fun e => ht (h ▸ e).symm
      · exact absurd rfl hl
    · fin_cases a <;> fin_cases b
      all_goals first
        | rfl
        | exact absurd rfl ha
        | exact absurd rfl hb
        | exact h.symm
        | exact h
  ·
    have hs : (s : K) ≠ 1 := fun hs => hst ⟨hs1.mp hs, ht1.mp h⟩
    refine ⟨1, fun l hl => ?_, fun a b ha hb => ?_⟩
    · fin_cases l
      · exact fun e => hs e.symm
      · exact absurd rfl hl
      · exact fun e => hs (h ▸ e).symm
    · fin_cases a <;> fin_cases b
      all_goals first
        | rfl
        | exact absurd rfl ha
        | exact absurd rfl hb
        | exact h.symm
        | exact h
  ·
    have hs : (s : K) ≠ 1 := fun hs => hst ⟨hs1.mp hs, ht1.mp (h ▸ hs)⟩
    refine ⟨0, fun l hl => ?_, fun a b ha hb => ?_⟩
    · fin_cases l
      · exact absurd rfl hl
      · exact hs
      · exact fun e => hs (h.trans e)
    · fin_cases a <;> fin_cases b
      all_goals first
        | rfl
        | exact absurd rfl ha
        | exact absurd rfl hb
        | exact h.symm
        | exact h

theorem eq_or_eq_sq_of_isOddCoord {s₁ t₁ s₂ t₂ : Kˣ} (hs₁ : s₁ ^ 3 = 1) (ht₁ : t₁ ^ 3 = 1)
    (hs₂ : s₂ ^ 3 = 1) (ht₂ : t₂ ^ 3 = 1) {k : Fin 3} (h₁ : IsOddCoord s₁ t₁ k)
    (h₂ : IsOddCoord s₂ t₂ k) :
    diagUnits 1 s₂ t₂ = diagUnits 1 s₁ t₁ ∨ diagUnits 1 s₂ t₂ = diagUnits 1 s₁ t₁ ^ 2 := by
  have hsq : diagUnits (1 : Kˣ) s₁ t₁ ^ 2 = diagUnits 1 (s₁ ^ 2) (t₁ ^ 2) := by
    rw [sq, diagUnits_mul, one_mul, sq, sq]
  rw [hsq]
  have hne : ∀ u : Kˣ, (u : K) ≠ 1 → u ≠ 1 := fun u h e => h (by rw [e, Units.val_one])
  have heq : ∀ u : Kˣ, (u : K) = 1 → u = 1 := fun u h => Units.ext h
  fin_cases k
  ·
    have e₁ : (s₁ : K) = t₁ := h₁.2 1 2 (by decide) (by decide)
    have e₂ : (s₂ : K) = t₂ := h₂.2 1 2 (by decide) (by decide)
    have n₁ : (s₁ : K) ≠ 1 := fun e => h₁.1 1 (by decide) e
    have n₂ : (s₂ : K) ≠ 1 := fun e => h₂.1 1 (by decide) e
    have et₁ : t₁ = s₁ := Units.ext e₁.symm
    have et₂ : t₂ = s₂ := Units.ext e₂.symm
    rw [et₁, et₂]
    rcases units_cube_root_cases hs₁ (hne _ n₁) hs₂ (hne _ n₂) with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
  ·
    have e₁ : (t₁ : K) = 1 := (h₁.2 0 2 (by decide) (by decide)).symm
    have e₂ : (t₂ : K) = 1 := (h₂.2 0 2 (by decide) (by decide)).symm
    have n₁ : (s₁ : K) ≠ 1 := fun e => h₁.1 0 (by decide) e.symm
    have n₂ : (s₂ : K) ≠ 1 := fun e => h₂.1 0 (by decide) e.symm
    rw [heq _ e₁, heq _ e₂, one_pow]
    rcases units_cube_root_cases hs₁ (hne _ n₁) hs₂ (hne _ n₂) with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
  ·
    have e₁ : (s₁ : K) = 1 := (h₁.2 0 1 (by decide) (by decide)).symm
    have e₂ : (s₂ : K) = 1 := (h₂.2 0 1 (by decide) (by decide)).symm
    have n₁ : (t₁ : K) ≠ 1 := fun e => h₁.1 0 (by decide) e.symm
    have n₂ : (t₂ : K) ≠ 1 := fun e => h₂.1 0 (by decide) e.symm
    rw [heq _ e₁, heq _ e₂, one_pow]
    rcases units_cube_root_cases ht₁ (hne _ n₁) ht₂ (hne _ n₂) with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])

end Roots

variable {G : Type} [Group G] {X A : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def imageSL (ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K)
    (P : Subgroup G) : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) :=
  (P.subgroupOf X).map ι.toMonoidHom

noncomputable def imageSLEquiv (ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K) {P : Subgroup G}
    (hP : P ≤ X) : P ≃* imageSL ι P :=
  (Subgroup.subgroupOfEquivOfLe hP).symm.trans
    ((P.subgroupOf X).equivMapOfInjective ι.toMonoidHom ι.injective)

theorem sup_eq_of_imageSL (ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K) {P₁ P₂ : Subgroup G}
    (h₁ : P₁ ≤ X) (h₂ : P₂ ≤ X) (h : imageSL ι P₁ ⊔ imageSL ι P₂ = ⊤) : P₁ ⊔ P₂ = X := by
  have hmap : (P₁.subgroupOf X ⊔ P₂.subgroupOf X).map ι.toMonoidHom = (⊤ : Subgroup X).map
      ι.toMonoidHom := by
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ ι.surjective]
    exact h
  have htop : P₁.subgroupOf X ⊔ P₂.subgroupOf X = ⊤ :=
    Subgroup.map_injective ι.injective hmap
  rw [← Subgroup.subgroupOf_sup h₁ h₂, Subgroup.subgroupOf_eq_top] at htop
  exact le_antisymm (sup_le h₁ h₂) htop

theorem imageSL_le_diagSL_of_commute (ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K)
    {P : Subgroup G} {u : X} (hcomm : ∀ x ∈ P, (u : G) * x = x * u)
    (hu : ((ι u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag)
    (hinj : Function.Injective fun i =>
      ((ι u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i) :
    imageSL ι P ≤ diagSL K := by
  rintro _ ⟨x, hx, rfl⟩
  have hux : u * x = x * u := Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp hx))
  have h := congrArg (fun y : X =>
    ((ι y : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hux
  simp only [map_mul, Matrix.SpecialLinearGroup.coe_mul] at h
  rw [← hu.diagonal_diag] at h
  exact CFSG.RankThree.PartTwo.Sec4.Res417Frame.isDiag_of_commute_diagonal hinj h.symm

theorem mul_comm_of_actSL (ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K)
    {b : Subgroup.normalizer (X : Set G)} {D : GL (Fin 3) K} (hD : actSL ι b = slConjugation 3 K D)
    {x : X} (hx : (b : G) * x = x * b) :
    ((ι x : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (D : Matrix (Fin 3) (Fin 3) K) =
      (D : Matrix (Fin 3) (Fin 3) K) *
        ((ι x : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  have h := coe_eq_conj_of_actSL ι hD (x := x) (y := x)
    (by rw [hx, mul_inv_cancel_right])
  have hDD : ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (D : Matrix (Fin 3) (Fin 3) K) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((ι x : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (D : Matrix (Fin 3) (Fin 3) K) =
      (D : Matrix (Fin 3) (Fin 3) K) *
        ((ι x : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (D : Matrix (Fin 3) (Fin 3) K) := by
        rw [← h]
    _ = _ := by rw [Matrix.mul_assoc _ _ (D : Matrix (Fin 3) (Fin 3) K), hDD, Matrix.mul_one]

theorem not_imageSL_le_diagSL {Q : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    [Group.IsPerfect Q] (hQ : 1 < Nat.card Q) : ¬ Q ≤ diagSL K := by
  intro hle
  have hc : ∀ a b : Q, a * b = b * a := fun a b =>
    Subtype.ext (mul_comm_of_isDiag_SL (hle a.2) (hle b.2))
  have := subsingleton_of_isPerfect_of_comm hc
  rw [Nat.card_unique (α := Q)] at hQ
  exact lt_irrefl 1 hQ

theorem one_lt_card_SL2 [Finite K] : 1 < Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
  rw [Finite.one_lt_card_iff_nontrivial]
  refine ⟨⟨1, Matrix.SpecialLinearGroup.transvection (i := 0) (j := 1) (by decide) 1, ?_⟩⟩
  intro h
  have h' := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K =>
    (M : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp [Matrix.SpecialLinearGroup.transvection_coe] at h'

end CFSG.RankThree.PartTwo.Sec21.Item228Insp2Proof
