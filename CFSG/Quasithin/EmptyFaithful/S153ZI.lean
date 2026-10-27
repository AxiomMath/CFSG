module

public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin.Z391

open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem disjoint_sSup_of_sSupIndep {α : Type*} [CompleteLattice α] [IsModularLattice α] {s Y Z : Set α}
    [Finite s] (hs : sSupIndep s) (hY : Y ⊆ s) (hZ : Z ⊆ s) (hYZ : Disjoint Y Z) :
    Disjoint (sSup Y) (sSup Z) := by
  have hind := (sSupIndep_iff s).1 hs
  have hst : Disjoint {x : ↥s | (x : α) ∈ Y} {x : ↥s | (x : α) ∈ Z} := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact Set.disjoint_left.1 hYZ hx hx'
  have h := hind.disjoint_biSup_biSup' hst (Set.toFinite _)
  have e : ∀ W : Set α, W ⊆ s → (⨆ i ∈ {x : ↥s | (x : α) ∈ W}, (i : α)) = sSup W := by
    intro W hW
    refine le_antisymm (iSup₂_le fun i hi => le_sSup hi) (sSup_le fun T hT => ?_)
    exact le_iSup₂_of_le (⟨T, hW hT⟩ : ↥s) hT le_rfl
  rwa [e Y hY, e Z hZ] at h

theorem exists_index_two_sub [Finite Γ] {A A₁ : Subgroup Γ} (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hA₁A : A₁ ≤ A) (hne : A₁ ≠ A) :
    ∃ (a : Γ) (A' : Subgroup Γ), a ∈ A ∧ A₁ ≤ A' ∧ A' ≤ A ∧ a ∉ A' ∧
      ∀ x ∈ A, x ∈ A' ∨ a⁻¹ * x ∈ A' := by
  classical
  obtain ⟨a, haA, haA₁⟩ : ∃ a ∈ A, a ∉ A₁ := by
    by_contra h
    exact hne (le_antisymm hA₁A fun a ha => by_contra fun h' => h ⟨a, ha, h'⟩)
  let 𝒮 : Set (Subgroup Γ) := {B | A₁ ≤ B ∧ B ≤ A ∧ a ∉ B}
  have h𝒮 : 𝒮.Nonempty := ⟨A₁, le_rfl, hA₁A, haA₁⟩
  obtain ⟨A', hA', hmax⟩ := Set.exists_max_image 𝒮 (fun B => Nat.card B) (Set.toFinite 𝒮) h𝒮
  refine ⟨a, A', haA, hA'.1, hA'.2.1, hA'.2.2, fun x hx => ?_⟩
  by_cases hxA' : x ∈ A'
  · exact Or.inl hxA'
  right
  have hx2 : x ^ 2 = 1 := hA2 x hx
  have hxinv : x⁻¹ = x := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact hx2
  let B' : Subgroup Γ :=
    { carrier := {y | y ∈ A ∧ (y ∈ A' ∨ x * y ∈ A')}
      one_mem' := ⟨A.one_mem, Or.inl A'.one_mem⟩
      mul_mem' := by
        rintro y z ⟨hyA, hy⟩ ⟨hzA, hz⟩
        refine ⟨A.mul_mem hyA hzA, ?_⟩
        rcases hy with hy | hy <;> rcases hz with hz | hz
        · exact Or.inl (A'.mul_mem hy hz)
        · right
          have : x * (y * z) = y * (x * z) := by
            rw [← mul_assoc, hAc x hx y hyA, mul_assoc]
          rw [this]; exact A'.mul_mem hy hz
        · right
          have : x * (y * z) = (x * y) * z := by rw [mul_assoc]
          rw [this]; exact A'.mul_mem hy hz
        · left
          have : (x * y) * (x * z) = y * z := by
            calc (x * y) * (x * z) = x * (y * x) * z := by group
              _ = x * (x * y) * z := by rw [hAc y hyA x hx]
              _ = (x * x) * (y * z) := by group
              _ = y * z := by rw [← pow_two, hx2, one_mul]
          rw [← this]; exact A'.mul_mem hy hz
      inv_mem' := by
        rintro y ⟨hyA, hy⟩
        refine ⟨A.inv_mem hyA, ?_⟩
        rcases hy with hy | hy
        · exact Or.inl (A'.inv_mem hy)
        · right
          have : x * y⁻¹ = (x * y)⁻¹ := by
            rw [mul_inv_rev, hxinv]
            exact hAc x hx y⁻¹ (A.inv_mem hyA)
          rw [this]; exact A'.inv_mem hy }
  have hxB' : x ∈ B' := ⟨hx, Or.inr (by rw [← pow_two, hx2]; exact A'.one_mem)⟩
  have hA'B' : A' ≤ B' := fun y hy => ⟨hA'.2.1 hy, Or.inl hy⟩
  have hB'A : B' ≤ A := fun y hy => hy.1
  by_cases haB' : a ∈ B'
  · rcases haB'.2 with h | h
    · exact absurd h hA'.2.2
    ·
      have : a⁻¹ * x = (x * a)⁻¹ := by
        rw [mul_inv_rev, hxinv]
      rw [this]
      exact A'.inv_mem h
  · exfalso
    have hB'𝒮 : B' ∈ 𝒮 := ⟨hA'.1.trans hA'B', hB'A, haB'⟩
    have hle := hmax B' hB'𝒮
    have hlt : A' < B' := lt_of_le_of_ne hA'B' (fun h => hxA' (h ▸ hxB'))
    have := Subgroup.card_lt_of_lt hlt
    omega


theorem smul_iSup_translate (a : Γ) (A' : Subgroup Γ) (S : Subgroup Q) :
    a • (⨆ t : ↥A', (t : Γ) • S) = ⨆ t : ↥A', (a * (t : Γ)) • S := by
  have h : ∀ T : Subgroup Q, a • T = T.map (MulDistribMulAction.toMonoidHom Q a) := fun T => rfl
  rw [h, Subgroup.map_iSup]
  refine iSup_congr fun t => ?_
  rw [← h, mul_smul]

theorem rk_eq_log_of_elem [Finite Γ] {A : Subgroup Γ} (hA2 : ∀ x ∈ A, x ^ 2 = 1) :
    Nat.card ↥A = 2 ^ rk ↥A := by
  have : IsPGroup 2 ↥A :=
    isPGroup_two_of_sq_eq_one (fun x : ↥A => Subtype.ext (by simpa using hA2 _ x.2))
  exact card_eq_two_pow_of_isPGroup this

theorem rk_index_two [Finite Γ] {A A' : Subgroup Γ} {a : Γ} (haA : a ∈ A)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hA'A : A' ≤ A)
    (haA' : a ∉ A') (hsplit : ∀ x ∈ A, x ∈ A' ∨ a⁻¹ * x ∈ A') : rk ↥A = rk ↥A' + 1 := by
  have hidx : (A'.subgroupOf A).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨a, haA⟩, fun b => ?_⟩
    have hb := hsplit (b : Γ) b.2
    have ha2 := hA2 a haA
    have hainv : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact ha2
    have e : (b : Γ) * a = a⁻¹ * (b : Γ) := by rw [hainv]; exact hAc b b.2 a haA
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rw [e]
    by_cases h1 : (b : Γ) ∈ A'
    · have h2 : a⁻¹ * (b : Γ) ∉ A' := fun h => haA' (by
        have h3 := A'.mul_mem h (A'.inv_mem h1)
        rw [mul_inv_cancel_right] at h3
        simpa using A'.inv_mem h3)
      exact Or.inr ⟨h1, h2⟩
    · rcases hb with hb | hb
      · exact absurd hb h1
      · exact Or.inl ⟨hb, h1⟩
  have h1 := Subgroup.index_mul_card (A'.subgroupOf A)
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'A).toEquiv] at h1
  have h2 : Nat.card ↥A = 2 * Nat.card ↥A' := by rw [← h1]
  have hA'pos : Nat.card ↥A' ≠ 0 := Nat.card_pos.ne'
  unfold rk
  rw [h2, padicValNat.mul (by norm_num) hA'pos]
  have h3 : padicValNat 2 2 = 1 := by simp
  omega

end CFSG.Quasithin.Z391
