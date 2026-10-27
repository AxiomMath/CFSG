module

public import CFSG.Quasithin.Vol2.Ch11SecB414MM

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Assembly.LowTwoRank (StatedSL)
open Matrix

variable {F : Type} [Field F] {G : Type} [Group G]
  {Γ V Z L X : Subgroup G} {k : ℕ} {α : ↥Γ →* PGL3 F} (m : Model Γ V Z F k α)
  (hLΓ : L ≤ Γ) (hXΓ : X ≤ Γ) (hL : (L.subgroupOf Γ).map α = Ptheta F 0)
  {ν : Fˣ} (hX : (X.subgroupOf Γ).map α = Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν)))

include hLΓ hXΓ hL hX

theorem Model.Y_le_bot : L ⊔ X ≤ Subgroup.normalizer (m.pre ⊥ : Set G) :=
  m.le_normalizer_Y hLΓ hXΓ hL hX (fun _ _ _ _ M hM => by
    rw [AddSubgroup.mem_bot] at hM ⊢; rw [hM, cnj, Matrix.mul_zero, Matrix.zero_mul])
    (fun _ M hM => by
      rw [AddSubgroup.mem_bot] at hM ⊢
      rw [hM, twAdj, Matrix.mul_zero, Matrix.zero_mul, smul_zero])

theorem Model.Y_le_Wp : L ⊔ X ≤ Subgroup.normalizer (m.pre Wp : Set G) :=
  m.le_normalizer_Y hLΓ hXΓ hL hX (fun _ h10 h20 _ _ hM => Wp_cnj h10 h20 hM)
    (fun c _ hM => Wp_dg k c hM)

theorem Model.Y_le_W2 : L ⊔ X ≤ Subgroup.normalizer (m.pre W2 : Set G) :=
  m.le_normalizer_Y hLΓ hXΓ hL hX (fun _ h10 h20 hdet _ hM => (W2_cnj h10 h20 hdet hM).1)
    (fun c _ hM => W2_dg k c hM)

theorem Model.Y_le_W3 [CharP F 2] : L ⊔ X ≤ Subgroup.normalizer (m.pre W3 : Set G) :=
  m.le_normalizer_Y hLΓ hXΓ hL hX (fun _ h10 h20 hdet _ hM => W3_cnj h10 h20 hdet hM)
    (fun c _ hM => W3_dg k c hM)

theorem Model.Y_le_W4 : L ⊔ X ≤ Subgroup.normalizer (m.pre W4 : Set G) :=
  m.le_normalizer_Y hLΓ hXΓ hL hX (fun _ h10 h20 hdet _ hM => (W4_cnj h10 h20 hdet hM).1)
    (fun c _ hM => W4_dg k c hM)

theorem Model.Y_le_Wsl : L ⊔ X ≤ Subgroup.normalizer (m.pre Wsl : Set G) :=
  m.le_normalizer_Y hLΓ hXΓ hL hX (fun _ _ _ hdet _ hM => Wsl_cnj hdet hM)
    (fun c _ hM => Wsl_dg k c hM)

omit hL hX in
theorem Model.Y_le_W2a [CharP F 2] (m : Model Γ V Z F 0 α)
    (hL : (L.subgroupOf Γ).map α = Ptheta F 0)
    (hX : (X.subgroupOf Γ).map α = Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν))) :
    L ⊔ X ≤ Subgroup.normalizer (m.pre W2a : Set G) :=
  m.le_normalizer_Y hLΓ hXΓ hL hX (fun _ h10 h20 hdet _ hM => W2a_cnj h10 h20 hdet hM)
    (fun c _ hM => W2a_dg c hM)

omit hL hX in
theorem Model.Y_le_W4a [CharP F 2] (m : Model Γ V Z F 0 α)
    (hL : (L.subgroupOf Γ).map α = Ptheta F 0)
    (hX : (X.subgroupOf Γ).map α = Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν))) :
    L ⊔ X ≤ Subgroup.normalizer (m.pre W4a : Set G) :=
  m.le_normalizer_Y hLΓ hXΓ hL hX (fun _ h10 h20 hdet _ hM => W4a_cnj h10 h20 hdet hM)
    (fun c _ hM => W4a_dg c hM)

section Min

variable [CharP F 2]

omit hLΓ hXΓ hL hX

theorem Model.min_Wp_W2a {J : Subgroup G} (h1 : m.pre Wp ≤ J) (h2 : J ≤ m.pre W2a) :
    J = m.pre Wp ∨ J = m.pre W2a := by
  refine m.eq_or_eq_of_index_two (M₀ := hatI F) (fun M hM => ?_) h1 h2
  have hs := sub_hatI_mem_Wp hM.1
  rcases hM.2 with h | h
  · left
    rwa [h, zero_smul, sub_zero] at hs
  · right
    rwa [h, one_smul] at hs

theorem Model.min_W3_W4a {J : Subgroup G} (h1 : m.pre W3 ≤ J) (h2 : J ≤ m.pre W4a) :
    J = m.pre W3 ∨ J = m.pre W4a := by
  refine m.eq_or_eq_of_index_two (M₀ := dD F) (fun M hM => ?_) h1 h2
  have hs := sub_dD_mem_W3 hM.1
  rcases hM.2 with h | h
  · left
    rwa [h, zero_smul, sub_zero] at hs
  · right
    rwa [h, one_smul] at hs

variable [Finite F]

omit [CharP F 2] in
theorem eq_four (hF : Nat.card F = 4) [CharP F 2] {ν : Fˣ} (hν : ν ≠ 1) (t : F) :
    t = 0 ∨ t = 1 ∨ t = ν ∨ t = 1 + ν := by
  have hν1 : (ν : F) ≠ 1 := fun h => hν (Units.ext h)
  have hν0 : (ν : F) ≠ 0 := ν.ne_zero
  have h1ν : (1 : F) + ν ≠ 0 := fun h => hν1 (by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination h - h2)
  by_cases ht : t = 0
  · exact Or.inl ht
  right
  exact eq_of_card_four hF one_ne_zero hν0 h1ν (Ne.symm hν1)
    (fun h => hν0 (by linear_combination -h)) (fun h => one_ne_zero (by linear_combination -h))
    ht

theorem Model.min_W2a_W2 (hF : Nat.card F = 4) (hν : ν ≠ 1) {J : Subgroup G}
    (h1 : m.pre W2a ≤ J) (h2 : J ≤ m.pre W2) : J = m.pre W2a ∨ J = m.pre W2 := by
  refine m.eq_or_eq_of_index_two (M₀ := (ν : F) • hatI F) (fun M hM => ?_) h1 h2
  have hI : (ν : F) • hatI F ∈ (W2 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hatI]
  rcases eq_four hF hν (M 1 1) with h | h | h | h
  · exact Or.inl ⟨hM, Or.inl h⟩
  · exact Or.inl ⟨hM, Or.inr h⟩
  · refine Or.inr ⟨W2.sub_mem hM hI, Or.inl ?_⟩
    simp [hatI, h]
  · refine Or.inr ⟨W2.sub_mem hM hI, Or.inr ?_⟩
    simp [hatI, h]

theorem Model.min_W4a_W4 (hF : Nat.card F = 4) (hν : ν ≠ 1) {J : Subgroup G}
    (h1 : m.pre W4a ≤ J) (h2 : J ≤ m.pre W4) : J = m.pre W4a ∨ J = m.pre W4 := by
  refine m.eq_or_eq_of_index_two (M₀ := (ν : F) • dD F) (fun M hM => ?_) h1 h2
  have hD : (ν : F) • dD F ∈ (W4 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Matrix.trace_smul, (dD_mem_W4 (F := F)).1, smul_zero]
    · simp [dD]
    · simp [dD]
  rcases eq_four hF hν (M 0 0) with h | h | h | h
  · exact Or.inl ⟨hM, Or.inl h⟩
  · exact Or.inl ⟨hM, Or.inr h⟩
  · refine Or.inr ⟨W4.sub_mem hM hD, Or.inl ?_⟩
    simp [dD, h]
  · refine Or.inr ⟨W4.sub_mem hM hD, Or.inr ?_⟩
    simp [dD, h]

end Min

end CFSG.Quasithin.H13.Ch4.B414.M
