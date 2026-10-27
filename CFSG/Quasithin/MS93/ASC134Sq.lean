module

public import CFSG.Quasithin.EmptyFaithful.SzMSWC134
public import CFSG.Quasithin.MS93.C134SqCond

public section

namespace CFSG.Quasithin.MS93.MRes

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped Pointwise

@[expose] def AS_C_1_34_corrOneSq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) →
    (∃ (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ∧ IsModO2Surj L α) →
    C134SqCond R L → ∃ i : ℕ, IsC134CaseCorr i G₀ R L

@[expose] def AS_C_1_34_corrWOneSq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) →
    (∃ (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ∧ IsModO2Surj L α) →
    C134SqCond R L → ∃ i : ℕ, SzMSW.IsC134CaseCorrW i G₀ R L

theorem corrOneSq_of_corrWOneSq (h : AS_C_1_34_corrWOneSq) : AS_C_1_34_corrOneSq := by
  intro G _ _ G₀ R L hMS hL hG hsl3 hsq
  obtain ⟨i, hi⟩ := h G G₀ R L hMS hL hG hsl3 hsq
  exact ⟨i, hi.corr⟩

end CFSG.Quasithin.MS93.MRes
