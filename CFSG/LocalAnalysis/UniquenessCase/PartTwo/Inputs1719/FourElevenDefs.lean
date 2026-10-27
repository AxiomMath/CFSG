module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
import CFSG.LocalAnalysis.WeakClosure81.InFGroupLargeMembers
import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.WeakClosure81

structure FourElevenSetting (Q : Type) [Group Q] [Finite Q] (L : Subgroup Q) (p : ℕ) : Prop where
  normal : L.Normal
  fstar_eq : Fstar (⊤ : Subgroup Q) = L
  prime : p.Prime
  ne_two : p ≠ 2
  isL3 : LieModel ↥L .PSL 3 p 1 ∨ LieModel ↥L .PSU 3 p 1
  nonabelian : ∃ a b : ↥L, a * b ≠ b * a
  not_psu33 : p = 3 → ¬ LieModel ↥L .PSU 3 3 1
  sup_eq_top : ∃ T : Subgroup Q, IsSylowIn 2 T ⊤ ∧ L ⊔ T = ⊤

@[expose] def W4Lem4_11Prime : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L : Subgroup Q) (p : ℕ), FourElevenSetting Q L p →
    InFGroup 1 Q ∨ (p = 5 ∧ InFGroup 2 Q)

@[expose] def FourElevenCase (j : ℕ) (P : ℕ → Prop) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L : Subgroup Q) (p : ℕ), FourElevenSetting Q L p → P p →
    ∀ T : Subgroup Q, IsSylowIn 2 T ⊤ → ∀ Ω : Set (Subgroup Q), IsOmegaColl Ω →
      (∀ A ∈ Ω, A ≤ T → 2 ^ (j + 1) ≤ Nat.card A) → genEi j T Ω ⊔ T = ⊤

abbrev FourElevenLarge : Prop := FourElevenCase 1 fun p => 7 ≤ p

abbrev FourElevenThree : Prop := FourElevenCase 1 fun p => p = 3

abbrev FourElevenFive : Prop := FourElevenCase 2 fun p => p = 5

theorem w4Lem4_11Prime_of (hL : FourElevenLarge) (h3 : FourElevenThree) (h5 : FourElevenFive) :
    W4Lem4_11Prime := by
  intro Q _ _ L p hS
  have hsimple : IsSimpleGroup ↥L := by
    rcases hS.isL3 with h | h
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  have hC : Subgroup.centralizer (L : Set Q) = ⊥ :=
    centralizer_eq_bot_of_fstar_top_eq hS.fstar_eq hsimple hS.nonabelian
  have hF : ∀ {j : ℕ}, (∀ T : Subgroup Q, IsSylowIn 2 T ⊤ → ∀ Ω : Set (Subgroup Q),
      IsOmegaColl Ω → (∀ A ∈ Ω, A ≤ T → 2 ^ (j + 1) ≤ Nat.card A) → genEi j T Ω ⊔ T = ⊤) →
      InFGroup j Q := fun h =>
    inFGroup_of_genEi_sup_eq_top hS.normal hsimple hS.nonabelian hC hS.sup_eq_top h
  have h2 := hS.prime.two_le
  have hne := hS.ne_two
  rcases (by omega : p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ 7 ≤ p) with hp | hp | hp | hp | hp
  · exact Or.inl (hF (h3 Q L p hS hp))
  · exact absurd hS.prime (by rw [hp]; norm_num)
  · exact Or.inr ⟨hp, hF (h5 Q L p hS hp)⟩
  · exact absurd hS.prime (by rw [hp]; norm_num)
  · exact Or.inl (hF (hL Q L p hS hp))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
