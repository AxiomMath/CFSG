module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def C8Good (D : Data G) (V₀ V L : Subgroup G) : Prop :=
  D.M ≤ normalizer (L : Set G) ∧ IsPGroup 2 ↥(L ⊓ F11.CTilde D.M V₀ V)

@[expose] def C8TleKGood (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_8 D V₀ V hV L → C8Good D V₀ V L →
      ∀ (v₀ : IntMod V hV) (T₀ K T' : Subgroup G), C8SetUp D V₀ V L hV v₀ T₀ K T' → T' ≤ K

@[expose] def C8InvThreePrimeGood (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_8 D V₀ V hV L → C8Good D V₀ V L →
      ∀ (v₀ : IntMod V hV) (T₀ K T' : Subgroup G), C8SetUp D V₀ V L hV v₀ T₀ K T' →
        ∃ N : Subgroup G, N ≤ K ∧ (N.subgroupOf K).Normal ∧ ¬ 3 ∣ Nat.card N ∧
          ∀ t ∈ K, t ^ 2 = 1 → t ∈ N

@[expose] def C8SchurSp6 : Prop :=
  ∀ (X Q : Type) [Group X] [Group Q] [Finite Q], IsSpn X 6 1 → Group.IsPerfect Q →
    ∀ q : Q →* X, Function.Surjective q → q.ker ≤ Subgroup.center Q → Nat.card q.ker ∣ 2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
