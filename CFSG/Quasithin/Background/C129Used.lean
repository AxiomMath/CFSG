module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Quasithin.Background.C2Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def IsBorelOfBlockUsed {G : Type*} [Group G] (L B : Subgroup G) : Prop :=
  if Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 then B ≤ pCoreOf 2 L
  else ∃ S : Subgroup G, IsSylowTwoOf S L ∧
    B ⊔ pCoreOf 2 L ≤ L ⊓ Subgroup.normalizer (S : Set G)

@[expose] def ASC129StatementUsed (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (H T M : Subgroup G), IsSQTKIn H → CharTwo H → IsSylowTwoOf T H → cgsIn H T ≤ M → M ≤ H →
    ∃ (r : ℕ) (Lb : Fin r → Subgroup G), r ≤ 2 ∧
      (∀ i, IsChi0Block H (Lb i) ∧ IsBorelOfBlockUsed (Lb i) (Lb i ⊓ M) ∧
        ⁅Lb i, thompsonJ T⁆ = Lb i) ∧
      ∀ h ∈ H, ∃ m ∈ M, ∃ x : Fin r → G, (∀ i, x i ∈ Lb i) ∧ h = m * (List.ofFn x).prod

end CFSG.Quasithin
