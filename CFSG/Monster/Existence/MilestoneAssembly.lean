module

public import CFSG.Monster.Existence.TwoPoint.GriessGraph

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

theorem monsterExistenceStatement_MGriess_of_open
    (hStroth : ∀ d₀ : Blueprint.NativeSporadic.B, orderOf d₀ = 2 →
      Matrix.rank (d₀.val.val - 1) = 1860 →
      ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (d : G), orderOf d = 2 →
        Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
          Subgroup.centralizer ({d₀} : Set Blueprint.NativeSporadic.B)) →
        Nonempty (G ≃* Blueprint.NativeSporadic.B))
    (I : GMSInterfaces (phiB uBar) MGriess) (hex : OddExhaustive tGriess xGriess)
    (hTh : Finite TauCeti.SporadicName.Th.Group ∧
      Nat.card TauCeti.SporadicName.Th.Group ≤ 90745943887872000)
    (h1 : TwoPointShape (cent2 tGriess uGriess) 1)
    (h6 : ∃ y, y ∈ tableVIISet tGriess xGriess tGriess .four_B ∧
      TwoPointShape (cent2 tGriess y) 6)
    (hiii : ∀ α β : MGriess, IsConj tGriess α → IsConj tGriess β →
      IsConj (α * β) threeARep →
      (∃ γ, IsConj tGriess γ ∧ IsConj (α * γ) threeARep ∧ IsConj tGriess (β * γ)) ∧
      (∀ γ γ', IsConj tGriess γ → IsConj (α * γ) threeARep → IsConj tGriess (β * γ) →
        IsConj tGriess γ' → IsConj (α * γ') threeARep → IsConj tGriess (β * γ') →
        ∃ g ∈ cent2 α β, g * γ * g⁻¹ = γ') ∧
      ∀ γ, IsConj tGriess γ → IsConj (α * γ) threeARep → IsConj tGriess (β * γ) →
        CFSG.Blueprint.LieModel ↥(cent2 α β ⊓ cent γ) .PSp 4 2 1)
    (hv : ∀ α β : MGriess, IsConj tGriess α → IsConj tGriess β → IsConj (α * β) threeARep →
      (∃ D : Set ↥(cent2 α β), CFSG.Blueprint.Fischer.Pair ↥(cent2 α β) D ∧
        {γ | IsConj tGriess γ ∧ IsConj tGriess (α * γ) ∧ IsConj tGriess (β * γ)} =
          Subtype.val '' D ∧
        ∀ γ ∈ D, Nat.card ↥(Subgroup.centralizer ({γ} : Set ↥(cent2 α β))) =
          2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13) ∧
      Set.ncard {γ | IsConj tGriess γ ∧ IsConj tGriess (α * γ) ∧ IsConj tGriess (β * γ)} = 31671)
    (h4d : ∀ α β : MGriess, IsConj tGriess α → IsConj tGriess β → IsConj tGriess (α * β) →
      ∃ γ δ : MGriess, IsLongTriangle tGriess {α, β, γ} ∧ IsConj tGriess δ ∧
        IsConj (α * δ) threeARep ∧ IsConj (β * δ) threeARep ∧
        (cent2 α β ⊓ cent γ) ⊔ (cent2 α β ⊓ cent δ) = cent2 α β ∧
        CFSG.Blueprint.LieModel ↥(cent2 α β ⊓ cent δ) .PSp 4 2 1) :
    MonsterExistenceStatement MGriess := by
  obtain ⟨⟨hfin, hsimp, hnab, hcard⟩, ht, hx, hnc, hinv, hA, hB⟩ :=
    monster_existence_clauses_one_two_of_stroth hStroth
  exact ⟨⟨hfin, hsimp, hnab, hcard⟩, tGriess, xGriess, ht, hx, hnc, hinv, hA, hB,
    isTwoAGraphData_MGriess_of I hex hcard (hA _ (IsConj.refl _)) hTh h1 h6 hiii hv h4d⟩

end CFSG.Monster.Existence
