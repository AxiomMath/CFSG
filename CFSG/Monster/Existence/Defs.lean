module

public import CFSG.Monster.Griess.AutFinite
public import CFSG.Blueprint.Catalog
public import CFSG.Open.MonsterDefs
public import CFSG.Blueprint.FischerDefs

public section

namespace CFSG.Monster.Existence

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

abbrev MGriess : Type := ↥CFSG.Monster.Griess.AutO

@[expose] def twoBCentralizerOrder : ℕ := 2 ^ 46 * 3 ^ 9 * 5 ^ 4 * 7 ^ 2 * 11 * 13 * 23

@[expose] def suborbitClassOrder : Fin 9 → ℕ := ![1, 2, 2, 3, 3, 4, 4, 5, 6]

variable {G : Type} [Group G]

abbrev cent (x : G) : Subgroup G := Subgroup.centralizer {x}

abbrev cent2 (α β : G) : Subgroup G := cent α ⊓ cent β

abbrev pointStab (s : Set G) : Subgroup G := ⨅ x ∈ s, cent x

@[expose] def conjSet (g : G) (s : Set G) : Set G := (fun x => g * x * g⁻¹) '' s

@[expose] def HasTwoShape (H : Subgroup G) (k : ℕ) (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∃ (N : Subgroup H) (_ : N.Normal), Nat.card N = 2 ^ k ∧ P (H ⧸ N)

@[expose] def HasLayeredTwoShape (H : Subgroup G) (a b : ℕ) (P : ∀ (X : Type) [Group X], Prop) :
    Prop :=
  ∃ (N : Subgroup H) (_ : N.Normal) (N₀ : Subgroup H) (_ : N₀.Normal), N₀ ≤ N ∧
    IsElementaryAbelian 2 N₀ ∧ Nat.card N₀ = 2 ^ a ∧
    IsElementaryAbelian 2 (N ⧸ N₀.subgroupOf N) ∧ Nat.card N = 2 ^ (a + b) ∧ P (H ⧸ N)

@[expose] def TwoPointShape (H : Subgroup G) : Fin 9 → Prop
  | 0 => HasTwoShape H 1 fun X _ => Nonempty (X ≃* NativeSporadic.B)
  | 1 => ∃ (N : Subgroup H) (_ : N.Normal), IsElementaryAbelian 2 N ∧ Nat.card N = 2 ^ 2 ∧
      LieModel (H ⧸ N) .twistedE6 0 2 1
  | 2 => HasLayeredTwoShape H 2 22 fun X _ => Nonempty (X ≃* NativeSporadic.Co2)
  | 3 => Nonempty (H ≃* NativeSporadic.Fi23)
  | 4 => Nonempty (H ≃* NativeSporadic.Th)
  | 5 => ∃ (N : Subgroup H) (_ : N.Normal), IsExtraspecialPGroup 2 N ∧ Nat.card N = 2 ^ 23 ∧
      Nonempty (H ⧸ N ≃* NativeSporadic.McL)
  | 6 => HasTwoShape H 1 fun X _ => LieModel X .F4 0 2 1
  | 7 => Nonempty (H ≃* NativeSporadic.HN)
  | 8 => HasTwoShape H 1 fun X _ => Nonempty (X ≃* NativeSporadic.Fi22)

@[expose] def IsTwoACentralizer (a : G) : Prop :=
  Group.IsPerfect (cent a) ∧ (Subgroup.center (cent a)).map (cent a).subtype = Subgroup.zpowers a ∧
    Nonempty (cent a ⧸ Subgroup.center (cent a) ≃* NativeSporadic.B)

@[expose] def IsTwoBCentralizer (z : G) : Prop :=
  IsExtraspecialPGroup 2 (pCore 2 (cent z)) ∧ Nat.card (pCore 2 (cent z)) = 2 ^ 25 ∧
    Subgroup.centralizer (inSubgroup (pCore 2) (cent z) : Set G) ≤ inSubgroup (pCore 2) (cent z) ∧
    Nonempty (cent z ⧸ pCore 2 (cent z) ≃* NativeSporadic.Co1) ∧
    Nat.card (cent z) = twoBCentralizerOrder ∧ ¬ 17 ∣ Nat.card (cent z)

@[expose] def IsTriangle (a : G) (s : Set G) : Prop :=
  s.ncard = 3 ∧ (∀ x ∈ s, IsConj a x) ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → IsConj a (x * y)

@[expose] def IsShortTriangle (a : G) (s : Set G) : Prop :=
  IsTriangle a s ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → x * y ∈ s

@[expose] def IsLongTriangle (a : G) (s : Set G) : Prop :=
  IsTriangle a s ∧ ¬ IsShortTriangle a s

@[expose] def IsTwoAGraphData (a z : G) : Prop :=
  (∀ α β β' : G, IsConj a α → IsConj a β → IsConj a β' → IsConj (α * β) (α * β') →
    ∃ g ∈ cent α, g * β * g⁻¹ = β') ∧
  ∃ c : Fin 9 → G,
    (∀ i j, IsConj (c i) (c j) → i = j) ∧ c 0 = 1 ∧ IsConj a (c 1) ∧ IsConj z (c 2) ∧
    (∀ i, orderOf (c i) = suborbitClassOrder i) ∧
    (∀ α β : G, IsConj a α → IsConj a β → ∃ i, IsConj (α * β) (c i)) ∧
    (∀ i, ∃ α β : G, IsConj a α ∧ IsConj a β ∧ IsConj (α * β) (c i)) ∧
    (∀ (α β : G) (i : Fin 9), IsConj a α → IsConj a β → IsConj (α * β) (c i) →
      TwoPointShape (cent2 α β) i) ∧
    (∀ α β : G, IsConj a α → IsConj a β → IsConj (α * β) (c 3) →
      (∃ γ, IsConj a γ ∧ IsConj (α * γ) (c 3) ∧ IsConj a (β * γ)) ∧
      (∀ γ γ', IsConj a γ → IsConj (α * γ) (c 3) → IsConj a (β * γ) →
        IsConj a γ' → IsConj (α * γ') (c 3) → IsConj a (β * γ') →
        ∃ g ∈ cent2 α β, g * γ * g⁻¹ = γ') ∧
      ∀ γ, IsConj a γ → IsConj (α * γ) (c 3) → IsConj a (β * γ) →
        LieModel ↥(cent2 α β ⊓ cent γ) .PSp 4 2 1) ∧
    (∀ α β : G, IsConj a α → IsConj a β → IsConj (α * β) (c 6) →
      α ≠ β ∧ ¬ IsConj a (α * β) ∧
        ∃! γ, IsConj a γ ∧ IsConj a (α * γ) ∧ IsConj a (γ * β)) ∧
    (∀ α β : G, IsConj a α → IsConj a β → IsConj (α * β) (c 3) →
      (∃ D : Set ↥(cent2 α β), CFSG.Blueprint.Fischer.Pair ↥(cent2 α β) D ∧
        {γ | IsConj a γ ∧ IsConj a (α * γ) ∧ IsConj a (β * γ)} =
          Subtype.val '' D ∧
        ∀ γ ∈ D, Nat.card ↥(Subgroup.centralizer ({γ} : Set ↥(cent2 α β))) =
          2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13) ∧
      Set.ncard {γ | IsConj a γ ∧ IsConj a (α * γ) ∧ IsConj a (β * γ)} = 31671) ∧
    (∃ s₁ s₂ : Set G, IsTriangle a s₁ ∧ IsTriangle a s₂ ∧ (∀ g : G, conjSet g s₁ ≠ s₂) ∧
      ∀ s, IsTriangle a s → ∃ g : G, conjSet g s = s₁ ∨ conjSet g s = s₂) ∧
    (∀ α β : G, IsConj a α → IsConj a β → IsConj a (α * β) →
      {s | IsShortTriangle a s ∧ α ∈ s ∧ β ∈ s}.ncard = 1 ∧
      {s | IsLongTriangle a s ∧ α ∈ s ∧ β ∈ s}.ncard = 3968055) ∧
    (∀ s, IsLongTriangle a s →
      LieModel (pointStab s ⧸ pCore 2 (pointStab s)) .PSU 6 2 1 ∧
      HasLayeredTwoShape (pointStab s) 3 20 fun X _ => LieModel X .PSU 6 2 1) ∧
    (∀ α β : G, IsConj a α → IsConj a β → IsConj a (α * β) →
      ∃ γ δ : G, IsLongTriangle a {α, β, γ} ∧ IsConj a δ ∧ IsConj (α * δ) (c 3) ∧
        IsConj (β * δ) (c 3) ∧
        (cent2 α β ⊓ cent γ) ⊔ (cent2 α β ⊓ cent δ) = cent2 α β ∧
        LieModel ↥(cent2 α β ⊓ cent δ) .PSp 4 2 1)

@[expose] def MonsterExistenceStatement (G : Type) [Group G] : Prop :=
  (Finite G ∧ IsSimpleGroup G ∧ (∃ x y : G, x * y ≠ y * x) ∧ Nat.card G = CFSG.Open.monsterOrder) ∧
  ∃ a z : G, orderOf a = 2 ∧ orderOf z = 2 ∧ ¬ IsConj a z ∧
    (∀ t : G, orderOf t = 2 → IsConj a t ∨ IsConj z t) ∧
    (∀ α, IsConj a α → IsTwoACentralizer α) ∧
    (∀ ζ, IsConj z ζ → IsTwoBCentralizer ζ) ∧
    IsTwoAGraphData a z

end CFSG.Monster.Existence
