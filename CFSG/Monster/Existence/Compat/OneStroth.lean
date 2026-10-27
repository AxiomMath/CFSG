module

public import CFSG.Monster.Existence.Compat.Centralizers
public import CFSG.Sporadic.B
public import CFSG.Monster.Existence.AssemblyHS
public import CFSG.Monster.Existence.BabyOrder

public section

namespace CFSG.Monster.Existence.Compat

open CFSG CFSG.Open CFSG.Blueprint CFSG.Monster.Griess

theorem compat_one_of_stroth
    (hStroth : ∀ d₀ : Blueprint.NativeSporadic.B, orderOf d₀ = 2 →
      Matrix.rank (d₀.val.val - 1) = 1860 →
      ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (d : G), orderOf d = 2 →
        Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
          Subgroup.centralizer ({d₀} : Set Blueprint.NativeSporadic.B)) →
        Nonempty (G ≃* Blueprint.NativeSporadic.B)) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G), IsSimpleGroup G ∧ Nat.card G = monsterOrder ∧
      ∃ a z : G, MonsterIsF1Type a z ∧ ¬ IsConj a z ∧
        ∀ t : G, orderOf t = 2 → IsConj a t ∨ IsConj z t := by
  obtain ⟨⟨hfin, hsimple, -, hcard⟩, ha, hz, hnc, hinv, hA, hB'⟩ :=
    monster_existence_clauses_one_two_of_stroth hStroth
  exact ⟨MGriess, inferInstance, hfin, hsimple, hcard, tGriess, xGriess,
    isF1Type_of_canonical ha hz (hA _ (IsConj.refl _)) (hB' _ (IsConj.refl _))
      CFSG.Sporadic.B.fam_b_simplicity card_nativeB, hnc, hinv⟩

end CFSG.Monster.Existence.Compat
