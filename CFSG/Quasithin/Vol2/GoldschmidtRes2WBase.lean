module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2Pair
public import CFSG.Quasithin.Vol2.Ch3E213MFam
public import CFSG.Quasithin.Vol2.Ch3E215MA

public section

namespace CFSG.Quasithin.Res2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B6 B2F

@[expose] def E215DataW {G : Type} [Group G] (X M V : Subgroup G) (g : G) : Prop :=
  (kerIn M X ⊓ V).relIndex V < (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) ∨
    ⁅kerIn M X ⊓ V, conjSub g (kerIn M X ⊓ V)⁆ = ⊥

@[expose] def E215ConclW {G : Type} [Group G] (H T M V : Subgroup G) : Prop :=
  (∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A →
    (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤ 4) →
    ∃ g ∈ H, E2.Pair (Ch3n.pairI V g) (T ⊓ Ch3n.pairI V g) (M ⊓ Ch3n.pairI V g) V g ∧
      CharTwo (Ch3n.pairI V g) ∧ Ch3n.pairI V g ≠ V ∧
      (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g) ⊓ V).relIndex V ≤
        (V ⊓ conjSub g V).relIndex (kerIn (M ⊓ Ch3n.pairI V g) (Ch3n.pairI V g) ⊓ V) ∧
      E215DataW (Ch3n.pairI V g) (M ⊓ Ch3n.pairI V g) V g

variable {G : Type} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

theorem count_lt_of_e215DataW (h : E2.Pair X T M V g) (hchar : CharTwo X) (hXV : X ≠ V)
    (hrank : (kerIn M X ⊓ V).relIndex V ≤ (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V))
    (hdata : E215DataW X M V g) :
    (V ⊓ Subgroup.centralizer ((conjSub g (kerIn M X ⊓ V) : Subgroup G) : Set G)).relIndex V <
      ((conjSub g (kerIn M X ⊓ V) ⊓ Subgroup.centralizer (V : Set G)).relIndex
        (conjSub g (kerIn M X ⊓ V))) ^ 2 := by
  rcases hdata with hlt | hBA
  · exact Ch3E215M.count_lt_of_lt h hchar hXV hlt
  · exact Ch3E215M.count_lt_of_commute h hchar hXV hrank hBA

theorem relIndex_le_four {T₁ : Subgroup G} (h : E2.Pair X T₁ M V g) (hchar : CharTwo X)
    (hXV : X ≠ V) (hT : T₁ ≤ T)
    (hb : ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A →
      (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤ 4) :
    (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) ≤ 4 := by
  obtain ⟨hAT, -, hAel, -⟩ := Ch3n.exists_cubic_of_pair h hchar hXV
  rw [← Ch3E215M.relIndex_A_eq h hchar hXV]
  exact hb _ (hAT.trans hT) hAel

theorem e215DataW_of_dihedral (h : E2.Pair X T M V g) (hchar : CharTwo X) (hXV : X ≠ V)
    {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hcard : (kerIn M X).relIndex X = 2 * ℓ ^ e) :
    E215DataW X M V g := by
  have hV2 : (kerIn M X ⊓ V).relIndex V ≤ 2 := by
    have h1 := Ch3E213M.relIndex_le_two_pow h (n := 1) (hℓ.odd_of_ne_two hℓ2).pow
      (by rw [hcard, pow_one])
    rwa [pow_one] at h1
  rcases (Ch3E215M.two_le_relIndex h hchar hXV).lt_or_eq with hlt | heq
  · exact Or.inl (hV2.trans_lt hlt)
  · exact Or.inr (commutator_eq_bot_of_relIndex_two h heq.symm)

end CFSG.Quasithin.Res2
