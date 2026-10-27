module

public import CFSG.Monster.Existence.TwoPoint.LongTriangle
public import CFSG.Monster.Existence.BabyOrder
public import CFSG.Monster.Existence.Compat.Remaining
public import CFSG.Monster.Existence.TwoPoint.HNTwoB
public import CFSG.Monster.Existence.TwoPoint.EvenShapes
public import CFSG.Monster.Existence.TwoPoint.OddAssembly

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

theorem natCard_cent_tGriess_of
    (hA : IsTwoACentralizer tGriess) :
    Nat.card ↥(Subgroup.centralizer ({tGriess} : Set MGriess)) = twoBabyOrder := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := hA
  have hc : Nat.card ↥((Subgroup.center ↥(cent tGriess)).map (cent tGriess).subtype) =
      Nat.card ↥(Subgroup.center ↥(cent tGriess)) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  rw [hZ, Nat.card_zpowers, orderOf_tGriess] at hc
  have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(cent tGriess))
  rw [Nat.card_congr e.toEquiv, card_nativeB, ← hc] at this
  rw [show Subgroup.centralizer ({tGriess} : Set MGriess) = cent tGriess from rfl, this]
  norm_num [CFSG.Open.monsterBabyOrder, twoBabyOrder]

theorem isTwoAGraphData_MGriess_of
    (I : GMSInterfaces (phiB uBar) MGriess)
    (hex : OddExhaustive tGriess xGriess) (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
    (hA : IsTwoACentralizer tGriess)
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
    IsTwoAGraphData tGriess xGriess := by
  have hCa := natCard_cent_tGriess_of hA
  obtain ⟨y, hy, hs3, hs4, hs7, h3A, h3C⟩ :=
    oddShapes_MGriess I hex hcard hCa hTh CFSG.Monster.Existence.Compat.card_nativeTh
      exists_hn_two_point'
  have hsep := oddTypesSeparated_MGriess I (hy 0).1 (hy 0).2 (hy 1).1 (hy 1).2 h3A h3C
  obtain ⟨y4A, hy4A, hs5⟩ := exists_four_A_rep
  obtain ⟨y4B, hy4B, hs6⟩ := h6
  obtain ⟨y6A, hy6A, hs8⟩ := exists_six_A_rep I
  set b : Fin 9 → MGriess := ![tGriess, uGriess, tGriess * xGriess, y4A, y4B, y6A, y 0, y 1, y 2]
    with hbdef
  have hb : ∀ j, nineClass tGriess xGriess j (b j) := by
    intro j
    fin_cases j
    · exact nineClass_zero.2 rfl
    · exact (nineClass_even 0).2 uGriess_mem_twoANbr
    · exact (nineClass_even 1).2 tGriess_mul_xGriess_mem_twoBNbr
    · exact (nineClass_even 2).2 hy4A
    · exact (nineClass_even 3).2 hy4B
    · exact (nineClass_even 4).2 hy6A
    · exact (nineClass_odd 0).2 (hy 0)
    · exact (nineClass_odd 1).2 (hy 1)
    · exact (nineClass_odd 2).2 (hy 2)
  have hshape : ∀ i, TwoPointShape (cent2 tGriess (b (classIndex i))) i := by
    intro i
    fin_cases i
    · exact twoPointShape_zero_of_isTwoACentralizer orderOf_tGriess hA
    · exact h1
    · exact twoPointShape_tGriess_mul_xGriess
    · exact hs3
    · exact hs4
    · exact hs5
    · exact hs6
    · exact hs7
    · exact hs8
  have hc3 : ∀ x : MGriess, IsConj x (tGriess * b (classIndex 3)) ↔ IsConj x threeARep :=
    fun x => ⟨fun h => h.trans h3A, fun h => h.trans h3A.symm⟩
  refine isTwoAGraphData_of_tables I gmsF1Type_MGriess_uncond hex hsep b hb hshape ?_ ?_
    (four_c_MGriess I) ?_
  · intro α β hα hβ hαβ
    simp only [hc3] at hαβ ⊢
    exact hiii α β hα hβ hαβ
  · intro α β hα hβ hαβ
    rw [hc3] at hαβ
    exact hv α β hα hβ hαβ
  · intro α β hα hβ hαβ
    simp only [hc3]
    exact h4d α β hα hβ hαβ

end CFSG.Monster.Existence
