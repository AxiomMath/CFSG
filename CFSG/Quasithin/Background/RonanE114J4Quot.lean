module

public import CFSG.Quasithin.Background.RonanE114D4Quot

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Quasithin CFSG.Quasithin.E1

theorem nParam_top_le_of_solvable_quotient {i : ℕ} (hi : 1 ≤ i) {Q : Type} [Group Q] [Finite Q]
    (R : Subgroup Q) [R.Normal] (hR : Group.IsSolvable ↥R)
    (h : nParam (⊤ : Subgroup (Q ⧸ R)) ≤ (i : ℕ∞)) : nParam (⊤ : Subgroup Q) ≤ (i : ℕ∞) :=
  (nParam_le_iff (by omega)).mpr
    (inE_of_solvable_quotient hi (Nat.card Q) Q le_rfl R hR ((nParam_le_iff (by omega)).mp h))

theorem nParam_top_le_of_equiv_quotient {i : ℕ} (hi : 1 ≤ i) {Q Q' : Type} [Group Q] [Finite Q]
    [Group Q'] [Finite Q'] (R : Subgroup Q) [R.Normal] (hR : Group.IsSolvable ↥R)
    (e : (Q ⧸ R) ≃* Q') (h : nParam (⊤ : Subgroup Q') ≤ (i : ℕ∞)) :
    nParam (⊤ : Subgroup Q) ≤ (i : ℕ∞) :=
  nParam_top_le_of_solvable_quotient hi R hR (by rwa [E1.Eleven.nParam_top_mulEquiv e])

theorem nParam_le_of_equiv_quotient {i : ℕ} (hi : 1 ≤ i) {G Q' : Type} [Group G] [Finite G]
    (D : Subgroup G) [Group Q'] [Finite Q'] (R : Subgroup ↥D) [R.Normal]
    (hR : Group.IsSolvable ↥R) (e : (↥D ⧸ R) ≃* Q') (h : nParam (⊤ : Subgroup Q') ≤ (i : ℕ∞)) :
    nParam D ≤ (i : ℕ∞) := by
  rw [E1.nParam_subgroupOf]
  exact nParam_top_le_of_equiv_quotient hi R hR e h

end CFSG.Quasithin.RonanE114
