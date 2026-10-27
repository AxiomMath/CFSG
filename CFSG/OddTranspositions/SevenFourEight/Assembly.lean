module

public import CFSG.OddTranspositions.SevenFourEight.WidthGtOne
public import CFSG.OddTranspositions.SevenFourEight.OddCoreThreeTransp
public import CFSG.OddTranspositions.SevenFourEight.OddCoreCentral
public import CFSG.OddTranspositions.SevenFourEight.PCoreNotCentral
public import CFSG.OddTranspositions.SevenFourEight.SevenFive
public import CFSG.OddTranspositions.SevenFourEight.SevenSix
public import CFSG.OddTranspositions.SevenFourEight.CenterHalpha
public import CFSG.OddTranspositions.SevenFourEight.SevenEight
import CFSG.OddTranspositions.SevenThreeConclusion

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 CFSG.Timmesfeld.Connectivity
open CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem aalphaStar_nonempty (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) :
    (AalphaStar D hC.alpha).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  obtain ⟨w, hw, -⟩ := sevenThree hC hrad (localSecond_of_forall_secondKind hsecond)
    (fun w hw => by rw [h] at hw; exact absurd hw (Set.notMem_empty w)) hnot3
  rw [h] at hw
  exact Set.notMem_empty w hw

theorem oddCore_le_center_Halpha
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hmin : SmallerTwoStar (Nat.card G)) :
    CFSG.oddCore ↥(Halpha D hC.alpha) ≤ Subgroup.center ↥(Halpha D hC.alpha) :=
  oddCore_le_center_Halpha_of_widthTwo hC hrad hsecond hnot3
    (exists_commute_DalphaStar hC hrad hsecond hnot3 hmin)
    (threeTransp_DstarH_oddCore hC hrad hsecond hnot3 hmin)

theorem pCore_two_not_le_center_Halpha
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hmin : SmallerTwoStar (Nat.card G)) :
    ¬ CFSG.pCore 2 ↥(Halpha D hC.alpha) ≤ Subgroup.center ↥(Halpha D hC.alpha) :=
  pCore_two_not_le_center_Halpha_of_oddCore_le hC hrad hsecond hnot3
    (oddCore_le_center_Halpha hC hrad hsecond hnot3 hmin)
    (threeTransp_imageClass hC hrad hsecond hnot3 hmin)

theorem sevenFive
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hmin : SmallerTwoStar (Nat.card G)) :
    hC.alpha = {hC.d} ∧
      (∃ p : ℕ, p.Prime ∧ p ≠ 3 ∧ ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → orderOf (x * y) = p) ∧
      Group.IsSolvable ↥(Halpha D hC.alpha) ∧
      ¬ 2 ∣ (CFSG.pCore 2 ↥(commutator ↥(Halpha D hC.alpha))).index :=
  sevenFive_of_pCore_not_le hC hrad hsecond hnot3
    (threeTransp_imageClass hC hrad hsecond hnot3 hmin)
    (pCore_two_not_le_center_Halpha hC hrad hsecond hnot3 hmin)

theorem sevenSix
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hmin : SmallerTwoStar (Nat.card G))
    {p : ℕ} (hp : ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → orderOf (x * y) = p) :
    ∃ m : ℕ, 2 ≤ m ∧
      (∀ v ∈ commSet D hC.d,
        {y | ∃ q ∈ (CFSG.pCore 2 ↥(Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype, q * v * q⁻¹ = y}.ncard = m ∧
          (commSet D hC.d ∩ commSet D v).ncard = m - 1) ∧
      (commSet D hC.d).ncard = p * m ∧
      {y | y ∈ D ∧ ¬ Commute y hC.d}.ncard = m ^ 2 * (p - 1) ∧
      (∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).ncard = p) ∧
      Nat.card ↥(Halpha D hC.alpha) = 2 * p * m ^ 2 * Nat.card (Subgroup.center ↥(Halpha D hC.alpha)) := by
  obtain ⟨hα, ⟨p', hp'p, hp'3, hp'⟩, -, hH'⟩ := sevenFive hC hrad hsecond hnot3 hmin
  have hpe : p = p' := by
    obtain ⟨w, hw⟩ := aalphaStar_nonempty hC hrad hsecond hnot3
    obtain ⟨hwD, hwu, -⟩ := mem_Gamma_iff.mp (show w ∈ Gamma hC from hw)
    rw [← hp _ hC.hd _ hwD (fun h => hwu h.symm), hp' _ hC.hd _ hwD (fun h => hwu h.symm)]
  subst hpe
  exact sevenSix_of_sevenFive hC hsecond hα hp'p hp'3 hp hH'
    (pCore_two_not_le_center_Halpha hC hrad hsecond hnot3 hmin)

theorem center_Halpha_le
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hmin : SmallerTwoStar (Nat.card G)) :
    ∀ z ∈ Subgroup.center ↥(Halpha D hC.alpha), (z : G) = 1 ∨ (z : G) = hC.d := by
  obtain ⟨hα, ⟨p, hpp, hp3, hp⟩, -, hH'⟩ := sevenFive hC hrad hsecond hnot3 hmin
  have hQ := pCore_two_not_le_center_Halpha hC hrad hsecond hnot3 hmin
  obtain ⟨m, -, -, -, -, hμ, -⟩ := sevenSix_of_sevenFive hC hsecond hα hpp hp3 hp hH' hQ
  exact center_Halpha_le_of_sevenSix hC hrad hsecond hα hpp hp hμ
    (not_commute_of_mem_commSet_inter hC hα hH')
    (mul_self_eq_one_of_mem_center_Halpha hC hsecond hα hpp hp3 hp hH' hQ)

theorem sevenEight
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hmin : SmallerTwoStar (Nat.card G))
    {p : ℕ} (hp : ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → orderOf (x * y) = p) : p = 3 := by
  obtain ⟨hα, -, -, -⟩ := sevenFive hC hrad hsecond hnot3 hmin
  obtain ⟨m, -, -, -, hl, hμ, hH⟩ := sevenSix hC hrad hsecond hnot3 hmin hp
  exact sevenEight_of_sevenSix hC hsecond hp hα (aalphaStar_nonempty hC hrad hsecond hnot3)
    hl hμ hH (center_Halpha_le hC hrad hsecond hnot3 hmin)

theorem false_of_sevenSetting
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hmin : SmallerTwoStar (Nat.card G)) : False := by
  obtain ⟨-, ⟨p, -, hp3, hp⟩, -, -⟩ := sevenFive hC hrad hsecond hnot3 hmin
  exact hp3 (sevenEight hC hrad hsecond hnot3 hmin hp)

end CFSG.OddTranspositions

end
