
module

public import CFSG.Monster.B.TwoA.Base.IncidenceBase

public import CFSG.Monster.B.TwoA.Base.Par45A

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B

theorem natCard_Echain :
    ∀ i : ℕ, 1 ≤ i → i ≤ 5 → Nat.card (Echain i) = 2 ^ i := by
  intro i h1 h5
  interval_cases i
  · exact natCard_zpowers_xhat
  · exact natCard_Vhat_pow
  · exact natCard_E3_pow
  · exact natCard_E4
  · exact natCard_E5

theorem natCard_obj
    (x : ParGeom) : Nat.card x.1.2 = 2 ^ parType x := by
  obtain ⟨h1, h5, g, -, hg⟩ := x.2
  rw [hg, natCard_conjSub]
  exact natCard_Echain _ h1 h5

theorem le_of_natCard_le_type
    {x y : ParGeom} (hle : y.1.2 ≤ x.1.2) :
    parType y ≤ parType x := by
  have h := Subgroup.card_le_of_le hle
  rw [natCard_obj, natCard_obj] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

theorem le_of_parInc
    {x y : ParGeom} (h : parInc x y) (ht : parType x ≤ parType y) :
    x.1.2 ≤ y.1.2 := by
  rcases h with rfl | ⟨hne, h | h⟩
  · exact le_rfl
  · exact h
  · have := le_of_natCard_le_type h
    exact absurd (le_antisymm ht this) hne

theorem IsParFlag.isChain
    {F : Set ParGeom} (hF : IsParFlag F) :
    ∀ x ∈ F, ∀ y ∈ F, x.1.2 ≤ y.1.2 ∨ y.1.2 ≤ x.1.2 := by
  intro x hx y hy
  rcases le_total (parType x) (parType y) with h | h
  · exact .inl (le_of_parInc (hF x hx y hy) h)
  · exact .inr (le_of_parInc (hF y hy x hx) h)

attribute [local instance] parAction

theorem short_centralizer_parabolic_incidence_data :
    Finite ParGeom ∧
    (∀ x : ParGeom, 1 ≤ parType x ∧ parType x ≤ 5 ∧ ∃ g ∈ Shat,
      x.1.2 = conjSub g (Echain (parType x))) ∧
    (∀ x : ParGeom, Nat.card x.1.2 = 2 ^ parType x) ∧
    (∀ x y : ParGeom, parType x ≠ parType y → (parInc x y ↔ x.1.2 ≤ y.1.2 ∨ y.1.2 ≤ x.1.2)) ∧
    (∀ x y : ParGeom, parInc x y → parType x = parType y → x = y) ∧
    (∀ x : ParGeom, parInc x x) ∧ (∀ x y : ParGeom, parInc x y → parInc y x) ∧
    (∀ x y : ParGeom, parInc x y → parType x ≤ parType y → x.1.2 ≤ y.1.2) ∧
    (∀ F : Set ParGeom, IsParFlag F → ∀ x ∈ F, ∀ y ∈ F, x.1.2 ≤ y.1.2 ∨ y.1.2 ≤ x.1.2) ∧
    (∀ (g : Shat) (x : ParGeom),
      (g • x : ParGeom).1 = (parType x, conjSub (g : Dfull) x.1.2)) ∧
    (∀ (g : Shat) (x y : ParGeom), parInc (g • x) (g • y) ↔ parInc x y) ∧
    IsParFlag stdParFlag ∧ parType '' stdParFlag = Set.Icc 1 5 :=
  ⟨finite_ParGeom, fun x => x.2, natCard_obj, fun _ _ h => parInc_iff_of_ne h,
    fun _ _ h ht => eq_of_parInc h ht, parInc_refl, fun _ _ h => parInc_symm h,
    fun _ _ h ht => le_of_parInc h ht, fun _ hF => hF.isChain, coe_parAction, parInc_smul_iff,
    stdParFlag_isParFlag.1, stdParFlag_isParFlag.2⟩

end CFSG.Monster.B.TwoA
