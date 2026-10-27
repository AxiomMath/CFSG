module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LeviInvCentral

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {Λ : Type} [Group Λ]

theorem mem_centralizer_iSup {ι : Type*} {X : ι → Subgroup Λ} {y : Λ}
    (h : ∀ i, ∀ x ∈ X i, Commute y x) :
    y ∈ Subgroup.centralizer ((⨆ i, X i : Subgroup Λ) : Set Λ) := by
  have hle : (⨆ i, X i) ≤ Subgroup.centralizer ({y} : Set Λ) :=
    iSup_le fun i x hx => Subgroup.mem_centralizer_singleton_iff.mpr (h i x hx).symm
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem le_centralizer_iSup {ι : Type*} {X : ι → Subgroup Λ} {Y : Subgroup Λ}
    (h : ∀ i, ⁅Y, X i⁆ = ⊥) : Y ≤ Subgroup.centralizer ((⨆ i, X i : Subgroup Λ) : Set Λ) :=
  fun _ hy => mem_centralizer_iSup fun i x hx =>
    Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp (h i) hy) x hx |>.symm

theorem commutator_ne_bot_of_opp [Finite Λ]
    (hO2 : ∀ R : Subgroup Λ, R.Normal → IsPGroup 2 R → R = ⊥) {L : Subgroup Λ} [L.Normal]
    (hL : Opp 2 L = L) (hL0 : L ≠ ⊥) : ⁅L, L⁆ ≠ ⊥ := fun h =>
  hL0 (hO2 L inferInstance (isPGroup_of_opp_eq_of_commutator_eq_bot hL h))

theorem eq_bot_of_le_centralizer [Finite Λ]
    (hO2 : ∀ R : Subgroup Λ, R.Normal → IsPGroup 2 R → R = ⊥) {X N : Subgroup Λ} [N.Normal]
    (hX : Opp 2 X = X) (hXN : X ≤ N) (hXC : X ≤ Subgroup.centralizer (N : Set Λ)) :
    X = ⊥ := by
  rw [← hX, eq_bot_iff]
  exact opp_le_of_forall fun x hx h2 =>
    (Subgroup.mem_bot).mpr (eq_one_of_isTwoElt_of_mem_center hO2 (hXN hx) (hXC hx) h2)

theorem le_of_le_sup_of_commute [Finite Λ]
    (hO2 : ∀ R : Subgroup Λ, R.Normal → IsPGroup 2 R → R = ⊥) {S T X : Subgroup Λ}
    [S.Normal] [T.Normal] (hST : ⁅S, T⁆ = ⊥) (hX : Opp 2 X = X) (hXN : X ≤ S ⊔ T)
    (hXT : ⁅X, T⁆ = ⊥) : X ≤ S := by
  have : (S ⊔ T).Normal := Subgroup.sup_normal S T
  rw [← hX]
  refine opp_le_of_forall fun x hx h2 => ?_
  have hxT : ∀ t ∈ T, Commute x t := fun t ht =>
    (Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hXT hx) t ht).symm
  obtain ⟨s, hs, z, hzN, hzC, hsz, rfl⟩ := exists_mul_central hST (hXN hx) hxT
  exact mem_of_isTwoElt_mul hs hsz (odd_orderOf_of_mem_center hO2 hzN hzC) h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq

end
