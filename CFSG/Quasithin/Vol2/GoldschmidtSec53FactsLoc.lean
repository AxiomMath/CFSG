module

import CFSG.Quasithin.Vol2.Ch5Sec1Basic
public import CFSG.Quasithin.Vol2.Ch5Sec3Statements

public section

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F1

section Defs

variable {G : Type} [Group G]

abbrev fG1 (M L H B : Subgroup G) : Subgroup G := L ⊔ (sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H)

abbrev fG2 (M L H D : Subgroup G) : Subgroup G := D ⊔ (sec52S M H ⊓ L) ⊔ oTwoUpper H

end Defs

variable {G : Type} [Group G] [Finite G] {T M L V H B D L₂ : Subgroup G} {n : ℕ}

theorem fG1_eq (h527 : Stmt5_2_7) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    fG1 M L H B = L ⊔ (B ⊔ D) := by
  obtain ⟨-, ⟨e1, -⟩, -⟩ := h527 G T M L V H B D L₂ n hyp
  rw [fG1, e1, sup_assoc]

theorem fG2_eq (h527 : Stmt5_2_7) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    fG2 M L H D = oTwoUpper H ⊔ (B ⊔ D) := by
  obtain ⟨-, ⟨-, e2, -⟩, -⟩ := h527 G T M L V H B D L₂ n hyp
  rw [fG2, e2, sup_assoc]

theorem fG12_eq (h527 : Stmt5_2_7) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    fG1 M L H B ⊓ fG2 M L H D = sec53S T L ⊔ (B ⊔ D) := by
  obtain ⟨-, ⟨e1, e2, e3, hST, -⟩, -⟩ := h527 G T M L V H B D L₂ n hyp
  rw [fG1, fG2, e1, e2, e3, hST, sup_assoc]

theorem pCoreOf_fG12 (h527 : Stmt5_2_7) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    pCoreOf 2 (fG1 M L H B ⊓ fG2 M L H D) = sec53S T L := by
  obtain ⟨-, ⟨e1, e2, -, hST, -, hO2⟩, -⟩ := h527 G T M L V H B D L₂ n hyp
  rw [fG1, fG2, e1, e2, ← hO2, hST]

theorem sec53S_le_fG12 (h527 : Stmt5_2_7) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    sec53S T L ≤ fG1 M L H B ⊓ fG2 M L H D := by
  rw [← pCoreOf_fG12 h527 hyp]
  exact CFSG.LieType.BorelTits.pCoreOf_le 2 _

theorem D_le_L (hyp : Hyp5_2_4 G T M L V H B D L₂ n) : D ≤ L :=
  hyp.notation59.2.1.1.trans inf_le_left

theorem B_le_normalizer_L (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    B ≤ Subgroup.normalizer (L : Set G) :=
  (hyp.notation59.1.1.trans inf_le_left).trans hyp.toHyp5_1_8.toHyp5_0_1.normal

theorem BD_le_normalizer_L (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    B ⊔ D ≤ Subgroup.normalizer (L : Set G) :=
  sup_le (B_le_normalizer_L hyp) ((D_le_L hyp).trans Subgroup.le_normalizer)

theorem BD_le_normalizer_K (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    B ⊔ D ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
  sup_le (hyp.notation59.1.1.trans (inf_le_right.trans (le_normalizer_oTwoUpper H))) hyp.D_le

theorem T_le_normalizer_L (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    T ≤ Subgroup.normalizer (L : Set G) :=
  hyp.toHyp5_1_8.toHyp5_0_1.T_le.trans hyp.toHyp5_1_8.toHyp5_0_1.normal

theorem T_le_normalizer_K (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
  hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)

theorem T_le_normalizer_S (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    T ≤ Subgroup.normalizer (sec53S T L : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have htL : t ∈ Subgroup.normalizer (L : Set G) := T_le_normalizer_L hyp ht
  constructor
  · rintro ⟨hyT, hyL⟩
    exact ⟨T.mul_mem (T.mul_mem ht hyT) (T.inv_mem ht),
      (Subgroup.mem_normalizer_iff.mp htL y).mp hyL⟩
  · rintro ⟨hyT, hyL⟩
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp htL y).mpr hyL⟩
    have := T.mul_mem (T.mul_mem (T.inv_mem ht) hyT) ht
    simpa [mul_assoc] using this

theorem perfectCore_fG1 (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hsol : Group.IsSolvable ↥(fG1 M L H B ⊓ fG2 M L H D)) : perfectCore (fG1 M L H B) = L := by
  have h := hyp.toHyp5_1_8.toHyp5_0_1
  have hBM : B ≤ M := hyp.notation59.1.1.trans inf_le_left
  have hLG : L ≤ fG1 M L H B := le_sup_left.trans le_sup_left
  have hsup : fG1 M L H B = L ⊔ ((sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H)) := sup_assoc _ _ _
  have hnorm : fG1 M L H B ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer (inf_le_right.trans Subgroup.le_normalizer))
      (inf_le_left.trans (hBM.trans h.normal))
  have hAn : (L.subgroupOf (fG1 M L H B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mpr hnorm
  have hle : (sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H) ≤ fG1 M L H B ⊓ fG2 M L H D :=
    sup_le (le_inf (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_left))
      (le_inf le_sup_right (inf_le_right.trans le_sup_right))
  have hs : Group.IsSolvable ↥((sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  exact le_antisymm (perfectCore_le_of_sup_solvable hLG hAn hsup hs)
    (le_perfectCore_of_perfect hLG h.commutator_eq)

theorem perfectCore_fG2 {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m f : ℕ}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T t m f)
    (hsol : Group.IsSolvable ↥(fG1 M L H B ⊓ fG2 M L H D)) :
    perfectCore (fG2 M L H D) = oTwoUpper H := by
  have hDL : D ≤ L := D_le_L hyp
  have hKG : oTwoUpper H ≤ fG2 M L H D := le_sup_right
  have hsup : fG2 M L H D = oTwoUpper H ⊔ (D ⊔ (sec52S M H ⊓ L)) := sup_comm _ _
  have hSH : sec52S M H ≤ H :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (M ⊓ H)).trans inf_le_right
  have hnorm : fG2 M L H D ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    sup_le (sup_le hyp.D_le (inf_le_left.trans (hSH.trans (le_normalizer_oTwoUpper H))))
      Subgroup.le_normalizer
  have hAn : ((oTwoUpper H).subgroupOf (fG2 M L H D)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mpr hnorm
  have hle : D ⊔ (sec52S M H ⊓ L) ≤ fG1 M L H B ⊓ fG2 M L H D :=
    sup_le (le_inf (hDL.trans (le_sup_left.trans le_sup_left)) (le_sup_left.trans le_sup_left))
      (le_inf (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_left))
  have hs : Group.IsSolvable ↥(D ⊔ (sec52S M H ⊓ L)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  exact le_antisymm (perfectCore_le_of_sup_solvable hKG hAn hsup hs)
    (le_perfectCore_of_perfect hKG hty.2.1.2.1.2.1)

end CFSG.Quasithin.H13.Sec53F
