module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Setup
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.LocalAnalysis.LargeEvenClassification.ClassTwoPowerStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement

variable {p : ℕ} {G : Type} [Group G] [Finite G] {D : Subgroup G}

theorem uc45_normal_abelian_le_center (h : Base45 p G D) (Y : Subgroup G) [Y.Normal]
    (hY2 : IsPGroup 2 Y) (hYab : IsMulCommutative ↥Y) : Y ≤ Subgroup.center G := by
  have hBbot : ⁅Y, D⁆ = ⊥ := by
    by_contra hBne
    let B : Subgroup G := ⁅Y, D⁆
    have hBleY : B ≤ Y := Subgroup.commutator_le_left (H₁ := Y) (H₂ := D)
    have hB2 : IsPGroup 2 B := hY2.to_le hBleY
    have hBab : IsMulCommutative ↥B := by
      rw [← Subgroup.le_centralizer_iff_isMulCommutative]
      intro b₁ hb₁ b₂ hb₂
      have hYle : Y ≤ Subgroup.centralizer (Y : Set G) :=
        Subgroup.le_centralizer_iff_isMulCommutative.mpr hYab
      exact Subgroup.mem_centralizer_iff.mp (hYle (hBleY hb₁)) b₂ (hBleY hb₂)
    have hDnormB : D ≤ Subgroup.normalizer (B : Set G) :=
      Subgroup.normalizer_commutator_ge_right Y D
    have hCop : Nat.Coprime (Nat.card D) (Nat.card Y) := by
      obtain ⟨k, hk⟩ := hY2.exists_card_eq
      rw [h.card_three, hk]
      exact (by decide : Nat.Coprime 3 2).pow_right k
    have hIdem : ⁅B, D⁆ = B :=
      CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime Y D hCop
        Subgroup.le_normalizer_of_normal
    have hDB : ⁅D, B⁆ = B := (Subgroup.commutator_comm D B).trans hIdem
    exact h.noAbel2 B hB2 (show B ≠ ⊥ from hBne) hBab hDnormB hDB
  have hDcentral : D ≤ Subgroup.centralizer (Y : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBbot)
  have htop : (⊤ : Subgroup G) ≤ Subgroup.centralizer (Y : Set G) := by
    rw [← h.gen]
    exact Subgroup.normalClosure_le_normal hDcentral
  exact Subgroup.centralizer_eq_top_iff_subset.mp (top_le_iff.mp htop)

theorem uc45_char_abelian_le_center (h : Base45 p G D) (A : Subgroup ↥(Xof G))
    [A.Characteristic] (hA : IsMulCommutative ↥A) :
    A.map (Xof G).subtype ≤ Subgroup.center G := by
  let Y : Subgroup G := A.map (Xof G).subtype
  haveI hYnormal : Y.Normal := ConjAct.normal_of_characteristic_of_normal
  have hY2 : IsPGroup 2 Y :=
    ((xof_isPGroup (G := G)).to_subgroup A).map (Xof G).subtype
  have hYab : IsMulCommutative ↥Y :=
    (A.equivMapOfInjective (Xof G).subtype Subtype.coe_injective).surjective.isMulCommutative hA
  exact uc45_normal_abelian_le_center h Y hY2 hYab

theorem uc45_ZX_le (h : Base45 p G D) : ZXof G ≤ Subgroup.center G :=
  uc45_char_abelian_le_center h (Subgroup.center ↥(Xof G)) inferInstance

theorem uc45_class_two (h : Base45 p G D) :
    commutator ↥(Xof G) ≤ Subgroup.center ↥(Xof G) ∧
      ∀ x : ↥(Xof G), x ^ 2 ∈ Subgroup.center ↥(Xof G) := by
  have hX2 : IsPGroup 2 ↥(Xof G) := xof_isPGroup (G := G)
  haveI : Group.IsNilpotent ↥(Xof G) := hX2.isNilpotent
  have hchar : ∀ A : Subgroup ↥(Xof G), A.Characteristic → IsMulCommutative ↥A →
      A ≤ Subgroup.center ↥(Xof G) := by
    intro A hAchar hAab a ha
    haveI : A.Characteristic := hAchar
    have hcenter : A.map (Xof G).subtype ≤ Subgroup.center G :=
      uc45_char_abelian_le_center h A hAab
    have hamem : (a : G) ∈ A.map (Xof G).subtype := ⟨a, ha, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hcenter hamem) (b : G))
  have hnclass : Group.nilpotencyClass ↥(Xof G) ≤ 2 :=
    CFSG.LargeEvenClassification.Helpers.characteristic_abelian_central_nilpotency_class_two hchar
  have hcentral : commutator ↥(Xof G) ≤ Subgroup.center ↥(Xof G) :=
    CFSG.LargeEvenClassification.Helpers.class_two_commutator_central hnclass
  obtain ⟨_, _, hsquares⟩ :=
    CFSG.LargeEvenClassification.Helpers.two_group_class_two_characteristic_abelian_central_squares
      hX2 hcentral hchar
  exact ⟨hcentral, hsquares⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
