module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.NF314pt

open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem relIndex_sup_of_le_normalizer {A B : Subgroup G}
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) :
    B.relIndex (A ⊔ B) = (A ⊓ B).relIndex A := by
  set X := A ⊔ B with hX
  have hAX : A ≤ X := le_sup_left
  have hBX : B ≤ X := le_sup_right
  have hXA : X ≤ Subgroup.normalizer (A : Set G) := sup_le Subgroup.le_normalizer hBA
  have hAn : (A.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAX).mpr hXA
  have h1 : (A.subgroupOf X).index = A.relIndex B := by
    have := Subgroup.relIndex_sup_right (B.subgroupOf X) (A.subgroupOf X)
    rw [← Subgroup.subgroupOf_sup hBX hAX, sup_comm, ← hX, Subgroup.subgroupOf_self,
      Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hBX] at this
    exact this
  have hcardA : Nat.card (A.subgroupOf X) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv
  have hcardB : Nat.card (B.subgroupOf X) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv
  have e1 : Nat.card A * A.relIndex B = Nat.card X := by
    have := Subgroup.card_mul_index (A.subgroupOf X)
    rw [h1, hcardA] at this
    exact this
  have e2 : Nat.card B * B.relIndex X = Nat.card X := by
    have := Subgroup.card_mul_index (B.subgroupOf X)
    rw [hcardB] at this
    exact this
  have e3 : Nat.card ↥(A ⊓ B) * A.relIndex B = Nat.card B := by
    have := Subgroup.card_mul_index ((A ⊓ B).subgroupOf B)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ B ≤ B)).toEquiv] at this
    have h5 : ((A ⊓ B).subgroupOf B).index = A.relIndex B := Subgroup.inf_relIndex_right A B
    rw [h5] at this
    exact this
  have e4 : Nat.card ↥(A ⊓ B) * (A ⊓ B).relIndex A = Nat.card A := by
    have := Subgroup.card_mul_index ((A ⊓ B).subgroupOf A)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ B ≤ A)).toEquiv] at this
    exact this
  have hb : 0 < Nat.card B := Nat.card_pos
  have hci : 0 < Nat.card ↥(A ⊓ B) * A.relIndex B := by rw [e3]; exact hb
  apply Nat.eq_of_mul_eq_mul_right hci
  calc B.relIndex X * (Nat.card ↥(A ⊓ B) * A.relIndex B)
      = B.relIndex X * Nat.card B := by rw [e3]
    _ = Nat.card X := by rw [mul_comm]; exact e2
    _ = Nat.card A * A.relIndex B := e1.symm
    _ = Nat.card ↥(A ⊓ B) * (A ⊓ B).relIndex A * A.relIndex B := by rw [e4]
    _ = (A ⊓ B).relIndex A * (Nat.card ↥(A ⊓ B) * A.relIndex B) := by ring

theorem isSylowTwoOf_sup_of_normalizer {A B S : Subgroup G} (hB2 : IsPGroup 2 B)
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) (hS : IsSylowTwoOf S A) (hSB : S ≤ B) :
    IsSylowTwoOf B (A ⊔ B) := by
  refine ⟨le_sup_right, hB2, ?_⟩
  show ¬ 2 ∣ B.relIndex (A ⊔ B)
  rw [relIndex_sup_of_le_normalizer hBA]
  intro h
  apply hS.2.2
  exact h.trans (Subgroup.relIndex_dvd_of_le_left A (le_inf hS.1 hSB))

end CFSG.Quasithin.H13.NF314pt
