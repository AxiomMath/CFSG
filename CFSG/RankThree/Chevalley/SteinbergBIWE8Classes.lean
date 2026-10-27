
module

public import CFSG.RankThree.Chevalley.SteinbergBIWE8ClassesBase

public import CFSG.RankThree.Chevalley.SteinbergBIWE8Certs

public noncomputable section

namespace CFSG.RankThree.Chevalley.WeylE8

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.WE8.Native

theorem isConj_y0_of_sq {y : W8} (hy : y * y = z) : IsConj y0 y := by
  classical
  let _ : Fintype W8 := Fintype.ofFinite W8
  let C : Finset W8 := Finset.univ.filter (IsConj y0)
  let Y : Finset W8 := Finset.univ.filter fun w => w * w = z
  have hC : C.card = 15120 := by
    rw [← card_isConj_y0, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : C ⊆ Y := by
    intro w hw
    obtain ⟨u, rfl⟩ := isConj_iff.1 (Finset.mem_filter.1 hw).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, conj_y0_sq u⟩
  have hY : Y.card ≤ 15120 := by
    have hle : Nat.card {w : W8 // w * w = z} ≤ Nat.card {w : W8 // SgnSym (-1) w} :=
      Nat.card_le_card_of_injective (fun w => ⟨w.1, skew_of_sq_eq_neg (sq_eq_z_smul w.2)⟩)
        fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hle
    exact hle.trans card_skew_le
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hC]; exact hY)
  have hyY : y ∈ Y := Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩
  rw [← heq] at hyY
  exact (Finset.mem_filter.1 hyY).2

end CFSG.RankThree.Chevalley.WeylE8
