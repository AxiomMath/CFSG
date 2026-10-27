module

public import CFSG.Quasithin.Background.C124YLL2Odd

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Matrix
open scoped MatrixGroups

namespace L2Ctx

variable {W : Type*} [CommGroup W] [Finite W] {F : Type} [Field F] [Finite F]
  {Xs Ls : Subgroup (MulAut W)} {U Z : Subgroup W} (C : L2Ctx F Xs Ls U Z)

include C in
theorem card_le_two_mul {B : Subgroup (MulAut W)} (hBX : B ≤ Xs) (hab : IsElemAbelian2 B)
    {t : MulAut W} (htB : t ∈ B) (htL : t ∉ Ls) :
    Nat.card B ≤ 2 * Nat.card ↥(B ⊓ Ls) := by
  set B0 : Subgroup ↥B := (B ⊓ Ls).subgroupOf B with hB0
  have h1 := Subgroup.card_mul_index B0
  have h2 : Nat.card B0 = Nat.card ↥(B ⊓ Ls) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hidx : B0.index ≤ 2 := by
    let t' : ↥B := ⟨t, htB⟩
    have hsurj : Function.Surjective (fun b : Bool => (QuotientGroup.mk (if b then t' else 1) :
        ↥B ⧸ B0)) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H b =>
        by_cases hb : (b : MulAut W) ∈ Ls
        · refine ⟨false, ?_⟩
          simp only [Bool.false_eq_true, ite_false]
          rw [QuotientGroup.eq]
          exact (Subgroup.mem_subgroupOf).2 ⟨by simp, by simpa using hb⟩
        · refine ⟨true, ?_⟩
          simp only [ite_true]
          rw [QuotientGroup.eq]
          refine (Subgroup.mem_subgroupOf).2 ⟨B.mul_mem (B.inv_mem htB) b.2, ?_⟩
          have ht2 : t ^ 2 = 1 := hab.2 t htB
          have htinv : t⁻¹ = t := by
            have : t * t = 1 := by simpa [pow_two] using ht2
            exact inv_eq_of_mul_eq_one_right this
          let tX : ↥Xs := ⟨t, hBX htB⟩
          let bX : ↥Xs := ⟨b, hBX b.2⟩
          have hb2 : (b : MulAut W) ^ 2 = 1 := hab.2 b b.2
          have hmul := C.odd_mul_mem (x := tX) (y := bX)
            (Subtype.ext (by simpa using ht2)) (Subtype.ext (by simpa using hb2))
            (Subtype.ext (by simpa using hab.2 (t * b) (B.mul_mem htB b.2))) htL hb
          have e : ((t'⁻¹ * b : ↥B) : MulAut W) = t * b := by
            simp [t', htinv]
          show ((t'⁻¹ * b : ↥B) : MulAut W) ∈ Ls
          rw [e]
          exact hmul
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    exact this
  rw [h2] at h1
  rw [← h1]
  exact Nat.mul_le_mul_left _ hidx |>.trans (by omega)

end L2Ctx

end CFSG.Quasithin.C124.YL
