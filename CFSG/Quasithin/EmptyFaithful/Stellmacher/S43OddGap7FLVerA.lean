module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7FLData
public import CFSG.Quasithin.EmptyFaithful.SzF53MTab

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F53Mod Equiv

namespace F53.Stellmacher.S43

namespace Odd

namespace Gap7

namespace FL

theorem enc_mul : ∀ a b : orth.W, enc (a * b) = enc a ^^^ enc b := by decide +kernel

theorem enc_one : enc 1 = 0 := by decide +kernel

theorem enc_inj : ∀ a b : orth.W, enc a = enc b → a = b := by decide +kernel

private theorem mem_Y0_fin : ∀ w : orth.W,
    w ∈ spanF (commGensF orth S5SylF (spanF (commGensF orth S5SylF Finset.univ))) ↔
      pY (enc w) = 0 := by
  decide +kernel

theorem mem_Y0_iff (w : orth.W) :
    w ∈ commW orth S5Syl (commW orth S5Syl ⊤) ↔ pY (enc w) = 0 := by
  have hTop : ∀ u : orth.W, u ∈ (⊤ : Subgroup orth.W) ↔ u ∈ (Finset.univ : Finset orth.W) := by
    intro u; simp
  have hC : ∀ u, u ∈ commW orth S5Syl ⊤ ↔ u ∈ spanF (commGensF orth S5SylF Finset.univ) :=
    fun u => mem_commW_iff orth mem_S5Syl_iff hTop u
  rw [mem_commW_iff orth mem_S5Syl_iff hC w]
  exact mem_Y0_fin w

theorem decomp : ∀ s : Perm (Fin 5), (ptOrb s = 7 ∧ s ∈ S5SylF) ∨
    (ptOrb s < 7 ∧ (tHat (ptD s % 4) * orbRepE s)⁻¹ * s ∈ S5ThatF) := by
  decide +kernel

theorem stab_eq : ∀ e ∈ stabL,
    tHat e.2.1 * stabRep e * tHat e.2.2.1 = orbRep e.1 ∧ e.2.1 < 4 ∧ e.2.2.1 < 4 := by
  decide +kernel

theorem tHat_mem : ∀ i < 4, tHat i ∈ S5ThatF := by decide +kernel

theorem prmOrb_lt : ∀ l < 18, prmOrb l < 7 := by decide +kernel

theorem fix_eq : ∀ k < 7, ∀ w : orth.W, (∀ e ∈ stabL, e.1 = k → orth.act (stabElt e) w = w) →
    w = prodSel ((List.range 18).map fun l => coord l w)
      ((List.range 18).map fun l => if prmOrb l = k then prmVec l else 1) := by
  decide +kernel

theorem colsN_nb : ∀ i < 30, ∀ x ∈ colsN, nb x i = 0 := by decide +kernel

end FL

end Gap7

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
