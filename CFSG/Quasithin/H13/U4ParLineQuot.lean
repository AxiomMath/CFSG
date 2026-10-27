module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qBlock
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316B

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem isPSL_modO2_perfectCore_parP2 :
    CFSG.Quasithin.IsPSL 2 2 (2 * m) (CFSG.Quasithin.ModO2 (perfectCore (parP2 h))) := by
  obtain ⟨F, hFld, hFintype, hFcard, α, hα, hαker, -⟩ :=
    CFSG.Quasithin.F112R.isOmega4MinusType_perfectCore_parP2 h
  letI := hFld
  letI := hFintype
  have hFchar : CharP F 2 := charP_of_card_eq_prime_pow (by simpa using hFcard)
  letI := hFchar
  have hFnat : Nat.card F = 2 ^ (2 * m) := by rw [Nat.card_eq_fintype_card, hFcard]
  let e : CFSG.Quasithin.ModO2 (perfectCore (parP2 h)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hαker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  have hn : 2 ≤ 2 * m := by have := h.one_le; omega
  exact CFSG.Quasithin.H13.L3316.isPSL2_of_equiv_sl2 hn hFnat e

theorem isSimpleGroup_modO2_perfectCore_parP2 :
    IsSimpleGroup (CFSG.Quasithin.ModO2 (perfectCore (parP2 h))) :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 (2 * m)
    (isPSL_modO2_perfectCore_parP2 h)).2

end CFSG.Quasithin.H13.U4Par

end
