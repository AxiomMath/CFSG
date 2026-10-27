module

public import CFSG.RankThree.PartOne.FOC.PSUFamily
public import CFSG.RankThree.PartOne.FOC.PSU5Inner
public import CFSG.RankThree.PartOne.FOC.PSU5Outer

public section

namespace CFSG.RankThree.PartOne.FOC

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.Sec66T (lieModel_classical_iff psu5)

theorem psuFiveSpecial : PSUFiveSpecial := by
  intro T _ _ f hs hnab h5 hadm hmodel
  have hC : StatedClassicalModel T .PSU 5 2 f := (lieModel_classical_iff (by decide)).mp hmodel
  obtain ⟨K, _, hKf, h, hn3, hne, ⟨e⟩⟩ := exists_psu_model hC
  have : Finite (psu5 h) := Finite.of_equiv T e.toEquiv
  have : IsSimpleGroup (psu5 h) := e.symm.isSimpleGroup
  have hnab' : ∃ a b : psu5 h, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul]; exact h'))⟩
  have hin : InnerComp 5 T :=
    InnerComp.of_mulEquiv e Nat.prime_five (innerComp_psu_five (h := h) h5 hnab')
  have hout : OuterComp 5 T := OuterComp.of_mulEquiv e Nat.prime_five (outerComp_psu_five h h5)
  exact fieldInnerT_of_comp (center_eq_bot_of_nonab hs hnab) hin hout

theorem fieldInnerLie_PSU_final (hdefI : DefInnerComponent) (hdefO : DefOuterComponent) (ℓ : ℕ) :
    FieldInnerLie .PSU ℓ :=
  fieldInnerLie_PSU hdefI hdefO psuFiveSpecial ℓ

end CFSG.RankThree.PartOne.FOC
