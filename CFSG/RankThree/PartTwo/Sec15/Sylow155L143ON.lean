module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Open.LocalVocabulary
public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143RowGen
import CFSG.RankThree.PartTwo.Sec14.Item148Res9ONProofInner

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155L143

theorem L143Row.of_isElemAbelian {S : Type*} [Group S] {x : S} {E : Subgroup S}
    (hxE : x ∈ E) (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : 27 ≤ Nat.card E) : L143Row x :=
  L143Row.of_mem E hxE
    (fun e he f hf => congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨f, hf⟩)) hE.2 hcard

theorem l143RowsT_ON (T : Type)
    [Group T] (hT : Nonempty (T ≃* CFSG.Blueprint.NativeSporadic.ON)) : L143Rows T := by
  obtain ⟨ψ⟩ := hT
  haveI : Finite CFSG.Blueprint.NativeSporadic.ON :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.ON.card_ON]; norm_num)
  haveI : Finite T := Finite.of_equiv _ ψ.symm.toEquiv
  intro x hx3 _
  have hP : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hx3)
  obtain ⟨E, hxE, hcard, hE⟩ := CFSG.RankThree.PartTwo.Sec14.Res9ON.exists_elemAbelian_le_ON ψ hP
  exact L143Row.of_isElemAbelian (hxE (Subgroup.mem_zpowers x)) hE (by rw [hcard]; norm_num)

end CFSG.RankThree.PartTwo.Sec15.Sylow155L143
