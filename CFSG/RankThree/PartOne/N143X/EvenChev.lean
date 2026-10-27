module

public import CFSG.RankThree.PartOne.N143X.EvenExcl
public import CFSG.Blueprint.Catalog
import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.RankThree.PartTwo.Census.Exceptional.E6Two
import CFSG.RankThree.PartTwo.Census.Exceptional.TwistedE6

public section

namespace CFSG.RankThree.PartOne.N143X

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti
  CFSG.RankThree.PartTwo.Census.Exceptional CFSG.TauCetiBridge.Even

theorem false_of_chevalley_exc
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {f : ℕ}
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨ (t = .F4 ∧ 2 ≤ f))
    (hmod : ChevalleyExceptionalModel X t 2 f) (he : evenRank X ≤ 3) : False := by
  rcases ht with rfl | rfl | rfl | rfl | ⟨rfl, hf2⟩
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
    let q : PrimePower := ⟨2, f, Nat.prime_two, hadm.2.1⟩
    have hv : (LieTypeIndex.E6 q).Valid :=
      (LieTypeIndex.valid_iff _).2 ⟨(LieTypeIndex.inStandardRange_iff _).2 trivial,
        fun h => (LieTypeIndex.isDuplicateRepresentative_iff _).1 h⟩
    obtain ⟨b⟩ := chevalleyBridgesEven.e6 q hv rfl K (by rw [PrimePower.card_def]; exact hK)
    exact false_of_four_le_carrier (e.trans b) he (four_le_twoLocalOddRank_E6 q hv)
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
    let q : PrimePower := ⟨2, f, Nat.prime_two, hadm.2.1⟩
    have hv : (LieTypeIndex.E7 q).Valid :=
      (LieTypeIndex.valid_iff _).2 ⟨(LieTypeIndex.inStandardRange_iff _).2 trivial,
        fun h => (LieTypeIndex.isDuplicateRepresentative_iff _).1 h⟩
    obtain ⟨b⟩ := chevalleyBridgesEven.e7 q hv rfl K (by rw [PrimePower.card_def]; exact hK)
    exact false_of_four_le_carrier (e.trans b) he (four_le_twoLocalOddRank_E7 q hv)
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
    let q : PrimePower := ⟨2, f, Nat.prime_two, hadm.2.1⟩
    have hv : (LieTypeIndex.E8 q).Valid :=
      (LieTypeIndex.valid_iff _).2 ⟨(LieTypeIndex.inStandardRange_iff _).2 trivial,
        fun h => (LieTypeIndex.isDuplicateRepresentative_iff _).1 h⟩
    obtain ⟨b⟩ := chevalleyBridgesEven.e8 q hv rfl K (by rw [PrimePower.card_def]; exact hK)
    exact false_of_four_le_carrier (e.trans b) he (four_le_twoLocalOddRank_E8 q hv)
  · obtain ⟨hadm, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hmod
    let q : PrimePower := ⟨2, f, Nat.prime_two, hadm.2.1⟩
    have hv : (LieTypeIndex.twistedE6 q).Valid :=
      (LieTypeIndex.valid_iff _).2 ⟨(LieTypeIndex.inStandardRange_iff _).2 trivial,
        fun h => (LieTypeIndex.isDuplicateRepresentative_iff _).1 h⟩
    obtain ⟨b⟩ := chevalleyBridgesEven.twistedE6 q hv rfl K
      (by rw [PrimePower.card_def]; exact hK) σ
      (fun x => by rw [PrimePower.card_def]; exact hσ x)
    exact false_of_four_le_carrier (e.trans b) he (four_le_twoLocalOddRank_twistedE6 q hv)
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
    let q : PrimePower := ⟨2, f, Nat.prime_two, hadm.2.1⟩
    have hv : (LieTypeIndex.F4 q).Valid :=
      (LieTypeIndex.valid_iff _).2 ⟨(LieTypeIndex.inStandardRange_iff _).2 trivial,
        fun h => (LieTypeIndex.isDuplicateRepresentative_iff _).1 h⟩
    obtain ⟨b⟩ := chevalleyBridgesEven.f4 q hv rfl K (by rw [PrimePower.card_def]; exact hK)
    exact false_of_four_le_carrier (e.trans b) he
      (four_le_twoLocalOddRank_F4 q hv (by simp [q]; omega))

end CFSG.RankThree.PartOne.N143X
