module

public import CFSG.RankThree.PartOne.FOC.SpOuter
public import CFSG.RankThree.PartOne.FOC.Cases
public import CFSG.RankThree.PartOne.FOC.Equiv
import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon

public section

namespace CFSG.RankThree.PartOne.FOC

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.Sec66T (lieModel_classical_iff)

theorem exists_equiv_statedSp {T : Type} [Group T] {ℓ n f : ℕ} (hM : LieModel T .PSp n ℓ f) :
    ℓ.Prime ∧ 1 ≤ f ∧ 2 ≤ n ∧ ¬ (n = 2 ∧ ℓ ^ f = 2) ∧
      ∃ (K : Type) (_ : Field K), Finite K ∧ Nat.card K = ℓ ^ f ∧
        Nonempty (T ≃* StatedProj (StatedSp n K)) := by
  have hC : StatedClassicalModel T .PSp n ℓ f := (lieModel_classical_iff (by decide)).mp hM
  obtain ⟨⟨hℓ, hf, hn2, hne⟩, K, _, _, hK, ⟨e0⟩⟩ := hC
  exact ⟨hℓ, hf, hn2, fun ⟨h1, h2⟩ => hne (by rw [h1, h2]), K, inferInstance, inferInstance, hK,
    ⟨e0⟩⟩

theorem fieldInnerLie_PSp (hdef : DefInnerComponent) (ℓ : ℕ) : FieldInnerLie .PSp ℓ := by
  intro T _ _ n f p hp hp5 hsimple hnab hadm hmodel
  obtain ⟨hℓ, hf, hn2, hne, K, _, _, hK, ⟨e⟩⟩ := exists_equiv_statedSp hmodel
  have hs : IsSimpleGroup (StatedProj (StatedSp n K)) := e.symm.isSimpleGroup
  have hnab' : ∃ a b : StatedProj (StatedSp n K), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  refine FieldInnerT.of_mulEquiv e hp ?_
  by_cases hpℓ : p = ℓ
  · subst hpℓ
    have hmodel' : LieModel (StatedProj (StatedSp n K)) .PSp n p f :=
      (lieModel_classical_iff (by decide)).mpr ⟨hadm, K, inferInstance, inferInstance, hK,
        ⟨MulEquiv.refl _⟩⟩
    exact fieldInnerT_of_comp (center_eq_bot_of_nonab hs hnab')
      (hdef _ .PSp n f p hp hp5 hadm hs hmodel') (outerComp_sp hℓ hf hK hn2 hp (by omega))
  · exact fieldInnerT_sp hℓ hf hK hn2 hne hp hp5 hpℓ hs hnab'

end CFSG.RankThree.PartOne.FOC
