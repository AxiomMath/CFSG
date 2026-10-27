module

public import CFSG.Quasithin.Background.Harris.KFact2d.Defs

public section

namespace CFSG.Quasithin.Background.Harris.OrdinaryProofs

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Background.Harris.KFact2d

variable {X : Type} [Group X]

theorem le_pCoreOf_two_of_le_normalizer [Finite X] {E M : Subgroup X} (hEM : E ≤ M)
    (hM : M ≤ Subgroup.normalizer (E : Set X)) (hE : IsElemAbelian 2 E) :
    E ≤ pCoreOf 2 M := by
  have hnorm : (E.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hEM]
    intro h k hh hk
    exact (Subgroup.mem_normalizer_iff.mp (hM hk) h).mp hh
  have hp : IsPGroup 2 E := fun g => ⟨1, by
    have := hE.2 (g : X) g.2
    simp only [pow_one]
    exact Subtype.ext (by simpa using this)⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 hEM hnorm hp

theorem V_le_pCoreOf_of_maximal [Finite X] {T M V : Subgroup X}
    (hTM : T ≤ M) (hVT : V ≤ T)
    (hV : IsElemAbelian 2 V)
    (hmax : ∀ B : Subgroup X, T ≤ B → B ≤ M → B = T ∨ B = M)
    (hA : AtomCond T M V) : V ≤ pCoreOf 2 M := by
  have hVM : V ≤ M := hVT.trans hTM
  by_cases hMV : M ≤ Subgroup.normalizer (V : Set X)
  · exact le_pCoreOf_two_of_le_normalizer hVM hMV hV
  · have hel : IsElemAbelian 2 (conjClosure V M) := hA M hTM le_rfl hMV hmax
    have hNM : conjClosure V M ≤ M :=
      conjClosure_le fun h hh z hz => M.mul_mem (M.mul_mem hh (hVM hz)) (M.inv_mem hh)
    have hVN : V ≤ conjClosure V M := le_conjClosure V M
    exact hVN.trans (le_pCoreOf_two_of_le_normalizer hNM
      (le_normalizer_conjClosure V M) hel)

end CFSG.Quasithin.Background.Harris.OrdinaryProofs

end
