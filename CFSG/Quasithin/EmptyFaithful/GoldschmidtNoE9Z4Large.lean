module

public import CFSG.Quasithin.EmptyFaithful.S14612GC
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4GenMain
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4G15Main
import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4MinMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

@[expose] def NoE9Z4LargeBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → IsE9Z4Shape T H p →
      2 ^ 9 < Nat.card ↥(pCoreOf 2 H) →
      pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) ≠
        conjClosure (VZ T M) H → False

theorem noE9Z4Large_of_big (h35 : Lemma1435) (h5 : Stage1461Five) (hbig : NoE9Z4LargeBig) :
    NoE9Z4Large := by
  intro G _ _ T M S H PQ p hred hmax hshape hlt
  by_cases hB : pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) =
      conjClosure (VZ T M) H
  · by_cases hA : ∀ u ∈ conjClosure (VZ T M) H, (∀ x ∈ H, ⁅u, x⁆ ∈ quasithinOmegaOneCenter T) →
        ∀ y ∈ pCoreOf 2 H, ⁅u, y⁆ = 1
    · exact noE9Z4_caseA h35 h5 S hred hshape hB hA
    · push Not at hA
      exact noE9Z4_caseB h35 h5 S hred hshape hB hA
  · exact hbig G T M S H PQ p hred hmax hshape hlt hB

theorem noE9Z4_of_big (h35 : Lemma1435) (h5 : Stage1461Five) (hbig : NoE9Z4LargeBig) :
    NoE9Z4 :=
  noE9Z4_of_res h35 h5 ⟨noE9Z4Min_of h35, noE9Z4Large_of_big h35 h5 hbig⟩

end CFSG.Quasithin
