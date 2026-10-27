module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7Cent
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7Cases
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7L2
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7L3
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Main

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem genSeven_of_shape92 {Q : Type} [Group Q] [Finite Q]
    (hQ : F09.Shape92 Q) {X : Subgroup Q} (hX : IsL2Odd (Bar2 X) 7)
    (hcyc : ∀ P : Subgroup Q, IsPGroup 3 P → IsCyclic P) : GenSeven Q X := by
  rcases shape92_cases_seven hQ hX hcyc with ⟨p, f, hp3, h⟩ | ⟨p, f, hq, h⟩ | ⟨p, f, hp2, hq, h⟩
  · exact genSeven_of_psl2 hp3 h hX hcyc
  · exact genSeven_of_psl3 hq h hX hcyc
  · exact u3GenSeven_holds Q p f hp2 hq h X hX hcyc

namespace Slice

variable {G : Type} [Group G] [Finite G] {D : Data G} {L D₃ Y H : Subgroup G} {q : ℕ}

theorem false_of_hN_eq_seven (S : Slice D L D₃ Y H q) (hq : q = 7)
    (hN : ∀ A : Subgroup G, A ≤ Y → (Nat.card A).Prime → Odd (Nat.card A) →
      normalizer (A : Set G) ≤ D.M)
    {E : Subgroup G} (hyp : F09.Hyp91 D Y H E)
    (h92L : H = F09.L9 Y H ⊔ (H ⊓ D.M)) (h92S : F09.Shape92 (F09.Lbar9 Y H))
    (h17 : F09.I9 H ≤ D.M) : False :=
  S.false_of_genSeven hN h92L h17
    (genSeven_of_shape92 h92S (S.isL2Odd_bar2_xbar9 hq) (isCyclic_of_isPGroup_lbar9 hyp))

end Slice

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
