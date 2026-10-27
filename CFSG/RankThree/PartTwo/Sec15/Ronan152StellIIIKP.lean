module

public import CFSG.RankThree.S4Free.StellmacherWSz
public import CFSG.RankThree.PartTwo.Setup
public import CFSG.RankThree.S4Free.StellmacherSzAll

public section

namespace CFSG.RankThree.PartTwo

open CFSG.Assembly.RankThreeEven (sigmaA)

@[expose] def StellmacherKP : Prop :=
  S4Free.StellmacherSzAll.{0, 0} ∧ KFacts.KPSz

namespace TheoremFourHyp

variable {G : Type} [Group G] [Finite G]

theorem three_dvd_card (h : TheoremFourHyp G) : 3 ∣ Nat.card G := by
  have h3 : (3 : ℕ) ∈ sigmaA G := h.sigmaA_eq ▸ Set.mem_singleton 3
  simp only [sigmaA] at h3
  split_ifs at h3 <;> exact h3.2.2.1

theorem szSections (h : TheoremFourHyp G) (hSz : KFacts.KPSz) {U : Subgroup G}
    (hU3 : ¬ 3 ∣ Nat.card U) : S4Free.SzSections ↥U :=
  S4Free.szSections_of_kProper hSz h.kProper h.three_dvd_card hU3

end TheoremFourHyp

end CFSG.RankThree.PartTwo
