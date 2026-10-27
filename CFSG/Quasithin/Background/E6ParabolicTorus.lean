module

public import CFSG.Quasithin.Background.E6TwentySevenMain
public import CFSG.Quasithin.Background.E6TorusCover
public import CFSG.Quasithin.Vol2.Ch12Sec2E22BorelLiftLie
public import CFSG.Quasithin.Vol2.Ch4Sec4W4413

public section

namespace CFSG.Quasithin
namespace E6

open CFSG.Open CFSG.QuasithinUnique

theorem parabolicTorusFact_of_e22C (hE22 : E2.E22StatementC)
    (hT : E2.E22TorusFacts) : ParabolicTorusFact := by
  intro Γ _ _ H S MH hs hnab hqtke hO2 hmin _ hn1
  have hSQ : SQTKGroup ↥H :=
    ⟨stronglyQuasithin_of_pCoreOf_ne_bot hqtke hO2, kGroup_of_pCoreOf_ne_bot hqtke hs hnab hO2⟩
  obtain ⟨n, -, hnH, hsolv, R, -, -, -, ⟨C, hCM, hCodd, hCi⟩, hall⟩ :=
    E2.e22BorelLift hE22 (E2.e22TorusCover_of_facts hT) hmin hSQ hn1
  obtain ⟨-, -, hCab, Y, hYC, hYcyc, hYcard, hYN⟩ := hall C hCM hCodd hCi
  have hMH : MH ∈ maxOver H S := hmin.uniqueMax ▸ Set.mem_singleton MH
  have hSyl : IsSylowTwoOf S MH := A4.isSylowTwoOf_mono hmin.isSylow hMH.2 hMH.1.1.le
  obtain ⟨h1, h2⟩ := H13.Ch4.Lemma4413.mul_eq hCM hCodd hCi hSyl
  refine ⟨hsolv, n, C, Y, hnH, hYC, hCM, fun a ha b hb => ?_, hCodd, by rw [h1, h2], hYcyc,
    hYcard, hYN⟩
  exact congrArg Subtype.val (hCab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

variable {G : Type} [Group G] [Finite G]

end E6
end CFSG.Quasithin
