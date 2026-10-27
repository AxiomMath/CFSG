module

public import CFSG.RankThree.PartOne.MultRes.Trim
public import CFSG.RankThree.PartOne.Census3.Interface

public section

namespace CFSG.RankThree.PartOne.Q1327S

open CFSG CFSG.Blueprint TauCeti CFSG.RankThree.PartOne

theorem not_sectionExcluded_of_mem {s : SporadicName} (hs : s ∈ Census3.sporadicsThm3) :
    ¬ Mult.SectionExcluded s := by
  simp only [Census3.sporadicsThm3, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Mult.SectionExcluded]

theorem center_eq_bot_of_sporadic
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) {s : SporadicName}
    (hs : s ∈ Census3.sporadicsThm3) (e : K ⧸ Subgroup.center K ≃* NativeSporadic.Carrier s)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hZ : IsPGroup p (Subgroup.center K)) :
    Subgroup.center K = ⊥ := by
  by_contra hne
  have : Fact p.Prime := ⟨hp⟩
  have hpd : p ∣ Nat.card (Subgroup.center K) := by
    obtain ⟨n, hn⟩ := hZ.exists_card_eq
    rcases n with _ | n
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hn)) hne
    · rw [hn]
      exact dvd_pow_self p n.succ_ne_zero
  have : Group.IsPerfect K := hK.1
  obtain ⟨hpair, hnot⟩ := Mult.sporadic_residual_of_center e hp (by omega) hpd
  exact hnot (Mult.SporadicResidualKernelsTrim.trivial_of_pair
    MultRes.sporadicResidualKernelsTrim_holds (not_sectionExcluded_of_mem hs) hpair)

end CFSG.RankThree.PartOne.Q1327S
