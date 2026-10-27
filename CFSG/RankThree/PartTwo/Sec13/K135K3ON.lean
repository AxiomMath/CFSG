module

public import CFSG.RankThree.PartTwo.Sec13.K135K3Sylow
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KF148ONA7.SevenCent
public import CFSG.Sporadic.Schreier.SteinbergBIONOuterTwo
public import CFSG.Milestones.ASVolI.A3Spor.Out
public import CFSG.Sporadic.ON

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup CFSG.Blueprint

theorem k3_ON
    {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.ON) :
    ∀ P : Subgroup (MulAut S), IsPGroup 7 P → 7 ^ 3 ≤ Nat.card P →
      ∀ α : MulAut S, α ^ 3 = 1 → (∀ π ∈ P, α * π = π * α) → α = 1 := by
  have hsimp := CFSG.Sporadic.ON.fam_on_simplicity
  have hcard : Nat.card NativeSporadic.ON = 460815505920 := CFSG.Sporadic.ON.card_ON
  have hnp : ¬ Nat.Prime 460815505920 := by norm_num
  haveI : IsSimpleGroup NativeSporadic.ON := hsimp.2.2
  haveI : Finite NativeSporadic.ON := hsimp.1
  have hcen : Subgroup.center S = ⊥ := by
    refine center_eq_bot_of_simple_card (X := NativeSporadic.ON) e ?_
    intro hp
    rw [hcard] at hp
    exact hnp hp
  have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ∣ 2 :=
    CFSG.Sporadic.SteinbergBI.cti_on_outer_order_divides_two ⟨e⟩
  have hodd : ∀ β : MulAut S, Odd (orderOf β) → ∃ l : S, β = MulAut.conj l :=
    CFSG.ASVolI.burnsideA315s_oddInner_of_not_dvd fun q hq hq2 hdvd =>
      hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hdvd.trans hout))
  have h7 : ¬ 7 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) := fun h => by
    have := Nat.le_of_dvd (by norm_num) (h.trans hout)
    omega
  intro P hP hcard α hα hcomm
  refine k3_of_data hcen hodd (inner_of_not_dvd_outer (by norm_num) h7) ?_ P hP hcard α hα hcomm
  intro Q hQ hQcard l hl3 hcommQ
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hdvd : 7 ∣ Nat.card Q := by
    rcases hQ.card_eq_or_dvd with h | h
    · exfalso
      have : 7 ^ 3 ≤ 1 := h ▸ hQcard
      omega
    · exact h
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 7 hdvd
  have hu' : orderOf (u : S) = 7 := by rw [Subgroup.orderOf_coe]; exact hu
  have hc := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KF148ONA7.card_centralizer_seven_ON
    e hu'
  have hl : l ∈ Subgroup.centralizer ({(u : S)} : Set S) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact (hcommQ u u.2).symm
  refine eq_one_of_pow_three_of_coprime _ ?_ hl hl3
  rcases hc with h | h <;> rw [h] <;> norm_num

end CFSG.RankThree.PartTwo.Sec13.F135Last
