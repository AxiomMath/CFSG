module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PerfectCoreLemma
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.MonsterLargePrime

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG CFSG.Monster.Existence CFSG.Blueprint CFSG.AGLEmbedding

theorem isPerfect_of_isSimpleGroup_card_not_prime {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (h : ¬ (Nat.card X).Prime) : Group.IsPerfect X := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h1 | h1
  · exfalso
    have hc : IsMulCommutative X := (commutator_eq_bot_iff X).mp h1
    letI : CommGroup X := { ‹Group X› with mul_comm := fun a b => hc.is_comm.comm a b }
    exact h IsSimpleGroup.prime_card
  · exact h1

theorem PerfectCoreOf.toCell {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} (h : PerfectCoreOf p H) (hp : ¬ p ^ 2 ∣ Nat.card H) :
    PerfectCoreCell p H := by
  obtain ⟨L, hLH, hLn, hL, hcop⟩ := h
  exact ⟨L, hLH, hLn, hL, hcop, kernelTrivialAt_of_not_sq_dvd fun hd =>
    hp (hd.trans (Subgroup.card_dvd_of_le hLH))⟩

theorem card_cent_of_twoA {G : Type} [Group G] [Finite G] {a : G}
    (ha : orderOf a = 2) (h : IsTwoACentralizer a) :
    Nat.card (cent a) = Nat.card NativeSporadic.B * 2 := by
  obtain ⟨hperf, hcen, ⟨e⟩⟩ := h
  have hcenter : Nat.card (Subgroup.center (cent a)) = 2 := by
    have h1 : Nat.card ((Subgroup.center (cent a)).map (cent a).subtype) =
        Nat.card (Subgroup.center (cent a)) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ (cent a).subtype_injective).toEquiv.symm
    rw [← h1, hcen, Nat.card_zpowers, ha]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (cent a)), hcenter,
    Nat.card_congr e.toEquiv]

theorem perfectCoreCell_cent_of_twoA {G : Type} [Group G] [Finite G] {a : G}
    (ha : orderOf a = 2) (h : IsTwoACentralizer a) {p : ℕ} [Fact p.Prime]
    (hp : ¬ p ^ 2 ∣ 2 * Nat.card NativeSporadic.B) : PerfectCoreCell p (cent a) := by
  have hperf := h.1
  have hcard := card_cent_of_twoA ha h
  have hcoreOf : PerfectCoreOf p (cent a) :=
    ⟨cent a, le_rfl, fun g hg l hl => (cent a).mul_mem ((cent a).mul_mem hg hl)
      ((cent a).inv_mem hg), hperf, by simp⟩
  refine hcoreOf.toCell ?_
  rw [hcard, mul_comm]
  exact hp

theorem perfectCoreCell_cent_of_twoB {G : Type} [Group G] [Finite G] {z : G}
    (h : IsTwoBCentralizer z) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hCo1 : Group.IsPerfect NativeSporadic.Co1) (hp : ¬ p ^ 2 ∣ twoBCentralizerOrder) :
    PerfectCoreCell p (cent z) := by
  obtain ⟨-, hQcard, -, ⟨e⟩, hcard, -⟩ := h
  have : (pCore 2 (cent z)).Normal := pCore_normal
  have hN : IsPGroup 2 (pCore 2 (cent z)) := IsPGroup.of_card hQcard
  refine (perfectCoreOf_of_mulEquiv hp2 (pCore 2 (cent z)) hN hCo1 e).toCell ?_
  rw [hcard]
  exact hp

theorem perfectCoreOf_twoPointOne {G : Type} [Group G] [Finite G] {H : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2)
    (he6 : ∀ (X : Type) [Group X], LieModel X .twistedE6 0 2 1 → Group.IsPerfect X)
    (h : TwoPointShape H 1) : PerfectCoreOf p H := by
  have h' : ∃ (N : Subgroup H) (_ : N.Normal), IsElementaryAbelian 2 N ∧ Nat.card N = 2 ^ 2 ∧
      LieModel (H ⧸ N) .twistedE6 0 2 1 := h
  obtain ⟨N, hNn, -, hcard, hlie⟩ := h'
  have h1 : IsPGroup 2 N := IsPGroup.of_card hcard
  have h2 : Group.IsPerfect (H ⧸ N) := he6 _ hlie
  exact perfectCoreOf_of_quotient hp2 N h1 h2

theorem perfectCoreOf_twoPointTwo {G : Type} [Group G] [Finite G] {H : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hCo2 : Group.IsPerfect NativeSporadic.Co2)
    (h : TwoPointShape H 2) : PerfectCoreOf p H := by
  have h' : HasLayeredTwoShape H 2 22 fun X _ => Nonempty (X ≃* NativeSporadic.Co2) := h
  obtain ⟨N, hNn, N₀, hN₀n, -, -, -, -, hcard, ⟨e⟩⟩ := h'
  exact perfectCoreOf_of_mulEquiv hp2 N (IsPGroup.of_card hcard) hCo2 e

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
