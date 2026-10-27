module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanMonsterRows

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG.Blueprint CFSG.Open CFSG.AGLEmbedding

theorem ker_eq_bot_of_cyclic_sylow {E S : Type} [Group E] [Finite E] [Group.IsPerfect E] [Group S]
    {p : ℕ} [Fact p.Prime] (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hp : IsPGroup p π.ker) (Q : Sylow p S)
    (hQ : IsCyclic (Q : Subgroup S)) : π.ker = ⊥ := by
  obtain C : Sylow p π.ker := default
  have hCbot := CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπ hC C Q hQ
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hmult : (Nat.card π.ker).factorization p = k := by
    rw [hk, Nat.Prime.factorization_pow (Fact.out : p.Prime)]
    simp
  have h1 : Nat.card (C : Subgroup π.ker) = p ^ k := by
    rw [C.card_eq_multiplicity, hmult]
  rw [hCbot, Subgroup.card_bot] at h1
  have hk0 : k = 0 := by
    by_contra hne
    have : 1 < p ^ k := Nat.one_lt_pow hne (Fact.out : p.Prime).one_lt
    omega
  exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])

theorem kernelTrivialAt_of_not_sq_dvd {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (h : ¬ p ^ 2 ∣ Nat.card X) : KernelTrivialAt X p := by
  intro E _ _ _ π hπ hC hp
  obtain Q : Sylow p X := default
  exact ker_eq_bot_of_cyclic_sylow π hπ hC hp Q (CFSG.SectionRank.sylow_isCyclic_of_not_sq_dvd h Q)

theorem le_thirteen_of_sq_dvd_monsterOrder {p : ℕ} (hp : p.Prime) (h : p ^ 2 ∣ monsterOrder) :
    p ≤ 13 := by
  by_cases hp2 : p = 2
  · omega
  rcases MonsterRows.prime_eq_of_sq_dvd_monsterOrder hp hp2 h with h | h | h | h | h <;> omega

theorem not_sq_dvd_monsterOrder_of_gt_thirteen {p : ℕ} (hp : p.Prime) (h13 : 13 < p) :
    ¬ p ^ 2 ∣ monsterOrder := fun h => by
  have := le_thirteen_of_sq_dvd_monsterOrder hp h
  omega

theorem kernelTrivialAt_of_card_monsterOrder_of_gt_thirteen {X : Type} [Group X]
    (hcard : Nat.card X = monsterOrder) {p : ℕ} [hp : Fact p.Prime] (h13 : 13 < p) :
    KernelTrivialAt X p := by
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num [monsterOrder])
  exact kernelTrivialAt_of_not_sq_dvd (by
    rw [hcard]
    exact not_sq_dvd_monsterOrder_of_gt_thirteen hp.out h13)

theorem kernelTrivialAt_carrier_M_of_gt_thirteen
    (hMcard : Nat.card MonsterY443Derived = monsterOrder) {p : ℕ} [Fact p.Prime] (h13 : 13 < p) :
    KernelTrivialAt (NativeSporadic.Carrier .M) p :=
  kernelTrivialAt_of_card_monsterOrder_of_gt_thirteen
    (MonsterRows.card_eq_monsterOrder hMcard (MulEquiv.refl _)) h13

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
