module

public import CFSG.RankThree.PartOne.K1320.Members
public import CFSG.RankThree.PartOne.S13K.Row1Pair

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Open
open CFSG.Timmesfeld.Orders (Profile profile_ordA)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem psl_two_degree_eq {X : Type} [Group X] {a b : ℕ} (h1 : StatedClassicalModel X .PSL 2 2 a)
    (h2 : StatedClassicalModel X .PSL 2 2 b) : a = b := by
  have c1 := (CFSG.Timmesfeld.card_statedClassicalModel_two h1).1 rfl
  have c2 := (CFSG.Timmesfeld.card_statedClassicalModel_two h2).1 rfl
  obtain ⟨⟨-, ha, -, -, -⟩, -⟩ := h1
  obtain ⟨⟨-, hb, -, -, -⟩, -⟩ := h2
  have heq : ordA (2 - 1) (2 ^ a) = ordA (2 - 1) (2 ^ b) := c1.symm.trans c2
  have P1 := profile_ordA (n := 1) (f := a) (by norm_num) ha
  have P2 := profile_ordA (n := 1) (f := b) (by norm_num) hb
  norm_num at heq
  rw [heq] at P1
  obtain ⟨hN, -⟩ := Profile.transfer P1 P2
  norm_num at hN
  exact hN

variable {G : Type} [Group G] [Finite G]

section Pair

variable {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem centrallyLThree_of_pair
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hF13 : Sec13Facts G p A c L E) (hcard : Nat.card E = p ^ 3) {z : MulAut E}
    (hz : Inverter p E z) {J : Subgroup G} (hJ : J ∈ thetaCompZeroStarE p E) {s t : MulAut E}
    (hs : s ∈ reflectionSet p E) (hsJ : s ∈ torusImage E J) (ht : t ∈ reflectionSet p E)
    (htJ : t ∈ torusImage E J) (h3 : orderOf (s * t) = 3) :
    ∃ f' : ℕ, KFAt p E f' s ∧ KFAt p E f' t ∧ CentrallyLThree f' ↥(kZero p E s ⊔ kZero p E t) := by
  obtain ⟨B, c', h', hF', hc'E, hc'1, hEB, r, hr, hmodel, hW⟩ :=
    member_package hF13 hcard hz hJ
  have hg : s * t ∈ torusImage E J := (torusImage E J).mul_mem hsJ htJ
  have hg3 : (s * t) ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one _
  have hg1 : s * t ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at h3
    omega
  have hr1 : r = 1 := row_one_of_order_three hr hW hg hg3 hg1
  subst hr1
  obtain ⟨f', hf1, hpf, hm⟩ := hmodel
  have hst : s ≠ t := fun h1 => by
    rw [h1, RefFacts.mul_self_eq_one ht.1, orderOf_one] at h3
    omega
  exact ⟨f', S13K.kfAt_row1 hGA h' hF' hEB hpf hf1 hm s hs hsJ,
    S13K.kfAt_row1 hGA h' hF' hEB hpf hf1 hm t ht htJ,
    (S13K.kfPairL_row1 hGA h' hF' hEB hpf hf1 hm s hs hsJ t ht htJ hst).2 h3⟩

end Pair

end CFSG.RankThree.PartOne.K1320
