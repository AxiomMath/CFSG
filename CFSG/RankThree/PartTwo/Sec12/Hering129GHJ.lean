module

public import CFSG.RankThree.PartTwo.Sec12.Hering129Steps
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem Cfg129.not_mem_D {A L K S : Subgroup G} {c b a : G} (cfg : Cfg129 G A c L b a K S) :
    c ∉ D129 a b := by
  intro hcD
  obtain ⟨hbA, haA, haL, hb1, ha1, -, hbL, -⟩ := cfg.point_facts
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := cfg.std.isE27.1
  have hab : a * b = b * a := congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, haA⟩ ⟨b, hbA⟩)
  have hb3 : orderOf b = 3 := orderOf_eq_prime (hAe.2 b hbA) hb1
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hAe.2 a haA) ha1
  obtain ⟨i, j, hij⟩ := Sec4.exists_zpow_mul_of_mem_sup hab hcD
  have hbjL : b ^ j ∈ L := by
    have h1 : b ^ j = (a ^ i)⁻¹ * c := by rw [hij, inv_mul_cancel_left]
    rw [h1]
    exact L.mul_mem (L.inv_mem (L.zpow_mem haL i)) cfg.std.mem_L
  have hbj1 : b ^ j = 1 := by
    by_contra hne
    exact hbL (mem_of_mem_zpowers_of_ne_one hb3 (Subgroup.zpow_mem_zpowers b j) hne hbjL)
  have hca : c ∈ Subgroup.zpowers a := by
    rw [hij, hbj1, mul_one]
    exact Subgroup.zpow_mem_zpowers a i
  exact cfg.ha_not
    (mem_of_mem_zpowers_of_ne_one ha3 hca cfg.std.ne_one (Subgroup.mem_zpowers c))

@[expose] def Gap129HJOmega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
    (K S : Subgroup G), Cfg129 G A c L b a K S → HJType129 L K →
    ∀ x ∈ D129 a b, x ∉ Subgroup.zpowers b → ¬ StarConditionAt A x

theorem false_of_hj_branch_notT (h128 : Item128BarAt) (hΩ : Gap129HJOmega) {A L K S : Subgroup G}
    {c b a : G} (cfg : Cfg129 G A c L b a K S) (hHJ : HJType129 L K) (hAT : A ∉ partTwoT G) :
    False := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hxD, hxb, -⟩ := cfg.point_facts
  exact false_of_hj_omega h128 cfg hAT (hΩ G A c L b a K S cfg hHJ (a * b) hxD hxb)

end CFSG.RankThree.PartTwo.Sec12
