module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummand
import CFSG.GH74.Constrained

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem ggRCS_orderOf_bar {r : G} {e : ↥(Subgroup.centralizer ({r} : Set G))}
    (he3 : orderOf (e : G) = 3) : orderOf (QuotientGroup.mk e : GGRCSNbar r) = 3 := by
  let P := CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer ({r} : Set G))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he3N : orderOf e = 3 := by
    rw [← Subgroup.orderOf_coe e]
    exact he3
  have hpow : (QuotientGroup.mk e : GGRCSNbar r) ^ 3 = 1 := by
    change (QuotientGroup.mk' P e) ^ 3 = 1
    rw [← map_pow, show e ^ 3 = 1 from by rw [← he3N]; exact pow_orderOf_eq_one e,
      map_one]
  have hdvd : orderOf (QuotientGroup.mk e : GGRCSNbar r) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one hpow
  have hne : orderOf (QuotientGroup.mk e : GGRCSNbar r) ≠ 1 := by
    intro h1
    have heP : e ∈ P := by
      refine (QuotientGroup.eq_one_iff (N := P) e).mp ?_
      exact orderOf_eq_one_iff.mp h1
    have hP : IsPGroup 2 P := CFSG.pCore_isPGroup
    obtain ⟨k, hk⟩ := hP.exists_orderOf_eq_pow (⟨e, heP⟩ : P)
    have h2 : orderOf e = 2 ^ k := by
      rw [← Subgroup.orderOf_mk e heP]
      exact hk
    rw [he3N] at h2
    cases k with
    | zero => norm_num at h2
    | succ j =>
      rw [pow_succ] at h2
      omega
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd h hne
  · exact h

theorem ggRCS_centralizer_bar_le {M : Subgroup G} {r : G}
    {e : ↥(Subgroup.centralizer ({r} : Set G))} (he3 : orderOf (e : G) = 3)
    (hM : Subgroup.centralizer ({(e : G)} : Set G) ≤ M) :
    Subgroup.centralizer ({(QuotientGroup.mk e : GGRCSNbar r)} : Set (GGRCSNbar r)) ≤
      ggRCSImg r M := by
  let H := Subgroup.centralizer ({r} : Set G)
  let N := ↥H
  let P := CFSG.Assembly.pCore 2 N
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have he3N : orderOf e = 3 := by
    rw [← Subgroup.orderOf_coe e]
    exact he3
  have hP : IsPGroup 2 P := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card P) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hcent := CFSG.GH74.centralizer_singleton_quotient_eq_map 3 P hcop
    ⟨1, by rw [pow_one]; exact he3N⟩
  change Subgroup.centralizer ({(QuotientGroup.mk' P e)} : Set (N ⧸ P)) ≤
    (M.subgroupOf H).map (QuotientGroup.mk' P)
  rw [hcent]
  apply Subgroup.map_mono
  intro n hn
  rw [Subgroup.mem_subgroupOf]
  apply hM
  rw [Subgroup.mem_centralizer_singleton_iff] at hn ⊢
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul]
  exact congrArg Subtype.val hn

theorem ggRCS_bar_data_of_centralizer_le {M : Subgroup G} {r : G} {S₁ : Subgroup (GGRCSNbar r)}
    {e : ↥(Subgroup.centralizer ({r} : Set G))} (he3 : orderOf (e : G) = 3)
    (hM : Subgroup.centralizer ({(e : G)} : Set G) ≤ M)
    (heS₁ : (QuotientGroup.mk e : GGRCSNbar r) ∈ S₁) :
    ∃ ē : GGRCSNbar r, ē ∈ S₁ ∧ orderOf ē = 3 ∧
      Subgroup.centralizer ({ē} : Set (GGRCSNbar r)) ≤ ggRCSImg r M :=
  ⟨_, heS₁, ggRCS_orderOf_bar he3, ggRCS_centralizer_bar_le he3 hM⟩

end CFSG.StandardType
