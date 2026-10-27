module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transfer

public section

namespace CFSG.RankThree.PartTwo.Sec21

theorem eq_one_of_mem_center_of_abelian_sylow {K : Type} [Group K] [Finite K]
    (hperf : Group.IsPerfect K) {p : ℕ} [Fact p.Prime] (P : Sylow p K)
    (hPab : ∀ x ∈ (P : Subgroup K), ∀ y ∈ (P : Subgroup K), x * y = y * x) {z : K}
    (hz : z ∈ Subgroup.center K) (hzp : z ^ p = 1) : z = 1 := by
  haveI : (Subgroup.zpowers z).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz)
  have hpg : IsPGroup p (Subgroup.zpowers z) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzp, one_zpow]
  exact Sec4.RonanK432.eq_one_of_mem_center_of_abelian_sylow hperf P
    (fun x y hx hy => hPab x hx y hy) hz (hpg.le_sylow_of_normal P (Subgroup.mem_zpowers z))

end CFSG.RankThree.PartTwo.Sec21
