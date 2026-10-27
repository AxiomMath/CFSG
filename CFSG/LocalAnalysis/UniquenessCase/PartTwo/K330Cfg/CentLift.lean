module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentDefs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Data.Nat.GCD.Basic
import CFSG.GH74.GLS.Stage2.OddAut.HeisPair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

private lemma k330c_pow_ne_one_of_coprime {G : Type*} [Group G] {x : G} {m p : ℕ}
    (hm : Nat.Coprime m p) (hx : x ≠ 1) (hxp : x ^ p = 1) : x ^ m ≠ 1 := by
  intro hxm
  have hg : x ^ (m.gcd p) = 1 := pow_gcd_eq_one.mpr ⟨hxm, hxp⟩
  rw [hm.gcd_eq_one, pow_one] at hg
  exact hx hg

private lemma k330c_ne_one_of_quotient_ne_one {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {x : G} (hx : (x : G ⧸ N) ≠ 1) : x ≠ 1 :=
  fun h => hx (by simp [h])

theorem e9c7Free_quotient {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    (hN : N ≤ Subgroup.center H) {m : ℕ} (hm : Nat.Coprime m 21)
    (hNm : ∀ z ∈ N, z ^ m = 1) (h : E9C7Free H) : E9C7Free (H ⧸ N) := by
  intro a b r hrel
  obtain ⟨a₀, ha₀⟩ := QuotientGroup.mk'_surjective N a
  obtain ⟨b₀, hb₀⟩ := QuotientGroup.mk'_surjective N b
  obtain ⟨r₀, hr₀⟩ := QuotientGroup.mk'_surjective N r
  subst ha₀
  subst hb₀
  subst hr₀
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hrel
  have hcomm9 : Commute (QuotientGroup.mk' N a₀) (QuotientGroup.mk' N b₀) := h9
  have hm3 : Nat.Coprime m 3 := hm.of_dvd_right (by norm_num)
  have hm7 : Nat.Coprime m 7 := hm.of_dvd_right (by norm_num)
  have ha3N : a₀ ^ 3 ∈ N := by
    rw [← QuotientGroup.eq_one_iff (N := N) (a₀ ^ 3)]
    simpa using h5
  have hb3N : b₀ ^ 3 ∈ N := by
    rw [← QuotientGroup.eq_one_iff (N := N) (b₀ ^ 3)]
    simpa using h6
  have hr7N : r₀ ^ 7 ∈ N := by
    rw [← QuotientGroup.eq_one_iff (N := N) (r₀ ^ 7)]
    simpa using h8
  have ha3 : (a₀ ^ m) ^ 3 = 1 := by
    rw [pow_right_comm, hNm (a₀ ^ 3) ha3N]
  have hb3 : (b₀ ^ m) ^ 3 = 1 := by
    rw [pow_right_comm, hNm (b₀ ^ 3) hb3N]
  have hr7 : (r₀ ^ m) ^ 7 = 1 := by
    rw [pow_right_comm, hNm (r₀ ^ 7) hr7N]
  have hcabN : (a₀ * b₀) / (b₀ * a₀) ∈ N := by
    rw [← QuotientGroup.eq_iff_div_mem (N := N)]
    simpa using h9
  set c : H := (a₀ * b₀) / (b₀ * a₀) with hcdef
  have hc : ∀ g : H, Commute g c := fun g => Subgroup.mem_center_iff.mp (hN hcabN) g
  have hab : a₀ * b₀ = c * (b₀ * a₀) := by
    rw [hcdef, div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one]
  have habm : (a₀ ^ m) * (b₀ ^ m) = (b₀ ^ m) * (a₀ ^ m) := by
    have hkey := CFSG.GH74.GLS.Stage2.OddAut.pow_mul_pow_comm_central hc hab m m
    have hcm : c ^ (m * m) = 1 := by
      rw [pow_mul, hNm c hcabN, one_pow]
    rw [hkey, hcm, one_mul]
  have hcarN : (a₀ * r₀) / (r₀ * a₀) ∈ N := by
    rw [← QuotientGroup.eq_iff_div_mem (N := N)]
    simpa using h10
  set car : H := (a₀ * r₀) / (r₀ * a₀) with hcardef
  have hcar : ∀ g : H, Commute g car := fun g => Subgroup.mem_center_iff.mp (hN hcarN) g
  have har : a₀ * r₀ = car * (r₀ * a₀) := by
    rw [hcardef, div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one]
  have harm : (a₀ ^ m) * (r₀ ^ m) = (r₀ ^ m) * (a₀ ^ m) := by
    have hkey := CFSG.GH74.GLS.Stage2.OddAut.pow_mul_pow_comm_central hcar har m m
    have hcm : car ^ (m * m) = 1 := by
      rw [pow_mul, hNm car hcarN, one_pow]
    rw [hkey, hcm, one_mul]
  have hcbrN : (b₀ * r₀) / (r₀ * b₀) ∈ N := by
    rw [← QuotientGroup.eq_iff_div_mem (N := N)]
    simpa using h11
  set cbr : H := (b₀ * r₀) / (r₀ * b₀) with hcbrdef
  have hcbr : ∀ g : H, Commute g cbr := fun g => Subgroup.mem_center_iff.mp (hN hcbrN) g
  have hbr : b₀ * r₀ = cbr * (r₀ * b₀) := by
    rw [hcbrdef, div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one]
  have hbrm : (b₀ ^ m) * (r₀ ^ m) = (r₀ ^ m) * (b₀ ^ m) := by
    have hkey := CFSG.GH74.GLS.Stage2.OddAut.pow_mul_pow_comm_central hcbr hbr m m
    have hcm : cbr ^ (m * m) = 1 := by
      rw [pow_mul, hNm cbr hcbrN, one_pow]
    rw [hkey, hcm, one_mul]
  have ha_ne : a₀ ^ m ≠ 1 := by
    apply k330c_ne_one_of_quotient_ne_one N
    simpa using k330c_pow_ne_one_of_coprime hm3 h1 h5
  have hb_ne : b₀ ^ m ≠ 1 := by
    apply k330c_ne_one_of_quotient_ne_one N
    simpa using k330c_pow_ne_one_of_coprime hm3 h2 h6
  have hr_ne : r₀ ^ m ≠ 1 := by
    apply k330c_ne_one_of_quotient_ne_one N
    simpa using k330c_pow_ne_one_of_coprime hm7 h7 h8
  have hab_ne : a₀ ^ m * b₀ ^ m ≠ 1 := by
    intro hzero
    have h5' : ((QuotientGroup.mk' N a₀) * (QuotientGroup.mk' N b₀)) ^ 3 = 1 := by
      rw [hcomm9.mul_pow 3, h5, h6, mul_one]
    have hQ : ((QuotientGroup.mk' N a₀) * (QuotientGroup.mk' N b₀)) ^ m = 1 := by
      rw [hcomm9.mul_pow m]
      simpa only [map_mul, map_pow, map_one] using
        congrArg (QuotientGroup.mk' N) hzero
    exact k330c_pow_ne_one_of_coprime hm3 h3 h5' hQ
  have hab2_ne : a₀ ^ m * (b₀ ^ m) ^ 2 ≠ 1 := by
    intro hzero
    have h5'' : ((QuotientGroup.mk' N a₀) * (QuotientGroup.mk' N b₀) ^ 2) ^ 3 = 1 := by
      rw [(hcomm9.pow_right 2).mul_pow 3, h5, one_mul, pow_right_comm, h6, one_pow]
    have hQ : ((QuotientGroup.mk' N a₀) * (QuotientGroup.mk' N b₀) ^ 2) ^ m = 1 := by
      rw [(hcomm9.pow_right 2).mul_pow m]
      simpa only [map_mul, map_pow, map_one, pow_right_comm] using
        congrArg (QuotientGroup.mk' N) hzero
    exact k330c_pow_ne_one_of_coprime hm3 h4 h5'' hQ
  exact h (a₀ ^ m) (b₀ ^ m) (r₀ ^ m)
    ⟨ha_ne, hb_ne, hab_ne, hab2_ne, ha3, hb3, hr_ne, hr7, habm, harm, hbrm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
