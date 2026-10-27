module

public import CFSG.RankThree.PartTwo.Sec11.Item1119NUFam
import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarGeneric
import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolNumbers
public import CFSG.RankThree.PartTwo.Sec11.Item1117Res5ProofSymTypes

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace Item1119NU

section Part1


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem sym1119_x_le_27 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (hG2 : NumFamG2) (hD4 : NumFamD4) (hL3 : NumFamL3)
    (hctx : Sym1119Ctx G A c L a R Y d x s r g) : orderOf x ≤ 27 := by
  have hbig := hctx.big
  have h := hbig.toSec11Data
  obtain ⟨hcN, hsN, hx3Y, hgY, D, -⟩ := Item1120V0Bar.v0_data h45 h113 h117 hbig
  have key : orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨x ^ 3, hx3Y⟩) ≤
      3 * orderOf (Sec4.Item426.thetaAut Y hsN) := by
    rcases hbig.isList with hZ | hZ | hZ
    · exact hG2 _ hZ _ _ _ _ _ D.alpha_cube D.J_comp D.J_type D.xi_mem D.xi_sylow D.xi_nine
        D.sigma_three D.sigma_alpha D.sigma_J D.sigma_xi D.gamma_cube D.P_three D.lower_bound
    · exact hD4 _ hZ _ _ _ _ _ D.alpha_cube D.J_comp D.J_type D.xi_mem D.xi_sylow D.xi_nine
        D.sigma_three D.sigma_alpha D.sigma_J D.sigma_xi D.gamma_cube D.P_three D.lower_bound
    · exact hL3 G Y (sec11K L a) c s hcN hsN _ _ _ hZ D
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  have hs3 : s ^ 3 = 1 := by
    have hsc : s ∈ Subgroup.zpowers c := hctx.s_eq_c ▸ Subgroup.mem_zpowers s
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hsc
    exact Item1119Sym.aux_Numbers_zpow_pow_three hc3 j
  have hτ : orderOf (Sec4.Item426.thetaAut Y hsN) ≤ 3 :=
    orderOf_le_of_pow_eq_one (by norm_num) (Sec4.Item426.thetaAut_pow_eq_one Y hsN hs3)
  have hξ := Item1120V0Bar.orderOf_mk_x_cube h hx3Y
  have hx3 : orderOf x = 3 * orderOf (x ^ 3) := by
    obtain ⟨k, hk⟩ := Item1117Proof.x_pow_eq_one h
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
    have hgt := hctx.big.orderOf_x_gt
    have hj1 : j ≠ 0 := by
      rintro rfl
      rw [hj] at hgt
      norm_num at hgt
    have h3 : 3 ∣ orderOf x := by
      rw [hj]
      exact dvd_pow_self 3 hj1
    rw [orderOf_pow' x (by norm_num : (3 : ℕ) ≠ 0), Nat.gcd_eq_right h3]
    exact (Nat.mul_div_cancel' h3).symm
  omega

end Part1

end Item1119NU

end CFSG.RankThree.PartTwo.Sec11

end
