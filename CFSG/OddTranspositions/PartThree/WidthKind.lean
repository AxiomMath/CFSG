module

import CFSG.OddTranspositions.A3Bound
public import CFSG.OddTranspositions.AscTheoremTwo
public import CFSG.OddTranspositions.Width
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.OddTranspositions.O4PairTenWidth
public import CFSG.OddTranspositions.SixEight
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate43
import CFSG.Timmesfeld.Exceptional.Residual

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

section

variable {G : Type} [Group G] {D : Set G}

theorem false_of_four_commuting_of_widthLe_three (hw : WidthLe D 3) {a b c e : G}
    (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D) (he : e ∈ D)
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e)
    (hce : c ≠ e)
    (hab' : Commute a b) (hac' : Commute a c) (hae' : Commute a e)
    (hbc' : Commute b c) (hbe' : Commute b e) (hce' : Commute c e) : False := by
  classical
  have hsub : (↑({a, b, c, e} : Finset G) : Set G) ⊆ D := by
    intro z hz
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact he
  have hcomm : ∀ x ∈ ({a, b, c, e} : Finset G), ∀ y ∈ ({a, b, c, e} : Finset G),
      x ≠ y → Commute x y := by
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hxy
        | exact hab' | exact hac' | exact hae'
        | exact hab'.symm | exact hbc' | exact hbe'
        | exact hac'.symm | exact hbc'.symm | exact hce'
        | exact hae'.symm | exact hbe'.symm | exact hce'.symm
  have hle := hw _ hsub hcomm
  have hcard : ({a, b, c, e} : Finset G).card = 4 :=
    Finset.card_eq_four.mpr ⟨a, b, c, e, hab, hac, hae, hbc, hbe, hce, rfl⟩
  omega

theorem mul_mem_of_firstKind_triangle (hD : IsOddTransp D) (hN : IsNormalSet D)
    {u w v : G} (ht : IsTriangle D u w v) (hodd : Odd (orderOf (u * v * w))) :
    u * v ∈ D ∧ u * v ≠ u ∧ u * v ≠ v ∧ Commute u (u * v) ∧
      Commute v (u * v) ∧ ¬ Commute w (u * v) := by
  have huvD : u * v ∈ D := ht.mul_mem_of_odd hD hN hodd
  have huv_ne_u : u * v ≠ u := by
    intro h
    have h1 : u * v = u * 1 := by simpa using h
    exact hD.ne_one ht.2.1 (mul_left_cancel h1)
  have huv_ne_v : u * v ≠ v := by
    intro h
    have h1 : u * v = 1 * v := by simpa using h
    exact hD.ne_one ht.1 (mul_right_cancel h1)
  exact ⟨huvD, huv_ne_u, huv_ne_v,
    (Commute.refl u).mul_right ht.2.2.2.2.1,
    ht.2.2.2.2.1.symm.mul_right (Commute.refl v),
    ht.not_commute_mul hD⟩

theorem exists_mem_of_thirdKind_triangle (hD : IsOddTransp D) (hN : IsNormalSet D)
    {u w v : G} (ht : IsTriangle D u w v) (hthird : IsThirdKind u w v) :
    ∃ e ∈ D, e ≠ u ∧ e ≠ v ∧ Commute u e ∧ Commute v e ∧ ¬ Commute w e ∧
      ∀ d : G, Commute u d → Commute v d → Commute w d → Commute d e := by
  obtain ⟨n, hn, hn1, hord⟩ := hthird
  obtain ⟨hzz, -, hzx, hzv, hzw, heD⟩ := ht.third_kind hD hN hn hord
  set z : G := (u * v * w) ^ n with hzdef
  have hzz' : z * z = 1 := by simpa [← hzdef] using hzz
  have hzu : Commute z u := by simpa [← hzdef] using hzx
  have hzv : Commute z v := by simpa [← hzdef] using hzv
  have hzw : Commute z w := by simpa [← hzdef] using hzw
  have heD' : u * v * z ∈ D := by simpa [← hzdef] using heD
  have hu_huv : Commute u (u * v) := (Commute.refl u).mul_right ht.2.2.2.2.1
  have hv_huv : Commute v (u * v) := ht.2.2.2.2.1.symm.mul_right (Commute.refl v)
  have hue : Commute u (u * v * z) := by
    simpa using hu_huv.mul_right hzu.symm
  have hve : Commute v (u * v * z) := by
    simpa using hv_huv.mul_right hzv.symm
  have he_ne_u : u * v * z ≠ u := by
    intro heq
    have h1 : u * v = u * z := by
      simpa [mul_assoc, hzz'] using congrArg (fun x => x * z) heq
    have h2 : z = v := (mul_left_cancel h1).symm
    exact ht.2.2.2.2.2.2 (h2 ▸ hzw)
  have he_ne_v : u * v * z ≠ v := by
    intro heq
    have h1 : u * v = v * z := by
      simpa [mul_assoc, hzz'] using congrArg (fun x => x * z) heq
    have h2 : u = z := by
      calc u = u * (v * v) := by rw [hD.mul_self_eq_one ht.2.1, mul_one]
        _ = (u * v) * v := by group
        _ = (v * z) * v := by rw [h1]
        _ = v * (z * v) := by group
        _ = v * (v * z) := by rw [hzv.eq]
        _ = (v * v) * z := by group
        _ = z := by rw [hD.mul_self_eq_one ht.2.1, one_mul]
    exact ht.2.2.2.2.2.1 (h2.symm ▸ hzw)
  have hnc_we : ¬ Commute w (u * v * z) := by
    intro hc
    apply ht.not_commute_mul hD
    have h : u * v = (u * v * z) * z := by
      show u * v = u * v * z * z
      rw [mul_assoc (u * v) z z, hzz', mul_one]
    rw [h]
    exact hc.mul_right hzw.symm
  refine ⟨u * v * z, heD', he_ne_u, he_ne_v, hue, hve, hnc_we, ?_⟩
  intro d hdu hdv hdw
  have hduv : Commute d (u * v) := hdu.symm.mul_right hdv.symm
  have hduvw : Commute d (u * v * w) := hduv.mul_right hdw.symm
  have hdz : Commute d z := by
    simpa [← hzdef] using hduvw.pow_right n
  simpa using hduv.mul_right hdz

theorem false_of_firstKind_of_widthLe_three (hD : IsOddTransp D) (hN : IsNormalSet D)
    (hw : WidthLe D 3) {d x y t : G} (hd : d ∈ D)
    (hxd : Commute x d) (hyd : Commute y d) (htd : Commute t d)
    (ht : IsTriangle D x y t) (hodd : Odd (orderOf (x * t * y))) : False := by
  obtain ⟨hxtD, hxt_ne_x, hxt_ne_t, hx_xt, ht_xt, hnc_yxt⟩ :=
    mul_mem_of_firstKind_triangle hD hN ht hodd
  have hd_ne_x : d ≠ x := fun h => ht.2.2.2.2.2.1 ((h ▸ hyd).symm)
  have hd_ne_t : d ≠ t := fun h => ht.2.2.2.2.2.2 ((h ▸ hyd).symm)
  have hd_ne_xt : d ≠ x * t := fun h => hnc_yxt (h ▸ hyd)
  exact false_of_four_commuting_of_widthLe_three hw hd ht.1 ht.2.1 hxtD
    hd_ne_x hd_ne_t hd_ne_xt ht.2.2.2.1 hxt_ne_x.symm hxt_ne_t.symm
    hxd.symm htd.symm (hxd.symm.mul_right htd.symm) ht.2.2.2.2.1 hx_xt ht_xt

theorem false_of_thirdKind_of_widthLe_three (hD : IsOddTransp D) (hN : IsNormalSet D)
    (hw : WidthLe D 3) {d x y t : G} (hd : d ∈ D)
    (hxd : Commute x d) (hyd : Commute y d) (htd : Commute t d)
    (ht : IsTriangle D x y t) (hthird : IsThirdKind x y t) : False := by
  obtain ⟨e, heD, he_ne_x, he_ne_t, hxe, hte, hnc_ey, hde⟩ :=
    exists_mem_of_thirdKind_triangle hD hN ht hthird
  have hd_ne_x : d ≠ x := fun h => ht.2.2.2.2.2.1 ((h ▸ hyd).symm)
  have hd_ne_t : d ≠ t := fun h => ht.2.2.2.2.2.2 ((h ▸ hyd).symm)
  have hd_ne_e : d ≠ e := fun h => hnc_ey (h ▸ hyd)
  exact false_of_four_commuting_of_widthLe_three hw hd ht.1 ht.2.1 heD
    hd_ne_x hd_ne_t hd_ne_e ht.2.2.2.1 he_ne_x.symm he_ne_t.symm
    hxd.symm htd.symm (hde d hxd htd hyd) ht.2.2.2.2.1 hxe hte

end

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem localSecond_of_widthLe_three (hD : IsOddTransp D) (hN : IsNormalSet D)
    (hw : WidthLe D 3) : LocalSecond D := by
  intro d hd x y t hxd hyd htd ht
  rcases IsTriangle.orderOf_cases hD hN ht with hfirst | hfour | hthird
  · exact (false_of_firstKind_of_widthLe_three hD hN hw hd hxd hyd htd ht hfirst.1).elim
  · exact hfour
  · exact (false_of_thirdKind_of_widthLe_three hD hN hw hd hxd hyd htd ht hthird).elim

theorem orderOf_mul_eq_four_of_threeTransp (hD : IsOddTransp D) (hN : IsNormalSet D)
    (h3 : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) {u w v : G}
    (ht : IsTriangle D u w v) : orderOf (u * v * w) = 4 := by
  have hdvd : orderOf (u * v * w) ∣ 2 ^ 2 := by
    simpa using orderOf_mul_dvd_four_of_threeTransposition hD h3 ht
  rcases IsTriangle.orderOf_cases hD hN ht with ⟨hodd, hgt⟩ | hfour | hthird
  · obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hk] at hodd
    cases k with
    | zero => rw [hk, pow_zero] at hgt; omega
    | succ k => exact absurd hodd (by simp [pow_succ, Nat.not_odd_iff_even])
  · exact hfour
  · obtain ⟨n, hn, hn1, hord⟩ := hthird
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hord] at hk
    have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk3 with rfl | rfl | rfl
    · norm_num at hk
    · norm_num at hk
      omega
    · norm_num at hk
      obtain ⟨j, hj⟩ := hn
      omega

theorem lemma8_3_of_theoremTwo (h2 : AschbacherTheoremTwo) (hS : Setup G D)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hw : WidthLe D 3) :
    (∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) ∨ QZ.O4PairData G D :=
  h2 G D hS hC (localSecond_of_widthLe_three hS.oddT hS.normal hw) hrad

theorem o4PairData_of_widthLe_three_of_thirdKind (h2 : AschbacherTheoremTwo) (hS : Setup G D)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hw : WidthLe D 3) {u w v : G} (ht : IsTriangle D u w v) (h3 : IsThirdKind u w v) :
    QZ.O4PairData G D := by
  rcases lemma8_3_of_theoremTwo h2 hS hC hrad hw with hthree | ho4
  · exfalso
    have h4 := orderOf_mul_eq_four_of_threeTransp hS.oddT hS.normal hthree ht
    obtain ⟨n, hn, hn1, hord⟩ := h3
    rw [h4] at hord
    obtain ⟨j, hj⟩ := hn
    omega
  · exact ho4

end CFSG.OddTranspositions.PartThree
