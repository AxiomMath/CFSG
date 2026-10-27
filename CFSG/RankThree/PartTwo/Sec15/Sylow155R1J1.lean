module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1AutDefs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1J1Lem
public import CFSG.Quasithin.H13.NQCatT513J1

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.Blueprint

theorem res1J1_no_order_21
    (g : NativeSporadic.J1) :
    orderOf g ≠ 21 := by
  rw [← MulEquiv.orderOf_eq CFSG.Sporadic.J1.nativeEquiv g]
  exact CFSG.Quasithin.H13.NQCat.T513P.j1J_no_order_21 _

theorem res1AutCent_J1 :
    Res1AutCent NativeSporadic.J1 := by
  intro α V y hy hα hαy hV hαV _
  have hfin : Finite NativeSporadic.J1 := CFSG.Sporadic.J1.fam_j1_simplicity.1
  haveI := CFSG.Sporadic.Schreier.finite_mulAut_J1
  have hout := (CFSG.Sporadic.Schreier.at_j1_schreier).2.1
  have hsurj : Function.Surjective
      (MulAut.conj : NativeSporadic.J1 →* MulAut NativeSporadic.J1) := fun φ => by
    obtain ⟨g, hg⟩ := hout φ
    exact ⟨g, hg.symm⟩
  have hdvdAut : Nat.card (MulAut NativeSporadic.J1) ∣ 175560 := by
    have h := Subgroup.card_dvd_of_surjective hsurj
    rwa [CFSG.Sporadic.J1.card_J1] at h
  have hV8 : Nat.card V ∣ 8 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := V)).1 hV
    have h1 : Nat.card V ∣ 8 * 21945 := by
      have := (Subgroup.card_subgroup_dvd_card V).trans hdvdAut
      simpa using this
    rw [hk] at h1 ⊢
    exact (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 21945)).dvd_of_dvd_mul_right h1
  obtain ⟨x, rfl⟩ := hout α
  have hxy : Commute x y := by
    have h : x * y * x⁻¹ = y := by simpa [MulAut.conj_apply] using hαy
    exact mul_inv_eq_iff_eq_mul.1 h
  have h7 : ¬ 7 ∣ orderOf (MulAut.conj x) := by
    intro h7
    have hx7 : 7 ∣ orderOf x :=
      h7.trans (orderOf_map_dvd (MulAut.conj : NativeSporadic.J1 →* MulAut NativeSporadic.J1) x)
    have hord : orderOf (x ^ (orderOf x / 7)) = 7 :=
      orderOf_pow_orderOf_div (orderOf_pos x).ne' hx7
    have hcomm : Commute (x ^ (orderOf x / 7)) y := hxy.pow_left _
    have hco : (orderOf (x ^ (orderOf x / 7))).Coprime (orderOf y) := by
      rw [hord, hy] <;> norm_num
    have h21 : orderOf (x ^ (orderOf x / 7) * y) = 21 := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco, hord, hy] <;> norm_num
    exact res1J1_no_order_21 _ h21
  have h67 : Nat.Coprime (orderOf (MulAut.conj x)) (6 * 7) :=
    Nat.Coprime.mul_right hα ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h7).symm
  exact res1J1_centralizes_of_pow_eq_one hV8 hαV (pow_orderOf_eq_one _) h67

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
