module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Defs
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.JFacts
import CFSG.CGT.PushingUpLit.SYMB.ProdCard

public section

namespace CFSG.StandardType.FF81.CatQ1

open CFSG.Open
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private theorem fixedSubgroup_eq_sup {K : Type} [Group K] (β : MulAut K)
    (O J : Subgroup K) (hfix : ∀ x : K, x ∈ O ⊔ J ↔ β x = x) :
    fixedSubgroup β = O ⊔ J := by
  ext x
  exact (hfix x).symm

private theorem card_sup_eq_mul_card {K : Type} [Group K] (O J : Subgroup K)
    (hdisj : O ⊓ J = ⊥) (hcomm : ∀ x ∈ O, ∀ y ∈ J, x * y = y * x) :
    Nat.card ↥(O ⊔ J) = Nat.card ↥O * Nat.card ↥J := by
  have h := CFSG.CGT.PushingUpLit.SYMB.card_sup_mul_card_inf_of_commute (C := O) (D := J) hcomm
  rw [hdisj, Subgroup.card_bot, mul_one] at h
  exact h

private theorem exists_mul_of_mem_sup_of_commute {K : Type} [Group K] {H J : Subgroup K}
    (hcomm : ∀ x ∈ H, ∀ y ∈ J, x * y = y * x) {x : K} (hx : x ∈ H ⊔ J) :
    ∃ h ∈ H, ∃ j ∈ J, x = h * j := by
  have hcent : H ≤ Subgroup.centralizer (J : Set K) := fun h hh =>
    Subgroup.mem_centralizer_iff.mpr fun j hj => (hcomm h hh j hj).symm
  have hnorm : H ≤ Subgroup.normalizer (J : Set K) :=
    hcent.trans (Subgroup.centralizer_le_normalizer (J : Set K))
  have hx' : x ∈ ((H ⊔ J : Subgroup K) : Set K) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right H J hnorm] at hx'
  obtain ⟨h, hh, j, hj, rfl⟩ := hx'
  exact ⟨h, hh, j, hj, rfl⟩

theorem not_fixedTooBig_of_product {K : Type} [Group K] [Finite K] (β : MulAut K)
    (O J : Subgroup K) (hfix : ∀ x : K, x ∈ O ⊔ J ↔ β x = x) (hdisj : O ⊓ J = ⊥)
    (hcomm : ∀ x ∈ O, ∀ y ∈ J, x * y = y * x) (hO : Nat.Coprime (Nat.card O) 3)
    (hJ : StatedClassicalModel J .PSL 4 2 1 ∨ StatedClassicalModel J .PSL 5 2 1) :
    ¬ FixedTooBig β := by
  unfold FixedTooBig
  rintro (h27 | hnot | ⟨x, hx, hx9⟩)
  ·
    rw [fixedSubgroup_eq_sup β O J hfix, card_sup_eq_mul_card O J hdisj hcomm] at h27
    have hcop : Nat.Coprime 27 (Nat.card O) := by
      have h := (hO.pow_right 3).symm
      norm_num at h
      exact h
    exact not_twentySeven_dvd_card_of_modelJ ↥J hJ (hcop.dvd_of_dvd_mul_left h27)
  ·
    have hle : J ≤ fixedSubgroup β := by
      rw [fixedSubgroup_eq_sup β O J hfix]
      exact le_sup_right
    exact hnot ((twentyThousand_dvd_card_of_modelJ ↥J hJ).trans
      (Subgroup.card_dvd_of_le hle))
  ·
    obtain ⟨o, ho, j, hj, rfl⟩ :=
      exists_mul_of_mem_sup_of_commute hcomm ((hfix x).mpr hx)
    have hcommute : Commute o j := hcomm o ho j hj
    have h9 : (o * j) ^ 9 = 1 := by
      rw [← hx9]
      exact pow_orderOf_eq_one (o * j)
    have hmul : o ^ 9 * j ^ 9 = 1 := by
      rw [← hcommute.mul_pow 9]
      exact h9
    have ho9 : o ^ 9 = 1 := by
      have hmem : o ^ 9 ∈ O ⊓ J := by
        refine ⟨O.pow_mem ho 9, ?_⟩
        rw [eq_inv_of_mul_eq_one_left hmul]
        exact J.inv_mem (J.pow_mem hj 9)
      rwa [hdisj, Subgroup.mem_bot] at hmem
    have hcop9 : Nat.Coprime (Nat.card O) 9 := by
      have h := hO.pow_right 2
      norm_num at h
      exact h
    have hone : orderOf o ∣ 1 := by
      have h := Nat.dvd_gcd (Subgroup.orderOf_dvd_natCard O ho)
        (orderOf_dvd_iff_pow_eq_one.mpr ho9)
      rwa [hcop9.gcd_eq_one] at h
    have ho_eq_one : o = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hone)
    have hj9 : orderOf j = 9 := by
      rw [ho_eq_one] at hx9
      simpa using hx9
    exact orderOf_ne_nine_of_modelJ ↥J hJ ⟨j, hj⟩ (by rw [Subgroup.orderOf_mk]; exact hj9)

end CFSG.StandardType.FF81.CatQ1

end
