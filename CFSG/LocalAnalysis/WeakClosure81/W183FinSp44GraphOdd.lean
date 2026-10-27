module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Emb
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Klein
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44DataOdd
public import CFSG.Timmesfeld.Bridge.Asc72Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSp4)

namespace Sp44

private def w183finSp44_oddData_valid : Bool :=
  oddData.all fun e =>
    validB ((e.2.2.1, e.2.2.2.1) : El) && validB ((e.2.2.2.2.1, e.2.2.2.2.2) : El)

private theorem w183finSp44_oddData_valid_eq : w183finSp44_oddData_valid = true := by
  decide +kernel

private theorem w183finSp44_validB_powE {x : El} (hx : validB x = true) :
    ∀ n, validB (powE n x) = true
  | 0 => validB_oneE
  | n + 1 => validB_gmulE hx (w183finSp44_validB_powE hx n)

private theorem w183finSp44_autOf_powE {x : El} (hx : validB x = true) :
    ∀ n, autOf (powE n x) = autOf x ^ n
  | 0 => by rw [powE, pow_zero, autOf_oneE]
  | n + 1 => by
      rw [powE, autOf_gmulE hx (w183finSp44_validB_powE hx n),
        w183finSp44_autOf_powE hx n, pow_succ']

private theorem w183finSp44_autOf_oddRow {a w wi c : El}
    (ha : validB a = true) (hw : validB w = true) (hwi : validB wi = true)
    (hwwi : gmulE w wi = oneE) (hc : c = gmulE a (gmulE wi (gmulE a w))) :
    autOf c = autOf a * ((autOf w)⁻¹ * autOf a * autOf w) := by
  have haw : validB (gmulE a w) := validB_gmulE ha hw
  have hwiaw : validB (gmulE wi (gmulE a w)) := validB_gmulE hwi haw
  have hwwi_aut : autOf w * autOf wi = 1 := by
    rw [← autOf_gmulE hw hwi, hwwi, autOf_oneE]
  have hwi_inv : autOf wi = (autOf w)⁻¹ := eq_inv_of_mul_eq_one_right hwwi_aut
  rw [hc, autOf_gmulE ha hwiaw, autOf_gmulE hwi haw, autOf_gmulE ha hw, hwi_inv]
  group

private theorem w183finSp44_eq_of_dvd4 {n : Nat} (hdvd : n ∣ 4) (h1 : n ≠ 1) (h2 : n ≠ 2) :
    n = 4 := by
  have hle : n ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases n
  · norm_num at hdvd
  · omega
  · omega
  · norm_num at hdvd
  · rfl

private theorem w183finSp44_eq_of_dvd6 {n : Nat} (hdvd : n ∣ 6) (h1 : n ≠ 1) (h2 : n ≠ 2)
    (h3 : n ≠ 3) : n = 6 := by
  have hle : n ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases n
  · norm_num at hdvd
  · omega
  · omega
  · omega
  · norm_num at hdvd
  · norm_num at hdvd
  · rfl

private theorem w183finSp44_eq_of_dvd10 {n : Nat} (hdvd : n ∣ 10) (h1 : n ≠ 1) (h2 : n ≠ 2)
    (h5 : n ≠ 5) : n = 10 := by
  have hle : n ≤ 10 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases n
  · norm_num at hdvd
  · omega
  · omega
  · norm_num at hdvd
  · norm_num at hdvd
  · omega
  · norm_num at hdvd
  · norm_num at hdvd
  · norm_num at hdvd
  · norm_num at hdvd
  · rfl

private theorem w183finSp44_orderOf_autOf_odd {a w wi c : El}
    (ha : validB a = true) (hw : validB w = true) (hwi : validB wi = true)
    (hc : c = gmulE a (gmulE wi (gmulE a w)))
    (h2 : powE 2 c ≠ oneE)
    (h4 : powE 4 c = oneE ∨ (powE 6 c = oneE ∧ powE 3 c ≠ oneE) ∨
      (powE 10 c = oneE ∧ powE 5 c ≠ oneE)) :
    orderOf (autOf c) ∈ ({4, 6, 10} : Finset Nat) := by
  have hcval : validB c = true := by
    rw [hc]
    exact validB_gmulE ha (validB_gmulE hwi (validB_gmulE ha hw))
  have h2' : (autOf c) ^ 2 ≠ 1 := by
    intro h
    apply h2
    apply autOf_inj (w183finSp44_validB_powE hcval 2) validB_oneE
    rw [w183finSp44_autOf_powE hcval 2, h, autOf_oneE]
  have hne1 : orderOf (autOf c) ≠ 1 := by
    intro h
    have hc1 : autOf c = 1 := by
      have := pow_orderOf_eq_one (autOf c)
      rwa [h, pow_one] at this
    exact h2' (by rw [hc1, one_pow])
  have hne2 : orderOf (autOf c) ≠ 2 := by
    intro h
    exact h2' (by rw [← h]; exact pow_orderOf_eq_one _)
  rcases h4 with h4 | ⟨h6, h6'⟩ | ⟨h10, h10'⟩
  · have hdvd : orderOf (autOf c) ∣ 4 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      rw [← w183finSp44_autOf_powE hcval 4, h4, autOf_oneE]
    have h4eq : orderOf (autOf c) = 4 := w183finSp44_eq_of_dvd4 hdvd hne1 hne2
    rw [h4eq]
    simp
  · have hdvd : orderOf (autOf c) ∣ 6 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      rw [← w183finSp44_autOf_powE hcval 6, h6, autOf_oneE]
    have hne3 : orderOf (autOf c) ≠ 3 := by
      intro h
      apply h6'
      apply autOf_inj (w183finSp44_validB_powE hcval 3) validB_oneE
      rw [w183finSp44_autOf_powE hcval 3, ← h, pow_orderOf_eq_one, autOf_oneE]
    have h6eq : orderOf (autOf c) = 6 := w183finSp44_eq_of_dvd6 hdvd hne1 hne2 hne3
    rw [h6eq]
    simp
  · have hdvd : orderOf (autOf c) ∣ 10 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      rw [← w183finSp44_autOf_powE hcval 10, h10, autOf_oneE]
    have hne5 : orderOf (autOf c) ≠ 5 := by
      intro h
      apply h10'
      apply autOf_inj (w183finSp44_validB_powE hcval 5) validB_oneE
      rw [w183finSp44_autOf_powE hcval 5, ← h, pow_orderOf_eq_one, autOf_oneE]
    have h10eq : orderOf (autOf c) = 10 := w183finSp44_eq_of_dvd10 hdvd hne1 hne2 hne5
    rw [h10eq]
    simp

theorem involution_conj_even_product (α : MulAut S4) (hα : orderOf α = 2) :
    ∃ β : MulAut S4, IsConj α β ∧ ¬ (orderOf (α * β) ∣ 2 ∨ Odd (orderOf (α * β))) := by
  obtain ⟨k, x, hx, hxaut⟩ := exists_conj_invs α hα
  have hcover : (oddData.any fun e => (e.1, e.2.1) == x) = true :=
    List.all_eq_true.mp oddData_cover x hx
  obtain ⟨e, he, hxe⟩ := List.any_eq_true.mp hcover
  have hxe' : (e.1, e.2.1) = x := beq_iff_eq.mp hxe
  have hxPel : x ∈ Pel := (List.mem_filter.mp hx).1
  have hvalrow :
      (validB ((e.2.2.1, e.2.2.2.1) : El) && validB ((e.2.2.2.2.1, e.2.2.2.2.2) : El)) =
        true :=
    List.all_eq_true.mp w183finSp44_oddData_valid_eq e he
  let a : El := (e.1, e.2.1)
  let w : El := (e.2.2.1, e.2.2.2.1)
  let wi : El := (e.2.2.2.2.1, e.2.2.2.2.2)
  let c : El := gmulE a (gmulE wi (gmulE a w))
  have haval : validB a = true := by
    change validB ((e.1, e.2.1) : El) = true
    rw [hxe']
    exact Pel_valid x hxPel
  have hwval : validB w = true := by
    change validB ((e.2.2.1, e.2.2.2.1) : El) = true
    exact (Bool.and_eq_true_iff.mp hvalrow).1
  have hwival : validB wi = true := by
    change validB ((e.2.2.2.2.1, e.2.2.2.2.2) : El) = true
    exact (Bool.and_eq_true_iff.mp hvalrow).2
  have hraw := List.all_eq_true.mp oddData_check e he
  simp only [checkOdd, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at hraw
  obtain ⟨⟨⟨⟨-, -⟩, hwwi⟩, h2⟩, h4⟩ := hraw
  rw [or_assoc] at h4
  have hc : c = gmulE a (gmulE wi (gmulE a w)) := rfl
  have hcaut : autOf c = autOf a * ((autOf w)⁻¹ * autOf a * autOf w) :=
    w183finSp44_autOf_oddRow haval hwval hwival hwwi hc
  have hmem : orderOf (autOf c) ∈ ({4, 6, 10} : Finset Nat) :=
    w183finSp44_orderOf_autOf_odd haval hwval hwival hc h2 h4
  have hnotdvd : ¬ orderOf (autOf c) ∣ 2 := by
    have h := hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h <;> rw [h] <;> norm_num
  have heven : Even (orderOf (autOf c)) := by
    have h := hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h <;> rw [h] <;> norm_num
  have hauta : autOf a = autOf x := by
    change autOf ((e.1, e.2.1) : El) = autOf x
    rw [hxe']
  have hauta' : autOf a = k * α * k⁻¹ := by
    rw [hauta]
    exact hxaut.symm
  have hα_eq : α = k⁻¹ * autOf a * k := by
    rw [hauta']
    group
  refine ⟨k⁻¹ * ((autOf w)⁻¹ * autOf a * autOf w) * k, ?_, ?_⟩
  · rw [isConj_iff]
    refine ⟨k⁻¹ * (autOf w)⁻¹ * k, ?_⟩
    rw [hα_eq]
    group
  · have hprod : α * (k⁻¹ * ((autOf w)⁻¹ * autOf a * autOf w) * k) =
        MulAut.conj k⁻¹ (autOf a * ((autOf w)⁻¹ * autOf a * autOf w)) := by
      rw [hα_eq, MulAut.conj_apply]
      group
    have hord : orderOf (α * (k⁻¹ * ((autOf w)⁻¹ * autOf a * autOf w) * k)) =
        orderOf (autOf c) := by
      rw [hprod, hcaut]
      exact (MulAut.conj k⁻¹).orderOf_eq _
    rw [hord, not_or]
    exact ⟨hnotdvd, Nat.not_odd_iff_even.mpr heven⟩

end Sp44

theorem finGraphOddSp44_holds :
    ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → IsSp4 ↥L 2 →
      Subgroup.centralizer (L : Set Y) = ⊥ → (∃ τ : Y, ActsOnDynkinMod ⊥ L τ) →
      ∀ a : Y, orderOf a = 2 →
        ¬ CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : Y | IsConj a x} := by
  intro Y _ _ L hLn hSp hC hτ a ha
  intro hOT
  obtain ⟨f, hfinj, hL⟩ := Sp44.exists_emb Y L hLn hSp hC
  have hfbij : Function.Bijective f := Sp44.emb_bijective Y L f hfinj hL hτ
  have hα : orderOf (f a) = 2 := by
    rw [← ha]
    exact orderOf_injective f hfinj a
  obtain ⟨β, hconj, hβ⟩ := Sp44.involution_conj_even_product (f a) hα
  obtain ⟨b, hb⟩ := hfbij.2 β
  have hconj' : IsConj (f a) (f b) := by rwa [← hb] at hconj
  let e := MulEquiv.ofBijective f hfbij
  have hconj_ab : IsConj a b := by
    have h := (e.symm.toMonoidHom).map_isConj (show IsConj (e a) (e b) from hconj')
    simpa using h
  have hord : orderOf (f a * f b) = orderOf (a * b) := by
    rw [← map_mul]
    exact orderOf_injective f hfinj (a * b)
  have hord' : orderOf (f a * β) = orderOf (a * b) := by
    rw [← hb]
    exact hord
  have hnot' : ¬ (orderOf (a * b) ∣ 2 ∨ Odd (orderOf (a * b))) := by
    rw [hord'] at hβ
    exact hβ
  exact hnot' (hOT.2 a (IsConj.refl a) b hconj_ab)

end CFSG.LocalAnalysis.WeakClosure81

end
