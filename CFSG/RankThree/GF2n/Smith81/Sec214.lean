module

public import CFSG.RankThree.GF2n.Smith81.Sec2Defs
public import CFSG.RankThree.GF2n.Tim81.FStarSimple
public import CFSG.RankThree.GF2n.Smith81.Bridge
public import CFSG.RankThree.GF2n.Smith81.TiFusion

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

section Dihedral

theorem isPGroup_closure_dihedral {x w : G} (hx : x * x = 1) (hw : w * w = 1)
    (h4 : orderOf (x * w) = 4) : IsPGroup 2 (Subgroup.closure ({x, w} : Set G)) := by
  set r := x * w with hr
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hr4 : r ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one r
  have hrinv : r⁻¹ = w * x := by rw [hr, mul_inv_rev, hxinv, hwinv]
  have hxrx : x * r * x⁻¹ = r⁻¹ := by
    rw [hrinv, hr, hxinv]
    calc x * (x * w) * x = (x * x) * w * x := by group
      _ = w * x := by rw [hx, one_mul]
  have hconj : ∀ k : ℤ, x * r ^ k * x = r ^ (-k) := by
    intro k
    have := conj_zpow (a := x) (b := r) (i := k)
    rw [hxrx, inv_zpow', hxinv] at this
    exact this.symm
  have hxr : ∀ j : ℤ, x * r ^ j = r ^ (-j) * x := by
    intro j
    calc x * r ^ j = (x * r ^ j * x) * x := by rw [mul_assoc (x * r ^ j) x x, hx, mul_one]
      _ = r ^ (-j) * x := by rw [hconj]
  have key : ∀ g ∈ Subgroup.closure ({x, w} : Set G), ∃ i : ℤ, g = r ^ i ∨ g = r ^ i * x := by
    intro g hg
    refine Subgroup.closure_induction
      (p := fun g _ => ∃ i : ℤ, g = r ^ i ∨ g = r ^ i * x) ?_ ?_ ?_ ?_ hg
    · rintro g (rfl | rfl)
      · exact ⟨0, Or.inr (by simp)⟩
      · refine ⟨-1, Or.inr ?_⟩
        rw [zpow_neg_one, hrinv, mul_assoc, hx, mul_one]
    · exact ⟨0, Or.inl (by simp)⟩
    · rintro a b _ _ ⟨i, rfl | rfl⟩ ⟨j, rfl | rfl⟩
      · exact ⟨i + j, Or.inl (zpow_add r i j).symm⟩
      · exact ⟨i + j, Or.inr (by rw [zpow_add, mul_assoc])⟩
      · refine ⟨i - j, Or.inr ?_⟩
        rw [mul_assoc, hxr, ← mul_assoc, ← zpow_add, sub_eq_add_neg]
      · refine ⟨i - j, Or.inl ?_⟩
        calc r ^ i * x * (r ^ j * x) = r ^ i * (x * r ^ j) * x := by group
          _ = r ^ i * (r ^ (-j) * x) * x := by rw [hxr]
          _ = r ^ i * r ^ (-j) * (x * x) := by group
          _ = r ^ (i - j) := by rw [hx, mul_one, ← zpow_add, sub_eq_add_neg]
    · rintro a _ ⟨i, rfl | rfl⟩
      · exact ⟨-i, Or.inl (zpow_neg r i).symm⟩
      · refine ⟨i, Or.inr ?_⟩
        calc (r ^ i * x)⁻¹ = x⁻¹ * (r ^ i)⁻¹ := mul_inv_rev _ _
          _ = x * r ^ (-i) := by rw [hxinv, ← zpow_neg]
          _ = r ^ i * x := by rw [hxr, neg_neg]
  intro g
  obtain ⟨i, hi | hi⟩ := key g.1 g.2
  · refine ⟨2, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, hi, show (2 : ℕ) ^ 2 = 4 by norm_num, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul]
    simp [hr4]
  · refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, hi]
    have hsq : (r ^ i * x) * (r ^ i * x) = 1 := by
      calc (r ^ i * x) * (r ^ i * x) = r ^ i * (x * r ^ i) * x := by group
        _ = r ^ i * (r ^ (-i) * x) * x := by rw [hxr]
        _ = r ^ i * r ^ (-i) * (x * x) := by group
        _ = 1 := by rw [hx, mul_one, ← zpow_add, add_neg_cancel, zpow_zero]
    simpa [pow_two] using hsq

end Dihedral

section Main

variable [Finite G] {M Q Z : Subgroup G}

open scoped Pointwise

theorem exists_conj_mem_M_of_isPGroup (H : StrothHyp M Q Z) {P : Subgroup G}
    (hP : IsPGroup 2 P) : ∃ g : G, ∀ p ∈ P, g⁻¹ * p * g ∈ M := by
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  obtain ⟨T, hTM, -⟩ := H.toTim81Hyp.exists_sylow_le_M
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  refine ⟨g, fun p hp => ?_⟩
  have hpS : p ∈ (S : Subgroup G) := hPS hp
  have hcoe : ((g • T : Sylow 2 G) : Subgroup G) = MulAut.conj g • (T : Subgroup G) :=
    Sylow.coe_subgroup_smul
  rw [← hg, hcoe, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hpS
  exact hTM hpS

end Main

section PowHalf

theorem commute_pow_half {x y : G} (hx : x * x = 1) (hy : y * y = 1) {k : ℕ}
    (hk : (x * y) ^ (2 * k) = 1) : Commute x ((x * y) ^ k) ∧ Commute y ((x * y) ^ k) := by
  set r := x * y with hr
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hxr : x * r * x⁻¹ = r⁻¹ := by
    rw [hr, mul_inv_rev, hxinv, hyinv]
    calc x * (x * y) * x = (x * x) * y * x := by group
      _ = y * x := by rw [hx, one_mul]
  have hyr : y * r * y⁻¹ = r⁻¹ := by
    rw [hr, mul_inv_rev, hxinv, hyinv]
    calc y * (x * y) * y = y * x * (y * y) := by group
      _ = y * x := by rw [hy, mul_one]
  have hkk : r ^ k * r ^ k = 1 := by rw [← pow_add, ← two_mul]; exact hk
  have hkinv : (r ^ k)⁻¹ = r ^ k := inv_eq_of_mul_eq_one_right hkk
  constructor
  · have h1 : x * r ^ k * x⁻¹ = r ^ k := by
      rw [← conj_pow, hxr, inv_pow, hkinv]
    exact (mul_inv_eq_iff_eq_mul.mp h1)
  · have h1 : y * r ^ k * y⁻¹ = r ^ k := by
      rw [← conj_pow, hyr, inv_pow, hkinv]
    exact (mul_inv_eq_iff_eq_mul.mp h1)

end PowHalf

section Fourteen

variable [Finite G] {M Q Z : Subgroup G}

theorem smith_2_14 (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (h212 : ∀ x : G, x ∈ M → x ∉ Q → IsConj z x → ∀ y ∈ cosetSet x Z, IsConj z y → y = x)
    (h213 : Timmesfeld.IsRootInvolutionSet (conjClassSet z ∩ (M : Set G)))
    {x y : G} (hx : IsConj z x) (hy : IsConj z y) (h4 : 4 ∣ orderOf (x * y)) :
    orderOf (x * y) = 4 ∧ IsConj z ((x * y) ^ 2) ∧
      ∀ A X Y : Subgroup G, IsZConjugate Z A → IsZConjugate Z X → IsZConjugate Z Y →
        (x * y) ^ 2 ∈ A → x ∈ X → y ∈ Y →
        {C : Subgroup G | IsZConjugate Z C ∧ C ≤ QB X ∧ C ≤ QB Y} = {A} := by
  classical
  have hxx := mul_self_eq_one_of_isConj_Z H hz hx
  have hyy := mul_self_eq_one_of_isConj_Z H hz hy
  obtain ⟨w, hww, hxw4, hxw2, d, hd, hwd⟩ := exists_dihedral_eight hxx hyy h4
  have hwc : IsConj z w := by
    rcases hwd with h | h
    · exact IsConj.trans hx (isConj_iff.mpr ⟨d, h.symm⟩)
    · exact IsConj.trans hy (isConj_iff.mpr ⟨d, h.symm⟩)
  obtain ⟨g, hg⟩ := exists_conj_mem_M_of_isPGroup H (isPGroup_closure_dihedral hxx hww hxw4)
  have hxM : g⁻¹ * x * g ∈ M := hg x (Subgroup.subset_closure (by simp))
  have hwM : g⁻¹ * w * g ∈ M := hg w (Subgroup.subset_closure (by simp))
  have hxc' : IsConj z (g⁻¹ * x * g) :=
    IsConj.trans hx (isConj_iff.mpr ⟨g⁻¹, by simp⟩)
  have hwc' : IsConj z (g⁻¹ * w * g) :=
    IsConj.trans hwc (isConj_iff.mpr ⟨g⁻¹, by simp⟩)
  have h4' : orderOf (g⁻¹ * x * g * (g⁻¹ * w * g)) = 4 := by
    have e : g⁻¹ * x * g * (g⁻¹ * w * g) = g⁻¹ * (x * w) * g⁻¹⁻¹ := by group
    rw [e, CFSG.Timmesfeld.CorB.orderOf_conj, hxw4]
  have hsq := h213.2.2 _ ⟨hxc', hxM⟩ _ ⟨hwc', hwM⟩ h4'
  have haxw : IsConj z ((x * w) ^ 2) := by
    have e : (x * w) ^ 2 = g * ((g⁻¹ * x * g * (g⁻¹ * w * g)) ^ 2) * g⁻¹ := by
      simp only [pow_two]; group
    rw [e]
    exact conjClassSet_conj hsq.1 g
  have haa : IsConj z ((x * y) ^ (orderOf (x * y) / 2)) := hxw2 ▸ haxw
  have hm2 : (x * y) ^ (2 * (orderOf (x * y) / 2)) = 1 := by
    rw [Nat.mul_div_cancel' (dvd_trans (by norm_num : 2 ∣ 4) h4)]
    exact pow_orderOf_eq_one _
  obtain ⟨hxa, hya⟩ := commute_pow_half hxx hyy hm2
  obtain ⟨c, hc⟩ := isConj_iff.mp haa
  set x'' := c⁻¹ * x * c with hx''
  set y'' := c⁻¹ * y * c with hy''
  have hxz : Commute x'' z := by
    show x'' * z = z * x''
    have h1 := hxa.eq
    rw [← hc] at h1
    calc x'' * z = c⁻¹ * (x * (c * z * c⁻¹)) * c := by rw [hx'']; group
      _ = c⁻¹ * ((c * z * c⁻¹) * x) * c := by rw [h1]
      _ = z * x'' := by rw [hx'']; group
  have hyz : Commute y'' z := by
    show y'' * z = z * y''
    have h1 := hya.eq
    rw [← hc] at h1
    calc y'' * z = c⁻¹ * (y * (c * z * c⁻¹)) * c := by rw [hy'']; group
      _ = c⁻¹ * ((c * z * c⁻¹) * y) * c := by rw [h1]
      _ = z * y'' := by rw [hy'']; group
  have hx''M : x'' ∈ M := mem_M_of_commute_Z H hz hz1 hxz.eq
  have hy''M : y'' ∈ M := mem_M_of_commute_Z H hz hz1 hyz.eq
  have hx''c : IsConj z x'' := IsConj.trans hx (isConj_iff.mpr ⟨c⁻¹, by simp [hx'']⟩)
  have hy''c : IsConj z y'' := IsConj.trans hy (isConj_iff.mpr ⟨c⁻¹, by simp [hy'']⟩)
  have hxx'' := mul_self_eq_one_of_isConj_Z H hz hx''c
  have hyy'' := mul_self_eq_one_of_isConj_Z H hz hy''c
  have hord : orderOf (x'' * y'') = orderOf (x * y) := by
    have e : x'' * y'' = c⁻¹ * (x * y) * c⁻¹⁻¹ := by rw [hx'', hy'']; group
    rw [e, CFSG.Timmesfeld.CorB.orderOf_conj]
  have hm4 : orderOf (x * y) = 4 := by
    have h := h213.2.1 x'' ⟨hx''c, hx''M⟩ y'' ⟨hy''c, hy''M⟩
    rw [hord] at h
    obtain ⟨k, hk⟩ := h4
    rcases h with h | h | ⟨j, hj⟩
    · omega
    · exact h
    · omega
  have hhalf : (x * y) ^ (orderOf (x * y) / 2) = (x * y) ^ 2 := by rw [hm4]
  have hsqz : (x'' * y'') ^ 2 = z := by
    have e : (x'' * y'') ^ 2 = c⁻¹ * (x * y) ^ 2 * c := by
      rw [hx'', hy'']; simp only [pow_two]; group
    rw [e, ← hhalf, ← hc]; group
  have hxyz : x'' * y'' * x'' * y'' = z := by rw [← hsqz, pow_two]; group
  have hz1' : z ≠ 1 := hz1
  have hxQ : x'' ∈ Q := by
    by_contra hxQ
    have e : x'' * z = y'' * x'' * y''⁻¹ := by
      have hyinv : y''⁻¹ = y'' := inv_eq_of_mul_eq_one_right hyy''
      rw [hyinv]
      calc x'' * z = x'' * (x'' * y'' * x'' * y'') := by rw [hxyz]
        _ = (x'' * x'') * y'' * x'' * y'' := by group
        _ = y'' * x'' * y'' := by rw [hxx'', one_mul]
    have hconj : IsConj z (x'' * z) := by
      rw [e]
      exact IsConj.trans hx''c (isConj_iff.mpr ⟨y'', rfl⟩)
    have := h212 x'' hx''M hxQ hx''c (x'' * z) ⟨z, hz, rfl⟩ hconj
    exact hz1 (mul_left_cancel (this.trans (mul_one x'').symm))
  have hyQ : y'' ∈ Q := by
    by_contra hyQ
    have e : y'' * z = x'' * y'' * x''⁻¹ := by
      have hxinv : x''⁻¹ = x'' := inv_eq_of_mul_eq_one_right hxx''
      rw [hxinv]
      have h1 : x'' * y'' * x'' = z * y'' := by
        have hyinv : y''⁻¹ = y'' := inv_eq_of_mul_eq_one_right hyy''
        calc x'' * y'' * x'' = (x'' * y'' * x'' * y'') * y''⁻¹ := by group
          _ = z * y'' := by rw [hxyz, hyinv]
      rw [h1]
      exact hyz.eq
    have hconj : IsConj z (y'' * z) := by
      rw [e]
      exact IsConj.trans hy''c (isConj_iff.mpr ⟨x'', rfl⟩)
    have := h212 y'' hy''M hyQ hy''c (y'' * z) ⟨z, hz, rfl⟩ hconj
    exact hz1 (mul_left_cancel (this.trans (mul_one y'').symm))
  refine ⟨hm4, ?_, ?_⟩
  · rw [← hhalf]
    exact haa
  · intro A X Y hA hX hY haA hxX hyY
    have hx1 : x ≠ 1 := ne_one_of_isConj_Z hz1 hx
    have hy1 : y ≠ 1 := ne_one_of_isConj_Z hz1 hy
    have ha1 : (x * y) ^ 2 ≠ 1 := by rw [← hhalf]; exact ne_one_of_isConj_Z hz1 haa
    have hacz : (x * y) ^ 2 ∈ conjSubgroup c Z := by
      rw [← hhalf, ← hc, mem_conjSubgroup]
      simpa [mul_assoc] using hz
    have hAc : A = conjSubgroup c Z := hA.eq_of_mem H ⟨c, rfl⟩ ha1 haA hacz
    have hxQA : x ∈ QB A := by
      rw [hAc, QB_conj_eq H c, mem_conjSubgroup]
      exact hxQ
    have hyQA : y ∈ QB A := by
      rw [hAc, QB_conj_eq H c, mem_conjSubgroup]
      exact hyQ
    have hXA : X ≤ QB A := hA.le_QB_of_mem H hX hx1 hxX hxQA
    have hYA : Y ≤ QB A := hA.le_QB_of_mem H hY hy1 hyY hyQA
    have hAX : A ≤ QB X := (hA.le_QB_iff H hX).mp hXA
    have hAY : A ≤ QB Y := (hA.le_QB_iff H hY).mp hYA
    ext C
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hC, hCX, hCY⟩
      have hXC : X ≤ QB C := (hC.le_QB_iff H hX).mpr hCX
      have hYC : Y ≤ QB C := (hC.le_QB_iff H hY).mpr hCY
      have hcomm : ⁅x, y⁆ ∈ C := hC.comm_mem_QB H (hXC hxX) (hYC hyY)
      have hxy : ⁅x, y⁆ = (x * y) ^ 2 := by
        have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
        have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
        rw [commutatorElement_def, hxinv, hyinv, pow_two]
        group
      rw [hxy] at hcomm
      exact (hC.eq_of_mem H hA ha1 hcomm haA)
    · rintro rfl
      exact ⟨hA, hAX, hAY⟩

end Fourteen

end CFSG.RankThree.GF2n.Smith81
