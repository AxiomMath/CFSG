module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemL43Classify
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenM12
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemL43

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] noncomputable def uZeroSL : SL4 := phiHom (Multiplicative.ofAdd ![1, 0, 0])

@[expose] noncomputable def vZeroSL : SL4 := phiHom (Multiplicative.ofAdd ![0, 1, 0])

theorem coe_uZeroSL : (uZeroSL : Mat4) = p0Mat 1 0 0 := phiMat_u

theorem coe_vZeroSL : (vZeroSL : Mat4) = p0Mat 0 1 0 := phiMat_v

theorem uZeroSL_mem : uZeroSL ∈ pZeroGrp := ⟨_, rfl⟩

theorem vZeroSL_mem : vZeroSL ∈ pZeroGrp := ⟨_, rfl⟩

theorem zSL_mem_pZeroGrp : zSL ∈ pZeroGrp := mem_pZeroGrp_iff.mpr (by decide)

theorem coe_uZeroSL_inv : ((uZeroSL⁻¹ : SL4) : Mat4) = uDualᵀ := by
  have h : uZeroSL * ⟨uDualᵀ, det_dual_transpose.1⟩ = 1 := Subtype.ext (by
    change (uZeroSL : Mat4) * uDualᵀ = 1
    rw [coe_uZeroSL]
    exact mul_dual_transpose.1)
  rw [inv_eq_of_mul_eq_one_right h]

theorem coe_vZeroSL_inv : ((vZeroSL⁻¹ : SL4) : Mat4) = vDualᵀ := by
  have h : vZeroSL * ⟨vDualᵀ, det_dual_transpose.2.1⟩ = 1 := Subtype.ext (by
    change (vZeroSL : Mat4) * vDualᵀ = 1
    rw [coe_vZeroSL]
    exact mul_dual_transpose.2.1)
  rw [inv_eq_of_mul_eq_one_right h]

theorem coe_zSL_inv : ((zSL⁻¹ : SL4) : Mat4) = zDualᵀ := by
  have h : zSL * ⟨zDualᵀ, det_dual_transpose.2.2⟩ = 1 := Subtype.ext mul_dual_transpose.2.2
  rw [inv_eq_of_mul_eq_one_right h]

theorem eq_of_proj_eq_of_pow_three {g g' : SL4} (hg : g ^ 3 = 1) (hg' : g' ^ 3 = 1)
    (h : piL g = piL g') : g = g' := by
  rw [proj_eq_proj_iff] at h
  have hcZ : g⁻¹ * g' ∈ Subgroup.center SL4 := scalars_le_center 4 (ZMod 3) h
  have hgc : Commute g (g⁻¹ * g') := Subgroup.mem_center_iff.mp hcZ g
  have h3 : (g⁻¹ * g') ^ 3 = 1 := by
    have e : g' = g * (g⁻¹ * g') := by group
    have e3 : g' ^ 3 = g ^ 3 * (g⁻¹ * g') ^ 3 := by
      conv_lhs => rw [e]
      exact hgc.mul_pow 3
    rw [hg, hg', one_mul] at e3
    exact e3.symm
  have hc1 := eq_one_of_mem_scalars_of_pow_three h h3
  rw [inv_mul_eq_one] at hc1
  exact hc1

theorem fieldAut_eq_one (σ : ZMod 3 ≃+* ZMod 3) : fieldAut 4 (ZMod 3) σ = 1 := by
  have hσ : σ = 1 := RingEquiv.ext fun x => by
    have h := RingHom.ext_zmod σ.toRingHom (RingHom.id (ZMod 3))
    exact congrArg (fun f : ZMod 3 →+* ZMod 3 => f x) h
  rw [hσ, map_one]

theorem pow_four_eq_one {x : ZMod 3} (hx : x ≠ 0) : x ^ 4 = 1 := by
  revert x
  decide

theorem comm_of_conjAut_fix {A : GL (Fin 4) (ZMod 3)} {g : SL4} (hg : g ^ 3 = 1)
    (h : conjAut 4 (ZMod 3) A (piL g) = piL g) : (A : Mat4) * (g : Mat4) = (g : Mat4) * A := by
  rw [conjAut_proj] at h
  have hc3 : (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 (ZMod 3)
      A g) ^ 3 = 1 := by
    rw [← map_pow, hg, map_one]
  have heq := eq_of_proj_eq_of_pow_three hc3 hg h
  have hm := congrArg (fun x : SL4 => (x : Mat4)) heq
  simp only [coe_slConjugation] at hm
  calc (A : Mat4) * (g : Mat4) = (A : Mat4) * (g : Mat4) * (((A⁻¹ : GL (Fin 4) (ZMod 3)) : Mat4) *
        (A : Mat4)) := by
          rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
            Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one]
    _ = (g : Mat4) * A := by rw [← Matrix.mul_assoc, hm]

theorem dual_of_fix {A : GL (Fin 4) (ZMod 3)} {g : SL4} (hg : g ^ 3 = 1)
    (h : conjAut 4 (ZMod 3) A (dualAut 4 (ZMod 3) (piL g)) = piL g) :
    (A : Mat4) * ((g⁻¹ : SL4) : Mat4)ᵀ = (g : Mat4) * A := by
  rw [dualAut_proj, conjAut_proj] at h
  have hd3 : ((g⁻¹).transpose : SL4) ^ 3 = 1 := by
    have e : ((g⁻¹).transpose : SL4) =
        CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 4 (ZMod 3) g := rfl
    rw [e, ← map_pow, hg, map_one]
  have hc3 : (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 (ZMod 3)
      A (g⁻¹).transpose) ^ 3 = 1 := by
    rw [← map_pow, hd3, map_one]
  have heq := eq_of_proj_eq_of_pow_three hc3 hg h
  have hm := congrArg (fun x : SL4 => (x : Mat4)) heq
  simp only [coe_slConjugation, SpecialLinearGroup.coe_transpose] at hm
  calc (A : Mat4) * ((g⁻¹ : SL4) : Mat4)ᵀ = (A : Mat4) * ((g⁻¹ : SL4) : Mat4)ᵀ *
        (((A⁻¹ : GL (Fin 4) (ZMod 3)) : Mat4) * (A : Mat4)) := by
          rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
            Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one]
    _ = (g : Mat4) * A := by rw [← Matrix.mul_assoc, hm]

theorem mem_range_conj_of_fix (α : MulAut PSL43) (hα : ∀ f ∈ pZeroGrp.map piL, α f = f) :
    α ∈ (MulAut.conj : PSL43 →* MulAut PSL43).range := by
  obtain ⟨-, hform⟩ := automorphism_generation (n := 4) (K := ZMod 3) (by norm_num)
  obtain ⟨A, σ, ε, hε, rfl⟩ := hform α
  rw [fieldAut_eq_one, mul_one] at hα ⊢
  have hu3 : uZeroSL ^ 3 = 1 := isElemAbelian_pZeroGrp.2 _ uZeroSL_mem
  have hv3 : vZeroSL ^ 3 = 1 := isElemAbelian_pZeroGrp.2 _ vZeroSL_mem
  have hz3 : zSL ^ 3 = 1 := zSL_pow_three
  have hfu := hα _ ⟨uZeroSL, uZeroSL_mem, rfl⟩
  have hfv := hα _ ⟨vZeroSL, vZeroSL_mem, rfl⟩
  have hfz := hα _ ⟨zSL, zSL_mem_pZeroGrp, rfl⟩
  have hdetA : (A : Mat4).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  ·
    rw [pow_zero, mul_one] at hfu hfv hfz ⊢
    have hAu := comm_of_conjAut_fix hu3 hfu
    have hAv := comm_of_conjAut_fix hv3 hfv
    rw [coe_uZeroSL] at hAu
    rw [coe_vZeroSL] at hAv
    have hA := eq_o1Mat_of_comm hAu hAv
    have hdet1 : (A : Mat4).det = 1 := by
      rw [hA, det_o1Mat] at hdetA ⊢
      exact pow_four_eq_one fun h0 => hdetA (by rw [h0]; decide)
    obtain ⟨g, hgv⟩ : ∃ g : SL4, (g : Mat4) = (A : Mat4) := ⟨⟨(A : Mat4), hdet1⟩, rfl⟩
    have hgA : SpecialLinearGroup.toGL g = A := Units.ext (by
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      exact hgv)
    refine ⟨piL g, ?_⟩
    rw [KFacts.conj_proj_eq_conjAut, hgA]
  ·
    exfalso
    rw [pow_one] at hfu hfv hfz
    have hAu := dual_of_fix hu3 hfu
    have hAv := dual_of_fix hv3 hfv
    have hAz := dual_of_fix hz3 hfz
    rw [coe_uZeroSL_inv, Matrix.transpose_transpose, coe_uZeroSL] at hAu
    rw [coe_vZeroSL_inv, Matrix.transpose_transpose, coe_vZeroSL] at hAv
    rw [coe_zSL_inv, Matrix.transpose_transpose] at hAz
    obtain ⟨h0, h1, h2, h3⟩ := row_three_eq_zero_of_dual hAu hAv hAz
    apply hdetA
    refine Matrix.det_eq_zero_of_row_eq_zero 3 fun j => ?_
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3

theorem card_map_of_injOn {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {H : Subgroup X}
    (h : ∀ x ∈ H, ∀ y ∈ H, f x = f y → x = y) : Nat.card (H.map f) = Nat.card H := by
  have hinj : Function.Injective (f.comp H.subtype) := fun a b hab =>
    Subtype.ext (h a a.2 b b.2 hab)
  have hmap : H.map f = (f.comp H.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hmap]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

theorem card_map_piL_of_le {H : Subgroup SL4} (hH : H ≤ unitriangular 4 (ZMod 3)) :
    Nat.card (H.map piL) = Nat.card H :=
  card_map_of_injOn piL fun _ hx _ hy hxy => proj_injOn_unitriangular 4 (hH hx) (hH hy) hxy

theorem eq_bot_of_le_normalizer {W : Subgroup PSL43} (hW3 : ¬ 3 ∣ Nat.card W)
    (hN : pZeroGrp.map piL ≤ Subgroup.normalizer (W : Set PSL43)) : W = ⊥ := by
  have hBe : CFSG.Assembly.IsElemAbelian 3 (bZeroGrp.map piL) :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ isElemAbelian_bZeroGrp
  have hB9 : 3 ^ 2 ≤ Nat.card (bZeroGrp.map piL) := by
    rw [card_map_piL_of_le (bZeroGrp_le.trans pZeroGrp_le_unitriangular), card_bZeroGrp]
    norm_num
  have hBN : bZeroGrp.map piL ≤ Subgroup.normalizer (W : Set PSL43) :=
    (Subgroup.map_mono bZeroGrp_le).trans hN
  have hcop : Nat.Coprime 3 (Nat.card W) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hW3
  rw [eq_bot_iff]
  refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hBe hB9 hBN hcop ?_
  rintro _ ⟨b, hb, rfl⟩ hv1 x ⟨hxW, hxC⟩
  have hb1 : b ≠ 1 := fun h => hv1 (by rw [h, map_one])
  have hx3 := pow_three_eq_one_of_mem_centralizer hb hb1
    (Subgroup.mem_centralizer_singleton_iff.mp hxC)
  have hdvd : orderOf x ∣ Nat.gcd 3 (Nat.card W) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx3) (Subgroup.orderOf_dvd_natCard W hxW)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  exact Subgroup.mem_bot.mpr hdvd

theorem noSignalizer_pZero (hcen : Subgroup.center PSL43 = ⊥) :
    Item434SporGen.NoSignalizer (pZeroGrp.map piL) :=
  Item434SporGen.noSignalizer_of_inner hcen (fun _ hW3 hN => eq_bot_of_le_normalizer hW3 hN)
    mem_range_conj_of_fix

end CFSG.RankThree.PartTwo.Sec4.Item434RemL43
