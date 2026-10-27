module

public import CFSG.Timmesfeld.Transvection.QTwoSetup
public import CFSG.Fischer.Classification.PartIII.Beta.Iso

public section

namespace CFSG.Timmesfeld.Transvection.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Fischer.Classification CFSG.Fischer.Classification.F3 CFSG.Blueprint.Fischer

variable {H : Type} [Group H] {D : Set H} {m : ℕ}
  {b : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem exists_orthonormal_anisotropic (hQ : QHyp H D) (hb : IsF3Form b) (hm : 4 ≤ m)
    (φ : H ≃* R3 b) (hφ : ∀ g, g ∈ D ↔ φ g ∈ D3 b) :
    ∃ u v w : Fin m → ZMod 3, b u u = 1 ∧ b v v = 1 ∧ b w w = 1 ∧ b u v = 0 ∧ b u w = 0 ∧
      b v w = 0 ∧ ∀ z, b z u = 0 → b z v = 0 → b z w = 0 → b z z = 0 → z = 0 := by
  obtain ⟨e₁, he₁, e₂, he₂, he, hc⟩ := hQ.rank
  obtain ⟨g, hg, hge₁, hge₂, hall⟩ := hQ.thick e₁ he₁ e₂ he₂ he hc
  obtain ⟨u, hu, hue⟩ := mem_D3_iff.1 ((hφ e₁).1 he₁)
  obtain ⟨v, hv, hve⟩ := mem_D3_iff.1 ((hφ e₂).1 he₂)
  obtain ⟨w, hw, hwe⟩ := mem_D3_iff.1 ((hφ g).1 hg)
  have hcomm : ∀ {x y : H}, x * y = y * x → φ x * φ y = φ y * φ x := fun h => by
    rw [← map_mul, ← map_mul, h]
  have horth : ∀ {x y : H} {a c : Fin m → ZMod 3}, b a a = 1 → b c c = 1 →
      reflBar b a = φ x → reflBar b c = φ y → x ≠ y → x * y = y * x → b a c = 0 := by
    intro x y a c ha hc' hax hcy hxy h
    have h' := hcomm h
    rw [← hax, ← hcy, reflBar_commute_iff hb hm ha hc'] at h'
    rcases h' with h0 | h1 | h1
    · exact h0
    · exact absurd (φ.injective (by rw [← hax, ← hcy, h1])) hxy
    · exact absurd (φ.injective (by rw [← hax, ← hcy, h1, reflBar_neg])) hxy
  have huv := horth hu hv hue hve he hc
  have huw := horth hu hw hue hwe (fun h => hge₁ h.symm) (hall e₁ he₁ rfl hc)
  have hvw := horth hv hw hve hwe (fun h => hge₂ h.symm) (hall e₂ he₂ hc.symm rfl)
  refine ⟨u, v, w, hu, hv, hw, huv, huw, hvw, fun z hzu hzv hzw hzz => ?_⟩
  by_contra hz0
  have hwz : b w z = 0 := by rw [hb.symm]; exact hzw
  set x := w + z with hx
  have hxx : b x x = 1 := by rw [hx, norm_add hb, hw, hwz, hzz]; ring
  have hxu : b x u = 0 := by
    rw [hx, LinearMap.BilinForm.add_left, hb.symm w u, huw, hzu, add_zero]
  have hxv : b x v = 0 := by
    rw [hx, LinearMap.BilinForm.add_left, hb.symm w v, hvw, hzv, add_zero]
  have hwx : b w x = 1 := by rw [hx, LinearMap.BilinForm.add_right, hw, hwz, add_zero]
  set d := φ.symm (reflBar b x) with hd
  have hφd : φ d = reflBar b x := by rw [hd, MulEquiv.apply_symm_apply]
  have hdD : d ∈ D := (hφ d).2 (hφd ▸ reflBar_mem_D3 hxx)
  have hcomm' : ∀ {y : H} {a : Fin m → ZMod 3}, b a a = 1 → reflBar b a = φ y → b x a = 0 →
      d * y = y * d := by
    intro y a ha hay hxa
    apply φ.injective
    rw [map_mul, map_mul, hφd, ← hay]
    exact (reflBar_commute_iff hb hm hxx ha).2 (Or.inl hxa)
  have hdg := hcomm (hall d hdD (hcomm' hu hue hxu) (hcomm' hv hve hxv))
  rw [hφd, ← hwe, reflBar_commute_iff hb hm hxx hw] at hdg
  rcases hdg with h0 | h1 | h1
  · rw [hb.symm, hwx] at h0
    exact one_ne_zero h0
  · apply hz0
    have : w + z = w + 0 := by rw [add_zero, ← hx, h1]
    exact add_left_cancel this
  ·
    have hzw' : z = w := by
      have h3 : (3 : ZMod 3) • w = 0 := by rw [show (3 : ZMod 3) = 0 by decide, zero_smul]
      rw [hx] at h1
      linear_combination (norm := module) h1 - h3
    rw [hzw', hw] at hzz
    exact one_ne_zero hzz

theorem orthonormal_three {u v w : Fin m → ZMod 3} (hb : IsF3Form b) (hu : b u u = 1)
    (hv : b v v = 1) (hw : b w w = 1) (huv : b u v = 0) (huw : b u w = 0) (hvw : b v w = 0) :
    ∀ i j, b (![u, v, w] i) (![u, v, w] j) = if i = j then 1 else 0 := by
  have hvu : b v u = 0 := by rw [hb.symm]; exact huv
  have hwu : b w u = 0 := by rw [hb.symm]; exact huw
  have hwv : b w v = 0 := by rw [hb.symm]; exact hvw
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hu, hv, hw, huv, huw, hvw, hvu, hwu, hwv]

theorem false_of_R3_six_le (hQ : QHyp H D) (hb : IsF3Form b) (hm : 6 ≤ m) (φ : H ≃* R3 b)
    (hφ : ∀ g, g ∈ D ↔ φ g ∈ D3 b) : False := by
  obtain ⟨u, v, w, hu, hv, hw, huv, huw, hvw, hiso⟩ :=
    exists_orthonormal_anisotropic hQ hb (by omega) φ hφ
  have hW := orthonormal_three hb hu hv hw huv huw hvw
  obtain ⟨z, hzU, hz0, hzz⟩ := exists_mem_isotropic hb (Beta.nondegOn_perpSub_orthonormal hb hW)
    (perpSub_threeDim hb (k := 3) (by omega) _)
  rw [mem_perpSub_three] at hzU
  exact hz0 (hiso z hzU.1 hzU.2.1 hzU.2.2 hzz)

theorem exists_isometry_I5Form {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)}
    {W : Fin 5 → Fin 5 → ZMod 3} (hW : ∀ i j, f (W i) (W j) = if i = j then 1 else 0) :
    ∃ e : (Fin 5 → ZMod 3) ≃ₗ[ZMod 3] (Fin 5 → ZMod 3), ∀ x y, f x y = I5Form (e x) (e y) := by
  have hli : LinearIndependent (ZMod 3) W := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrArg (fun x => f x (W j)) hg
    simpa [LinearMap.BilinForm.sum_left, LinearMap.BilinForm.smul_left, hW] using this
  let bW := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hbW : ∀ i, bW i = W i := fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨bW.equivFun, fun x y => ?_⟩
  conv_lhs => rw [← bW.sum_equivFun x, ← bW.sum_equivFun y]
  simp only [LinearMap.BilinForm.sum_left, LinearMap.BilinForm.sum_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hbW, hW, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_one]
  rw [I5Form_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem exists_mulEquiv_U2_four_of_R3_five (hQ : QHyp H D)
    {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)} (hf : IsF3Form f) (φ : H ≃* R3 f)
    (hφ : ∀ g, g ∈ D ↔ φ g ∈ D3 f) : ∃ ψ : H ≃* Unitary.U2 4, ψ '' D = Unitary.DU 4 := by
  obtain ⟨u, v, w, hu, hv, hw, huv, huw, hvw, hiso⟩ :=
    exists_orthonormal_anisotropic hQ hf (by norm_num) φ hφ
  have hW := orthonormal_three hf hu hv hw huv huw hvw
  have hnd := Beta.nondegOn_perpSub_orthonormal hf hW
  have htwo := perpSub_twoDim hf (k := 3) (by norm_num) ![u, v, w]
  obtain ⟨w₁, hw₁U, hw₁⟩ := exists_mem_norm_eq hf hnd htwo (c := 1) one_ne_zero
  obtain ⟨w₂, hw₂U, hw₂0, hw₁₂⟩ := htwo w₁ hw₁U
  have hw₁' := mem_perpSub_three.1 hw₁U
  have hw₂' := mem_perpSub_three.1 hw₂U
  have hw₂₁ : f w₂ w₁ = 0 := by rw [hf.symm]; exact hw₁₂
  have hw₂ : f w₂ w₂ = 1 := by
    have hcases : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
    rcases hcases (f w₂ w₂) with h0 | h1 | h2
    · exact absurd (hiso w₂ hw₂'.1 hw₂'.2.1 hw₂'.2.2 h0) hw₂0
    · exact h1
    · exfalso
      have hz := hiso (w₁ + w₂)
        (by rw [LinearMap.BilinForm.add_left, hw₁'.1, hw₂'.1, add_zero])
        (by rw [LinearMap.BilinForm.add_left, hw₁'.2.1, hw₂'.2.1, add_zero])
        (by rw [LinearMap.BilinForm.add_left, hw₁'.2.2, hw₂'.2.2, add_zero])
        (by rw [norm_add hf, hw₁, hw₁₂, h2]; decide)
      have h1' : f (w₁ + w₂) w₁ = 1 := by
        rw [LinearMap.BilinForm.add_left, hw₁, hw₂₁, add_zero]
      rw [hz, LinearMap.BilinForm.zero_left] at h1'
      exact zero_ne_one h1'
  have hW5 : ∀ i j, f (![u, v, w, w₁, w₂] i) (![u, v, w, w₁, w₂] j) =
      if i = j then 1 else 0 := by
    have hvu : f v u = 0 := by rw [hf.symm]; exact huv
    have hwu : f w u = 0 := by rw [hf.symm]; exact huw
    have hwv : f w v = 0 := by rw [hf.symm]; exact hvw
    have h1u : f u w₁ = 0 := by rw [hf.symm]; exact hw₁'.1
    have h1v : f v w₁ = 0 := by rw [hf.symm]; exact hw₁'.2.1
    have h1w : f w w₁ = 0 := by rw [hf.symm]; exact hw₁'.2.2
    have h2u : f u w₂ = 0 := by rw [hf.symm]; exact hw₂'.1
    have h2v : f v w₂ = 0 := by rw [hf.symm]; exact hw₂'.2.1
    have h2w : f w w₂ = 0 := by rw [hf.symm]; exact hw₂'.2.2
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hu, hv, hw, hw₁, hw₂, huv, huw, hvw, hvu, hwu, hwv, h1u, h1v, h1w, h2u, h2v, h2w,
        hw₁'.1, hw₁'.2.1, hw₁'.2.2, hw₂'.1, hw₂'.2.1, hw₂'.2.2, hw₁₂, hw₂₁]
  obtain ⟨e, he⟩ := exists_isometry_I5Form hW5
  obtain ⟨ψ₁, hψ₁⟩ := exists_mulEquiv_R3_of_isometry e he
  obtain ⟨β, hβ⟩ := exists_mulEquiv_U2_four_R3_I5
  have hφD : φ '' D = D3 f := by
    ext q
    refine ⟨?_, fun hq => ⟨φ.symm q, (hφ _).2 (by rwa [MulEquiv.apply_symm_apply]),
      MulEquiv.apply_symm_apply _ _⟩⟩
    rintro ⟨g, hg, rfl⟩
    exact (hφ g).1 hg
  refine ⟨φ.trans (ψ₁.trans β.symm), ?_⟩
  rw [MulEquiv.coe_trans, MulEquiv.coe_trans, Set.image_comp, Set.image_comp, hφD, hψ₁, ← hβ]
  exact CFSG.Fischer.image_symm_image β _

end CFSG.Timmesfeld.Transvection.QTwo
