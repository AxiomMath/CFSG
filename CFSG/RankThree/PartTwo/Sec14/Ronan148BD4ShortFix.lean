module

public import CFSG.CGT.Timmesfeld75.L2Aut
public import CFSG.HardMathSupport.Foote.ModuleExclusions.Hilbert90
import CFSG.Quasithin.Vol2.Ch6Sec1Lem14Stab

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open Matrix CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

namespace Res148BD4

variable {F : Type} [Field F]

theorem sl2_eq_one_of_commute [CharP F 2] {M : SL(2, F)} (hM : ∀ x : SL(2, F), M * x = x * M) :
    M = 1 := by
  have hc : M ∈ Subgroup.center SL(2, F) := Subgroup.mem_center_iff.2 fun x => (hM x).symm
  obtain ⟨r, hr, hrM⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hr1 : r = 1 := by
    have : (r - 1) * (r - 1) = 0 := by
      linear_combination hr - r * h2 + h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp this)
  apply Subtype.ext
  rw [← hrM, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem eq_refl_of_conj_sl2FieldAut [CharP F 2] {g : SL(2, F)} {σ : F ≃+* F}
    (h : ∀ x, g * sl2FieldAut σ x * g⁻¹ = x) : σ = RingEquiv.refl F := by
  have key : ∀ s : F, g * utriElt (σ s) = utriElt s * g := by
    intro s
    have h1 := h (utriElt s)
    rw [sl2FieldAut_utriElt] at h1
    calc g * utriElt (σ s) = g * utriElt (σ s) * g⁻¹ * g := by group
      _ = utriElt s * g := by rw [h1]
  have entry : ∀ (s : F) (i j : Fin 2),
      ((g * utriElt (σ s) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) i j =
        ((utriElt s * g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) i j := by
    intro s i j
    rw [key s]
  have hu : ∀ s : F, ((utriElt s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, s; 0, 1] := by
    intro s
    ext i j
    fin_cases i <;> fin_cases j
    · exact utriElt_apply_00 s
    · exact utriElt_apply_01 s
    · exact utriElt_apply_10 s
    · exact utriElt_apply_11 s
  set a := (g : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b := (g : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
  set c := (g : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d := (g : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  have e00 : ∀ s : F, a = a + s * c := by
    intro s
    have := entry s 0 0
    simp only [Matrix.SpecialLinearGroup.coe_mul, hu, Matrix.mul_apply, Fin.sum_univ_two] at this
    simpa [← ha, ← hc] using this
  have e01 : ∀ s : F, a * σ s + b = b + s * d := by
    intro s
    have := entry s 0 1
    simp only [Matrix.SpecialLinearGroup.coe_mul, hu, Matrix.mul_apply, Fin.sum_univ_two] at this
    simpa [← ha, ← hb, ← hd, mul_comm] using this
  have hc0 : c = 0 := by
    have := e00 1
    rw [one_mul] at this
    linear_combination -this
  have hdet : a * d - b * c = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    exact this
  rw [hc0, mul_zero, sub_zero] at hdet
  have had : a = d := by
    have := e01 1
    rw [map_one, mul_one, one_mul] at this
    linear_combination this
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact zero_ne_one hdet
  ext s
  have := e01 s
  rw [← had] at this
  have h' : a * σ s = a * s := by linear_combination this
  exact mul_left_cancel₀ ha0 h'

@[expose] def wThree (E : Type) [Field E] [CharP E 2] : SL(2, E) :=
  ⟨!![0, 1; 1, 1], by
    rw [Matrix.det_fin_two_of]
    have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
    linear_combination -h2⟩

theorem orderOf_wThree (E : Type) [Field E] [CharP E 2] : orderOf (wThree E) = 3 := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    simp only [wThree, pow_succ, pow_zero, one_mul]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination h2
  · intro h
    have := congrArg (fun m : SL(2, E) => (m : Matrix (Fin 2) (Fin 2) E) 0 0) h
    simp [wThree] at this

theorem eq_bot_of_normal_coprime_sl2 {E : Type} [Field E] [Finite E] [CharP E 2]
    (h4 : 4 ≤ Nat.card E) (N : Subgroup SL(2, E)) (hN : N.Normal)
    (hN3 : Nat.Coprime 3 (Nat.card N)) : N = ⊥ := by
  have hs := CFSG.Quasithin.H13.isSimpleGroup_sl2_of_charTwo h4
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have hw : wThree E ∈ N := by rw [h]; exact Subgroup.mem_top _
    have hdvd : orderOf (⟨wThree E, hw⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, orderOf_wThree] at hdvd
    exact absurd (Nat.Coprime.eq_one_of_dvd hN3 hdvd) (by norm_num)

theorem eq_bot_of_le_fixed [Finite F] [CharP F 2] {σ : F ≃+* F} (hσ : orderOf σ = 3)
    (h4 : 4 ≤ Nat.card (autFixedSubfield σ)) {g : SL(2, F)}
    (hg : g * sl2FieldAut σ g * sl2FieldAut σ (sl2FieldAut σ g) = 1) (M : Subgroup SL(2, F))
    (hMfix : ∀ x ∈ M, g * sl2FieldAut σ x * g⁻¹ = x)
    (hMnorm : ∀ y, g * sl2FieldAut σ y * g⁻¹ = y → ∀ x ∈ M, y * x * y⁻¹ ∈ M)
    (hM3 : Nat.Coprime 3 (Nat.card M)) : M = ⊥ := by
  classical
  set Φ : Matrix (Fin 2) (Fin 2) F ≃+* Matrix (Fin 2) (Fin 2) F := σ.mapMatrix with hΦ
  have hcoe : ∀ x : SL(2, F),
      ((sl2FieldAut σ x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = Φ x := fun x => rfl
  set G := (g : Matrix (Fin 2) (Fin 2) F) with hG
  set Gi := ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) with hGi
  have hGGi : G * Gi = 1 := by
    rw [hG, hGi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hGiG : Gi * G = 1 := by
    rw [hG, hGi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hAi : CFSG.HardMathSupport.Foote.ModuleExclusions.Ai σ G 3 = 1 := by
    have h := congrArg (fun m : SL(2, F) => (m : Matrix (Fin 2) (Fin 2) F)) hg
    simp only [Matrix.SpecialLinearGroup.coe_mul, hcoe, Matrix.SpecialLinearGroup.coe_one] at h
    change G * (G * (G * (1 : Matrix (Fin 2) (Fin 2) F).map σ).map σ).map σ = 1
    have e1 : ∀ N : Matrix (Fin 2) (Fin 2) F, N.map σ = Φ N := fun N => rfl
    rw [e1, e1, e1, map_one, mul_one, map_mul, ← mul_assoc]
    exact h
  obtain ⟨B, hBdet, hB⟩ := CFSG.HardMathSupport.Foote.ModuleExclusions.speiser σ G 3 hσ
    (by norm_num) hAi
  have hB' : G * Φ B = B := hB
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hBdet
  set Bi := B⁻¹ with hBi
  have hBBi : B * Bi = 1 := Matrix.mul_nonsing_inv B hBu
  have hBiB : Bi * B = 1 := Matrix.nonsing_inv_mul B hBu
  have hΦB : Φ B = Gi * B := by
    calc Φ B = Gi * G * Φ B := by rw [hGiG, one_mul]
      _ = Gi * B := by rw [mul_assoc, hB']
  have hΦBi : Φ Bi = Bi * G := by
    have h1 : Φ B * Φ Bi = 1 := by rw [← map_mul, hBBi, map_one]
    calc Φ Bi = Bi * B * Φ Bi := by rw [hBiB, one_mul]
      _ = Bi * (G * Φ B) * Φ Bi := by rw [hB']
      _ = Bi * G * (Φ B * Φ Bi) := by simp only [mul_assoc]
      _ = Bi * G := by rw [h1, mul_one]
  set F₀ := autFixedSubfield σ with hF₀
  set ι : F₀ →+* F := F₀.subtype with hι
  have : CharP F₀ 2 := (RingHom.charP_iff ι F₀.subtype_injective 2).mpr ‹CharP F 2›
  have hfixY : ∀ Y : Matrix (Fin 2) (Fin 2) F₀, Φ (Y.map ι) = Y.map ι := by
    intro Y
    ext i j
    exact (Y i j).2
  have hdetψ : ∀ Y : SL(2, F₀), (B * (Y : Matrix (Fin 2) (Fin 2) F₀).map ι * Bi).det = 1 := by
    intro Y
    have hY : ((Y : Matrix (Fin 2) (Fin 2) F₀).map ι).det = 1 := by
      have h := RingHom.map_det ι (Y : Matrix (Fin 2) (Fin 2) F₀)
      rw [Matrix.SpecialLinearGroup.det_coe, map_one] at h
      exact h.symm
    rw [Matrix.det_mul, Matrix.det_mul, hY, mul_one, ← Matrix.det_mul, hBBi, Matrix.det_one]
  let ψ : SL(2, F₀) →* SL(2, F) :=
    { toFun := fun Y => ⟨B * (Y : Matrix (Fin 2) (Fin 2) F₀).map ι * Bi, hdetψ Y⟩
      map_one' := by
        apply Subtype.ext
        change B * ((1 : SL(2, F₀)) : Matrix (Fin 2) (Fin 2) F₀).map ι * Bi = 1
        rw [Matrix.SpecialLinearGroup.coe_one, Matrix.map_one (⇑ι) ι.map_zero ι.map_one,
          mul_one, hBBi]
      map_mul' := fun Y Z => by
        apply Subtype.ext
        change B * ((Y * Z : SL(2, F₀)) : Matrix (Fin 2) (Fin 2) F₀).map ι * Bi =
          (B * (Y : Matrix (Fin 2) (Fin 2) F₀).map ι * Bi) *
            (B * (Z : Matrix (Fin 2) (Fin 2) F₀).map ι * Bi)
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]
        calc B * ((Y : Matrix (Fin 2) (Fin 2) F₀).map ι * (Z : Matrix (Fin 2) (Fin 2) F₀).map ι) *
            Bi = B * (Y : Matrix (Fin 2) (Fin 2) F₀).map ι * (Bi * B) *
              (Z : Matrix (Fin 2) (Fin 2) F₀).map ι * Bi := by
              rw [hBiB, mul_one, ← mul_assoc]
          _ = _ := by simp only [mul_assoc] }
  have hψ : ∀ Y : SL(2, F₀), ((ψ Y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      B * (Y : Matrix (Fin 2) (Fin 2) F₀).map ι * Bi := fun Y => rfl
  have hψinj : Function.Injective ψ := by
    intro Y Z h
    have h1 := congrArg (fun m : SL(2, F) => Bi * (m : Matrix (Fin 2) (Fin 2) F) * B) h
    simp only [hψ] at h1
    have e : ∀ W : Matrix (Fin 2) (Fin 2) F, Bi * (B * W * Bi) * B = W := by
      intro W
      calc Bi * (B * W * Bi) * B = (Bi * B) * W * (Bi * B) := by simp only [mul_assoc]
        _ = W := by rw [hBiB, one_mul, mul_one]
    rw [e, e] at h1
    apply Subtype.ext
    ext i j
    have := congrFun (congrFun h1 i) j
    exact this
  have hψfix : ∀ Y, g * sl2FieldAut σ (ψ Y) * g⁻¹ = ψ Y := by
    intro Y
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hcoe, hψ, map_mul,
      map_mul, hfixY, hΦB, hΦBi, ← hG, ← hGi]
    calc G * (Gi * B * (Y : Matrix (Fin 2) (Fin 2) F₀).map ι * (Bi * G)) * Gi =
        (G * Gi) * B * (Y : Matrix (Fin 2) (Fin 2) F₀).map ι * Bi * (G * Gi) := by
          simp only [mul_assoc]
      _ = B * (Y : Matrix (Fin 2) (Fin 2) F₀).map ι * Bi := by rw [hGGi, one_mul, mul_one]
  have hfixψ : ∀ x : SL(2, F), g * sl2FieldAut σ x * g⁻¹ = x → ∃ Y, ψ Y = x := by
    intro x hx
    set X := (x : Matrix (Fin 2) (Fin 2) F) with hX
    have hxm : G * Φ X * Gi = X := by
      have := congrArg (fun m : SL(2, F) => (m : Matrix (Fin 2) (Fin 2) F)) hx
      simpa only [Matrix.SpecialLinearGroup.coe_mul, hcoe] using this
    set W := Bi * X * B with hW
    have hWfix : Φ W = W := by
      rw [hW, map_mul, map_mul, hΦB, hΦBi]
      calc Bi * G * Φ X * (Gi * B) = Bi * (G * Φ X * Gi) * B := by simp only [mul_assoc]
        _ = W := by rw [hxm]
    have hWij : ∀ i j, σ (W i j) = W i j := fun i j => congrFun (congrFun hWfix i) j
    set W₀ : Matrix (Fin 2) (Fin 2) F₀ := fun i j => ⟨W i j, hWij i j⟩ with hW₀
    have hW₀map : W₀.map ι = W := by
      ext i j
      rfl
    have hW₀det : W₀.det = 1 := by
      apply ι.injective
      rw [RingHom.map_det, map_one]
      change (W₀.map ι).det = 1
      rw [hW₀map, hW, Matrix.det_mul, Matrix.det_mul, x.2, mul_one, ← Matrix.det_mul, hBiB,
        Matrix.det_one]
    refine ⟨⟨W₀, hW₀det⟩, Subtype.ext ?_⟩
    change B * W₀.map ι * Bi = X
    rw [hW₀map, hW]
    calc B * (Bi * X * B) * Bi = (B * Bi) * X * (B * Bi) := by simp only [mul_assoc]
      _ = X := by rw [hBBi, one_mul, mul_one]
  set M' := M.comap ψ with hM'
  have hMr : M ≤ ψ.range := fun x hx => by
    obtain ⟨Y, hY⟩ := hfixψ x (hMfix x hx)
    exact ⟨Y, hY⟩
  have hmap : M'.map ψ = M := by
    rw [hM', Subgroup.map_comap_eq, inf_eq_right.2 hMr]
  have hM'n : M'.Normal := by
    refine ⟨fun x hx y => ?_⟩
    change ψ (y * x * y⁻¹) ∈ M
    rw [map_mul, map_mul, map_inv]
    exact hMnorm (ψ y) (hψfix y) (ψ x) hx
  have hM'3 : Nat.Coprime 3 (Nat.card M') := by
    rw [← Subgroup.card_map_of_injective hψinj, hmap]
    exact hM3
  have hF₀ : 4 ≤ Nat.card F₀ := h4
  have hbot := eq_bot_of_normal_coprime_sl2 hF₀ M' hM'n hM'3
  rw [← hmap, hbot, Subgroup.map_bot]

end Res148BD4

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
