module

public import CFSG.Quasithin.Background.HFL3Beta
public import CFSG.Quasithin.Background.HL3NineM

public section

namespace CFSG.Quasithin.H.L3Nine

open Matrix SU3 Tri

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] noncomputable def smulH {c : K} (hc : bar n c = c) (X : HMod n K) : HMod n K :=
  mkH (c • mat X) (by
    have e : conjM n (c • mat X) = c • conjM n (mat X) := by
      ext i j
      simp [conjM, hc]
    rw [e, Matrix.transpose_smul, herm_mat])

theorem mat_smulH {c : K} (hc : bar n c = c) (X : HMod n K) :
    mat (smulH hc X) = c • mat X := rfl

theorem rhoT_smulH (hK : Nat.card K = (2 ^ n) ^ 2) (A : GL (Fin 3) K) {c : K}
    (hc : bar n c = c) (X : HMod n K) : rhoT hK A (smulH hc X) = smulH hc (rhoT hK A X) :=
  mat_injective (by rw [mat_rhoT, mat_smulH, mat_smulH, mat_rhoT, tw_smul])

theorem card_mul_le_of_smulH (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {U W : Subgroup (HMod n K)} (hWU : W ≤ U)
    (hU : ∀ (c : K) (hc : bar n c = c), ∀ X ∈ U, smulH hc X ∈ U) {X₀ : HMod n K}
    (hX₀ : X₀ ∈ U) (h : ∀ (c : K) (hc : bar n c = c), c ≠ 0 → smulH hc X₀ ∉ W) :
    2 ^ n * Nat.card W ≤ Nat.card U := by
  let f : {b : K // bar n b = b} × ↥W → ↥U := fun p =>
    ⟨smulH p.1.2 X₀ * p.2, U.mul_mem (hU _ p.1.2 _ hX₀) (hWU p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨c, w⟩ ⟨c', w'⟩ he
    have h1 : mat (smulH c.2 X₀ * (w : HMod n K)) = mat (smulH c'.2 X₀ * (w' : HMod n K)) :=
      congrArg (fun x : ↥U => mat (x : HMod n K)) he
    rw [mat_mul, mat_mul, mat_smulH, mat_smulH] at h1
    have hcc : bar n ((c : K) - c') = (c : K) - c' := by rw [map_sub, c.2, c'.2]
    have h2 : smulH hcc X₀ = (w' : HMod n K) * (w : HMod n K)⁻¹ := mat_injective (by
      rw [mat_smulH, mat_mul, mat_inv, sub_smul]
      linear_combination (norm := abel_nf) h1)
    have hc : (c : K) = c' := by
      by_contra hne
      exact h _ hcc (sub_ne_zero.mpr hne) (h2 ▸ W.mul_mem w'.2 (W.inv_mem w.2))
    have hcc' : c = c' := Subtype.ext hc
    subst hcc'
    have hw : (w : HMod n K) = w' := mul_left_cancel (congrArg Subtype.val he)
    exact Prod.ext rfl (Subtype.ext hw)
  have hle := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, card_fixed hn hK] at hle

@[expose] noncomputable def e02s (n : ℕ) : HMod n K :=
  mkH (Matrix.single 0 2 1 + Matrix.single 2 0 1) (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjM, Matrix.single_apply])

theorem mat_e02s : mat (e02s (K := K) n) = Matrix.single 0 2 1 + Matrix.single 2 0 1 := rfl

theorem fix_trGL02 (hK : Nat.card K = (2 ^ n) ^ 2) :
    rhoT hK (trGL 0 2 (by decide) 1) (pt hK (Pi.single 0 1)) = pt hK (Pi.single 0 1) ∧
      rhoT hK (trGL 0 2 (by decide) 1) (pt hK (Pi.single 1 1)) = pt hK (Pi.single 1 1) ∧
      rhoT hK (trGL 0 2 (by decide) 1) (pt hK (Pi.single 0 1 + Pi.single 1 1)) =
        pt hK (Pi.single 0 1 + Pi.single 1 1) ∧
      rhoT hK (trGL 0 2 (by decide) 1) (e02s n) = e02s n := by
  have hv : ∀ v : Fin 3 → K, v 2 = 0 →
      ((trGL 0 2 (by decide) 1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := by
    intro v hv2
    ext i
    fin_cases i <;> simp [coe_trGL, Matrix.transvection, Matrix.add_mulVec, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, Matrix.single_apply, hv2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rhoT_pt, hv _ (by simp)]
  · rw [rhoT_pt, hv _ (by simp)]
  · rw [rhoT_pt, hv _ (by simp)]
  · apply mat_injective
    rw [mat_rhoT, mat_e02s]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [tw, coe_trGL, Matrix.transvection, conjM, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.single_apply, Matrix.one_apply, CharTwo.add_self_eq_zero]

theorem eq_root_of_fix (hK : Nat.card K = (2 ^ n) ^ 2) {y : GL (Fin 3) K}
    (h0 : rhoT hK y (pt hK (Pi.single 0 1)) = pt hK (Pi.single 0 1))
    (h1 : rhoT hK y (pt hK (Pi.single 1 1)) = pt hK (Pi.single 1 1))
    (h01 : rhoT hK y (pt hK (Pi.single 0 1 + Pi.single 1 1)) =
      pt hK (Pi.single 0 1 + Pi.single 1 1))
    (h2 : rhoT hK y (e02s n) = e02s n) :
    ∃ c : K, bar n c = c ∧ rhoT hK y = rhoT hK (trGL 0 2 (by decide) c) := by
  classical
  set Y := (y : Matrix (Fin 3) (Fin 3) K) with hY
  have hvec : ∀ v : Fin 3 → K, v ≠ 0 → rhoT hK y (pt hK v) = pt hK v → ∃ μ : K, Y *ᵥ v = μ • v :=
    fun v hv h => by
      rw [rhoT_pt] at h
      exact eq_smul_of_rk1_eq hv (congrArg mat h)
  obtain ⟨μ₀, hμ₀⟩ := hvec _ (by simp) h0
  obtain ⟨μ₁, hμ₁⟩ := hvec _ (by simp) h1
  obtain ⟨μ, hμ⟩ := hvec _ (fun h => by simpa using congrFun h 0) h01
  have c0 := congrFun hμ₀
  have c1 := congrFun hμ₁
  have c01 := congrFun hμ
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply] at c0 c1 c01
  have y00 : Y 0 0 = μ := by have := c0 0; have := c01 0; simp_all
  have y10 : Y 1 0 = 0 := by simpa using c0 1
  have y20 : Y 2 0 = 0 := by simpa using c0 2
  have y01 : Y 0 1 = 0 := by simpa using c1 0
  have y21 : Y 2 1 = 0 := by simpa using c1 2
  have y11 : Y 1 1 = μ := by have := c1 1; have := c01 1; simp_all
  have e := congrArg mat h2
  rw [mat_rhoT, mat_e02s] at e
  have e01 := congrFun (congrFun e 0) 1
  have e02 := congrFun (congrFun e 0) 2
  have e00 := congrFun (congrFun e 0) 0
  simp [tw, Matrix.mul_apply, Fin.sum_univ_three, conjM, Matrix.single_apply, ← hY, y10, y20,
    y01, y21] at e01 e02 e00
  have hμ0 : μ₀ = μ := by rw [← y00]; simpa using (c0 0).symm
  have hN : μ * bar n μ = 1 := by
    have n0 := congrArg mat h0
    rw [rhoT_pt, mat_pt, mat_pt, hμ₀, hμ0, rk1_smul] at n0
    have := congrFun (congrFun n0 0) 0
    simpa [rk1_apply] using this
  have hμne : μ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hN
    exact zero_ne_one hN
  have y12 : Y 1 2 = 0 := e01.resolve_left (by rw [y00]; exact hμne)
  have y22 : Y 2 2 = μ := by
    apply (bar n).injective
    rw [y00] at e02
    exact mul_left_cancel₀ hμne (e02.trans hN.symm)
  rw [y00] at e00
  set c := bar n μ * Y 0 2 with hcdef
  have hc : bar n c = c := by
    rw [hcdef, map_mul, bar_bar hK]
    linear_combination e00 - (bar n μ * Y 0 2) * CharTwo.two_eq_zero (R := K)
  have hYeq : Y = μ • Matrix.transvection 0 2 c := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.transvection, Matrix.single_apply, Matrix.one_apply, y00, y10, y20, y01, y21,
        y11, y12, y22, hcdef]
    linear_combination (-(Y 0 2)) * hN
  refine ⟨c, hc, ?_⟩
  let u : Kˣ := Units.mk0 μ hμne
  have hy : y = scalGL u * trGL 0 2 (by decide) c := by
    apply Units.ext
    rw [Units.val_mul, coe_scalGL, coe_trGL, Matrix.smul_mul, Matrix.one_mul]
    exact hYeq
  have hs : rhoT hK (scalGL u) = 1 := MulEquiv.ext fun X => mat_injective (by
    rw [mat_rhoT_scalGL]
    change (μ * bar n μ) • mat X = mat X
    rw [hN, one_smul])
  rw [hy, map_mul, hs, one_mul]

theorem card_fixV_le_of_card_gt (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : Subgroup (MulAut (HMod n K))} (hAL : A ≤ img hK) (hAe : IsElemAbelian2 A)
    (hcard : 2 ^ n < Nat.card A) : Nat.card (fixV A) ≤ 2 ^ (4 * n) := by
  classical
  have : Finite (MulAut (HMod n K)) := MulEquiv.finite_left
  obtain ⟨r, hrA, hr1⟩ : ∃ r ∈ A, r ≠ 1 := by
    by_contra h
    push Not at h
    rw [(Subgroup.eq_bot_iff_forall A).2 h, Subgroup.card_bot] at hcard
    have := Nat.one_le_two_pow (n := n)
    omega
  obtain ⟨g₀, hg₀⟩ := hAL hrA
  have hr2 : rhoT hK (SpecialLinearGroup.toGL g₀) * rhoT hK (SpecialLinearGroup.toGL g₀) = 1 := by
    change rho hK g₀ * rho hK g₀ = 1
    rw [hg₀, ← sq]
    exact hAe.2 r hrA
  obtain ⟨A', hA', hA'2⟩ := exists_sq_eq_one hn hK hr2
  have hdet : (A' : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    apply eq_one_of_sq_eq_one
    rw [← Matrix.det_mul, ← Units.val_mul, hA'2, Units.val_one, Matrix.det_one]
  set u : SpecialLinearGroup (Fin 3) K := ⟨A', hdet⟩ with hu
  have hur : rho hK u = r := by
    rw [hu, rho_mk hK hdet, hA', ← hg₀]
    rfl
  have huu : u * u = 1 := Subtype.ext (by
    change (A' : Matrix (Fin 3) (Fin 3) K) * A' = 1
    rw [← Units.val_mul, hA'2, Units.val_one])
  have hu1 : u ≠ 1 := fun h => hr1 (by rw [← hur, h, map_one])
  obtain ⟨W, hW⟩ := exists_conj_eq_transvection huu hu1
  set w := rho hK W with hw
  have hwr : w * r * w⁻¹ = rhoT hK (trGL 0 2 (by decide) 1) := by
    rw [← hur, hw, ← map_inv, ← map_mul, ← map_mul, hW, rho_transvection]
  have hcentr : ∀ s ∈ A, (∀ X ∈ fixV (Subgroup.zpowers r), s X = X) →
      ∃ c : {b : K // bar n b = b}, s = w⁻¹ * rhoT hK (trGL 0 2 (by decide) c.1) * w := by
    intro s hsA hs
    obtain ⟨g, hg⟩ := hAL hsA
    have hfix : ∀ X, rhoT hK (trGL 0 2 (by decide) 1) X = X → (w * s * w⁻¹) X = X := by
      intro X hX
      have h2 : r (w⁻¹ X) = w⁻¹ X := by
        have h3 : (w * r * w⁻¹) X = X := by rw [hwr]; exact hX
        rw [MulAut.mul_apply, MulAut.mul_apply] at h3
        calc r (w⁻¹ X) = w⁻¹ (w (r (w⁻¹ X))) := by rw [MulAut.inv_apply_self]
          _ = w⁻¹ X := by rw [h3]
      have h4 := hs _ (mem_fixV_zpowers_iff.mpr h2)
      rw [MulAut.mul_apply, MulAut.mul_apply, h4, MulAut.apply_inv_self]
    have hs' : w * s * w⁻¹ = rhoT hK (SpecialLinearGroup.toGL (W * g * W⁻¹)) := by
      rw [hw, ← hg, ← map_inv, ← map_mul, ← map_mul]
      rfl
    obtain ⟨hf0, hf1, hf01, hf2⟩ := fix_trGL02 (n := n) hK
    rw [hs'] at hfix
    obtain ⟨c, hc, hce⟩ := eq_root_of_fix hK (hfix _ hf0) (hfix _ hf1) (hfix _ hf01)
      (hfix _ hf2)
    refine ⟨⟨c, hc⟩, ?_⟩
    rw [← hce, ← hs']
    group
  obtain ⟨s, hsA, X₀, hX₀, hsX₀⟩ : ∃ s ∈ A, ∃ X₀ ∈ fixV (Subgroup.zpowers r), s X₀ ≠ X₀ := by
    by_contra h
    push Not at h
    let f : {b : K // bar n b = b} → MulAut (HMod n K) := fun c =>
      w⁻¹ * rhoT hK (trGL 0 2 (by decide) c.1) * w
    have hsub : (A : Set (MulAut (HMod n K))) ⊆ Set.range f := fun s hs => by
      obtain ⟨c, hc⟩ := hcentr s hs (h s hs)
      exact ⟨c, hc.symm⟩
    have h1 : Nat.card A ≤ Nat.card (Set.range f) := Nat.card_mono (Set.finite_range f) hsub
    have h2 : Nat.card (Set.range f) ≤ Nat.card {b : K // bar n b = b} :=
      Finite.card_range_le f
    rw [card_fixed hn hK] at h2
    omega
  obtain ⟨g, hg⟩ := hAL hsA
  set U := fixV (Subgroup.zpowers r) with hUdef
  set W' := U ⊓ fixV (Subgroup.zpowers s) with hW'
  have hU : ∀ (c : K) (hc : bar n c = c), ∀ X ∈ U, smulH hc X ∈ U := by
    intro c hc X hX
    rw [hUdef, mem_fixV_zpowers_iff, ← hg₀] at hX ⊢
    change rhoT hK (SpecialLinearGroup.toGL g₀) (smulH hc X) = smulH hc X
    rw [rhoT_smulH]
    exact congrArg (smulH hc) hX
  have hsep : ∀ (c : K) (hc : bar n c = c), c ≠ 0 → smulH hc X₀ ∉ W' := by
    intro c hc hc0 hmem
    apply hsX₀
    have h1 : s (smulH hc X₀) = smulH hc X₀ := mem_fixV_zpowers_iff.mp hmem.2
    have hci : bar n c⁻¹ = c⁻¹ := by rw [map_inv₀, hc]
    have h2 : smulH hci (smulH hc X₀) = X₀ := mat_injective (by
      rw [mat_smulH, mat_smulH, smul_smul, inv_mul_cancel₀ hc0, one_smul])
    rw [← hg] at h1 ⊢
    change rhoT hK (SpecialLinearGroup.toGL g) (smulH hc X₀) = smulH hc X₀ at h1
    change rhoT hK (SpecialLinearGroup.toGL g) X₀ = X₀
    rw [← h2, rhoT_smulH, h1]
  have hle := card_mul_le_of_smulH hn hK (inf_le_left : W' ≤ U) hU hX₀ hsep
  have hUle : Nat.card U ≤ 2 ^ (5 * n) := by
    rw [hUdef, ← hg₀]
    refine card_fixV_rhoT_le hn hK (A := SpecialLinearGroup.toGL g₀) ?_
    change rho hK g₀ ≠ 1
    rw [hg₀]
    exact hr1
  have hAW : fixV A ≤ W' := fun X hX =>
    ⟨mem_fixV_zpowers_iff.mpr (hX r hrA), mem_fixV_zpowers_iff.mpr (hX s hsA)⟩
  have h5 : Nat.card (fixV A) ≤ Nat.card W' := Subgroup.card_le_of_le hAW
  have h6 : 2 ^ n * Nat.card W' ≤ 2 ^ n * 2 ^ (4 * n) := by
    calc 2 ^ n * Nat.card W' ≤ 2 ^ (5 * n) := hle.trans hUle
      _ = 2 ^ n * 2 ^ (4 * n) := by rw [← pow_add]; ring_nf
  exact h5.trans (Nat.le_of_mul_le_mul_left h6 (by positivity))

end CFSG.Quasithin.H.L3Nine
