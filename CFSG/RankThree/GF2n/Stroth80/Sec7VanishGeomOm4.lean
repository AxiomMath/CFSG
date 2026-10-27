module

public import CFSG.RankThree.GF2n.Stroth80.Sec7VanishGeom
public import CFSG.RankThree.GF2n.Stroth80.Sec7OmegaMinusFourTrans
import CFSG.RankThree.GF2n.Stroth80.Sec7Unconditional

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

namespace OmegaMinusFourGeom

open OmegaMinusFourTrans

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem smul_e_eq_vec (a : K) : a • (minusPair K b c i₀).e = vec a 0 0 0 := by
  funext k
  rcases k with i | i | j
  · have hi : i = i₀ := Fin.ext (by have := i.isLt; simp only [i₀]; omega)
    subst hi
    simp [minusPair_e, vec]
  · simp [minusPair_e, vec]
  · simp [minusPair_e, vec]

theorem smul_f_eq_vec (d : K) : d • (minusPair K b c i₀).f = vec 0 d 0 0 := by
  funext k
  rcases k with i | i | j
  · simp [minusPair_f, vec]
  · have hi : i = i₀ := Fin.ext (by have := i.isLt; simp only [i₀]; omega)
    subst hi
    simp [minusPair_f, vec]
  · simp [minusPair_f, vec]

theorem vec_zero : (vec 0 0 0 0 : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) = 0 := by
  funext k
  rcases k with i | i | j <;> simp [vec]

variable (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
include hirr

theorem eq_zero_of_singular {p : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K}
    (hQ : quadMinus 2 K b c p = 0) (ha : p (.inl i₀) = 0) (hd : p (.inr (.inl i₀)) = 0) :
    p = 0 := by
  have hp := eq_vec p
  rw [ha, hd] at hp
  have h := hQ
  rw [hp, quadMinus_vec, zero_mul, zero_add] at h
  obtain ⟨hs, ht⟩ := binary_eq_zero hirr h
  rw [hp, hs, ht, vec_zero]

theorem singular_sub_smul {p p' : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K}
    (hQp : quadMinus 2 K b c p = 0) (hQp' : quadMinus 2 K b c p' = 0)
    (hpp' : polar (quadMinus 2 K b c) p p' = 0) (μ : K) :
    quadMinus 2 K b c (p' - μ • p) = 0 ∧ polar (quadMinus 2 K b c) p (p' - μ • p) = 0 := by
  have hpol : polar (quadMinus 2 K b c) p' (μ • p) = 0 := by
    rw [polar_smul_right, polar_comm, hpp', smul_zero]
  have hpp : polar (quadMinus 2 K b c) p p = 0 := by
    rw [polar_self, hQp, smul_zero]
  refine ⟨?_, ?_⟩
  · have h1 : quadMinus 2 K b c (μ • p) = 0 := by rw [QuadraticMap.map_smul, hQp, smul_zero]
    have e : polar (quadMinus 2 K b c) p' (-(μ • p)) = quadMinus 2 K b c (p' + -(μ • p)) -
        quadMinus 2 K b c p' - quadMinus 2 K b c (-(μ • p)) := rfl
    rw [polar_neg_right, hpol, neg_zero, QuadraticMap.map_neg, h1, hQp', sub_zero,
      sub_zero] at e
    rw [sub_eq_add_neg]
    exact e.symm
  · rw [polar_sub_right, polar_smul_right, hpp, hpp', smul_zero, sub_zero]

theorem exists_eq_smul_of_singular {p p' : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K} (hp : p ≠ 0)
    (hQp : quadMinus 2 K b c p = 0) (hQp' : quadMinus 2 K b c p' = 0)
    (hpp' : polar (quadMinus 2 K b c) p p' = 0) : ∃ μ : K, p' = μ • p := by
  have hpvec := eq_vec p
  by_cases ha : p (.inl i₀) = 0
  · by_cases hd : p (.inr (.inl i₀)) = 0
    · exact absurd (eq_zero_of_singular hirr hQp ha hd) hp
    ·
      refine ⟨p' (.inr (.inl i₀)) / p (.inr (.inl i₀)), ?_⟩
      set μ := p' (.inr (.inl i₀)) / p (.inr (.inl i₀))
      obtain ⟨hQr, hpr⟩ := singular_sub_smul hirr hQp hQp' hpp' μ
      set r := p' - μ • p with hr
      have hrd : r (.inr (.inl i₀)) = 0 := by
        rw [hr, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hd, sub_self]
      have hrvec := eq_vec r
      rw [hrd] at hrvec
      have h := hQr
      rw [hrvec, quadMinus_vec, mul_zero, zero_add] at h
      obtain ⟨hs, ht⟩ := binary_eq_zero hirr h
      rw [hs, ht, ← smul_e_eq_vec (b := b) (c := c)] at hrvec
      have hra : r (.inl i₀) = 0 := by
        have h1 := hpr
        rw [hrvec, polar_smul_right, polar_comm, hpvec, polar_e_vec, smul_eq_mul] at h1
        rcases mul_eq_zero.mp h1 with h1 | h1
        · exact h1
        · exact absurd h1 hd
      have hr0 : r = 0 := by
        rw [hrvec, hra, zero_smul]
      rw [hr] at hr0
      exact (sub_eq_zero.mp hr0)
  ·
    refine ⟨p' (.inl i₀) / p (.inl i₀), ?_⟩
    set μ := p' (.inl i₀) / p (.inl i₀)
    obtain ⟨hQr, hpr⟩ := singular_sub_smul hirr hQp hQp' hpp' μ
    set r := p' - μ • p with hr
    have hra : r (.inl i₀) = 0 := by
      rw [hr, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ ha, sub_self]
    have hrvec := eq_vec r
    rw [hra] at hrvec
    have h := hQr
    rw [hrvec, quadMinus_vec, zero_mul, zero_add] at h
    obtain ⟨hs, ht⟩ := binary_eq_zero hirr h
    rw [hs, ht, ← smul_f_eq_vec (b := b) (c := c)] at hrvec
    have hrd : r (.inr (.inl i₀)) = 0 := by
      have h1 := hpr
      rw [hrvec, polar_smul_right, polar_comm, hpvec, polar_f_vec, smul_eq_mul] at h1
      rcases mul_eq_zero.mp h1 with h1 | h1
      · exact h1
      · exact absurd h1 ha
    have hr0 : r = 0 := by
      rw [hrvec, hrd, zero_smul]
    rw [hr] at hr0
    exact (sub_eq_zero.mp hr0)

theorem eq_of_isometry_of_singular
    (F : (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) →ₗ[K] (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K))
    (hiso : ∀ w, quadMinus 2 K b c (F w) = quadMinus 2 K b c w)
    (hsing : ∀ w, quadMinus 2 K b c (F w - w) = 0) (w₀ : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) :
    F w₀ = w₀ := by
  set Q' := quadMinus 2 K b c
  set T : (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) →ₗ[K] (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) :=
    F - LinearMap.id with hT
  have hTw : ∀ w, T w = F w - w := fun w => rfl
  have h1 : ∀ y, polar Q' y (T y) = 0 := by
    intro y
    have e : Q' (y + T y) = Q' y := by rw [hTw, add_sub_cancel, hiso]
    have hp : polar Q' y (T y) = Q' (y + T y) - Q' y - Q' (T y) := rfl
    rw [hp, e, hTw, hsing, sub_self, sub_zero]
  have h2 : ∀ y y', polar Q' (T y) (T y') = 0 := by
    intro y y'
    have hp : polar Q' (T y) (T y') = Q' (T y + T y') - Q' (T y) - Q' (T y') := rfl
    rw [hp, ← map_add, hTw, hTw, hTw, hsing, hsing, hsing, sub_self, sub_zero]
  by_contra hne
  have hu : T w₀ ≠ 0 := fun h => hne (sub_eq_zero.mp (by rw [← hTw]; exact h))
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, polar Q' w₁ (T w₀) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hu
    refine hnd.1 (T w₀) fun y => ?_
    rw [polarBilin_apply_apply, polar_comm]
    exact hall y
  obtain ⟨μ, hμ⟩ := exists_eq_smul_of_singular hirr hu (by rw [hTw]; exact hsing w₀)
    (by rw [hTw]; exact hsing w₁) (h2 w₀ w₁)
  have hμ0 : μ = 0 := by
    have h := h1 w₁
    rw [hμ, polar_smul_right, smul_eq_mul] at h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h hw₁
  have hTw₁ : T w₁ = 0 := by rw [hμ, hμ0, zero_smul]
  have h3 := h1 (w₀ + w₁)
  rw [map_add, hTw₁, add_zero, polar_add_left, h1 w₀, zero_add] at h3
  exact hw₁ h3

end OmegaMinusFourGeom

open OmegaMinusFourGeom OmegaMinusFourTrans in
theorem omegaMinusFourGeom_holds : OmegaMinusFourGeomStatement := by
  intro G _ _ M Q Z B hc n t hs hno hom x hx hxt hmov
  classical
  have h34 : Stroth34Statement := stroth34Statement_unconditional
  have hRoot : Stroth310RootStatement := stroth310RootStatement_unconditional
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨hxH, hx2⟩ := conjMod_facts hc ht hx
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre ht
  have hxM : x ∈ M := hx.1
  obtain ⟨K, fK, finK, hK, b, c, hirr, hnat⟩ := hom
  haveI : CharP K 2 := sec7ctr_charP hc hK
  have hnat' := hnat
  obtain ⟨φ, hφ, hker, hact⟩ := hnat
  obtain ⟨-, hn, ψ, hψ⟩ := hact
  haveI := hn
  haveI : Nonempty (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have hX := addCommutantScalar_statedOmegaMinus (le_rfl : 2 ≤ 2) hirr
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  have E := ElemMatrixIso.minus (le_rfl : 2 ≤ 2) hirr
  have h3 : 3 ≤ Module.finrank K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
    omega
  obtain ⟨Fx, hFx⟩ := exists_fx_of_natural h34 (stroth310Chi_of_34 h34)
    sec7CentreMpStatement_holds sec7ZVStatement_holds sec7ZCardStatement_holds hc hs hZ0 hK hX
    φ hφ ψ hψ hxM hxt hxH
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hVR : ∀ y ∈ Rt M (LB M Q B) t, ∀ v ∈ Vt M (LB M Q B) B Z t,
      y * v * y⁻¹ ∈ Vt M (LB M Q B) B Z t := fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hy) v).mp hv
  have hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, x * v * x⁻¹ ∈ Vt M (LB M Q B) B Z t := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp
      (conjSubgroup_eq_self_iff.mp (endg_F0_Vt hc hxM hxt)) v).mp hv
  have hxR : ∀ y ∈ Rt M (LB M Q B) t, x * y * x⁻¹ ∈ Rt M (LB M Q B) t := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp
      (conjSubgroup_eq_self_iff.mp (endg_F0_Rt hc hxM hxt)) y).mp hy
  have hRM : ∀ y ∈ Rt M (LB M Q B) t, y ∈ M := fun y hy => hc.Rt_le_M t hy
  have hVM : ∀ v ∈ Vt M (LB M Q B) B Z t, v ∈ Q := fun v hv => hVQ hv
  have hFFx : ∀ w, Fx (Fx w) = w := by
    intro w
    obtain ⟨k, rfl⟩ := exists_secVec_eq ψ w
    set k₁ : ↥(Vt M (LB M Q B) B Z t) := ⟨x * k * x⁻¹, hxV k k.2⟩ with hk₁
    set k₂ : ↥(Vt M (LB M Q B) B Z t) := ⟨x * k₁ * x⁻¹, hxV k₁ k₁.2⟩ with hk₂
    have e1 : Fx (secVec ψ k) = secVec ψ k₁ := hFx k k₁ rfl
    have e2 : Fx (secVec ψ k₁) = secVec ψ k₂ := hFx k₁ k₂ rfl
    rw [e1, e2, secVec_eq_iff]
    have e3 : (k₂ : G) * (k : G)⁻¹ = ⁅x ^ 2, (k : G)⁆ := by
      rw [hk₂, hk₁]
      simp only [commutatorElement_def, pow_two]
      group
    rw [e3]
    exact Smith81.comm_mem_Z hc.hyp hx2 (hVM k k.2)
  have hcompat : ∀ g ∈ StatedOmega (StatedQuadMinus 2 K b c), ∃ g' ∈ StatedOmega
      (StatedQuadMinus 2 K b c), ∀ w, Fx ((g : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
        (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ Fx w) =
        (g' : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
          (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ w := by
    intro g hg
    have hgR : g ∈ φ.range := by rw [hφ]; exact hg
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hgR
    have ha' : x * (a : G) * x⁻¹ ∈ Rt M (LB M Q B) t := hxR a a.2
    have ha'M : x * (a : G) * x⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem hxM (hRM a a.2)) (M.inv_mem hxM)
    refine ⟨φ ⟨x * (a : G) * x⁻¹, ha'⟩, ?_, ?_⟩
    · rw [← hφ]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    intro w
    obtain ⟨k, rfl⟩ := exists_secVec_eq ψ w
    have eL : Fx ((φ a : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
        (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ Fx (secVec ψ k)) =
        secVec ψ ⟨x * ((a : G) * (x * k * x⁻¹) * (a : G)⁻¹) * x⁻¹,
          hxV _ (hVR a a.2 _ (hxV k k.2))⟩ := by
      have e1 : Fx (secVec ψ k) = secVec ψ ⟨x * k * x⁻¹, hxV k k.2⟩ :=
        hFx k ⟨x * k * x⁻¹, hxV k k.2⟩ rfl
      rw [e1]
      have e2 : (φ a : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
          (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ secVec ψ ⟨x * k * x⁻¹, hxV k k.2⟩ =
          secVec ψ ⟨(a : G) * (x * k * x⁻¹) * (a : G)⁻¹, hVR a a.2 _ (hxV k k.2)⟩ :=
        (hψ a ⟨x * k * x⁻¹, hxV k k.2⟩ _ rfl).symm
      rw [e2]
      exact hFx _ _ rfl
    have eR : (φ ⟨x * (a : G) * x⁻¹, ha'⟩ : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
        (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ secVec ψ k =
        secVec ψ ⟨x * (a : G) * x⁻¹ * k * (x * (a : G) * x⁻¹)⁻¹, hVR _ ha' k k.2⟩ :=
      (hψ ⟨x * (a : G) * x⁻¹, ha'⟩ k _ rfl).symm
    rw [eL, eR, secVec_eq_iff]
    have hz : x * (a : G) * x⁻¹ * ⁅x ^ 2, (k : G)⁆ * (x * (a : G) * x⁻¹)⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 ha'M) _).mp
        (Smith81.comm_mem_Z hc.hyp hx2 (hVM k k.2))
    convert hz using 1
    simp only [commutatorElement_def, pow_two, Subgroup.coe_mk]
    group
  have hN : ∀ A : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K,
      (∀ g ∈ StatedOmega (StatedQuadMinus 2 K b c),
        A * g * A⁻¹ ∈ StatedOmega (StatedQuadMinus 2 K b c)) →
      ∃ c' : K, c' ≠ 0 ∧ ∀ v, quadMinus 2 K b c
        (c' • ((A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
          (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ v)) = quadMinus 2 K b c v := by
    intro A hA
    obtain ⟨c', hc0, hcv⟩ := normalizerOmegaFor_minus K (le_rfl : 2 ≤ 2) hirr A hA
    exact ⟨c', hc0, fun v => by rw [coe_quadMinus]; exact hcv v⟩
  have iso : ∀ v, quadMinus 2 K b c (Fx v) = quadMinus 2 K b c v :=
    vanishGeom_isometry_of_normalizer hQ hN Fx hFFx hcompat
  have hnat'' : SpNat hc t ∨ OmegaNat hc t :=
    Or.inr ⟨K, fK, finK, hK, Or.inr ⟨2, b, c, le_rfl, hirr, hnat'⟩⟩
  have hsingB := hc.omega_singular h34 hRoot hs.toSec5 hnat'' hK E hQ h3 hX φ hφ ψ hψ
  obtain ⟨uB, hQuB, -, hBiff, -, -, -⟩ :=
    hc.omega_points_core h34 hRoot hs.toSec5 hnat'' hK E hQ h3 hX φ hφ hker ψ hψ hsingB
  have hcommV : ∀ k : ↥(Vt M (LB M Q B) B Z t), ⁅x, (k : G)⁆ ∈ Vt M (LB M Q B) B Z t := by
    intro k
    have e : ⁅x, (k : G)⁆ = (x * k * x⁻¹) * (k : G)⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact (Vt M (LB M Q B) B Z t).mul_mem (hxV k k.2) ((Vt M (LB M Q B) B Z t).inv_mem k.2)
  have hcommvec : ∀ k : ↥(Vt M (LB M Q B) B Z t),
      secVec ψ ⟨⁅x, (k : G)⁆, hcommV k⟩ = Fx (secVec ψ k) - secVec ψ k := by
    intro k
    have e : (⟨⁅x, (k : G)⁆, hcommV k⟩ : ↥(Vt M (LB M Q B) B Z t)) =
        ⟨x * k * x⁻¹, hxV k k.2⟩ * k⁻¹ := Subtype.ext (by simp [commutatorElement_def])
    rw [e, secVec_mul, secVec_inv, hFx k ⟨x * k * x⁻¹, hxV k k.2⟩ rfl, sub_eq_add_neg]
  by_contra hcon
  push Not at hcon
  have hsingC : ∀ k : ↥(Vt M (LB M Q B) B Z t),
      quadMinus 2 K b c (secVec ψ ⟨⁅x, (k : G)⁆, hcommV k⟩) = 0 := by
    intro k
    obtain ⟨r₀, hr₀, hu₀⟩ := hcon k k.2
    have hQM : Q ≤ M := fun q hq => hc.LB_le_M (Subgroup.mem_sup_left hq)
    have hbM : ∀ b' ∈ conjSubgroup r₀ B, b' ∈ M := fun b' hb' => by
      have hb'' : r₀⁻¹ * b' * r₀ ∈ B := mem_conjSubgroup.mp hb'
      have e : b' = r₀ * (r₀⁻¹ * b' * r₀) * r₀⁻¹ := by group
      rw [e]
      exact M.mul_mem (M.mul_mem (hRM r₀ hr₀) (hQM (hc.le hb''))) (M.inv_mem (hRM r₀ hr₀))
    have hHR : conjSubgroup r₀ B ≤ Subgroup.normalizer (Z : Set G) := fun b' hb' =>
      hc.hyp.Z_normal.2 (hbM b' hb')
    obtain ⟨a, ha, z, hz, haz⟩ := exists_mul_of_mem_sup_of_le_normalizer hHR hu₀
    have haV : a ∈ Vt M (LB M Q B) B Z t := by
      have hb' : r₀⁻¹ * a * r₀ ∈ B := mem_conjSubgroup.mp ha
      have e : a = r₀ * (r₀⁻¹ * a * r₀) * r₀⁻¹ := by group
      rw [e]
      exact hVR r₀ hr₀ _ (hBV hb')
    have hzV : z ∈ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt hz
    have hsv : secVec ψ ⟨⁅x, (k : G)⁆, hcommV k⟩ = secVec ψ ⟨a, haV⟩ := by
      have e : (⟨⁅x, (k : G)⁆, hcommV k⟩ : ↥(Vt M (LB M Q B) B Z t)) = ⟨a, haV⟩ * ⟨z, hzV⟩ :=
        Subtype.ext haz.symm
      rw [e, secVec_mul, (secVec_eq_zero_iff ψ ⟨z, hzV⟩).mpr hz, add_zero]
    rw [hsv]
    have hb' : r₀⁻¹ * a * r₀ ∈ B := mem_conjSubgroup.mp ha
    have hbV : r₀⁻¹ * a * r₀ ∈ Vt M (LB M Q B) B Z t := hBV hb'
    obtain ⟨c', hc'⟩ := (hBiff (secVec ψ ⟨r₀⁻¹ * a * r₀, hbV⟩)).mp ⟨⟨_, hbV⟩, hb', rfl⟩
    have hsa : secVec ψ ⟨a, haV⟩ = (φ ⟨r₀, hr₀⟩ : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
        (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ secVec ψ ⟨r₀⁻¹ * a * r₀, hbV⟩ :=
      hψ ⟨r₀, hr₀⟩ ⟨r₀⁻¹ * a * r₀, hbV⟩ ⟨a, haV⟩ (by group)
    have hmemr : (φ ⟨r₀, hr₀⟩ : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) ∈
        StatedOmega (StatedQuadMinus 2 K b c) := by
      rw [← hφ]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    rw [hsa, hc', vanishGeom_isometry_of_mem E hmemr, QuadraticMap.map_smul, hQuB, smul_zero]
  have hsingT : ∀ w, quadMinus 2 K b c (Fx w - w) = 0 := by
    intro w
    obtain ⟨k, rfl⟩ := exists_secVec_eq ψ w
    rw [← hcommvec]
    exact hsingC k
  obtain ⟨v₀, hv₀, hv₀Z⟩ := hmov
  apply hv₀Z
  have h0 := hcommvec ⟨v₀, hv₀⟩
  rw [eq_of_isometry_of_singular hirr Fx iso hsingT, sub_self] at h0
  exact (secVec_eq_zero_iff ψ _).mp h0

end CFSG.RankThree.GF2n.Stroth80
