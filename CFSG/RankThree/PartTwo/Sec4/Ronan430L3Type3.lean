module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan430L3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

variable {K : Type} [Field K]

theorem eq_one_of_commute_type3 {π : Bool} {q : ℕ} {y s : GL (Fin 3) K}
    (hy : Type123 π q K y 3) (hs2 : s * s = 1) (hdet : (s : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hc : y * s = s * y) : s = 1 := by
  obtain ⟨-, -, hirr⟩ := hy
  have hSS : (s : Matrix (Fin 3) (Fin 3) K) * s = 1 := by
    rw [← Units.val_mul, hs2, Units.val_one]
  have hYS : (y : Matrix (Fin 3) (Fin 3) K) * s = s * y := by
    rw [← Units.val_mul, ← Units.val_mul, hc]
  set S : Matrix (Fin 3) (Fin 3) K := (s : Matrix (Fin 3) (Fin 3) K) with hS
  set Y : Matrix (Fin 3) (Fin 3) K := (y : Matrix (Fin 3) (Fin 3) K) with hY
  set W : Submodule K (Fin 3 → K) := LinearMap.ker (Matrix.toLin' (S + 1)) with hW
  have hmemW : ∀ v, v ∈ W ↔ (S + 1) *ᵥ v = 0 := fun v => by
    rw [hW, LinearMap.mem_ker, Matrix.toLin'_apply]
  have hc' : (S + 1) * Y = Y * (S + 1) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hYS]
  have hinv : ∀ v ∈ W, Y *ᵥ v ∈ W := by
    intro v hv
    rw [hmemW] at hv ⊢
    rw [Matrix.mulVec_mulVec, hc', ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  rcases hirr W hinv with h | h
  ·
    have hinj : ∀ v, (S + 1) *ᵥ v = 0 → v = 0 := fun v hv => by
      have : v ∈ W := (hmemW v).mpr hv
      rw [h] at this
      exact (Submodule.mem_bot K).mp this
    have h0 : (S + 1) * (S - 1) = 0 := by
      simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hSS]
      abel
    have hcol : ∀ v, (S - 1) *ᵥ v = 0 := fun v =>
      hinj _ (by rw [Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec])
    have hS1 : S = 1 := by
      have : S - 1 = 0 := by
        ext i j
        have := congrFun (hcol (Pi.single j 1)) i
        simpa [Matrix.mulVec_single] using this
      exact sub_eq_zero.mp this
    exact Units.ext (by rw [Units.val_one, ← hS, hS1])
  ·
    have hS1 : S + 1 = 0 := by
      have : Matrix.toLin' (S + 1) = 0 := LinearMap.ker_eq_top.mp h
      exact Matrix.toLin'.injective (by rw [this, map_zero])
    have hSneg : S = -1 := eq_neg_of_add_eq_zero_left hS1
    rw [hSneg, Matrix.det_neg, Fintype.card_fin, Matrix.det_one] at hdet
    have h2 : (-1 : K) = 1 := by linear_combination hdet
    refine Units.ext ?_
    rw [Units.val_one, ← hS, hSneg]
    ext i j
    rw [Matrix.neg_apply]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, h2]
    · rw [Matrix.one_apply_ne hij, neg_zero]

theorem false_of_commute_mod_scalars_type3 {π : Bool} {q : ℕ} {y s : GL (Fin 3) K}
    (hy : Type123 π q K y 3) (hdet : (s : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hs2 : s * s ∈ StatedScalars (Fin 3) K) (hs1 : s ∉ StatedScalars (Fin 3) K)
    (hc : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K) : False := by
  obtain ⟨ν, hν⟩ := hs2
  obtain ⟨μ, hμ⟩ := hc
  have hsc : ∀ (u : Kˣ) (g : GL (Fin 3) K),
      GeneralLinearGroup.scalar (Fin 3) u * g = g * GeneralLinearGroup.scalar (Fin 3) u :=
    fun u g => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u g).eq.symm
  have hdetsc : ∀ u : Kˣ,
      ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
        (u : K) ^ 3 := fun u => by
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hν3 : (ν : K) ^ 3 = 1 := by
    have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K).det) hν
    simp only [Units.val_mul, Matrix.det_mul, hdet, mul_one] at h
    rw [← hdetsc ν, h]
  have hys : y * s * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ * s := by
    rw [hμ]
    group
  have hμ3 : (μ : K) ^ 3 = 1 := by
    have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K).det) hys
    simp only [Units.val_mul, Matrix.det_mul, hdet, mul_one] at h
    rw [hdetsc μ] at h
    have hy0 : (y : Matrix (Fin 3) (Fin 3) K).det * ((y⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    rw [← h, hy0]
  set t : GL (Fin 3) K := s * (s * s) with ht
  have ht' : t = s * GeneralLinearGroup.scalar (Fin 3) ν := by rw [ht, hν]
  have hscal1 : ∀ u : Kˣ, (u : K) ^ 3 = 1 →
      GeneralLinearGroup.scalar (Fin 3) u * GeneralLinearGroup.scalar (Fin 3) u *
        GeneralLinearGroup.scalar (Fin 3) u = 1 := fun u hu => by
    rw [← map_mul, ← map_mul]
    have : u * u * u = 1 := Units.ext (by
      rw [Units.val_mul, Units.val_mul, Units.val_one, ← hu]
      ring)
    rw [this, map_one]
  have htt : t * t = 1 := by
    have e1 : t * t = (s * s) * (s * s) * (s * s) := by rw [ht]; group
    rw [e1, ← hν]
    exact hscal1 ν hν3
  have htdet : (t : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [ht, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdet]
    ring
  have hyt : y * t = t * y := by
    have e1 : y * t * y⁻¹ = (y * s * y⁻¹) * (y * s * y⁻¹) * (y * s * y⁻¹) := by rw [ht]; group
    rw [hys] at e1
    have e2 : (GeneralLinearGroup.scalar (Fin 3) μ * s) *
        (GeneralLinearGroup.scalar (Fin 3) μ * s) * (GeneralLinearGroup.scalar (Fin 3) μ * s) =
        (GeneralLinearGroup.scalar (Fin 3) μ * GeneralLinearGroup.scalar (Fin 3) μ *
          GeneralLinearGroup.scalar (Fin 3) μ) * t := by
      rw [ht]
      calc (GeneralLinearGroup.scalar (Fin 3) μ * s) * (GeneralLinearGroup.scalar (Fin 3) μ * s) *
            (GeneralLinearGroup.scalar (Fin 3) μ * s) =
          GeneralLinearGroup.scalar (Fin 3) μ * (s * GeneralLinearGroup.scalar (Fin 3) μ) *
            (s * GeneralLinearGroup.scalar (Fin 3) μ) * s := by group
        _ = GeneralLinearGroup.scalar (Fin 3) μ * (GeneralLinearGroup.scalar (Fin 3) μ * s) *
            (GeneralLinearGroup.scalar (Fin 3) μ * s) * s := by rw [← hsc μ s]
        _ = GeneralLinearGroup.scalar (Fin 3) μ * GeneralLinearGroup.scalar (Fin 3) μ *
            (s * GeneralLinearGroup.scalar (Fin 3) μ) * s * s := by group
        _ = GeneralLinearGroup.scalar (Fin 3) μ * GeneralLinearGroup.scalar (Fin 3) μ *
            (GeneralLinearGroup.scalar (Fin 3) μ * s) * s * s := by rw [← hsc μ s]
        _ = _ := by group
    rw [e2, hscal1 μ hμ3, one_mul] at e1
    calc y * t = y * t * y⁻¹ * y := by group
      _ = t * y := by rw [e1]
  have h1 := eq_one_of_commute_type3 hy htt htdet hyt
  apply hs1
  refine ⟨ν⁻¹, ?_⟩
  rw [ht'] at h1
  have : s = (GeneralLinearGroup.scalar (Fin 3) ν)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [this, map_inv]

theorem false_of_commute_type3_of_cube {π : Bool} {q : ℕ} {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) {y V : GL (Fin 3) K} (hy : Type123 π q K y 3) (hV3 : V ^ 3 = 1)
    (hVZ : V ∉ StatedScalars (Fin 3) K) (hc : y * V = V * y) : False := by
  obtain ⟨-, -, hirr⟩ := hy
  have hM3 : (V : Matrix (Fin 3) (Fin 3) K) * V * V = 1 := by
    rw [← Units.val_mul, ← Units.val_mul, ← pow_three', hV3, Units.val_one]
  have hYM : (y : Matrix (Fin 3) (Fin 3) K) * V = V * y := by
    rw [← Units.val_mul, ← Units.val_mul, hc]
  have hdetV : (V : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    (V.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero
  set M : Matrix (Fin 3) (Fin 3) K := (V : Matrix (Fin 3) (Fin 3) K) with hM
  set Y : Matrix (Fin 3) (Fin 3) K := (y : Matrix (Fin 3) (Fin 3) K) with hY
  have hs : τ ^ 2 + τ + 1 = 0 := by
    have h : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hτ1)
  have hprod : (M - 1) * (M - τ • 1) * (M - τ ^ 2 • 1) = 0 := by
    have e : (M - 1) * (M - τ • 1) * (M - τ ^ 2 • 1) =
        M * M * M - (1 + τ + τ ^ 2) • (M * M) + (τ + τ ^ 2 + τ ^ 3) • M - τ ^ 3 • 1 := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, smul_smul, add_smul, smul_sub]
      module
    rw [e, hM3, hτ, show (1 + τ + τ ^ 2) = 0 by linear_combination hs,
      show τ + τ ^ 2 + 1 = 0 by linear_combination hs]
    simp
  have hsing : ∃ l : K, (M - l • 1).det = 0 := by
    by_contra hcon
    push Not at hcon
    have h1 := hcon 1
    have h2 := hcon τ
    have h3 := hcon (τ ^ 2)
    rw [one_smul] at h1
    have := congrArg Matrix.det hprod
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_zero] at this
    exact mul_ne_zero (mul_ne_zero h1 h2) h3 this
  obtain ⟨l, hl⟩ := hsing
  set W : Submodule K (Fin 3 → K) := LinearMap.ker (Matrix.toLin' (M - l • 1)) with hW
  have hmemW : ∀ v, v ∈ W ↔ (M - l • 1) *ᵥ v = 0 := fun v => by
    rw [hW, LinearMap.mem_ker, Matrix.toLin'_apply]
  have hc' : (M - l • 1) * Y = Y * (M - l • 1) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hYM]
  have hinv : ∀ v ∈ W, Y *ᵥ v ∈ W := by
    intro v hv
    rw [hmemW] at hv ⊢
    rw [Matrix.mulVec_mulVec, hc', ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  rcases hirr W hinv with h | h
  ·
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hl
    have : v ∈ W := (hmemW v).mpr hv
    rw [h] at this
    exact hv0 ((Submodule.mem_bot K).mp this)
  ·
    have h0 : M - l • 1 = 0 := by
      have : Matrix.toLin' (M - l • 1) = 0 := LinearMap.ker_eq_top.mp h
      exact Matrix.toLin'.injective (by rw [this, map_zero])
    have hMl : M = l • 1 := sub_eq_zero.mp h0
    have hl0 : l ≠ 0 := by
      rintro rfl
      apply hdetV
      rw [hMl, zero_smul, Matrix.det_zero]
    apply hVZ
    refine ⟨Units.mk0 l hl0, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, ← hM, hMl, Matrix.smul_one_eq_diagonal]
    rfl

variable {H : Type} [Group H] {L : Subgroup H} [hLn : L.Normal] {p f : ℕ} {π : Bool}

theorem eq_one_of_isPGLAt_type3 (hK : PiField π p f K) {e : L ≃* slPi π 3 (p ^ f) K} {x : H}
    {y : GL (Fin 3) K} (hy : IsPGLAt e x y) (h3 : Type123 π (p ^ f) K y 3) {t : H}
    (htL : t ∈ L) (ht2 : t * t = 1) (hxt : x * t = t * x) : t = 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set s : slPi π 3 (p ^ f) K := e ⟨t, htL⟩ with hsdef
  have hc : y * (s : GL (Fin 3) K) = (s : GL (Fin 3) K) * y := isPGLAt_commute_of_mem htL hxt hy
  have hs2 : (s : GL (Fin 3) K) * s = 1 := by
    rw [← Subgroup.coe_mul, hsdef, ← map_mul,
      show (⟨t, htL⟩ * ⟨t, htL⟩ : L) = 1 from Subtype.ext ht2, map_one, Subgroup.coe_one]
  have hdet : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    ((mem_slPi_iff hπ).mp s.2).2
  have h1 := eq_one_of_commute_type3 h3 hs2 hdet hc
  have h1' : s = 1 := Subtype.ext h1
  rw [hsdef, map_eq_one_iff _ e.injective] at h1'
  exact congrArg Subtype.val h1'

theorem eq_one_of_isPGLAtP_type3 (hK : PiField π p f K)
    {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {x : H} {y : GL (Fin 3) K} (hy : IsPGLAtP e x y)
    (h3 : Type123 π (p ^ f) K y 3) {t : H} (htL : t ∈ L) (ht2 : t * t = 1)
    (hxt : x * t = t * x) : t = 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  by_contra ht1
  set m : projImage (slPi π 3 (p ^ f) K) := e ⟨t, htL⟩ with hmdef
  have hm := hy.2 m
  rw [coe_slAct_eqP] at hm
  have heq : (⟨x * ((e.symm m : L) : H) * x⁻¹, hLn.conj_mem _ (e.symm m).2 x⟩ : L) =
      ⟨t, htL⟩ := by
    apply Subtype.ext
    rw [hmdef, MulEquiv.symm_apply_apply]
    change x * t * x⁻¹ = t
    rw [hxt, mul_inv_cancel_right]
  rw [heq] at hm
  obtain ⟨s, hsS, hsm⟩ := m.2
  have hmm : (m : ProjGenLinGroup (Fin 3) K) * m = 1 := by
    rw [← Subgroup.coe_mul, hmdef, ← map_mul,
      show (⟨t, htL⟩ * ⟨t, htL⟩ : L) = 1 from Subtype.ext ht2, map_one, Subgroup.coe_one]
  have hm1 : (m : ProjGenLinGroup (Fin 3) K) ≠ 1 := by
    intro h
    apply ht1
    have h1 : m = 1 := Subtype.ext h
    rw [hmdef, map_eq_one_iff _ e.injective] at h1
    exact congrArg Subtype.val h1
  have hs2 : s * s ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, hsm]
    exact hmm
  have hs1 : s ∉ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, hsm]
    exact hm1
  have hc : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, hsm,
      ← hm, mul_inv_cancel]
  exact false_of_commute_mod_scalars_type3 h3 ((mem_slPi_iff hπ).mp hsS).2 hs2 hs1 hc

end CFSG.RankThree.PartTwo.Sec4.Ronan430L3
