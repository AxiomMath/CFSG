module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentConfig
public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3TwoLocal
import CFSG.RankThree.PartTwo.Sec4.LThreePiMain
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec4.RonanK432L3HardMat
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree.PartTwo.Sec4 Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)

local notation "pmk" => Matrix.ProjGenLinGroup.mk

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_slPi_mk_eq (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : 9 ∣ qSubPi π (p ^ f)) {Y : GL (Fin 3) K} (hY : Y ∈ glPi π 3 (p ^ f) K) {a c : Kˣ}
    (ha : a ∈ rootsOfUnity (qSubPi π (p ^ f)) K)
    (hY3 : Y ^ 3 = GeneralLinearGroup.scalar (Fin 3) c) (hac : a ^ 3 = c) :
    ∃ s ∈ slPi π 3 (p ^ f) K, pmk s = pmk Y := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have := hK.finite
  have hN0 := qSubPi_ne_zero hK hq
  have : NeZero (qSubPi π (p ^ f)) := ⟨hN0⟩
  have hdetsc : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) c) = c ^ 3 :=
    Units.ext (by rw [GeneralLinearGroup.val_det_apply, det_scalar, Units.val_pow_eq_pow_val])
  set δ := GeneralLinearGroup.det Y * (a ^ 3)⁻¹ with hδ
  have hδ3 : δ ^ 3 = 1 := by
    have h1 : GeneralLinearGroup.det Y ^ 3 = c ^ 3 := by rw [← map_pow, hY3, hdetsc]
    rw [hδ, mul_pow, h1, ← hac, inv_pow, ← pow_mul, mul_inv_cancel]
  have hδN : δ ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
    obtain ⟨k, hk⟩ := dvd_trans (show 3 ∣ 9 by norm_num) h9
    rw [mem_rootsOfUnity, hk, pow_mul, hδ3, one_pow]
  have hcard := card_rootsOfUnity_qSubPi hK hq
  have ht3 : (⟨δ, hδN⟩ : rootsOfUnity (qSubPi π (p ^ f)) K) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hδ3)
  have htpow : (⟨δ, hδN⟩ : rootsOfUnity (qSubPi π (p ^ f)) K) ^
      (Nat.card (rootsOfUnity (qSubPi π (p ^ f)) K) / 3) = 1 := by
    obtain ⟨k, hk⟩ := h9
    rw [hcard, show qSubPi π (p ^ f) / 3 = 3 * k by omega, pow_mul, ht3, one_pow]
  obtain ⟨ζ, hζ⟩ := exists_pow_eq_of_pow_div (G := rootsOfUnity (qSubPi π (p ^ f)) K) (M := 3)
    (by rw [hcard]; exact dvd_trans (by norm_num) h9) htpow
  have hζ3 : (ζ : Kˣ) ^ 3 = δ := by
    have := congrArg Subtype.val hζ
    rwa [Subgroup.coe_pow] at this
  set ν := a * (ζ : Kˣ) with hν
  have hνN : ν ∈ rootsOfUnity (qSubPi π (p ^ f)) K := mul_mem ha ζ.2
  have hν3 : ν ^ 3 = GeneralLinearGroup.det Y := by
    rw [hν, mul_pow, hζ3, hδ, mul_comm (GeneralLinearGroup.det Y), mul_inv_cancel_left]
  refine ⟨GeneralLinearGroup.scalar (Fin 3) ν⁻¹ * Y, (mem_slPi_iff hπ).mpr ⟨mul_mem
    ((scalar_mem_glPi_iff hK ν⁻¹).mpr (inv_mem hνN)) hY, ?_⟩, ?_⟩
  · have h1 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) ν⁻¹ * Y) = 1 := by
      have hdet' : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) ν⁻¹) = ν⁻¹ ^ 3 :=
        Units.ext (by
          rw [GeneralLinearGroup.val_det_apply, det_scalar, Units.val_pow_eq_pow_val])
      rw [map_mul, hdet', inv_pow, hν3, inv_mul_cancel]
    rw [← GeneralLinearGroup.val_det_apply, h1, Units.val_one]
  · rw [map_mul, ProjGenLinGroup.mk_scalar, one_mul]

variable {ι : Type*} {α : ι → MulAut (projImage (slPi π 3 (p ^ f) K))}
  {e₀ : projImage (slPi π 3 (p ^ f) K)}

theorem CentConfig.false_of_inner (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) (hc : CentConfig π p f K α e₀) (he₀1 : e₀ ≠ 1) (he₀3 : e₀ ^ 3 = 1)
    (hinner : ∀ x, ∃ u : projImage (slPi π 3 (p ^ f) K), α x = MulAut.conj u) : False := by
  obtain ⟨s₀, hs₀, hs₀e⟩ := e₀.2
  have hs₀s : s₀ ∉ StatedScalars (Fin 3) K := fun h =>
    he₀1 (Subtype.ext (by rw [← hs₀e, mk_eq_one_iff_mem_statedScalars.mpr h]; rfl))
  have hs₀3 : s₀ ^ 3 ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow, hs₀e]
    exact congrArg Subtype.val he₀3
  obtain ⟨t, ht, hcomm, hnot⟩ :=
    RonanK432.L3Hard.exists_witness_of_order_three hK hq hs₀ hs₀s hs₀3
  set w := projOf _ ⟨t, ht⟩ * e₀ * (projOf _ ⟨t, ht⟩)⁻¹ with hw
  have hwc : (w : ProjGenLinGroup (Fin 3) K) = pmk t * pmk s₀ * (pmk t)⁻¹ := by
    rw [hw, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_projOf, ← hs₀e]
  have hwe : w * e₀ = e₀ * w := Subtype.ext (by
    simp only [Subgroup.coe_mul]
    rw [hwc, ← hs₀e]
    exact hcomm)
  have hw3 : w ^ 3 = 1 := by
    rw [hw, conj_pow, he₀3, mul_one, mul_inv_cancel]
  have hmem := hc.mem_zpowers_of_inner hK hq hq2 hinner hwe hw3
  apply hnot
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← hwc, ← hk, Subgroup.coe_zpow, ← hs₀e]

theorem CentConfig.false_of_block_lifts (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) (hc : CentConfig π p f K α e₀) (he₀1 : e₀ ≠ 1) (he₀3 : e₀ ^ 3 = 1)
    (h9 : 9 ∣ qSubPi π (p ^ f))
    (hlift : ∀ x, ∃ y ∈ glPi π 3 (p ^ f) K, (y : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 ∧
      (y : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 ∧ (y : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧
      (y : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
      ∀ m, (α x m : ProjGenLinGroup (Fin 3) K) = pmk y * m * (pmk y)⁻¹) : False := by
  refine hc.false_of_inner hK hq hq2 he₀1 he₀3 fun x => ?_
  obtain ⟨y, hy, h01, h02, h10, h20, hyx⟩ := hlift x
  obtain ⟨c, hc3⟩ := pow_three_mem_scalars hK hq hq2 (hc.pow_three x) hyx
  have hdet : (y : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    (y.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero
  have h00 : (y : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro h
    apply hdet
    rw [det_fin_three, h, h01, h02]
    ring
  set a := Units.mk0 _ h00 with ha
  have hrow : ∀ (B : Matrix (Fin 3) (Fin 3) K) (j : Fin 3),
      ((y : Matrix (Fin 3) (Fin 3) K) * B) 0 j = (y : Matrix (Fin 3) (Fin 3) K) 0 0 * B 0 j := by
    intro B j
    rw [Matrix.mul_apply, Fin.sum_univ_three, h01, h02]
    ring
  have hy3 : ((y ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 =
      (y : Matrix (Fin 3) (Fin 3) K) 0 0 ^ 3 := by
    rw [Units.val_pow_eq_pow_val, pow_succ', pow_succ', pow_one, hrow, hrow]
    ring
  have hac : a ^ 3 = c := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ha, Units.val_mk0, ← hy3, ← hc3]
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have haN : a ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
    cases π
    · have hU := hK.unitary
      rw [mem_rootsOfUnity']
      have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) K => A 0 0) ((mem_glPi_false hU).mp hy)
      simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.map_apply,
        h10, h20, map_zero, zero_mul, mul_zero, add_zero, Matrix.one_apply_eq,
        hU.bar_apply] at h
      rw [ha, Units.val_mk0]
      change (y : Matrix (Fin 3) (Fin 3) K) 0 0 ^ (p ^ f + 1) = 1
      rw [pow_succ]
      exact h
    · have := hK.finite
      exact mem_rootsOfUnity_of_card (by simpa [piCard] using hK.card) a
  obtain ⟨s, hs, hsy⟩ := exists_slPi_mk_eq hK hq h9 hy haN hc3.symm hac
  refine ⟨⟨pmk y, s, hs, hsy⟩, ?_⟩
  ext m
  rw [hyx, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]

theorem eq_of_mk_rootGL_eq {s t : K} (h : pmk (rootGL s) = pmk (rootGL t)) : s = t := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h00 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hu
  have h01 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 1) hu
  simp only [Units.val_mul, coe_rootGL, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.mul_diagonal] at h00 h01
  simp at h00 h01
  rw [h00, Units.val_one, mul_one] at h01
  exact h01

theorem CentConfig.false_of_rootGroup (hK : PiField true p f K) (hq : ModThree true (p ^ f))
    {α : ι → MulAut (projImage (slPi true 3 (p ^ f) K))}
    {e₀ : projImage (slPi true 3 (p ^ f) K)} (hc : CentConfig true p f K α e₀) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (he₀ : (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagTau hτ))
    (hdiag : ∀ x, ∃ a b c : Kˣ, ∀ m, (α x m : ProjGenLinGroup (Fin 3) K) =
      pmk (diagUnits a b c) * m * (pmk (diagUnits a b c))⁻¹) : False := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set φ : Multiplicative K →* projImage (slPi true 3 (p ^ f) K) :=
    (projOf (slPi true 3 (p ^ f) K)).comp ((rootHom K).codRestrict (slPi true 3 (p ^ f) K)
      fun t => rootGL_mem_slPi _ _) with hφ
  have hφc : ∀ t : K, (φ (Multiplicative.ofAdd t) : ProjGenLinGroup (Fin 3) K) = pmk (rootGL t) :=
    fun t => rfl
  have hU3 : ¬ 3 ∣ Nat.card φ.range := by
    have h := Subgroup.card_range_dvd φ
    have hcard : Nat.card (Multiplicative K) = p ^ f := by
      rw [show Nat.card (Multiplicative K) = Nat.card K from rfl, hK.card]
      rfl
    rw [hcard] at h
    intro h3
    have h3p : 3 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (dvd_trans h3 h)
    have hp3 : p = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hK.prime).mp h3p).symm
    subst hp3
    change 3 ^ f % 3 = 1 at hq
    have h0 : 3 ^ f % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by have := hK.one_le; omega))
    omega
  have hinv : ∀ x, ∀ w ∈ φ.range, α x w ∈ φ.range := by
    rintro x _ ⟨t, rfl⟩
    obtain ⟨a, b, c, hx⟩ := hdiag x
    refine ⟨Multiplicative.ofAdd ((a : K) * ((b⁻¹ : Kˣ) : K) * t.toAdd), Subtype.ext ?_⟩
    rw [hφc, hx, show φ t = φ (Multiplicative.ofAdd t.toAdd) from rfl, hφc, ← map_inv, ← map_mul,
      ← map_mul, diagUnits_conj_rootGL]
  obtain ⟨x₀, hx₀⟩ := hc.conj_e
  have hfix := congrArg Subtype.val
    (hc.hV _ hU3 hinv x₀ (φ (Multiplicative.ofAdd 1)) ⟨_, rfl⟩)
  rw [hx₀, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hφc, he₀,
    ← map_inv, ← map_mul, ← map_mul, diagTau_eq_diagUnits hτ hτ0, diagUnits_conj_rootGL] at hfix
  have h2 := eq_of_mk_rootGL_eq hfix
  simp only [Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, mul_one] at h2
  apply hτ1
  have h3 : τ = τ ^ 2 := by
    calc τ = τ * (τ ^ 2)⁻¹ * τ ^ 2 := by field_simp
      _ = τ ^ 2 := by rw [h2, one_mul]
  have : τ * (τ - 1) = 0 := by linear_combination -h3
  exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hτ0))

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
