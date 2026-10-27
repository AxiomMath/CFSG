module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofFixMat
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJPGL

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1613Res

open CFSG CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open scoped Matrix

variable {K : Type} [Field K]

theorem offdiag_eq_zero_of_commute_diagTau {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {h : GL (Fin 3) K} (hh : h * diagTau hτ = diagTau hτ * h) :
    ∀ i j : Fin 3, i ≠ j → (h : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hτ
    exact zero_ne_one hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h1
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h1, div_one]
  have hττ2 : τ ≠ τ ^ 2 := by
    intro h1
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, ← h1, mul_one]
    exact mul_left_cancel₀ hτ0 this
  set H : Matrix (Fin 3) (Fin 3) K := (h : Matrix (Fin 3) (Fin 3) K) with hHdef
  have hM := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) hh
  simp only [Units.val_mul, coe_diagTau] at hM
  rw [← hHdef] at hM
  have ent : ∀ i j, (H * !![τ, 0, 0; 0, τ ^ 2, 0; 0, 0, 1]) i j =
      (!![τ, 0, 0; 0, τ ^ 2, 0; 0, 0, 1] * H) i j := fun i j => by rw [hM]
  have aux : ∀ {X u v : K}, u ≠ v → X * u = v * X → X = 0 := fun {X u v} huv hX => by
    have h' : X * (u - v) = 0 := by rw [mul_sub, hX, mul_comm, sub_self]
    exact (mul_eq_zero.mp h').resolve_right (sub_ne_zero.mpr huv)
  have e01 := ent 0 1
  have e02 := ent 0 2
  have e10 := ent 1 0
  have e12 := ent 1 2
  have e20 := ent 2 0
  have e21 := ent 2 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e01 e02 e10 e12 e20 e21
  have y01 : H 0 1 = 0 := aux (Ne.symm hττ2) (by linear_combination e01)
  have y02 : H 0 2 = 0 := aux (Ne.symm hτ1) (by linear_combination e02)
  have y10 : H 1 0 = 0 := aux hττ2 (by linear_combination e10)
  have y12 : H 1 2 = 0 := aux (Ne.symm hτ2) (by linear_combination e12)
  have y20 : H 2 0 = 0 := aux hτ1 (by linear_combination e20)
  have y21 : H 2 1 = 0 := aux hτ2 (by linear_combination e21)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [y01, y02, y10, y12, y20, y21] at hij ⊢

theorem commute_of_commute_diagTau {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {h k : GL (Fin 3) K}
    (hh : h * diagTau hτ = diagTau hτ * h) (hk : k * diagTau hτ = diagTau hτ * k) :
    h * k = k * h := by
  have zh := offdiag_eq_zero_of_commute_diagTau hτ hτ1 hh
  have zk := offdiag_eq_zero_of_commute_diagTau hτ hτ1 hk
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  have h01 := zh 0 1 (by decide)
  have h02 := zh 0 2 (by decide)
  have h10 := zh 1 0 (by decide)
  have h12 := zh 1 2 (by decide)
  have h20 := zh 2 0 (by decide)
  have h21 := zh 2 1 (by decide)
  have k01 := zk 0 1 (by decide)
  have k02 := zk 0 2 (by decide)
  have k10 := zk 1 0 (by decide)
  have k12 := zk 1 2 (by decide)
  have k20 := zk 2 0 (by decide)
  have k21 := zk 2 1 (by decide)
  fin_cases i <;> fin_cases j <;>
    simp [h01, h02, h10, h12, h20, h21, k01, k02, k10, k12, k20, k21, mul_comm]

variable {p f : ℕ} {π : Bool}

theorem type1_of_commute_type3 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {y : GL (Fin 3) K} (hy3 : Type123 π (p ^ f) K y 3) {s : GL (Fin 3) K}
    (hs : s ∈ slPi π 3 (p ^ f) K) (hs1 : ProjGenLinGroup.mk s ≠ 1)
    (hs3 : ProjGenLinGroup.mk s ^ 3 = 1)
    (hys : ProjGenLinGroup.mk y * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk y)⁻¹ =
      ProjGenLinGroup.mk s) :
    Type123 π (p ^ f) K s 1 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have h3 := hK.three_ne_zero hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hsH : s ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hs
  have hsZ : s ∉ StatedScalars (Fin 3) K := fun hsZ =>
    hs1 ((mk_eq_one_iff_mem_statedScalars).mpr hsZ)
  have hs3' : s ^ 3 ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow, hs3]
  have hsdet : (s : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hs).2
  have hysZ : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, hys,
      mul_inv_cancel]
  obtain ⟨lam, hlam⟩ := hysZ
  have hysl : y * s * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) lam * s := by
    rw [hlam]
    group
  have hlam1 : lam ≠ 1 := by
    intro hlam1
    refine Sec12.KS128NotHJTC.false_of_commute_irreducible hτ hτ1 h3 hsdet hs3' hsZ ?_ hy3.2.2
    rw [hlam1, map_one, one_mul] at hysl
    calc y * s = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [hysl]
  have htr := trace_eq_zero_of_conj_eq_scalar_mul hlam1 hysl
  have hsZ' : s ∉ zPi π 3 (p ^ f) K := fun hz =>
    hsZ (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)
  have hs3'' : s ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact ⟨pow_mem hsH 3, hs3'⟩
  rcases type123_exhaust hK hq hsH hsZ' hs3'' with h1 | h2 | h3'
  · exact h1
  · exact absurd htr (trace_ne_zero_of_type2 hK hq h2)
  · exact absurd ⟨s, hs, fun m _ => rfl⟩ (not_inner_of_type3 hK hq hsH h3')

theorem commute_of_sq_of_commute_type1 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {s : GL (Fin 3) K} (hs1 : Type123 π (p ^ f) K s 1) {h k : GL (Fin 3) K}
    (hh2 : h ^ 2 ∈ StatedScalars (Fin 3) K) (hk2 : k ^ 2 ∈ StatedScalars (Fin 3) K)
    (hhs : ProjGenLinGroup.mk h * ProjGenLinGroup.mk s =
      ProjGenLinGroup.mk s * ProjGenLinGroup.mk h)
    (hks : ProjGenLinGroup.mk k * ProjGenLinGroup.mk s =
      ProjGenLinGroup.mk s * ProjGenLinGroup.mk k) :
    ProjGenLinGroup.mk h * ProjGenLinGroup.mk k =
      ProjGenLinGroup.mk k * ProjGenLinGroup.mk h := by
  obtain ⟨τ, hτ, hτ1, z, hz, g, -, hD⟩ := hs1
  obtain ⟨ζ, -, hζ⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hz
  have hsc : ∀ (c : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) c = GeneralLinearGroup.scalar (Fin 3) c * A :=
    fun c A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c A).eq
  have hcomm : ∀ x : GL (Fin 3) K, x ^ 2 ∈ StatedScalars (Fin 3) K →
      ProjGenLinGroup.mk x * ProjGenLinGroup.mk s =
        ProjGenLinGroup.mk s * ProjGenLinGroup.mk x → x * s = s * x := by
    intro x hx2 hxs
    have hxsZ : x * s * x⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K := by
      rw [← mk_eq_one_iff_mem_statedScalars]
      simp only [map_mul, map_inv]
      rw [hxs]
      group
    obtain ⟨μ, hμ⟩ := hxsZ
    have hxs' : x * s * x⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ * s := by
      rw [hμ]
      group
    have hμ1 := Proof1613Fix.eq_one_of_conj_eq_scalar_mul_of_sq hxs' hx2
    rw [hμ1, map_one, one_mul] at hxs'
    calc x * s = x * s * x⁻¹ * x := by group
      _ = s * x := by rw [hxs']
  have hhs' := hcomm h hh2 hhs
  have hks' := hcomm k hk2 hks
  have hconj : ∀ x : GL (Fin 3) K, x * s = s * x →
      (g⁻¹ * x * g) * diagTau hτ = diagTau hτ * (g⁻¹ * x * g) := by
    intro x hxs
    rw [← hD]
    have hxz : x * z = z * x := by rw [← hζ]; exact (hsc ζ x)
    calc g⁻¹ * x * g * (g⁻¹ * (s * z) * g) = g⁻¹ * (x * s) * z * g := by
          rw [show g⁻¹ * x * g * (g⁻¹ * (s * z) * g) = g⁻¹ * (x * s * z) * g by group]
          group
      _ = g⁻¹ * (s * x) * z * g := by rw [hxs]
      _ = g⁻¹ * s * (x * z) * g := by group
      _ = g⁻¹ * s * (z * x) * g := by rw [hxz]
      _ = g⁻¹ * (s * z) * g * (g⁻¹ * x * g) := by group
  have hc := commute_of_commute_diagTau hτ hτ1 (hconj h hhs') (hconj k hks')
  have hhk : h * k = k * h := by
    calc h * k = g * ((g⁻¹ * h * g) * (g⁻¹ * k * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * k * g) * (g⁻¹ * h * g)) * g⁻¹ := by rw [hc]
      _ = k * h := by group
  rw [← map_mul, ← map_mul, hhk]

end CFSG.RankThree.PartTwo.Sec16.Proof1613Res
