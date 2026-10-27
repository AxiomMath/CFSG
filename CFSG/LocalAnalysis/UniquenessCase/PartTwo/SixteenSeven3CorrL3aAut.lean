module

public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.RankThree.PartOne.N1322.ExtraspecialAbs
public import CFSG.Monster.B.Short.Extraspecial

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin
open CFSG.RankThree.PartOne.N1322 (ext27_pm ext27_center_cube)

private theorem s16c167_mulAut_eq_one_of_pos {H : Type} [Group H] [Finite H]
    (hcard : Nat.card H = 27) (hext : CFSG.IsExtraspecialPGroup 3 H) {θ : MulAut H}
    (hθ2 : θ * θ = 1) (hθz : ∀ z ∈ Subgroup.center H, θ z = z)
    (hθpos : ∀ a, θ a * a⁻¹ ∈ Subgroup.center H) : θ = 1 := by
  have hθ2' : ∀ x, θ (θ x) = x := fun x => by
    have := congrArg (fun f : MulAut H => f x) hθ2
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  ext a
  set ζ : H := θ a * a⁻¹ with hζdef
  have hz : ζ ∈ Subgroup.center H := by rw [hζdef]; exact hθpos a
  have hθa : θ a = ζ * a := by rw [hζdef]; group
  have h1 : θ (θ a) = ζ * (ζ * a) := by
    calc θ (θ a) = θ (ζ * a) := by rw [hθa]
      _ = θ ζ * θ a := map_mul θ ζ a
      _ = ζ * (ζ * a) := by rw [hθz ζ hz, hθa]
  have hsq : ζ ^ 2 = 1 := by
    have h4 : ζ ^ 2 * a = 1 * a := by
      rw [pow_two, mul_assoc, ← h1, hθ2' a, one_mul]
    exact mul_right_cancel h4
  have hcube : ζ ^ 3 = 1 := ext27_center_cube hext ζ hz
  have hζ1 : ζ = 1 := by
    calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hcube, hsq]; simp
  rw [hθa, hζ1, one_mul, MulAut.one_apply]

theorem s16c167_aut_eq_of_fix_center {H : Type} [Group H] [Finite H] (hH : IsPOnePlusTwo 3 H)
    {φ ψ : MulAut H} (hφ2 : φ * φ = 1) (hψ2 : ψ * ψ = 1) (hφψ : φ * ψ = ψ * φ)
    (hφz : ∀ z ∈ Subgroup.center H, φ z = z) (hψz : ∀ z ∈ Subgroup.center H, ψ z = z)
    (hφ1 : φ ≠ 1) (hψ1 : ψ ≠ 1) : φ = ψ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hext : CFSG.IsExtraspecialPGroup 3 H :=
    (CFSG.isExtraspecialPGroup_iff_isExtraspecial (p := 3) (P := H)).mpr hH.1
  have hcard : Nat.card H = 27 := by rw [hH.2.1]; norm_num
  have hφ2' : ∀ x, φ (φ x) = x := fun x => by
    have := congrArg (fun f : MulAut H => f x) hφ2
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  have hψ2' : ∀ x, ψ (ψ x) = x := fun x => by
    have := congrArg (fun f : MulAut H => f x) hψ2
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  have hφneg : ∀ a, φ a * a ∈ Subgroup.center H := by
    rcases ext27_pm hcard hext φ hφz hφ2' with hpos | hneg
    · exact absurd (s16c167_mulAut_eq_one_of_pos hcard hext hφ2 hφz hpos) hφ1
    · exact hneg
  have hψneg : ∀ a, ψ a * a ∈ Subgroup.center H := by
    rcases ext27_pm hcard hext ψ hψz hψ2' with hpos | hneg
    · exact absurd (s16c167_mulAut_eq_one_of_pos hcard hext hψ2 hψz hpos) hψ1
    · exact hneg
  set θ : MulAut H := φ * ψ with hθdef
  have hθ2 : θ * θ = 1 := by
    have hsq : θ * θ = (φ * φ) * (ψ * ψ) := by
      rw [hθdef]
      calc (φ * ψ) * (φ * ψ) = φ * (ψ * φ) * ψ := by group
        _ = φ * (φ * ψ) * ψ := by rw [← hφψ]
        _ = (φ * φ) * (ψ * ψ) := by group
    rw [hsq, hφ2, hψ2, mul_one]
  have hθz : ∀ z ∈ Subgroup.center H, θ z = z := by
    intro z hz
    rw [hθdef, MulAut.mul_apply, hψz z hz, hφz z hz]
  have hθpos : ∀ a, θ a * a⁻¹ ∈ Subgroup.center H := by
    intro a
    have hζ1 : ψ a * a ∈ Subgroup.center H := hψneg a
    have hζ2 : φ a * a ∈ Subgroup.center H := hφneg a
    have h1 : φ (ψ a) = (ψ a * a) * (φ a)⁻¹ := by
      calc φ (ψ a) = φ ((ψ a * a) * a⁻¹) := by
            rw [show (ψ a * a) * a⁻¹ = ψ a by group]
        _ = φ (ψ a * a) * (φ a)⁻¹ := by rw [map_mul, map_inv]
        _ = (ψ a * a) * (φ a)⁻¹ := by rw [hφz (ψ a * a) hζ1]
    have h2 : (φ a)⁻¹ = (φ a * a)⁻¹ * a := by
      calc (φ a)⁻¹ = ((φ a * a) * a⁻¹)⁻¹ := by
            rw [show (φ a * a) * a⁻¹ = φ a by group]
        _ = a * (φ a * a)⁻¹ := by rw [mul_inv_rev, inv_inv]
        _ = (φ a * a)⁻¹ * a := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hζ2) a
    have hkey : θ a * a⁻¹ = (ψ a * a) * (φ a * a)⁻¹ := by
      rw [hθdef, MulAut.mul_apply, h1, h2]
      group
    rw [hkey]
    exact Subgroup.mul_mem _ hζ1 (Subgroup.inv_mem _ hζ2)
  have hθ1 : θ = 1 := s16c167_mulAut_eq_one_of_pos hcard hext hθ2 hθz hθpos
  have hφψ1 : φ * ψ = 1 := by rw [← hθdef]; exact hθ1
  calc φ = φ * 1 := (mul_one φ).symm
    _ = φ * (φ * ψ) := by rw [hφψ1]
    _ = (φ * φ) * ψ := by rw [mul_assoc]
    _ = 1 * ψ := by rw [hφ2]
    _ = ψ := one_mul ψ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
