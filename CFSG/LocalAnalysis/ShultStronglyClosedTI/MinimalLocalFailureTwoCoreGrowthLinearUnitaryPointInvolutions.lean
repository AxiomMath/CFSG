module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearUnitaryPoint
public import Mathlib.Algebra.CharP.CharAndCard
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearUnitaryRoot

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowth

open Matrix CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.External

universe u

theorem mem_normal_sylow_of_pow_eq_one
    {G : Type u} [Group G] {p : ℕ} (S : Sylow p G)
    (hS : (S : Subgroup G).Normal) {x : G} (hx : x ^ p = 1) : x ∈ S := by
  let : (S : Subgroup G).Normal := hS
  let : CFSG.IsElementaryAbelian p (Subgroup.zpowers x) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hx
  have hX : IsPGroup p (Subgroup.zpowers x) :=
    CFSG.IsElementaryAbelian.isPGroup p (Subgroup.zpowers x)
  have hsup : IsPGroup p ((S : Subgroup G) ⊔ Subgroup.zpowers x : Subgroup G) :=
    S.isPGroup'.to_sup_of_normal_left hX
  have heq : (S : Subgroup G) ⊔ Subgroup.zpowers x = (S : Subgroup G) :=
    S.is_maximal' hsup le_sup_left
  have hmem : x ∈ (S : Subgroup G) ⊔ Subgroup.zpowers x :=
    (le_sup_right : Subgroup.zpowers x ≤ (S : Subgroup G) ⊔ Subgroup.zpowers x)
      (Subgroup.mem_zpowers x)
  rwa [heq] at hmem

variable {K : Type u} [Field K] [Finite K]

theorem unitary_point_involutions_mem_entire_root (J : HermitianForm 3 K)
    (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {g : ProjectiveSpecialUnitaryMatrixGroup J}
    (hg : g ∈ unitaryCoordinateStabilizer J 0) (horder : orderOf g = 2) :
    g ∈ (hermitianUnipotentPSU J hJ).range := by
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let R := (hermitianUnipotentPSU J hJ).range
  let U := unitaryCoordinateStabilizer J 0
  obtain ⟨_rho, S, _D, _hrho, _hnatural, hSR, _hScard, _hnormalizer,
    _hstab, hnormal, _hDle, _hcyclic, _hodd, _hDcard, _hinf, _hsup, _hreg, _htwo⟩ :=
    unitary_entire_root_point_structure J f hf hcard hfixed hJ
  have hSU : (S : Subgroup G) ≤ U := by
    rw [hSR]
    exact unitary_entire_root_fixes_first_coordinate J hJ
  let P : Sylow 2 U := S.subtype hSU
  have hPR : (P : Subgroup U) = R.subgroupOf U := by
    rw [Sylow.coe_subtype, hSR]
  have hPnormal : (P : Subgroup U).Normal := by
    rw [hPR]
    exact hnormal
  let x : U := ⟨g, hg⟩
  have hx : x ^ 2 = 1 := by
    apply Subtype.ext
    exact (orderOf_eq_prime_iff.mp horder).1
  have hxP := mem_normal_sylow_of_pow_eq_one P hPnormal hx
  change x ∈ (P : Subgroup U) at hxP
  rw [hPR] at hxP
  exact hxP

theorem unitary_point_involution_coordinates (J : HermitianForm 3 K)
    (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (g : ProjectiveSpecialUnitaryMatrixGroup J) :
    (g ∈ unitaryCoordinateStabilizer J 0 ∧ orderOf g = 2) ↔
      ∃ z : hermitianUnipotentCoord J,
        z.1.1 = 0 ∧ z.1.2 ≠ 0 ∧ hermitianUnipotentPSU J hJ z = g := by
  let : Fintype K := Fintype.ofFinite K
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (p := 2) (f := f * 2) (by
      simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  constructor
  · rintro ⟨hg, horder⟩
    obtain ⟨z, hz⟩ := unitary_point_involutions_mem_entire_root
      J f hf hcard hfixed hJ hg horder
    have hcoordinates := (unitary_projective_root_involution_iff J hJ z).mp
      (by rw [hz]; exact horder)
    exact ⟨z, hcoordinates.1, hcoordinates.2, hz⟩
  · rintro ⟨z, hfirst, hsecond, rfl⟩
    exact ⟨unitary_entire_root_fixes_first_coordinate J hJ ⟨z, rfl⟩,
      (unitary_projective_root_involution_iff J hJ z).mpr ⟨hfirst, hsecond⟩⟩

theorem unitary_entire_point_involutions_fix_middle (J : HermitianForm 3 K)
    (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {g : ProjectiveSpecialUnitaryMatrixGroup J}
    (hg : g ∈ unitaryCoordinateStabilizer J 0) (horder : orderOf g = 2) :
    g ∈ unitaryMiddleStabilizer J := by
  obtain ⟨z, hfirst, _hsecond, rfl⟩ :=
    (unitary_point_involution_coordinates J f hf hcard hfixed hJ g).mp ⟨hg, horder⟩
  exact (unitary_root_mem_middle_iff J hJ z).mpr hfirst

end CFSG.ShultStronglyClosedTI.TwoCoreGrowth
