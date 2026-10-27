module

public import CFSG.LargeExtraspecial.S10ModelC
public import CFSG.LargeExtraspecial.S4EightG
public import CFSG.LargeExtraspecial.S6Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S10
open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

public section


open CFSG CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S10
open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

namespace CertificateChecks.Batch19951

open CFSG CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S10
open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

private theorem σ₁_cube_0 : σ₁ * σ₁ * σ₁ = 1 := by
  decide +kernel

private theorem σ₂_cube_1 : σ₂ * σ₂ * σ₂ = 1 := by
  decide +kernel

private theorem σ₁_σ₂_comm_2 : σ₁ * σ₂ = σ₂ * σ₁ := by
  decide +kernel

private theorem τ₁_σ₁_3 : τ₁ * σ₁ = σ₁ * σ₁ * τ₁ := by
  decide +kernel

private theorem τ₁_σ₂_4 : τ₁ * σ₂ = σ₂ * τ₁ := by
  decide +kernel

private theorem τ₂_σ₁_5 : τ₂ * σ₁ = σ₁ * τ₂ := by
  decide +kernel

private theorem τ₂_σ₂_6 : τ₂ * σ₂ = σ₂ * σ₂ * τ₂ := by
  decide +kernel

private theorem τ₁_comm_σ₂_7 : τ₁⁻¹ * (σ₂ * τ₁ * σ₂⁻¹) = 1 := by
  decide +kernel

end CertificateChecks.Batch19951

namespace Certificates

open CertificateChecks

open CFSG CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S10 in
open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions in
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 in
theorem certificate19951 : (σ₁ * σ₁ * σ₁ = 1)
    ∧ (σ₂ * σ₂ * σ₂ = 1)
    ∧ (σ₁ * σ₂ = σ₂ * σ₁)
    ∧ (τ₁ * σ₁ = σ₁ * σ₁ * τ₁)
    ∧ (τ₁ * σ₂ = σ₂ * τ₁)
    ∧ (τ₂ * σ₁ = σ₁ * τ₂)
    ∧ (τ₂ * σ₂ = σ₂ * σ₂ * τ₂)
    ∧ (τ₁⁻¹ * (σ₂ * τ₁ * σ₂⁻¹) = 1) := by
  exact ⟨@CertificateChecks.Batch19951.σ₁_cube_0, @CertificateChecks.Batch19951.σ₂_cube_1, @CertificateChecks.Batch19951.σ₁_σ₂_comm_2,
    @CertificateChecks.Batch19951.τ₁_σ₁_3, @CertificateChecks.Batch19951.τ₁_σ₂_4, @CertificateChecks.Batch19951.τ₂_σ₁_5, @CertificateChecks.Batch19951.τ₂_σ₂_6,
    @CertificateChecks.Batch19951.τ₁_comm_σ₂_7⟩

end Certificates
