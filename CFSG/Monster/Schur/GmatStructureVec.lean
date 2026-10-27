module

public import CFSG.Monster.Schur.GmatStructurePhi

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Schur

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Griess CFSG.Monster.B Subgroup
open scoped IsMulCommutative

theorem visModLat_repVis_PhiV (g : Gvis) (w : Additive VisMod) :
    visModLat (((repVis g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive VisMod)) :
      Additive VisMod →ₗ[ZMod 2] Additive VisMod) w) = PhiV g • visModLat w := by
  obtain ⟨p, rfl⟩ := eq_thetaEquiv g
  rw [visModLat_repVis p w, PhiV_thetaEquiv, modTwoUnit_smul]

@[expose] def qN (q : Qmat) : rhoQvis :=
  ⟨⟨q.1, Qmat_le_Hmat q.2⟩, Subgroup.mem_subgroupOf.2 q.2⟩

theorem qN_mul (a b : Qmat) : qN (a * b) = qN a * qN b := rfl

@[expose] def vecQ (q : Qmat) : L2 :=
  visModLat (Additive.ofMul (QuotientGroup.mk (qN q) : VisMod))

theorem vecQ_mul (a b : Qmat) : vecQ (a * b) = vecQ a + vecQ b := by
  unfold vecQ
  rw [qN_mul, QuotientGroup.mk_mul, ofMul_mul, map_add]

theorem vecQ_one : vecQ 1 = 0 := by
  have := vecQ_mul 1 1
  rw [mul_one] at this
  exact left_eq_add.1 this

theorem rhoN_zQ_ne_one : rhoN zQ ≠ 1 := fun h => by
  have h1 := congrArg (fun a : rhoQvis => ((a : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB)) h
  simp only [coe_coe_rhoN_zQ] at h1
  exact xmat_ne_one (xmat_eq_xB ▸ h1)

theorem orderOf_rhoN_zQ : orderOf (rhoN zQ) = 2 := by
  refine orderOf_eq_prime ?_ rhoN_zQ_ne_one
  rw [pow_two, ← rhoN_mul]
  have : zQ * zQ = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, orderOf_zQ]
  rw [this, rhoN_one]

theorem vecQ_eq_zero_iff (q : Qmat) :
    vecQ q = 0 ↔ (q : SpaceB ≃ₗ[ℚ] SpaceB) = 1 ∨ (q : SpaceB ≃ₗ[ℚ] SpaceB) = xmat := by
  unfold vecQ
  rw [map_eq_zero_iff _ visModLat.injective, ← ofMul_one, Additive.ofMul.apply_eq_iff_eq,
    QuotientGroup.eq_one_iff]
  show qN q ∈ zRho ↔ _
  rw [zRho, mem_zpowers_iff_of_orderOf_eq_two orderOf_rhoN_zQ]
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg (fun a : rhoQvis => ((a : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB)) h)
    · right
      have h2 : ((qN q : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = ((rhoN zQ : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) :=
        congrArg (fun a : rhoQvis => ((a : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB)) h
      exact h2.trans (coe_coe_rhoN_zQ.trans xmat_eq_xB.symm)
  · rintro (h | h)
    · exact Or.inl (Subtype.ext (Subtype.ext h))
    · right
      refine Subtype.ext (Subtype.ext ?_)
      change (q : SpaceB ≃ₗ[ℚ] SpaceB) = ((rhoN zQ : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB)
      rw [coe_coe_rhoN_zQ, ← xmat_eq_xB]
      exact h

theorem vecQ_surjective : Function.Surjective vecQ := by
  intro v
  obtain ⟨w, rfl⟩ := visModLat.surjective v
  obtain ⟨y, rfl⟩ := Additive.ofMul.surjective w
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨⟨r.1.1, Subgroup.mem_subgroupOf.1 r.2⟩, rfl⟩

theorem vecQ_conj (g : Gvis) (q : Qmat) (hgq : (g : SpaceB ≃ₗ[ℚ] SpaceB) * q * (g : _)⁻¹ ∈ Qmat) :
    vecQ ⟨g * q * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹, hgq⟩ = PhiV g • vecQ q := by
  unfold vecQ
  rw [← visModLat_repVis_PhiV, repVis_apply]
  rfl

end CFSG.Monster.Schur
