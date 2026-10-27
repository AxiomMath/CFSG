module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CTypeA

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem statedOmega_isometry95 {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {f : (ι → K) → K} {g : GL ι K} (hg : g ∈ StatedOmega f) (v : ι → K) :
    f ((g : Matrix ι ι K) *ᵥ v) = f v := by
  let I : Subgroup (GL ι K) :=
    { carrier := {A | ∀ v, f ((A : Matrix ι ι K) *ᵥ v) = f v}
      one_mem' := fun v => by simp
      mul_mem' := fun {a b} ha hb v => by
        simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
        rw [ha, hb]
      inv_mem' := fun {a} ha v => by
        have := ha (((a⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)
        simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this.symm }
  have hcl : Subgroup.closure {A : GL ι K | ∀ v, f ((A : Matrix ι ι K) *ᵥ v) = f v} ≤ I :=
    (Subgroup.closure_le I).mpr fun A hA => hA
  have hg' : g ∈ Subgroup.closure {A : GL ι K | ∀ v, f ((A : Matrix ι ι K) *ᵥ v) = f v} :=
    Subgroup.commutator_le_self _ hg
  exact hcl hg' v

section Coord

variable {K : Type} [Field K] [Finite K] [CharP K 2] {hc : Ctx M Q Z B} {n : ℕ} {t : G}
  [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]

theorem Coord95.quad_secVec_eq_zero_of_isSingV (C : Coord95 hc t K) (hs : Sec9Hyp hc n t) {v : G}
    (hv : v ∈ Vt M (LB M Q B) B Z t) (hsing : IsSingV M Q Z B t v) :
    quadPlus 2 K (secVec C.ψ ⟨v, hv⟩) = 0 := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  obtain ⟨ρ, hρ, b, hb, hZ⟩ := hsing
  have hbV : b ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht hb
  have hρbV : ρ * b * ρ⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hρ) b).mp hbV
  have h1 : secVec C.ψ ⟨v, hv⟩ = secVec C.ψ ⟨ρ * b * ρ⁻¹, hρbV⟩ :=
    (secVec_eq_iff C.ψ _ _).mpr hZ
  obtain ⟨c, hc'⟩ := (C.hBiff (secVec C.ψ ⟨b, hbV⟩)).mp ⟨⟨b, hbV⟩, hb, rfl⟩
  have h2 : secVec C.ψ ⟨ρ * b * ρ⁻¹, hρbV⟩ =
      (C.φ ⟨ρ, hρ⟩ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ secVec C.ψ ⟨b, hbV⟩ :=
    C.hψ ⟨ρ, hρ⟩ ⟨b, hbV⟩ ⟨ρ * b * ρ⁻¹, hρbV⟩ rfl
  have hΩ : C.φ ⟨ρ, hρ⟩ ∈ StatedOmega (StatedQuadPlus 2 K) := C.hφ ▸ ⟨_, rfl⟩
  have h3 := statedOmega_isometry95 hΩ C.u
  rw [← coe_quadPlus 2 K] at h3
  rw [h1, h2, hc', Matrix.mulVec_smul, map_smul_eq_sq, h3, C.hQu, mul_zero]

end Coord

end HS9

end CFSG.RankThree.GF2n.Stroth80
