module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.corollary_11_2_a

namespace CFSG
end CFSG
open CFSG

/-!
# Corollary 11.2(b)

This file contains the Section 11 Corollary 11.2(b) statement and proof.
-/

section Section11

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Corollary 11.2(b). -/
public theorem CFSG.corollary_11_2_b
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) {g : G}
    (hgM : g ∉ M) (hAgM : A ≤ M.conjBy g) :
    section10Msigma M ⊓ Subgroup.centralizer ((A0.conjBy g) : Set G) = ⊥ := by
  have hcent_le_Mg : Subgroup.centralizer ((A0.conjBy g) : Set G) ≤ M.conjBy g := by
    intro x hx
    have hx_norm : x ∈ Subgroup.normalizer (A0.conjBy g : Set G) :=
      centralizer_le_normalizer (A0.conjBy g) hx
    have hx_back_norm : g⁻¹ * x * g ∈ Subgroup.normalizer (A0 : Set G) := by
      rw [Subgroup.mem_normalizer_iff] at hx_norm ⊢
      intro z
      constructor
      · intro hz
        have hz_g : g * z * g⁻¹ ∈ A0.conjBy g :=
          Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
        have hconj_g :
            x * (g * z * g⁻¹) * x⁻¹ ∈ A0.conjBy g :=
          (hx_norm (g * z * g⁻¹)).1 hz_g
        rcases Subgroup.mem_map.mp hconj_g with ⟨w, hw, hw_eq⟩
        have htarget : g⁻¹ * x * g * z * (g⁻¹ * x * g)⁻¹ = w := by
          calc
            g⁻¹ * x * g * z * (g⁻¹ * x * g)⁻¹ =
                g⁻¹ * (x * (g * z * g⁻¹) * x⁻¹) * g := by
              group
            _ = g⁻¹ * (g * w * g⁻¹) * g := by
              rw [← hw_eq]
              simp [MulAut.conj_apply]
            _ = w := by
              group
        rw [htarget]
        exact hw
      · intro hz
        have hpre :
            x * (g * z * g⁻¹) * x⁻¹ ∈ A0.conjBy g := by
          refine Subgroup.mem_map.mpr ?_
          refine ⟨g⁻¹ * x * g * z * (g⁻¹ * x * g)⁻¹, hz, ?_⟩
          simp [MulAut.conj_apply]
          group
        have hz_g_mem : g * z * g⁻¹ ∈ A0.conjBy g :=
          (hx_norm (g * z * g⁻¹)).2 hpre
        rcases Subgroup.mem_map.mp hz_g_mem with ⟨w, hw, hw_eq⟩
        have hw_eq : w = z := by
          apply (MulAut.conj g).injective
          simpa [MulAut.conj_apply] using hw_eq
        simpa [hw_eq] using hw
    have hx_back_M : g⁻¹ * x * g ∈ M :=
      h11.normalizer_A0_le hx_back_norm
    exact Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hx_back_M, by
      simp [MulAut.conj_apply, mul_assoc]⟩
  have hle :
      section10Msigma M ⊓ Subgroup.centralizer ((A0.conjBy g) : Set G) ≤
        section10Msigma M ⊓ M.conjBy g := by
    exact inf_le_inf_left _ hcent_le_Mg
  have hbot := corollary_11_2_a h11 hgM hAgM
  exact le_bot_iff.mp (by simpa [hbot] using hle)

end Section11
