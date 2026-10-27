module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCentralizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The normalizer of the Klein-four two-core

The source uses `N_G(V)=Ĥ`, where `V=O₂(Ĥ)`.  The point is that an element
normalizing `V` sends the distinguished involution `t` to another nontrivial
element of `V`; Theorem 2.6 fuses that element back to `t` inside `Ĥ`, and the
remaining factor centralizes `t`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the Klein-four branch, the ambient normalizer of `V=O₂(Ĥ)` is exactly
`Ĥ`. -/
public theorem firstCase_klein_normalizer_twoCore_eq_Hhat
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    Subgroup.normalizer (twoCoreOf c.Hhat : Set G) = c.Hhat := by
  classical
  have hVne : twoCoreOf c.Hhat ≠ ⊥ := by
    intro hbot
    have hpbot : pCore 2 c.Hhat = ⊥ := by
      apply (Subgroup.map_eq_bot_iff_of_injective (H := pCore 2 c.Hhat)
        (f := c.Hhat.subtype) c.Hhat.subtype_injective).mp
      simpa [twoCoreOf] using hbot
    have hc4 := hklein.card_four
    have hcbot : Nat.card (pCore 2 c.Hhat) = 1 := by
      rw [hpbot]
      simp
    omega
  have hUne : c.U ≠ ⊥ := (lemma_2_2 hmin c).2
  have hNormU : Subgroup.normalizer (c.U : Set G) = c.Hhat :=
    theorem26_normalizer_U_eq_Hhat hmin c hVne hUne
  have hVnormal : IsNormalIn (twoCoreOf c.Hhat) c.Hhat := by
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
      exact z.2
    · intro h hh v hv
      rcases Subgroup.mem_map.mp hv with ⟨z, hz, rfl⟩
      refine Subgroup.mem_map.mpr ⟨
        (⟨h, hh⟩ : ↥c.Hhat) * z * (⟨h, hh⟩ : ↥c.Hhat)⁻¹, ?_, by simp⟩
      exact (pCore_normal (p := 2) (G := ↥c.Hhat)).conj_mem
        z hz (⟨h, hh⟩ : ↥c.Hhat)
  have hVleS : twoCoreOf c.Hhat ≤ (c.S : Subgroup G) := by
    rw [← (theorem_2_6 hmin c).2.1]
    exact inf_le_left
  have hVklein : IsKleinFour (twoCoreOf c.Hhat) :=
    firstCase_klein_V_klein c hklein
  have hle : c.Hhat ≤ Subgroup.normalizer (twoCoreOf c.Hhat : Set G) :=
    le_normalizer_of_isNormalIn hVnormal
  refine le_antisymm ?_ hle
  intro g hg
  have htV : c.t ∈ twoCoreOf c.Hhat := by
    exact centralizerStructure_t_mem_twoCore c (theorem_2_6 hmin c)
  have htVne : c.t ≠ 1 := c.t_involution.1
  have hgtV : g * c.t * g⁻¹ ∈ twoCoreOf c.Hhat :=
    (Subgroup.mem_normalizer_iff.mp hg c.t).1 htV
  have hgtVne : g * c.t * g⁻¹ ≠ 1 := by
    intro h
    apply htVne
    calc
      c.t = g⁻¹ * (g * c.t * g⁻¹) * g := by group
      _ = 1 := by rw [h]; simp
  have hgtInv : IsInvolution (g * c.t * g⁻¹) := by
    refine ⟨hgtVne, ?_⟩
    rw [pow_two]
    calc
      (g * c.t * g⁻¹) * (g * c.t * g⁻¹) =
          g * (c.t * c.t) * g⁻¹ := by group
      _ = 1 := by rw [← pow_two, c.t_involution.2]; simp
  have htC : c.t ∈
      (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) := by
    rw [(theorem_2_6 hmin c).2.1]
    exact centralizerStructure_t_mem_twoCore c (theorem_2_6 hmin c)
  have hgtC : g * c.t * g⁻¹ ∈
      (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) := by
    have hS : g * c.t * g⁻¹ ∈ (c.S : Subgroup G) := by
      rw [← (theorem_2_6 hmin c).2.1] at hgtV
      exact hgtV.1
    have hC : g * c.t * g⁻¹ ∈ Subgroup.centralizer (c.U : Set G) := by
      -- `g` normalizes `V`, and `V=C_S(U)`; use the normalizer of `U`
      -- obtained above after first aligning the image of `t` in `V`.
      -- This conjunct is not needed for the fusion theorem below: derive it
      -- from membership in `V` directly.
      rw [← (theorem_2_6 hmin c).2.1] at hgtV
      exact hgtV.2
    exact ⟨hS, hC⟩
  obtain ⟨a, haHhat, ha⟩ :=
    theorem26_involutions_in_C_conjugate hmin c hNormU hgtInv c.t_involution
      hgtC htC
  have hag : a * g * c.t * (a * g)⁻¹ = c.t := by
    calc
      a * g * c.t * (a * g)⁻¹ =
          a * (g * c.t * g⁻¹) * a⁻¹ := by group
      _ = a * (g * c.t * g⁻¹) * a⁻¹ := rfl
      _ = c.t := ha
  have hagH : a * g ∈ c.H := by
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    calc
      (a * g) * c.t = ((a * g) * c.t * (a * g)⁻¹) * (a * g) := by group
      _ = c.t * (a * g) := by rw [hag]
  have hagHhat : a * g ∈ c.Hhat := c.H_le_Hhat hagH
  have hga : g = a⁻¹ * (a * g) := by group
  rw [hga]
  exact c.Hhat.mul_mem (c.Hhat.inv_mem haHhat) hagHhat

end CFSG.GorensteinWalter
