module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinData
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Ambient centralizers of the Klein-four two-core

In the Klein-four branch, every nonidentity element of
`V = O₂(Ĥ)` is an involution fused to the distinguished involution inside
`Ĥ`.  Consequently its ambient centralizer is contained in `Ĥ`.  This is the
centralizer bound used in the source's restriction (5).
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Every nonidentity element of the Klein-four two-core has ambient
centralizer contained in `Ĥ`. -/
public theorem firstCase_klein_centralizer_twoCore_le_Hhat
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    ∀ v : G, v ∈ twoCoreOf c.Hhat → v ≠ 1 →
      Subgroup.centralizer ({v} : Set G) ≤ c.Hhat := by
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
  have hNorm : Subgroup.normalizer (c.U : Set G) = c.Hhat :=
    theorem26_normalizer_U_eq_Hhat hmin c hVne hUne
  have hHhatne : c.Hhat ≠ ⊥ := by
    intro hbot
    have ht : c.t ∈ c.H := by
      rw [c.H_eq_centralizer]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have ht' : c.t ∈ c.Hhat := c.H_le_Hhat ht
    rw [hbot] at ht'
    exact c.t_involution.1 (Subgroup.mem_bot.mp ht')
  have hself : Subgroup.normalizer (c.Hhat : Set G) = c.Hhat :=
    normalizer_eq_of_nontrivial_normal_in_coatom
      (minimalCounterexample_isSimple hmin) c.Hhat_maximal le_rfl hHhatne
      (Subgroup.normal_subgroupOf_of_le_normalizer
        (H := c.Hhat) (N := c.Hhat) Subgroup.le_normalizer)
  intro v hv hvne
  have hvInv : IsInvolution v := by
    have hVK := firstCase_klein_V_klein c hklein
    refine ⟨hvne, ?_⟩
    simpa [pow_two] using
      congrArg Subtype.val (hVK.mul_self (⟨v, hv⟩ : twoCoreOf c.Hhat))
  have h26 := theorem_2_6 hmin c
  have htV : c.t ∈ twoCoreOf c.Hhat :=
    centralizerStructure_t_mem_twoCore c h26
  have htC : c.t ∈
      (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) := by
    rw [← h26.2.1] at htV
    exact htV
  have hvC : v ∈
      (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) := by
    rw [← h26.2.1] at hv
    exact hv
  obtain ⟨g, hgHhat, hgv⟩ :=
    theorem26_involutions_in_C_conjugate hmin c hNorm hvInv c.t_involution hvC htC
  intro x hx
  have hxconj : g * x * g⁻¹ ∈ c.H := by
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    calc
      (g * x * g⁻¹) * c.t = (g * x * g⁻¹) * (g * v * g⁻¹) := by rw [hgv]
      _ = g * (x * v) * g⁻¹ := by group
      _ = g * (v * x) * g⁻¹ := by rw [hx]
      _ = (g * v * g⁻¹) * (g * x * g⁻¹) := by group
      _ = c.t * (g * x * g⁻¹) := by rw [hgv]
  have hxHhat : g * x * g⁻¹ ∈ c.Hhat := c.H_le_Hhat hxconj
  have hgNorm : g ∈ Subgroup.normalizer (c.Hhat : Set G) := by
    rw [hself]
    exact hgHhat
  exact (Subgroup.mem_normalizer_iff.mp hgNorm x).2 hxHhat

end CFSG.GorensteinWalter
