module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.Interfaces
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR4

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
  CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
open CFSG.SeitzReduction.E6Pilot CFSG.SeitzReduction.TwistedE6Pilot

section FrameFacts

variable {K : Type} [Field K]

private def e6n0 : Fin TwistTag.E6.tag.rank := ⟨0, by decide⟩

private def e6n5 : Fin TwistTag.E6.tag.rank := ⟨5, by decide⟩

private theorem a2Root_eq_single :
    a2Root = (Pi.single e6n0 1 : Fin TwistTag.E6.tag.rank → ℤ) := by
  decide

private theorem mem_orbitField_twN0 (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c) (c : K) :
    c ∈ orbitField TwistTag.E6 K σ twN0 := by
  have hcard : (TwistTag.E6.orbit twN0).card = 2 := by decide
  rw [mem_orbitField, hcard, pow_two]
  exact hσσ c

end FrameFacts


section FrameData

variable {K : Type} [Field K]

private theorem coe_xC_eq_a2Gen (σ : K →+* K)
    (c : orbitField TwistTag.E6 K σ twN0) :
    (xC TwistTag.E6 K σ twN0 c : ModGL TwistTag.E6.tag K) =
      (a2Gen σ a2Root (c : K) : ModGL TwistTag.E6.tag K) := by
  have hcard : (TwistTag.E6.orbit twN0).card = 2 := by decide
  have hmin : TwistTag.E6.orbitMin twN0 = e6n0 := by decide
  have hp : TwistTag.E6.perm e6n0 = e6n5 := by decide
  rw [show (xC TwistTag.E6 K σ twN0 c : ModGL TwistTag.E6.tag K) =
      (orbitX TwistTag.E6 K σ twN0 c : ModGL TwistTag.E6.tag K) from rfl,
    coe_orbitX, hcard, hmin, List.range_succ, List.range_succ, List.range_zero]
  simp only [List.nil_append, List.cons_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, pow_zero, pow_one, Equiv.Perm.one_apply,
    RingHom.coe_one, id_eq, hp]
  rw [CFSG.SeitzReduction.E6Pilot.coe_a2Gen, a2Root_eq_single, permLattice_single, hp,
    pinnedX_single, pinnedX_single]

private theorem eta_xC (σ : K →+* K) [CharP K 2] (hσσ : ∀ c, σ (σ c) = c)
    (c : orbitField TwistTag.E6 K σ twN0) :
    etaAut σ hσσ (xC TwistTag.E6 K σ twN0 c) =
      xC TwistTag.E6 K σ twN0 ⟨σ (c : K), mem_orbitField_twN0 σ hσσ _⟩ := by
  apply Subtype.ext
  rw [coe_etaAut]
  rw [coe_xC_eq_a2Gen σ c,
    coe_xC_eq_a2Gen σ ⟨σ (c : K), mem_orbitField_twN0 σ hσσ _⟩]
  exact diagramMap_conj_a2Gen σ hσσ a2Root_mem (c : K)

private theorem xi_xC (σ : K →+* K) [CharP K 2] (hσσ : ∀ c, σ (σ c) = c)
    (c : orbitField TwistTag.E6 K σ twN0) :
    xiAut σ hσσ (xC TwistTag.E6 K σ twN0 c) =
      xC TwistTag.E6 K σ twN0 ⟨σ (c : K), mem_orbitField_twN0 σ hσσ _⟩ := by
  apply Subtype.ext
  rw [coe_xiAut]
  change pinnedX TwistTag.E6.tag K e6HighestRoot 1 *
      (diagramMap TwistTag.E6 K * (xC TwistTag.E6 K σ twN0 c :
        ModGL TwistTag.E6.tag K) * (diagramMap TwistTag.E6 K)⁻¹) *
        (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹ =
    (xC TwistTag.E6 K σ twN0 ⟨σ (c : K), mem_orbitField_twN0 σ hσσ _⟩ :
      ModGL TwistTag.E6.tag K)
  rw [coe_xC_eq_a2Gen σ c,
    coe_xC_eq_a2Gen σ ⟨σ (c : K), mem_orbitField_twN0 σ hσσ _⟩]
  rw [diagramMap_conj_a2Gen σ hσσ a2Root_mem (c : K)]
  have hcomm := commute_a2Gen_pinnedX_highRoot σ a2Root_mem (σ (c : K)) 1
  calc pinnedX TwistTag.E6.tag K e6HighestRoot 1 * a2Gen σ a2Root (σ (c : K)) *
        (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹
      = a2Gen σ a2Root (σ (c : K)) * pinnedX TwistTag.E6.tag K e6HighestRoot 1 *
          (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹ := by rw [← hcomm.eq]
    _ = a2Gen σ a2Root (σ (c : K)) := by rw [mul_assoc, mul_inv_cancel, mul_one]

private theorem inv_mul_xC (σ : K →+* K) [CharP K 2]
    (hσσ : ∀ c, σ (σ c) = c) (c : orbitField TwistTag.E6 K σ twN0) :
    (xC TwistTag.E6 K σ twN0 ⟨σ (c : K), mem_orbitField_twN0 σ hσσ _⟩)⁻¹ *
        xC TwistTag.E6 K σ twN0 c =
      xC TwistTag.E6 K σ twN0
        ⟨σ (c : K) + (c : K), mem_orbitField_twN0 σ hσσ _⟩ := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_inv,
    coe_xC_eq_a2Gen σ ⟨σ (c : K), mem_orbitField_twN0 σ hσσ _⟩,
    coe_xC_eq_a2Gen σ c,
    coe_xC_eq_a2Gen σ ⟨σ (c : K) + (c : K), mem_orbitField_twN0 σ hσσ _⟩]
  rw [inv_mul_eq_iff_eq_mul, ← Subgroup.coe_mul, ← a2Gen_add σ a2Root_mem]
  congr 1
  simp only
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

private theorem exists_frame_of_conj (σ : K →+* K) [CharP K 2]
    (hσσ : ∀ c, σ (σ c) = c)
    (α β φ : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ))
    (hφ : φ * α * φ⁻¹ = β) (c : orbitField TwistTag.E6 K σ twN0)
    (hc : σ (c : K) ≠ (c : K))
    (hβ : β (xC TwistTag.E6 K σ twN0 c) =
      xC TwistTag.E6 K σ twN0 ⟨σ (c : K), mem_orbitField_twN0 σ hσσ _⟩) :
    ∃ (ψ : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ))
      (x : ↥(graphFixedRootGroup TwistTag.E6 K σ))
      (d : (orbitField TwistTag.E6 K σ twN0)ˣ),
      ψ ((α x)⁻¹ * x) = xC TwistTag.E6 K σ twN0
        (d : orbitField TwistTag.E6 K σ twN0) := by
  have hne : σ (c : K) + (c : K) ≠ 0 :=
    fun h => hc (CharTwo.add_eq_zero.1 h)
  let s : orbitField TwistTag.E6 K σ twN0 :=
    ⟨σ (c : K) + (c : K), mem_orbitField_twN0 σ hσσ _⟩
  have hs : s ≠ 0 := fun h => hne (congrArg Subtype.val h)
  let d : (orbitField TwistTag.E6 K σ twN0)ˣ := Units.mk0 s hs
  let x : ↥(graphFixedRootGroup TwistTag.E6 K σ) := φ⁻¹ (xC TwistTag.E6 K σ twN0 c)
  refine ⟨φ, x, d, ?_⟩
  have hx : φ x = xC TwistTag.E6 K σ twN0 c := by
    simp [x]
  have hαx : φ (α x) = β (xC TwistTag.E6 K σ twN0 c) := by
    have h' : φ * α = β * φ := by rw [← hφ]; group
    have h'' := congrArg
      (fun g : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ) => g x) h'
    simpa only [MulAut.mul_apply, hx] using h''
  calc φ ((α x)⁻¹ * x) = (φ (α x))⁻¹ * φ x := by rw [map_mul, map_inv]
    _ = (β (xC TwistTag.E6 K σ twN0 c))⁻¹ * xC TwistTag.E6 K σ twN0 c := by
        rw [hαx, hx]
    _ = (xC TwistTag.E6 K σ twN0 ⟨σ (c : K), mem_orbitField_twN0 σ hσσ _⟩)⁻¹ *
          xC TwistTag.E6 K σ twN0 c := by rw [hβ]
    _ = xC TwistTag.E6 K σ twN0 (d : orbitField TwistTag.E6 K σ twN0) := by
        rw [inv_mul_xC σ hσσ c]
        congr 1

end FrameData

theorem tw2e6_exists_inv_mul_eq_frame {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (α : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)) (h2 : α * α = 1)
    (hout : ∀ c, α ≠ MulAut.conj c) :
    ∃ (ψ : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ))
      (x : ↥(graphFixedRootGroup TwistTag.E6 K σ)) (d : (orbitField TwistTag.E6 K σ twN0)ˣ),
      ψ ((α x)⁻¹ * x) = xC TwistTag.E6 K σ twN0 (d : orbitField TwistTag.E6 K σ twN0) := by
  have hα2 : α ^ 2 = 1 := by
    rw [pow_two]
    exact h2
  have hαout : α ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)).range := by
    rintro ⟨c, hc⟩
    exact hout c hc.symm
  have hσσ : ∀ c, σ (σ c) = c := apply_apply_eq hK hσ
  obtain ⟨c, hc⟩ := exists_apply_ne hf hK hσ
  have hmem : ∀ x : K, x ∈ orbitField TwistTag.E6 K σ twN0 :=
    mem_orbitField_twN0 σ hσσ
  have hclass := (conj_etaAut_or_xiAut_of_outer hf hK σ hσ).1
  rcases hclass α hα2 hαout with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · exact exists_frame_of_conj σ hσσ α _ φ hφ ⟨c, hmem c⟩ hc
      (eta_xC σ hσσ ⟨c, hmem c⟩)
  · exact exists_frame_of_conj σ hσσ α _ φ hφ ⟨c, hmem c⟩ hc
      (xi_xC σ hσσ ⟨c, hmem c⟩)

end CFSG.LocalAnalysis.WeakClosure81
