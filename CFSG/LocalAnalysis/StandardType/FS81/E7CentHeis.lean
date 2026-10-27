module

public import CFSG.LocalAnalysis.StandardType.FS81.E7CentPieces
public import CFSG.LocalAnalysis.SeitzReduction.EPilotHeisIrr
public import CFSG.Mathlib.Decide.Bounded
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.NormalForm
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalPairing
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.SeitzReduction CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.EPilot.HeisIrr CFSG.SeitzReduction.E7Pilot
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open scoped commutatorElement

variable {K : Type} [Field K]

theorem e7Cent_deg1_iform_d6HighRoot_check :
    ∀ μ ∈ rootFinset .E7, μ 0 = 1 →
      iform μ d6HighRoot = -1 ∨ iform μ d6HighRoot = 0 ∨ iform μ d6HighRoot = 1 := by
  decide +kernel

theorem e7Cent_deg1_iform_perp_check :
    ∀ μ ∈ rootFinset .E7, ∀ β ∈ rootFinset .E7, μ 0 = 1 → β 0 = 0 →
      iform μ β = -1 ∨ iform μ β = 0 ∨ iform μ β = 1 := by
  decide +kernel

theorem e7Cent_deg1_iform_d6HighRoot {μ : Fin (Tag.rank .E7) → ℤ} (hμ : μ ∈ Deg1 .E7) :
    iform μ d6HighRoot = -1 ∨ iform μ d6HighRoot = 0 ∨ iform μ d6HighRoot = 1 :=
  e7Cent_deg1_iform_d6HighRoot_check μ (mem_rootFinset.2 hμ.1) hμ.2

theorem e7Cent_deg1_iform_perp {μ : Fin (Tag.rank .E7) → ℤ} (hμ : μ ∈ Deg1 .E7)
    {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ perpRoots .E7) :
    iform μ β = -1 ∨ iform μ β = 0 ∨ iform μ β = 1 :=
  e7Cent_deg1_iform_perp_check μ (mem_rootFinset.2 hμ.1) β (mem_rootFinset.2 hβ.1) hμ.2 hβ.2

theorem e7Cent_neg_eq_self [CharP K 2] (f : (Fin (Tag.rank .E7) → ℤ) → K) : -f = f := by
  funext ν
  exact CharTwo.neg_eq (f ν)

theorem e7Cent_conj_d6HighRoot [CharP K 2] {q : ModGL .E7 K} (hq : q ∈ Qθ .E7 K) :
    pinnedX .E7 K d6HighRoot (1 : K) * q * (pinnedX .E7 K d6HighRoot (1 : K))⁻¹ ∈ Qθ .E7 K ∧
      heisCoord .E7 K
          (pinnedX .E7 K d6HighRoot (1 : K) * q *
            (pinnedX .E7 K d6HighRoot (1 : K))⁻¹) =
        heisCoord .E7 K q + shiftRoot K d6HighRoot (heisCoord .E7 K q) := by
  have h := heisCoord_conj_pinnedX_of_deg_zero (τ := .E7) (K := K)
    (Or.inr (Or.inl rfl)) isRoot_d6HighRoot (by decide) (1 : K) hq
  refine ⟨h.1, ?_⟩
  funext ν
  rw [h.2 ν]
  simp [shiftRoot]

theorem e7Cent_conj_of_deg_zero [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ)
    (hγ0 : γ 0 = 0) {q : ModGL .E7 K} (hq : q ∈ Qθ .E7 K) :
    pinnedX .E7 K γ (1 : K) * q * (pinnedX .E7 K γ (1 : K))⁻¹ ∈ Qθ .E7 K ∧
      heisCoord .E7 K (pinnedX .E7 K γ (1 : K) * q * (pinnedX .E7 K γ (1 : K))⁻¹) =
        heisCoord .E7 K q + shiftRoot K γ (heisCoord .E7 K q) := by
  have hγ0' : γ (iθ .E7) = 0 := by
    rw [show iθ .E7 = 0 from rfl]
    exact hγ0
  have h := heisCoord_conj_pinnedX_of_deg_zero (τ := .E7) (K := K)
    (Or.inr (Or.inl rfl)) hγ hγ0' (1 : K) hq
  refine ⟨h.1, ?_⟩
  funext ν
  rw [h.2 ν]
  simp [shiftRoot]

theorem e7Cent_heisCoord_mul {q q' : ModGL .E7 K} (hq : q ∈ Qθ .E7 K) (hq' : q' ∈ Qθ .E7 K) :
    heisCoord .E7 K (q * q') = heisCoord .E7 K q + heisCoord .E7 K q' :=
  (heisCoord_spec .E7 K).mul q hq q' hq'

theorem e7Cent_heisCoord_commutator_sigma [CharP K 2] {q : ModGL .E7 K}
    (hq : q ∈ Qθ .E7 K) :
    heisCoord .E7 K ⁅q, pinnedX .E7 K d6HighRoot (1 : K)⁆ =
      shiftRoot K d6HighRoot (heisCoord .E7 K q) := by
  set x := pinnedX .E7 K d6HighRoot (1 : K) with hx
  have hx2 : x * x = 1 := by
    rw [hx, ← pinnedX_add]
    rw [show (1 : K) + 1 = 0 by exact CharTwo.add_self_eq_zero 1, pinnedX_zero]
  have hqinv : q⁻¹ ∈ Qθ .E7 K := inv_mem hq
  have hconj := e7Cent_conj_d6HighRoot (K := K) hqinv
  have hmem : x * q⁻¹ * x⁻¹ ∈ Qθ .E7 K := by simpa [hx] using hconj.1
  generalize hr : x * q⁻¹ * x⁻¹ = r at hconj hmem
  have hmul : q * r ∈ Qθ .E7 K := mul_mem hq hmem
  have h1 : heisCoord .E7 K (q * r) = heisCoord .E7 K q + heisCoord .E7 K r :=
    e7Cent_heisCoord_mul hq hmem
  have h2 : heisCoord .E7 K r =
      heisCoord .E7 K q⁻¹ + shiftRoot K d6HighRoot (heisCoord .E7 K q⁻¹) := hconj.2
  have h3 : heisCoord .E7 K q⁻¹ = -heisCoord .E7 K q := heisCoord_inv hq
  have h4 : shiftRoot K d6HighRoot (heisCoord .E7 K q⁻¹) =
      -shiftRoot K d6HighRoot (heisCoord .E7 K q) := by
    rw [h3]
    funext ν
    simp only [shiftRoot, Pi.neg_apply]
    by_cases h : ν ∈ rootFinset .E7 <;> simp [h]
  have hcomm : ⁅q, x⁆ = q * r := by
    rw [commutatorElement_def, ← hr, mul_assoc q x q⁻¹, mul_assoc q (x * q⁻¹) x⁻¹]
  rw [hcomm, h1, h2, h4, h3]
  have hneg : -shiftRoot K d6HighRoot (heisCoord .E7 K q) =
      shiftRoot K d6HighRoot (heisCoord .E7 K q) := e7Cent_neg_eq_self _
  rw [hneg, ← add_assoc, add_neg_cancel, zero_add]

theorem e7Cent_mem_Uθ_of_heisCoord_eq {q₁ q₂ : ModGL .E7 K}
    (h₁ : q₁ ∈ Qθ .E7 K) (h₂ : q₂ ∈ Qθ .E7 K) (h : heisCoord .E7 K q₁ = heisCoord .E7 K q₂) :
    q₁ * q₂⁻¹ ∈ Uθ .E7 K := by
  have hs := heisCoord_spec .E7 K
  refine (hs.eq_zero_iff _ (mul_mem h₁ (inv_mem h₂))).1 ?_
  rw [hs.mul _ h₁ _ (inv_mem h₂), heisCoord_inv h₂, h]
  exact add_neg_cancel _

theorem e7Cent_mem_rootSpan_of_coord_support {S : Set (Fin (Tag.rank .E7) → ℤ)}
    (hS : ∀ μ ∈ S, IsRoot .E7 μ) (hθ : highRoot .E7 ∈ S) {q : ModGL .E7 K}
    (hq : q ∈ Qθ .E7 K) (hs : ∀ μ, heisCoord .E7 K q μ ≠ 0 → μ ∈ S) :
    q ∈ rootSpan .E7 K S := by
  classical
  let L := ((rootFinset .E7).filter (fun μ => μ 0 = 1 ∧ μ ∈ S)).toList
  have hnd : L.Nodup := Finset.nodup_toList _
  have hD : ∀ μ ∈ L, μ ∈ Deg1 .E7 := by
    intro μ hμ
    rw [Finset.mem_toList, Finset.mem_filter] at hμ
    exact ⟨mem_rootFinset.1 hμ.1, hμ.2.1⟩
  have hsupp : ∀ ν, ν ∉ L → heisCoord .E7 K q ν = 0 := by
    intro ν hν
    by_cases hνD : ν ∈ Deg1 .E7
    · by_contra hne
      exact hν (Finset.mem_toList.2 (Finset.mem_filter.2
        ⟨mem_rootFinset.2 hνD.1, hνD.2, hs ν hne⟩))
    · exact (heisCoord_spec .E7 K).support q hq ν hνD
  obtain ⟨u, hu, hqeq⟩ := exists_prodX_of_support hnd hD hq hsupp
  rw [hqeq]
  refine mul_mem ?_ ?_
  · exact rootSubgroup_le_rootSpan_of_mem (S := S) hθ hu
  · refine CoordAux.prodX_mem_rootSpan (S := S) (fun μ hμ => ?_) _
    rw [Finset.mem_toList, Finset.mem_filter] at hμ
    exact hμ.2.2

end CFSG.StandardType.FrameRoute.FS81
