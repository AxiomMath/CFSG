module

public import CFSG.Timmesfeld.ARS.CaseBMinusFrame
public import CFSG.Timmesfeld.ARS.CaseBSkeleton

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType Matrix

namespace CaseB

variable {G : Type} [Group G] {R : Set (Subgroup G)}

theorem hypB_of_mem {A D : Subgroup G} (hB : HypB G R A) (hD : D ∈ R) : HypB G R D :=
  have h8 := Sec8.of_mem hB.hyp.root hB.mem hD hB.sec8
  ⟨hB.hyp, hD, h8.1, h8.2, fun hmax =>
    hB.notMax (isSigmaMaximal_centralGroup_of_mem hB.hyp.root hD hB.mem hmax)⟩

theorem exists_skel {A : Subgroup G} (hB : HypB G R A) : ∃ f : ℕ, 1 ≤ f ∧
    ∃ Ψ : SpecialLinearGroup (Fin 4) (GaloisField 2 f) →* G, Skel R Ψ ∧ HypB G R (xg Ψ 0 3) := by
  have h := hB.hyp
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have h8 := hB.sec8
  obtain ⟨Δ, hΔ, hAΔ⟩ := hB.exists_isWeakTI
  obtain ⟨A₀, hA₀R, hAA₀⟩ := hiso A hB.mem
  have hA₀ : A₀ ∈ omegaSet R A := ⟨hA₀R, hAA₀⟩
  obtain ⟨A₁, hA₁, B₁, hB₁, hop, -⟩ := exists_levi_eq_sup h hB.mem h8 hA₀ hΔ hAΔ
  obtain ⟨E, hE, C, hC, hB₁E, hA₁C, hsEC, hECA, -⟩ :=
    exists_extremal_triple h hB.mem h8 hA₀ hΔ hAΔ hA₁ hB₁ hop.1
  have hX := isConfig_chain h hB.mem h8 hA₀ hΔ hAΔ hA₁ hB₁ hop.1 hE hC hB₁E hA₁C hECA hsEC
  obtain ⟨f, hf, -, Ψ, hinj, hΨA, hΨB, -⟩ := hX.exists_injective_A3 hR hiso
  have hS : Skel R Ψ := Skel.of_isConfig hR hX hinj hΨA hΨB
  exact ⟨f, hf, Ψ, hS, hypB_of_mem hB (hS.mem 0 3 (by decide))⟩

end CaseB

theorem caseBStep : CaseBStep := by
  intro G _ R h _ A hA hcoat hne hnmax
  obtain ⟨f, hf, Ψ, hS, hB⟩ := CaseB.exists_skel (⟨h, hA, hcoat, hne, hnmax⟩ : HypB G R A)
  obtain ⟨e, ι, hι⟩ := CaseB.exists_linParamU h hS
  have he1 := hι.one_le (CaseB.hU_ne_bot h hS hB)
  have he2 := hι.le_two h hS (CaseB.ptHyp_of_hypB hB)
  obtain rfl | rfl : e = 1 ∨ e = 2 := by omega
  · obtain ⟨hN, hF⟩ := CaseB.sp6Outcome hf h hS hB hι
    exact Output.of_nonSimplyLaced hN (.inr hF)
  · obtain ⟨hN, hF⟩ := CaseB.omega8Outcome hf h hS hB hι
    exact Output.of_nonSimplyLaced hN (.inr hF)

end CFSG.Timmesfeld.ARS
