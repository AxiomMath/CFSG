module

public import CFSG.Open.FusionDefs
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open

theorem mem_normalizer_subgroupOf_iff {X : Type} [Group X] {A M : Subgroup X} (hAM : A ≤ M)
    (n : M) :
    n ∈ Subgroup.normalizer ((A.subgroupOf M : Subgroup M) : Set M) ↔
      (n : X) ∈ Subgroup.normalizer (A : Set X) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hn x
    constructor
    · intro hx
      have := (hn ⟨x, hAM hx⟩).mp (Subgroup.mem_subgroupOf.mpr hx)
      simpa [Subgroup.mem_subgroupOf] using this
    · intro hx
      have hxM : x ∈ M := by
        have h1 : (n : X)⁻¹ * ((n : X) * x * (n : X)⁻¹) * (n : X) ∈ M :=
          M.mul_mem (M.mul_mem (M.inv_mem n.2) (hAM hx)) n.2
        simpa [mul_assoc] using h1
      have := (hn ⟨x, hxM⟩).mpr (by simpa [Subgroup.mem_subgroupOf] using hx)
      simpa [Subgroup.mem_subgroupOf] using this
  · intro hn h
    simpa [Subgroup.mem_subgroupOf] using hn (h : X)

theorem le_normalizer_of_fusionStronglyClosed {X : Type} [Group X] {A P : Subgroup X}
    (hAP : A ≤ P) (hcl : fusionStronglyClosed (A : Set X) P) :
    P ≤ Subgroup.normalizer (A : Set X) := by
  intro s hs
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hmem : s * h * s⁻¹ ∈ P := P.mul_mem (P.mul_mem hs (hAP hh)) (P.inv_mem hs)
    simpa using hcl h hh s⁻¹ (by simpa using hmem)
  · intro hh
    have hmem : s⁻¹ * (s * h * s⁻¹) * s ∈ P :=
      P.mul_mem (P.mul_mem (P.inv_mem hs) (hAP hh)) hs
    have hres := hcl (s * h * s⁻¹) hh s hmem
    have heq : s⁻¹ * (s * h * s⁻¹) * s = h := by group
    rwa [heq] at hres

theorem odd_relIndex_of_sylow_subgroupOf {X : Type} [Group X] [Finite X]
    {M P R T₀ : Subgroup X} (Pm : Sylow 2 M) (hPm : (Pm : Subgroup M) = P.subgroupOf M)
    (hT : T₀ = P ⊓ M) (hTR : T₀ ≤ R) (hRM : R ≤ M) : Odd (T₀.relIndex R) := by
  subst hT
  have hnot : ¬ 2 ∣ (P ⊓ M).relIndex R := by
    intro hdvd
    have hmul := Subgroup.relIndex_mul_relIndex (P ⊓ M) R M hTR hRM
    have hdvdM : 2 ∣ (P ⊓ M).relIndex M := by
      rw [← hmul]
      exact dvd_mul_of_dvd_left hdvd _
    rw [Subgroup.inf_relIndex_right] at hdvdM
    have hnotP : ¬ 2 ∣ (Pm : Subgroup M).index := Sylow.not_dvd_index Pm
    rw [hPm] at hnotP
    exact hnotP hdvdM
  exact Nat.not_even_iff_odd.mp fun he => hnot (even_iff_two_dvd.mp he)

end CFSG.StandardType.FrameRoute.FS81

end
