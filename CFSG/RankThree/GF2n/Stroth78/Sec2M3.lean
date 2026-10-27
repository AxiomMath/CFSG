module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem commutator_centerIn_H_CQ_le (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) :
    ⁅(centerIn (QaOf a) ⊓ H z : Subgroup G),
      (Q z ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G)⁆
      ≤ Q z ⊓ centerIn (QaOf a) := by
  refine le_inf ?_ ?_
  ·
    refine Subgroup.commutator_le.mpr ?_
    intro w hw c hc
    obtain ⟨-, hwH⟩ := Subgroup.mem_inf.mp hw
    obtain ⟨hcQ, -⟩ := Subgroup.mem_inf.mp hc
    have hconjQ : w * c * w⁻¹ ∈ Q z :=
      fStar_normal (M := H z) hwH hcQ
    have hcomm : ⁅w, c⁆ = (w * c * w⁻¹) * c⁻¹ := by
      rw [commutatorElement_def]
    rw [hcomm]
    exact (Q z).mul_mem hconjQ ((Q z).inv_mem hcQ)
  ·
    refine Subgroup.commutator_le.mpr ?_
    intro w hw c hc
    obtain ⟨hwZ, -⟩ := Subgroup.mem_inf.mp hw
    obtain ⟨-, hcCa⟩ := Subgroup.mem_inf.mp hc
    have hwQa : w ∈ QaOf a := (Subgroup.mem_inf.mp hwZ).1
    have hwCent : w ∈ Subgroup.centralizer (QaOf a : Set G) := (Subgroup.mem_inf.mp hwZ).2
    have hcQa : ∀ x ∈ QaOf a, c * x * c⁻¹ ∈ QaOf a := fun x hx =>
      fStar_normal (M := Subgroup.centralizer ({a} : Set G)) hcCa hx
    have hcQa_inv : ∀ x ∈ QaOf a, c⁻¹ * x * c ∈ QaOf a := by
      intro x hx
      change x ∈ fStar (Subgroup.centralizer ({a} : Set G)) at hx
      change c⁻¹ * x * c ∈ fStar (Subgroup.centralizer ({a} : Set G))
      have h := fStar_normal (M := Subgroup.centralizer ({a} : Set G))
        ((Subgroup.centralizer ({a} : Set G)).inv_mem hcCa) hx
      simpa using h
    have hcwQa : c * w * c⁻¹ ∈ QaOf a := hcQa w hwQa
    have hcwCent : c * w * c⁻¹ ∈ Subgroup.centralizer (QaOf a : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hcyc : c⁻¹ * y * c ∈ QaOf a := hcQa_inv y hy
      have hwcomm : (c⁻¹ * y * c) * w = w * (c⁻¹ * y * c) :=
        Subgroup.mem_centralizer_iff.mp hwCent (c⁻¹ * y * c) hcyc
      calc
        y * (c * w * c⁻¹) = c * ((c⁻¹ * y * c) * w) * c⁻¹ := by group
        _ = c * (w * (c⁻¹ * y * c)) * c⁻¹ := by rw [hwcomm]
        _ = (c * w * c⁻¹) * y := by group
    have hcwZ : c * w * c⁻¹ ∈ centerIn (QaOf a) :=
      Subgroup.mem_inf.mpr ⟨hcwQa, hcwCent⟩
    have hwinvZ : c * w⁻¹ * c⁻¹ ∈ centerIn (QaOf a) := by
      have h := (centerIn (QaOf a)).inv_mem hcwZ
      have heq : (c * w * c⁻¹)⁻¹ = c * w⁻¹ * c⁻¹ := by group
      rwa [heq] at h
    have hmul : w * (c * w⁻¹ * c⁻¹) ∈ centerIn (QaOf a) :=
      (centerIn (QaOf a)).mul_mem hwZ hwinvZ
    simpa [commutatorElement_def, mul_assoc] using hmul

end CFSG.RankThree.GF2n.Stroth78
