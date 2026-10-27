module

public import CFSG.LocalAnalysis.WeakClosure81.W172LiftAbs
public import CFSG.LocalAnalysis.WeakClosure81.W172LiftTransfer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup

variable {X : Type} [Group X] [Finite X]

theorem w172_lift_rank {Q : Subgroup X} [Q.Normal] (hQ : IsPGroup 2 ↥Q)
    (hsolv : Group.IsSolvable (X ⧸ Q)) (hO2 : CFSG.pCore 2 (X ⧸ Q) = ⊥)
    {S : Subgroup (X ⧸ Q)} {d₀ : X ⧸ Q} (hd₀ : d₀ * d₀ = 1) (hd₀1 : d₀ ≠ 1)
    (hcomm : ∀ s ∈ S, d₀ * (s * d₀ * s⁻¹) = (s * d₀ * s⁻¹) * d₀)
    (hno : ∀ s ∈ S, s * d₀ * s⁻¹ ≠ d₀ → ∀ u : X ⧸ Q, Odd (orderOf u) →
      d₀ * u * d₀⁻¹ = u⁻¹ → (s * d₀ * s⁻¹) * u * (s * d₀ * s⁻¹)⁻¹ = u⁻¹ → u = 1) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      (∃ B : Subgroup X, IsElemAbelian p B ∧
        Nat.card B = p ^ (Subgroup.centralizer ({d₀} : Set (X ⧸ Q))).relIndex S) ∧
      ∃ B : Subgroup X, IsElemAbelian p B ∧
        (∀ b ∈ B, (b : X ⧸ Q) ∈ Subgroup.centralizer ({d₀} : Set (X ⧸ Q))) ∧
        Nat.card B = p ^ ((Subgroup.centralizer ({d₀} : Set (X ⧸ Q))).relIndex S - 1) := by
  obtain ⟨p, hp, hp2, ⟨B₁, hB₁ea, hB₁card⟩, ⟨B₂, hB₂c, hB₂ea, hB₂card⟩⟩ :=
    w172_lift_abstract hsolv hO2 hd₀ hd₀1 hcomm hno
  obtain ⟨B₁', -, hB₁'ea, hB₁'card⟩ := w172_exists_lift_elemAbelian hQ hp hp2 hB₁ea
  obtain ⟨B₂', hB₂map, hB₂'ea, hB₂'card⟩ := w172_exists_lift_elemAbelian hQ hp hp2 hB₂ea
  refine ⟨p, hp, hp2, ⟨B₁', hB₁'ea, hB₁'card.trans hB₁card⟩, B₂', hB₂'ea, ?_,
    hB₂'card.trans hB₂card⟩
  intro b hb
  apply hB₂c
  rw [← hB₂map]
  exact Subgroup.mem_map_of_mem (QuotientGroup.mk' Q) hb

end CFSG.LocalAnalysis.WeakClosure81

end
