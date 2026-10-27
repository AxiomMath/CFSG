module

public import CFSG.Sporadic.Recognition.HSGraphStab
public import CFSG.Sporadic.Recognition.HSGraphGroup
public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

public section

namespace CFSG.Sporadic.Recognition.HSGraph

open CFSG.ComponentClassification.WittDesign MulAction

universe u

variable {Ω : Type u} {𝓑 : Finset (Finset Ω)}

structure MData (𝓑 : Finset (Finset Ω)) where
  carrier : Subgroup (Equiv.Perm Ω)
  le : carrier ≤ blockAut 𝓑
  card : Nat.card carrier = 443520
  simple : IsSimpleGroup carrier
  pt : ∀ a b : Ω, ∃ τ ∈ carrier, τ a = b
  blk : ∀ B ∈ 𝓑, ∀ C ∈ 𝓑, ∃ τ ∈ carrier, B.map τ.toEmbedding = C

theorem MData.exists_stab_vPt (D : MData 𝓑) (a b : Ω) :
    ∃ g : stabilizer (autGroup 𝓑) (vInf : Vert 𝓑), g • (vPt a : Vert 𝓑) = vPt b := by
  obtain ⟨τ, hτ, hab⟩ := D.pt a b
  exact ⟨extElem τ (D.le hτ), by rw [extElem_smul_vPt, hab]⟩

theorem MData.exists_stab_vBlk (D : MData 𝓑) (B C : {B // B ∈ 𝓑}) :
    ∃ g : stabilizer (autGroup 𝓑) (vInf : Vert 𝓑), g • (vBlk B : Vert 𝓑) = vBlk C := by
  obtain ⟨τ, hτ, h⟩ := D.blk B.1 B.2 C.1 C.2
  refine ⟨extElem τ (D.le hτ), ?_⟩
  rw [extElem_smul_vBlk]
  exact congrArg vBlk (Subtype.ext h)

theorem range_orbit_stabilizer [Nonempty Ω] (hne : 𝓑.Nonempty) (D : MData 𝓑) :
    Set.range (orbit (stabilizer (autGroup 𝓑) (vInf : Vert 𝓑)) : Vert 𝓑 → Set (Vert 𝓑)) =
      {{vInf}, Set.range vPt, Set.range vBlk} :=
  range_orbit_eq _ hne (fun g => g.2) (fun g u v => g.1.2 u v) D.exists_stab_vPt
    D.exists_stab_vBlk

theorem isPretransitive_autGroup (D : MData 𝓑)
    (hψ : ∃ ψ ∈ autGroup 𝓑, ∃ (a : Ω) (B : {B // B ∈ 𝓑}), ψ vInf = vPt a ∧ ψ (vPt a) = vBlk B) :
    IsPretransitive (autGroup 𝓑) (Vert 𝓑) := by
  obtain ⟨ψ, hψ, a₀, B₀, h1, h2⟩ := hψ
  have hall : ∀ u : Vert 𝓑, ∃ g : autGroup 𝓑, g • (vInf : Vert 𝓑) = u := by
    intro u
    rcases u with _ | b | C
    · exact ⟨1, one_smul _ _⟩
    · obtain ⟨s, hs⟩ := D.exists_stab_vPt a₀ b
      exact ⟨s.1 * ⟨ψ, hψ⟩, by rw [mul_smul]; exact (congrArg _ h1).trans hs⟩
    · obtain ⟨s, hs⟩ := D.exists_stab_vBlk B₀ C
      refine ⟨s.1 * (⟨ψ, hψ⟩ * ⟨ψ, hψ⟩), ?_⟩
      rw [mul_smul, mul_smul]
      exact (congrArg _ ((congrArg _ h1).trans h2)).trans hs
  refine ⟨fun x y => ?_⟩
  obtain ⟨g₁, h₁⟩ := hall x
  obtain ⟨g₂, h₂⟩ := hall y
  exact ⟨g₂ * g₁⁻¹, by rw [mul_smul, ← h₁, inv_smul_smul, h₂]⟩

variable [Fintype Ω] [DecidableEq Ω]

structure HSFacts (𝓑 : Finset (Finset Ω)) : Prop where
  card_aut : Nat.card (blockAut 𝓑) = 887040
  mdata : Nonempty (MData 𝓑)
  srg : (hsGraph 𝓑).IsSRGWith 100 22 0 6
  psi : ∃ ψ ∈ autGroup 𝓑, ∃ (a : Ω) (B : {B // B ∈ 𝓑}), ψ vInf = vPt a ∧ ψ (vPt a) = vBlk B
  odd : ∃ s ∈ autGroup 𝓑, s vInf = vInf ∧ Equiv.Perm.sign s = -1

omit [DecidableEq Ω] in
theorem natCard_vert (hΩ : Fintype.card Ω = 22) (h𝓑 : 𝓑.card = 77) :
    Nat.card (Vert 𝓑) = 100 := by
  rw [Nat.card_eq_fintype_card, card_vert, hΩ, h𝓑]

omit [DecidableEq Ω] in
theorem card_autGroup (D : MData 𝓑)
    (hψ : ∃ ψ ∈ autGroup 𝓑, ∃ (a : Ω) (B : {B // B ∈ 𝓑}), ψ vInf = vPt a ∧ ψ (vPt a) = vBlk B)
    (hΩ : Fintype.card Ω = 22) (h𝓑 : 𝓑.card = 77) :
    Nat.card (autGroup 𝓑) = 100 * Nat.card (blockAut 𝓑) := by
  have := isPretransitive_autGroup D hψ
  have h := ncard_orbit_mul_card_stabilizer (autGroup 𝓑) (vInf : Vert 𝓑)
  rw [orbit_eq_univ, Set.ncard_univ, natCard_vert hΩ h𝓑, card_stabilizer_vInf] at h
  exact h.symm

end CFSG.Sporadic.Recognition.HSGraph
