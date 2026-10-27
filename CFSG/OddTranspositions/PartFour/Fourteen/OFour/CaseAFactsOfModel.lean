module

public import CFSG.OddTranspositions.PartFour.Fourteen.OFour.Statements
import CFSG.GroupTheory.ConjClassGeneration
import CFSG.GroupTheory.PerfectCentralProd

public section

namespace CFSG.OddTranspositions.PartFour

theorem exists_triple_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {s : X}
    {t₀ : Y} (hconj : IsConj t₀ (e s))
    (htriple : ∃ Λ : Set Y, Λ ⊆ {y | IsConj t₀ y} ∧
      (∀ a ∈ Λ, ∀ b ∈ Λ, Commute a b) ∧
        ∃ v ∈ Λ, v ∈ Subgroup.closure (Λ \ {v})) :
    ∃ Λ : Set X, Λ ⊆ {x | IsConj s x} ∧
      (∀ a ∈ Λ, ∀ b ∈ Λ, Commute a b) ∧
        ∃ v ∈ Λ, v ∈ Subgroup.closure (Λ \ {v}) := by
  obtain ⟨Λ, hΛsub, hΛcomm, v, hvΛ, hvclos⟩ := htriple
  refine ⟨e ⁻¹' Λ, ?_, ?_, e.symm v, ?_, ?_⟩
  · intro x hx
    have h1 : IsConj t₀ (e x) := hΛsub hx
    have h2 : IsConj (e s) (e x) := hconj.symm.trans h1
    have h3 := MonoidHom.map_isConj (e.symm : Y →* X) h2
    simpa using h3
  · intro a ha b hb
    have hab : Commute (e a) (e b) := hΛcomm (e a) ha (e b) hb
    show a * b = b * a
    apply e.injective
    rw [map_mul, map_mul]
    exact hab.eq
  · simpa using hvΛ
  · have hmem : (e.symm : Y →* X) v ∈
        Subgroup.closure ((e.symm : Y →* X) '' (Λ \ {v})) := by
      rw [← MonoidHom.map_closure]
      exact ⟨v, hvclos, rfl⟩
    refine Subgroup.closure_mono ?_ hmem
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨?_, fun h => hy.2 (e.symm.injective h)⟩
    simpa using hy.1

theorem o4CaseAFacts_of_mulEquiv {X Y S : Type} [Group X] [Group Y] [Group S] (e : X ≃* Y)
    {N : Subgroup Y} (hN2 : N.index = 2) (hYN : commutator Y = N) (hNperf : commutator ↥N = ⊤)
    (φ : S ≃* ↥N)
    (hcover : ∀ (E : Type) [Group E] [Finite E] (p : E →* S),
      Function.Surjective p → p.ker ≤ Subgroup.center E → commutator E = ⊤ → p.ker = ⊥)
    {t₀ : Y} (ht₀ : ∀ t : Y, t * t = 1 → t ∉ N → IsConj t₀ t)
    (htriple : ∃ Λ : Set Y, Λ ⊆ {y | IsConj t₀ y} ∧ (∀ a ∈ Λ, ∀ b ∈ Λ, Commute a b) ∧
      ∃ v ∈ Λ, v ∈ Subgroup.closure (Λ \ {v}))
    {s : X} (hs : s * s = 1) (hgen : Subgroup.closure {x | IsConj s x} = ⊤)
    (hprim : ∀ B : Set X, B ⊆ {x | IsConj s x} → B.Nonempty →
      (∀ g : X, (fun y => g * y * g⁻¹) '' B = B ∨
        Disjoint ((fun y => g * y * g⁻¹) '' B) B) →
      B.Subsingleton ∨ B = {x | IsConj s x}) :
    O4CaseAFacts X {x | IsConj s x} := by
  have hes : e s * e s = 1 := by rw [← map_mul, hs, map_one]
  have hesN : e s ∉ N := by
    intro hmem
    have htop : Subgroup.closure {y : Y | IsConj (e s) y} = ⊤ :=
      CFSG.GroupTheory.closure_isConj_mulEquiv_eq_top e hgen
    have hNtop : N = ⊤ :=
      CFSG.GroupTheory.eq_top_of_mem_of_closure_isConj_eq_top
        (Subgroup.normal_of_index_eq_two hN2) hmem htop
    have hidx := hN2
    rw [hNtop, Subgroup.index_top] at hidx
    omega
  have hconj : IsConj t₀ (e s) := ht₀ (e s) hes hesN
  have hcmap : Subgroup.map (e : X →* Y) (commutator X) = commutator Y := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_equiv_top]
    rfl
  have hcmapN : Subgroup.map (e : X →* Y) (commutator X) = N := by
    rw [hcmap, hYN]
  have hNperf' : ⁅N, N⁆ = N := by
    rw [← Subgroup.map_subtype_commutator N, hNperf, Subgroup.map_top,
      Subgroup.range_subtype]
  let cX : ↥(commutator X) ≃* S :=
    (MulEquiv.commutatorCongr e).trans
      ((MulEquiv.subgroupCongr hcmap.symm).trans
        ((MulEquiv.subgroupCongr hcmapN).trans φ.symm))
  refine ⟨?_, ?_, CFSG.GroupTheory.ker_eq_bot_of_perfect_central_of_mulEquiv cX hcover, hprim, ?_⟩
  · have hidx := Subgroup.index_map_equiv (commutator X) e
    rw [hcmapN, hN2] at hidx
    exact hidx.symm
  · refine Subgroup.map_injective (f := (e : X →* Y)) e.injective ?_
    rw [Subgroup.map_commutator, hcmapN, hNperf']
  · exact exists_triple_of_mulEquiv e hconj htriple

end CFSG.OddTranspositions.PartFour
