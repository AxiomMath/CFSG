module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.PCore.Defs

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.oddCore_ne_bot_of_move
    {B : Subgroup G} {X : Subgroup (MulAut ↥B)} {τX : MulAut ↥B}
    (hτXmem : τX ∈ X)
    (hZ : (⊤ : Set ↥X) =
      (oddCore ↥X : Set ↥X) * (Subgroup.centralizer
        ({⟨τX, hτXmem⟩} : Set ↥X) : Set ↥X))
    {b : G} (hbB : b ∈ B)
    (hmove : ∃ σ : MulAut ↥B, σ ∈ X ∧
      σ ⟨b, hbB⟩ ∉ Subgroup.zpowers (⟨b, hbB⟩ : ↥B))
    (hmap : ∀ σ : MulAut ↥B, σ ∈ X → σ * τX = τX * σ →
      Subgroup.map σ (Subgroup.zpowers (⟨b, hbB⟩ : ↥B)) =
        Subgroup.zpowers (⟨b, hbB⟩ : ↥B)) :
    oddCore ↥X ≠ ⊥ := by
  intro hO
  obtain ⟨σ, hσX, hσmove⟩ := hmove
  have hmem : (⟨σ, hσX⟩ : ↥X) ∈ (⊤ : Set ↥X) := Set.mem_univ _
  rw [hZ, hO, Subgroup.coe_bot, Set.singleton_mul] at hmem
  obtain ⟨c, hc, hceq⟩ := hmem
  have hc' : c = (⟨σ, hσX⟩ : ↥X) := by
    rw [← hceq]
    exact (one_mul c).symm
  have hcommX : (⟨σ, hσX⟩ : ↥X) * ⟨τX, hτXmem⟩ =
      ⟨τX, hτXmem⟩ * ⟨σ, hσX⟩ := by
    rw [← hc']
    exact Subgroup.mem_centralizer_singleton_iff.mp hc
  have hcomm : σ * τX = τX * σ := by
    have h := congrArg (fun x : ↥X => (x : MulAut ↥B)) hcommX
    simpa using h
  have hσb : σ ⟨b, hbB⟩ ∈ Subgroup.zpowers (⟨b, hbB⟩ : ↥B) := by
    rw [← hmap σ hσX hcomm]
    exact Subgroup.mem_map_of_mem (σ : ↥B →* ↥B) (Subgroup.mem_zpowers _)
  exact hσmove hσb

end CFSG.RankThree.PartTwo.Sec21.FF81
