module

public import CFSG.Quasithin.Background.C116Two.OrbitCtx
public import CFSG.Quasithin.Background.C1PackC19

public section

namespace CFSG.Quasithin.C116Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem orbitBlocks_ctx {H T V L A : Subgroup G} (h : Ctx H T V L) (hAT : A ≤ T)
    {L' : Subgroup G} (hL' : L' ∈ orbitBlocks A L) : Ctx H T V L' := by
  obtain ⟨a, ha, rfl⟩ := hL'
  exact h.conj (hAT ha)

theorem orbit_family_hyps {H T V L A : Subgroup G} (h : Ctx H T V L) (hAT : A ≤ T) :
    (∀ i j : ↥(orbitBlocks A L), ∀ x ∈ blockU (i : Subgroup G), ∀ y ∈ blockU (j : Subgroup G),
        x * y = y * x) ∧
    (∀ i j : ↥(orbitBlocks A L), i ≠ j → ∀ l ∈ (i : Subgroup G), ∀ u ∈ blockU (j : Subgroup G),
        l * u = u * l) := by
  refine ⟨fun i j x hx y hy => ?_, fun i j hij l hl u hu => ?_⟩
  ·
    have hxV : x ∈ V := (orbitBlocks_ctx h hAT i.2).blockU_le_V hx
    have hyV : y ∈ V := (orbitBlocks_ctx h hAT j.2).blockU_le_V hy
    exact congrArg Subtype.val (h.red.2.2.1.1.is_comm.comm ⟨x, hxV⟩ ⟨y, hyV⟩)
  ·
    have hne : (i : Subgroup G) ≠ (j : Subgroup G) := fun heq => hij (Subtype.ext heq)
    have hcomm : ⁅(i : Subgroup G), (j : Subgroup G)⁆ = ⊥ :=
      distinctBlocksCommuteStatement H (i : Subgroup G) (j : Subgroup G)
        (orbitBlocks_ctx h hAT i.2).charTwo (orbitBlocks_ctx h hAT i.2).chi.1
        (orbitBlocks_ctx h hAT j.2).chi.1 hne
    have hc : (i : Subgroup G) ≤ Subgroup.centralizer (j : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact ((Subgroup.mem_centralizer_iff.mp (hc hl)) u (blockU_le_left (j : Subgroup G) hu)).symm

end CFSG.Quasithin.C116Two
