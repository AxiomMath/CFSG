module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5Base

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.B5

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem condD_of_arc (hS : Sit H M S) {β l δ δ'' : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) (hlδ : l ∈ nbrs δ) (hlδ'' : l ∈ nbrs δ'') (hδ : δ ≠ β) (hδ'' : δ'' ≠ β)
    (hne : δ'' ≠ δ) (h : Vn δ'' ≤ Vn β ⊔ Vn δ) : CondD H M := by
  intro β' l' δ' δ3 hβ' hl' hl'δ' hl'δ3 hδ' hδ3 hne3
  obtain ⟨g, rfl, rfl, rfl⟩ := arc_trans hS hβ hl hlδ hδ hβ' hl' hl'δ' hδ'
  have hl3 : vtype (g • l) = true := vtype_nbr_S5 hβ' hl'
  have hδ''g : g • δ'' ∈ nbrs (g • l) := (smul_mem_nbrs_iff' g).mpr (mem_nbrs_symm.mp hlδ'')
  have hβg : g • β ∈ nbrs (g • l) := mem_nbrs_symm.mpr hl'
  have hδg : g • δ ∈ nbrs (g • l) := mem_nbrs_symm.mp hl'δ'
  have h3g : δ3 ∈ nbrs (g • l) := mem_nbrs_symm.mp hl'δ3
  obtain ⟨δ4, -, -, -, hall⟩ := nbrs_S3_third hS hl3 hβg hδg hδ'.symm
  have e : δ3 = g • δ'' := by
    have a1 : g • δ'' ≠ g • β := fun h' => hδ'' (MulAction.injective g h')
    have a2 : g • δ'' ≠ g • δ := fun h' => hne (MulAction.injective g h')
    rcases hall _ hδ''g with h1 | h1 | h1
    · exact absurd h1 a1
    · exact absurd h1 a2
    · rcases hall _ h3g with h2 | h2 | h2
      · exact absurd h2 hδ3
      · exact absurd h2 hne3
      · rw [h2, h1]
  rw [e, Vn_smul, Vn_smul, Vn_smul, ← conjSub_sup]
  exact conjSub_mono _ h

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
