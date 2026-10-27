module

public import CFSG.Quasithin.EmptyFaithful.S151XF

public section

namespace CFSG.Quasithin.S151TB

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}

theorem omegaOneCenter_le (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) :
    quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter (s1516 T Z₁) := by
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1]
    exact Subgroup.one_mem _
  · exact (hc.h18.six z hz hz1).mem_omegaOneCenter

theorem centralizer_le_mZ (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) {z x : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) (hx : x ∈ g1_1516 Z₁)
    (hxz : x * z = z * x) : x ∈ mZ1516 Mc Z₁ := by
  refine ⟨hx, (hc.h18.six z hz hz1).centralizer_z_le ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hxz

theorem centralizerZ_le_mZ (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) {x : G}
    (hx : x ∈ g1_1516 Z₁) (hxZ : x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    x ∈ mZ1516 Mc Z₁ := by
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc.ctx.qtfe.omegaOneCenter_ne_bot
  have hzmem : (z : G) ∈ quasithinOmegaOneCenter T := z.2
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  exact centralizer_le_mZ hc hzmem hz1' hx (Subgroup.mem_centralizer_iff.1 hxZ (z : G) hzmem).symm

theorem s_le_mZ (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) : s1516 T Z₁ ≤ mZ1516 Mc Z₁ := fun _ hx =>
  ⟨s1516_le_g1 T Z₁ hx, hc.ctx.qtfe.t_le_mc (s1516_le T Z₁ hx)⟩

theorem sylow_inf (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) :
    IsSylowTwoOf (s1516 T Z₁ ⊓ L) L :=
  lemma_15_1_20_sylow hc.h18.four hc.hL

theorem not_le_centralizer (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hLG : L ≤ g1_1516 Z₁) :
    ¬ L ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := fun h =>
  hc.hL.not_le fun _ hx => centralizerZ_le_mZ hc (hLG hx) (h hx)

end CFSG.Quasithin.S151TB
