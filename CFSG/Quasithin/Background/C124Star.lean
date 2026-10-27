module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B2FactorizationBridge

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

@[expose] noncomputable def starHom (L : Subgroup G) (hL : L ≤ Subgroup.normalizer (V : Set G)) :
    ↥L →* ↥(autI hV L) :=
  (convHom hV L hL).codRestrict (autI hV L) fun l => by
    rw [← range_convHom hV L hL]
    exact ⟨l, rfl⟩

variable {L : Subgroup G} (hL : L ≤ Subgroup.normalizer (V : Set G))

theorem starHom_apply (l : ↥L) :
    ((starHom hV L hL l : ↥(autI hV L)) : MulAut (IntMod V hV)) = convI hV ⟨l, hL l.2⟩ := rfl

theorem starHom_surjective : Function.Surjective (starHom hV L hL) := by
  intro φ
  obtain ⟨g, hg, hgφ⟩ := (mem_autI hV).1 φ.2
  refine ⟨⟨(g : G), hg⟩, Subtype.ext ?_⟩
  rw [starHom_apply]
  exact (congrArg (convI hV) (Subtype.ext rfl)).trans hgφ

theorem ker_starHom :
    (starHom hV L hL).ker = (L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf L := by
  ext l
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨l.2, ?_⟩
    have h1 : convI hV ⟨l, hL l.2⟩ = 1 := by
      rw [← starHom_apply hV hL]
      exact congrArg Subtype.val h
    exact (convI_eq_one_iff hV _).1 h1
  · intro h
    refine Subtype.ext ?_
    rw [starHom_apply]
    exact (convI_eq_one_iff hV _).2 h.2

end CFSG.Quasithin.C124
