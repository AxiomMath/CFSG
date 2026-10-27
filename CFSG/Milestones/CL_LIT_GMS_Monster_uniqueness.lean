module

public import CFSG.Monster.GMS.Defs
public import CFSG.Monster.Griess.AutFinite
import CFSG.Monster.GMS.MonsterUniquenessFinal
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

universe u v w

namespace CFSG.Milestones

open CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS

theorem cl_lit_gms_monster_uniqueness
    (d₀ : B) (hd₀ : orderOf d₀ = 2)
    (hrank : Matrix.rank (d₀.val.val - 1) = 1860)
    (G : Type) [Group G] [Finite G] (a z : G) (hG : GMSF1Type d₀ a z) :
    Nonempty (G ≃* CFSG.Monster.Griess.AutO) :=
  nonempty_mulEquiv_autO_of_sls
    (fun d₀ hd₀ hrank H _ _ _ d hd hc =>
      cl_lit_stroth_leon_sims_baby_monster_recognition_models d₀ hd₀ hrank H d hd hc)
    d₀ hd₀ hrank G a z hG

theorem cl_lit_gms_monster_uniqueness_of_two
    (d₀ : B) (hd₀ : orderOf d₀ = 2)
    (hrank : Matrix.rank (d₀.val.val - 1) = 1860)
    (G H : Type) [Group G] [Group H] [Finite G] [Finite H] (a z : G) (b y : H)
    (hG : GMSF1Type d₀ a z) (hH : GMSF1Type d₀ b y) :
    Nonempty (G ≃* H) := by
  obtain ⟨e₁⟩ := cl_lit_gms_monster_uniqueness d₀ hd₀ hrank G a z hG
  obtain ⟨e₂⟩ := cl_lit_gms_monster_uniqueness d₀ hd₀ hrank H b y hH
  exact ⟨e₁.trans e₂.symm⟩

end CFSG.Milestones
