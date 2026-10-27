module

public import CFSG.Quasithin.EmptyFaithful.S153NMl2Frat
import CFSG.Quasithin.EmptyFaithful.S153NMs3Orb
import CFSG.Quasithin.EmptyFaithful.S153NMs3Two

public section

namespace CFSG.Quasithin.S153N

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {W : Type} [CommGroup W] [Finite W]

theorem relIndex_eq_three_of_case2 (hW : ∀ v : W, v ^ 2 = 1) {Γ J : Subgroup (MulAut W)} {w : W}
    {𝒪 : Set (Subgroup (MulAut W))} (hD : Insp67Data Γ w 𝒪) (hJ : J = ffJ Γ) (hc2 : B56Case2 J) :
    (stabAt Γ w).relIndex Γ = 3 := by
  subst hJ
  obtain ⟨hsup, -⟩ := frattini_ffJ_of_not_strong hW hD (not_isStrongFFModule_of_case2 hc2)
  have hw : w ∉ fixV (ffJ Γ) :=
    not_mem_fixV_of_gen hD.gen (B6.ffJ_le Γ) (ffJ_subgroupOf_normal Γ) (ne_bot_of_case2 hc2)
  rw [relIndex_stabAt_eq_ncard, image_eq_of_stabAt_sup (B6.ffJ_le Γ) (ffJ_subgroupOf_normal Γ) hsup]
  exact ncard_image_of_case2 hc2 hw

end CFSG.Quasithin.S153N
