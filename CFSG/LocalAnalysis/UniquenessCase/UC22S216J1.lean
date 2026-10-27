module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.GH74.Generic.S45.LLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s216_isJ1_bar2_of_isJ1_barInf {M L : Subgroup G} (hL : L ∈ calC M)
    (h : IsJ1 (BarInf L)) : IsJ1 (Bar2 L) := by
  obtain ⟨e⟩ := h
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  obtain ⟨e'⟩ := uc22p21k_barInf_equiv hq
  haveI : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr hq.1
  have hNC : CFSG.GH74.Generic.S45.NoCentralCover (CFSG.Blueprint.NativeSporadic.Carrier .J1) :=
    CFSG.GH74.Generic.S45.NoCentralCover.of_mulEquiv CFSG.Walter.walterJ1EquivNative
      CFSG.GH74.Generic.S45.noCentralCover_walterJ1
  let q : Bar2 L →* CFSG.Blueprint.NativeSporadic.Carrier .J1 :=
    (e.toMonoidHom.comp e'.symm.toMonoidHom).comp (QuotientGroup.mk' (center (Bar2 L)))
  have hqs : Function.Surjective q :=
    (e.surjective.comp e'.symm.surjective).comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center (Bar2 L) := by
    ext x
    simp only [q, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ e.injective, map_eq_one_iff _ e'.symm.injective,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hc : center (Bar2 L) = ⊥ := by
    rw [← hker]
    exact hNC (Bar2 L) inferInstance q hqs hker.le
  obtain ⟨e''⟩ := uc22p21k_barInf_equiv_of_center_bot hq hc
  exact ⟨e''.symm.trans e⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
