module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKStarNatMap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_natMap_ker_of_ne_bot (h : S16kBase D V₀ V L hV) (hV₀ : V₀ ≠ ⊥) :
    (s16kNatMap D V₀ V L hV).ker =
      commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) := by
  have hV₁ : v1Sub D.M V₀ V hV L = V₀ := v1Sub_of_ne_bot D.M V₀ V hV L hV₀
  have hker : (s16kNatMap D V₀ V L hV).ker = ⊥ := by
    rw [eq_bot_iff]
    rintro q hq
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV q
    rw [MonoidHom.mem_ker, s16kNatMap_mk] at hq
    have hx : x.val ∈ v1Sub D.M V₀ V hV L :=
      (mem_modNull (v1Sub D.M V₀ V hV L) V hV x).1
        ((QuotientGroup.eq_one_iff (N := modNull (v1Sub D.M V₀ V hV L) V hV) x).1 hq)
    rw [hV₁] at hx
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).2
      ((mem_modNull V₀ V hV x).2 hx)
  have hYM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV h.setting.hyp151.le
  have hYn : ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).2 h.mBar_le_normalizer
  have hfix : fixV (lBar V₀ V hV L) = ⊥ :=
    s15_Kbar_fixV_eq_bot_of_ne_bot h.setting.hyp151.hyp125 hV₀ hYM hYn h.ne
  rw [hker, hfix, inf_bot_eq]

theorem s16k_star_of_ne_bot (h : S16kBase D V₀ V L hV) (hV₀ : V₀ ≠ ⊥) :
    S16kStar D V₀ V L hV :=
  s16k_star_of_natMap h (s16k_natMap_ker_of_ne_bot h hV₀)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
