module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.Baum
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Config

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T L E : Subgroup G}

theorem ConfigA.not_pCoreOf_le (hA : ConfigA G₀ G₁ G₂ T L E) :
    ¬ pCoreOf 2 G₁ ≤ pCoreOf 2 G₂ := by
  intro hle
  have hQ₁T : pCoreOf 2 G₁ ≤ T := F7.isSylowTwoOf_pCoreOf_le hA.hyp.sylow₁
  have hQ₂T : pCoreOf 2 G₂ ≤ T := F7.isSylowTwoOf_pCoreOf_le hA.hyp.sylow₂
  have hTG₁ : T ≤ G₁ := hA.hyp.sylow₁.1
  have hJQ₁ : thompsonJ T ≤ pCoreOf 2 G₁ :=
    thompsonJ_le_of_starBound hA.star hA.hypV.elemAbelian
      (CFSG.Quasithin.CosetGeom.V_le_pCoreOf hA.hypV)
      (CFSG.Quasithin.CosetGeom.pCoreOf_le_centralizer hA.hypV) hQ₁T hTG₁
  have hJQ₂ : thompsonJ T ≤ pCoreOf 2 G₂ := hJQ₁.trans hle
  have hJeq : thompsonJ T = thompsonJ (pCoreOf 2 G₂) :=
    thompsonJ_eq_of_le hJQ₂ hQ₂T
  have hG₂ : G₂ ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    have h := (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G₂).trans
      (normalizer_le_normalizer_thompsonJ (pCoreOf 2 G₂))
    rwa [← hJeq] at h
  have hG₁ : G₁ ≤ Subgroup.normalizer (thompsonJ T : Set G) :=
    le_normalizer_thompsonJ_of_starBound hA.star hA.hypV.elemAbelian
      (CFSG.Quasithin.CosetGeom.V_le_pCoreOf hA.hypV)
      (CFSG.Quasithin.CosetGeom.pCoreOf_le_centralizer hA.hypV) hQ₁T hTG₁
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G₁)
  have hG₀ : G₀ ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    rw [hA.hyp.gen]
    exact sup_le hG₁ hG₂
  have hJ₂ : IsPGroup 2 (thompsonJ T) :=
    hA.hyp.sylow₁.2.1.to_le (thompsonJ_le_self T)
  have hJle : thompsonJ T ≤ pCoreOf 2 G₀ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((thompsonJ_le_self T).trans (hTG₁.trans hA.hyp.le₁)) hG₀ hJ₂
  have hJbot : thompsonJ T = ⊥ := le_bot_iff.mp (hA.hyp.o2_trivial ▸ hJle)
  have hE : E ≤ omegaOneCenterOf (thompsonJ T) :=
    le_omegaOneCenterOf_thompsonJ_of_starBound hA.star hA.hypV.elemAbelian
      (CFSG.Quasithin.CosetGeom.V_le_pCoreOf hA.hypV)
      (CFSG.Quasithin.CosetGeom.pCoreOf_le_centralizer hA.hypV) hQ₁T hTG₁
  have hEbot : E ≤ (⊥ : Subgroup G) := by
    rw [← hJbot]
    refine hE.trans ?_
    rw [omegaOneCenterOf]
    exact (Subgroup.closure_le _).mpr fun _ hx => hx.1.1
  exact hA.ne_bot (le_bot_iff.mp hEbot)

theorem relIndex_pCoreOf_inf_eq_two (hQ₁T : pCoreOf 2 G₁ ≤ T)
    (hT : (pCoreOf 2 G₂).relIndex T ≤ 2) (hQ : ¬ pCoreOf 2 G₁ ≤ pCoreOf 2 G₂) :
    (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) = 2 := by
  have hrelTotal : (pCoreOf 2 G₂).relIndex T ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Nat.card_pos.ne'
  have hle : (pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right hQ₁T hrelTotal).trans hT
  have hne : (pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Nat.card_pos.ne'
  have hne₁ : (pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) ≠ 1 := fun h =>
    hQ (Subgroup.relIndex_eq_one.mp h)
  have htwo : (pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) = 2 := by
    omega
  rw [Subgroup.inf_relIndex_left]
  exact htwo

theorem ConfigA.relIndex_pCoreOf_inf (hA : ConfigA G₀ G₁ G₂ T L E)
    (hT : (pCoreOf 2 G₂).relIndex T ≤ 2) :
    (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).relIndex (pCoreOf 2 G₁) = 2 :=
  relIndex_pCoreOf_inf_eq_two (F7.isSylowTwoOf_pCoreOf_le hA.hyp.sylow₁) hT hA.not_pCoreOf_le

end CFSG.Quasithin.F112Crit.APrime

end
