module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G]

namespace S152Fin

theorem exists_geom_config {M H T V : Subgroup G} (hAm : AmalgamHypV (M ⊔ H) M H T V)
    (hV : V ≠ ⊥) (hodd : Odd (critDist (M ⊔ H) M H V)) (hb2 : 2 ≤ critDist (M ⊔ H) M H V) :
    ∃ g : G, V ≤ conjSub g H ∧ ¬ V ≤ conjSub g (pCoreOf 2 H) ∧
      conjSub g (conjClosure V H) ≤ H ∧ conjClosure V H ≤ conjSub g H := by
  obtain ⟨γ, hγ⟩ := exists_isCriticalVertex hAm hV
  have hvt : vtype γ = true := vtype_eq_true_of_odd hAm.gen (by rw [hγ.dist_eq]; exact hodd)
  obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hvt
  have hstab : stab γ = conjSub (g : G) H := by
    rw [hg, stab_smul, stab_γ₁ hAm.le₂]
  have hN := hAm.normalizes
  obtain ⟨⟨γ', hγ'nb, hd'⟩, ⟨γ₂, hγ₂nb, hd₂⟩⟩ :=
    exists_nbrs_of_geodesic hAm.gen hγ.geodesic hb2
  refine ⟨(g : G), ?_, ?_, ?_, ?_⟩
  · rw [← hstab]
    exact V_le_stab_of_dist_le hAm hV hγ.dist_eq.le
  · intro hle
    apply hγ.not_le
    have h1 : conjSub (g : G) (pCoreOf 2 H) = pCoreOf 2 (stab γ) := by
      rw [hstab, pCoreOf_conjSub]
    rw [h1] at hle
    exact hle.trans (pCoreOf_stab_le_ballStab_one hAm.toAmalgamHyp γ)
  · have h1 : Vv V γ = conjSub (g : G) (conjClosure V H) := by
      rw [hg, Vv_smul hN, Vv_γ₁ hAm.le₂ hN]
    have h2 := Vv_le_pCoreOf_stab_inf hAm hV hγ₂nb hd₂
    rw [h1] at h2
    refine h2.trans ((pCoreOf_le 2 _).trans ?_)
    rw [stab_γ₁ hAm.le₂]
    exact inf_le_left
  · have h1 : Vv V (γ₁ (M ⊔ H) M H) = conjClosure V H := Vv_γ₁ hAm.le₂ hN
    have h2 := Vv_γ₁_le_pCoreOf_stab_inf hAm hV hγ'nb hd'
    rw [h1] at h2
    refine h2.trans ((pCoreOf_le 2 _).trans ?_)
    rw [← hstab]
    exact inf_le_right

end S152Fin

end CFSG.Quasithin
