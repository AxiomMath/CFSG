module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Recognition.SzVBEvenGeo1
public import CFSG.Quasithin.Recognition.SzVBEvenGeo2

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

structure CritFacts (G₀ G₁ G₂ T V : Subgroup G) (z : G) (u δ x ω p2 : CosetGeom G₀ G₁ G₂) :
    Prop where
  hC : GeoCtx G₀ G₁ G₂ T V z
  t_u : vtype u = true
  t_δ : vtype δ = false
  t_x : vtype x = true
  t_ω : vtype ω = false
  t_p2 : vtype p2 = false
  adj_δu : (graph G₀ G₁ G₂).Adj δ u
  adj_δx : (graph G₀ G₁ G₂).Adj δ x
  adj_uω : (graph G₀ G₁ G₂).Adj u ω
  adj_p2 : (graph G₀ G₁ G₂).Adj (γ₁ G₀ G₁ G₂) p2
  x_ne_u : x ≠ u
  Zu : Zv z u = Subgroup.zpowers z
  comm_ne : ⁅V, Vv V ω⁆ ≠ ⊥
  comm_le : ⁅V, Vv V ω⁆ ≤ Subgroup.zpowers z
  hcrit : ¬ V ≤ pCoreOf 2 (stab ω)
  V_le_stab_ω : V ≤ stab ω
  A_abel : IsElemAbelian 2 (Vv V u)
  A_rel : (pCoreOf 2 G₁).relIndex (Vv V u) ≤ 2
  A_inf : V ⊓ Vv V u = Subgroup.zpowers z
  Vω_le_A : Vv V ω ≤ Vv V u
  Vω_le_T : Vv V ω ≤ T
  Vω_le_Q1 : Vv V ω ≤ pCoreOf 2 G₂
  Vω_le_Qp2 : Vv V ω ≤ pCoreOf 2 (stab p2)
  Wβ_abel : ∀ β, (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β → IsElemAbelian 2 (Vv V β)
  Wβ_le_Qδ : ∀ β, (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β → Vv V β ≤ pCoreOf 2 (stab δ)
  Wx_le_Qβ : ∀ β, (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β → Vv V x ≤ pCoreOf 2 (stab β)
  EV3 : ∃ β, (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β ∧ β ≠ γ₁ G₀ G₁ G₂ ∧
    ¬ Vv V β ≤ pCoreOf 2 (stab u)

theorem exists_critFacts (hC : GeoCtx G₀ G₁ G₂ T V z) (hev : Even (critDist G₀ G₁ G₂ V))
    (hb : 3 ≤ critDist G₀ G₁ G₂ V) :
    ∃ u δ x ω p2 : CosetGeom G₀ G₁ G₂, CritFacts G₀ G₁ G₂ T V z u δ x ω p2 := by
  obtain ⟨p, hp, hp0, hp1, hcrit⟩ := exists_crit_geodesic hC
  have hN := hC.hyp.normalizes
  have hG := hC.hyp.gen
  have h₁ : G₁ ≤ G₀ := hC.hyp.le₁
  have h₂ : G₂ ≤ G₀ := hC.hyp.le₂
  set b := critDist G₀ G₁ G₂ V with hbdef
  have hbmod : b % 2 = 0 := Nat.even_iff.mp hev
  have hb4 : 4 ≤ b := by omega
  have h0 : vtype (p 0) = false := by rw [hp0]; exact vtype_γ₀
  have hVeven : ∀ i, i ≤ b → Even i → vtype (p i) = false := fun i hi he =>
    (vtype_geo_false_iff hC hp h0 hi).mpr he
  have hVodd : ∀ i, i ≤ b → ¬ Even i → vtype (p i) = true := by
    intro i hi hne
    cases hv : vtype (p i)
    · exact absurd ((vtype_geo_false_iff hC hp h0 hi).mp hv) hne
    · rfl
  have hev2 : Even (b - 2) := by rw [Nat.even_iff]; omega
  have hodd1 : ¬ Even (b - 1) := by rw [Nat.even_iff]; omega
  have hodd3 : ¬ Even (b - 3) := by rw [Nat.even_iff]; omega
  have hev2' : Even 2 := ⟨1, rfl⟩
  have hvu : vtype (p (b - 1)) = true := hVodd _ (by omega) hodd1
  have hvδ : vtype (p (b - 2)) = false := hVeven _ (by omega) hev2
  have hvx : vtype (p (b - 3)) = true := hVodd _ (by omega) hodd3
  have hvω : vtype (p b) = false := hVeven _ le_rfl hev
  have hvp2 : vtype (p 2) = false := hVeven _ (by omega) hev2'
  have hdist : ∀ i j, i ≤ j → j ≤ b → CosetGeom.dist (p i) (p j) = j - i := hp
  have hcrit' : ¬ Vv V (p 0) ≤ ballStab 1 (p b) := by
    rw [hp0, Vv_γ₀ hN]
    exact hcrit
  have hZγ₁ : Zv z (γ₁ G₀ G₁ G₂) = Subgroup.zpowers z :=
    Zv_γ₁ (G₂_le_normalizer_zpowers hC)
  obtain ⟨hcne, -, hcZ1, hcZ2⟩ := commutator_eq_Zv_of_geo hC hev hb hp h0 hcrit'
  rw [hp0, Vv_γ₀ hN] at hcne hcZ1 hcZ2
  rw [hp1, hZγ₁] at hcZ1
  have hZu : Zv z (p (b - 1)) = Subgroup.zpowers z := hcZ2.symm.trans hcZ1
  have hAinf : V ⊓ Vv V (p (b - 1)) = Subgroup.zpowers z := by
    have := inf_Vv_u_eq_Zv hC hev hb hp hp0 hp1 hcrit
    rwa [hZγ₁] at this
  have hωu : (graph G₀ G₁ G₂).Adj (p b) (p (b - 1)) := by
    have h := hp.adj (i := b - 1) (by omega)
    rw [show b - 1 + 1 = b by omega] at h
    exact h.symm
  have hdω0 : CosetGeom.dist (p b) (γ₀ G₀ G₁ G₂) = b := by
    have := hdist 0 b (Nat.zero_le _) le_rfl
    rw [hp0] at this
    rw [CosetGeom.dist_comm]
    omega
  have hdω1 : CosetGeom.dist (p b) (γ₁ G₀ G₁ G₂) = b - 1 := by
    have := hdist 1 b (by omega) le_rfl
    rw [hp1] at this
    rw [CosetGeom.dist_comm]
    exact this
  have hdωp2 : CosetGeom.dist (p b) (p 2) = b - 2 := by
    have := hdist 2 b (by omega) le_rfl
    rw [CosetGeom.dist_comm]
    exact this
  refine ⟨p (b - 1), p (b - 2), p (b - 3), p b, p 2, hC, hvu, hvδ, hvx, hvω, hvp2, ?_, ?_, ?_, ?_,
    ?_, hZu, hcne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hp.adj (i := b - 2) (by omega)
    rwa [show b - 2 + 1 = b - 1 by omega] at h
  · have h := hp.adj (i := b - 3) (by omega)
    rw [show b - 3 + 1 = b - 2 by omega] at h
    exact h.symm
  · have h := hp.adj (i := b - 1) (by omega)
    rwa [show b - 1 + 1 = b by omega] at h
  · have h := hp.adj (i := 1) (by omega)
    rwa [hp1] at h
  · exact hp.ne (by omega) (by omega)
  · exact hcZ1.le
  · rw [← ballStab_one_eq_pCoreOf hC]
    exact hcrit
  · have := Vv_le_stab_of_dist_le hC (x := γ₀ G₀ G₁ G₂) (y := p b) vtype_γ₀
      (by rw [CosetGeom.dist_comm, hdω0])
    rwa [Vv_γ₀ hN] at this
  · exact isElemAbelian_Vv_of_vtype hC hvu hb
  · have h := (relIndex_Vv_u hC hev hb hp hp0).2
    rwa [stab_γ₀ h₁] at h
  · exact hAinf
  · exact Vv_le_Vv_of_adj hωu hvω
  · have h1 : Vv V (p b) ≤ stab (γ₀ G₀ G₁ G₂) :=
      Vv_le_stab_of_dist_le hC hvω (by omega)
    have h2 : Vv V (p b) ≤ stab (γ₁ G₀ G₁ G₂) :=
      Vv_le_stab_of_dist_le hC hvω (by omega)
    rw [stab_γ₀ h₁] at h1
    rw [stab_γ₁ h₂] at h2
    rw [← hC.inf_eq]
    exact le_inf h1 h2
  · have := Vv_le_pCoreOf_of_dist_lt hC hvω (y := γ₁ G₀ G₁ G₂) (by omega)
    rwa [stab_γ₁ h₂] at this
  · exact Vv_le_pCoreOf_of_dist_lt hC hvω (y := p 2) (by omega)
  · intro β hβ
    exact isElemAbelian_Vv_of_vtype hC (vtype_eq_true_of_adj hβ vtype_γ₀) hb
  · intro β hβ
    have hvβ : vtype β = true := vtype_eq_true_of_adj hβ vtype_γ₀
    refine (Vv_B_le_iff hvβ).mpr fun x' hx' => ?_
    have hvx' : vtype x' = false := vtype_eq_false_of_adj hx' hvβ
    have hxd : dist x' (γ₀ G₀ G₁ G₂) ≤ 2 := by
      have h1 := dist_triangle hG x' β (γ₀ G₀ G₁ G₂)
      have h2 : dist x' β = 1 := dist_eq_one_iff_adj.mpr hx'.symm
      have h3 : dist β (γ₀ G₀ G₁ G₂) = 1 := dist_eq_one_iff_adj.mpr hβ.symm
      omega
    exact Vv_le_pCoreOf_delta hC hev hb hp hp0 hp1 hcrit hvx' hxd
  · intro β hβ
    have hd1 : dist (γ₀ G₀ G₁ G₂) β = 1 := dist_eq_one_iff_adj.mpr hβ
    have hdx : dist (p (b - 3)) (γ₀ G₀ G₁ G₂) = b - 3 := by
      have := hdist 0 (b - 3) (Nat.zero_le _) (by omega)
      rw [hp0] at this
      rw [CosetGeom.dist_comm]
      omega
    have h1 := dist_triangle hG (p (b - 3)) (γ₀ G₀ G₁ G₂) β
    exact Vv_le_pCoreOf_of_dist_lt_B hC hvx (by omega)
  · exact exists_nbr_not_le_pCoreOf_u hC hev hb hp hp0 hp1 hcrit

end CFSG.Quasithin.SzVB
