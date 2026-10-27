module

public import CFSG.Milestones.ASVolI.F45.Engine
public import CFSG.Milestones.ASVolI.F45.BN
public import CFSG.Milestones.ASVolI.F45.Poly
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F4Native

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

section Clauses

variable {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF45_two_trans_geods_of_facts45L {S : LieSetting.{0, 0}} (hS : S.Facts45L)
    {u v : S.ι.Γ} (huv : S.ι.graph.dist u v = S.m) :
    ∀ q₁ ∈ S.ι.geods S.m u v, ∀ q₂ ∈ S.ι.geods S.m u v, q₁ ≠ q₂ →
      ∀ r₁ ∈ S.ι.geods S.m u v, ∀ r₂ ∈ S.ι.geods S.m u v, r₁ ≠ r₂ →
        ∃ g ∈ stv S.ι u ⊓ stv S.ι v, g • q₁ = r₁ ∧ g • q₂ = r₂ := by
  have T := hS.transComp
  obtain ⟨P, hP0, hPm, hPnb⟩ := GPath.exists_geodesic' hS.poly.connected u v huv
  have hP : P ∈ GPath.nbPaths S.ι.graph u S.m := ⟨hP0, hPnb⟩
  rcases T.alt hP with ⟨⟨w, hw⟩, -⟩ | ⟨-, hII⟩
  · exact absurd (hS.poly.diam_le u w) (not_le.mpr hw)
  · rw [hPm] at hII
    intro q₁ hq₁ q₂ hq₂ hne r₁ hr₁ r₂ hr₂ hne'
    obtain ⟨g, hgu, hgv, h1, h2⟩ := hII.2.1 q₁ q₂ r₁ r₂ hq₁ hq₂ hr₁ hr₂ hne hne'
    exact ⟨g, ⟨MulAction.mem_stabilizer_iff.mpr hgu, MulAction.mem_stabilizer_iff.mpr hgv⟩,
      h1, h2⟩

theorem burnsideF45_clauses_of_facts45L (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime)
    (hm : 3 ≤ κ.m) (hS : (burnsideF45_setting hyp hp hm).Facts45L) :
    IsGenPolygon (incl M₁ M₂).graph κ.m ∧
    (∀ u v : (incl M₁ M₂).Γ, (incl M₁ M₂).graph.dist u v = κ.m →
      IsComplementIn (stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v) (Qu p Gp (incl M₁ M₂) u)
        (stv (incl M₁ M₂) u) ∧
      IsComplementIn (stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v) (Qu p Gp (incl M₁ M₂) v)
        (stv (incl M₁ M₂) v) ∧
      (∃ L₁ L₂ : Subgroup (incl M₁ M₂).G0, L₁ ≤ stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v ∧
        L₂ ≤ stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v ∧
        IsComplementIn L₁ (Qu p Gp (incl M₁ M₂) u) (GpIn Gp (incl M₁ M₂) ⊓ stv (incl M₁ M₂) u) ∧
        IsComplementIn L₂ (Qu p Gp (incl M₁ M₂) v) (GpIn Gp (incl M₁ M₂) ⊓ stv (incl M₁ M₂) v)) ∧
      ∀ q₁ ∈ (incl M₁ M₂).geods κ.m u v, ∀ q₂ ∈ (incl M₁ M₂).geods κ.m u v, q₁ ≠ q₂ →
        ∀ r₁ ∈ (incl M₁ M₂).geods κ.m u v, ∀ r₂ ∈ (incl M₁ M₂).geods κ.m u v, r₁ ≠ r₂ →
          ∃ g ∈ stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v, g • q₁ = r₁ ∧ g • q₂ = r₂) ∧
    (∀ u : (incl M₁ M₂).Γ, (incl M₁ M₂).PathTrans u (κ.m + 1)) := by
  set S := burnsideF45_setting hyp hp hm with hSdef
  have hQ : ∀ u : (incl M₁ M₂).Γ, Qu p Gp (incl M₁ M₂) u = S.Qbar u :=
    fun u => burnsideF45_Qu_eq_Qbar hyp hp hm u
  have hQle : ∀ u : (incl M₁ M₂).Γ, Qu p Gp (incl M₁ M₂) u ≤ GpIn Gp (incl M₁ M₂) ⊓ stv (incl M₁ M₂) u :=
    fun u => by rw [hQ u]; exact CFSG.LieType.BorelTits.pCoreOf_le p _
  refine ⟨hS.poly, fun u v huv => ?_, hS.trans⟩
  have hvu : (incl M₁ M₂).graph.dist v u = κ.m := by rw [SimpleGraph.dist_comm]; exact huv
  have c1 : IsComplementIn (stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v) (Qu p Gp (incl M₁ M₂) u)
      (stv (incl M₁ M₂) u) := by
    rw [hQ u]; exact hS.compl u v huv
  have c2 : IsComplementIn (stv (incl M₁ M₂) u ⊓ stv (incl M₁ M₂) v) (Qu p Gp (incl M₁ M₂) v)
      (stv (incl M₁ M₂) v) := by
    rw [hQ v, inf_comm]; exact hS.compl v u hvu
  refine ⟨c1, c2, ⟨_, _, inf_le_left, inf_le_left, c1.inf_left (hQle u) inf_le_right,
    c2.inf_left (hQle v) inf_le_right⟩, ?_⟩
  exact burnsideF45_two_trans_geods_of_facts45L hS huv

end Clauses

section Parabolics

theorem burnsideF45_parabolics
    {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4g κ p f Gp M₁ M₂) :
    IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂) := by
  obtain ⟨h1, h2, h3⟩ := hyp.chart_matches
  have hlp := (ChF.nativeChartCompatibility κ p f E Gp hyp.chart).1
  rw [← h1, ← h2, ← h3] at hlp
  exact hlp

end Parabolics

section G2

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN


theorem burnsideF45_facts45L_G2 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .G2 p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ GLKind.G2.m) :
    (burnsideF45_setting hyp hp hm).Facts45L := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, fK, finK, hcard, marking, -, -⟩ := burnsideF45_chart_G2 hyp.toHypF_4_4g
  letI := fK
  haveI := finK
  have hf : 1 ≤ f := hyp.model.2.1
  haveI : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hcard
  have hU := burnsideF4h_g2_sys_U_sylow (K := K) p
  exact burnsideF45_facts45L_of_system hyp hp hm (burnsideF45_parabolics hyp.toHypF_4_4g) marking
    (burnsideF4h_g2_sys K) rfl hU (fun i => burnsideF45_bn_modelBase (burnsideF4h_g2_sys K) hp hU i)

end G2

section F4tw

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN CFSG.ASVolI.ChF.ExceptionalRoots


theorem burnsideF45_facts45L_F4tw {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .F4tw p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ GLKind.F4tw.m) :
    (burnsideF45_setting hyp hp hm).Facts45L := by
  have hp2 : p = 2 := hyp.model.1
  subst hp2
  obtain ⟨a, K, fK, finK, charK, hscope, -, marking, -, -⟩ :=
    burnsideF4g_chart_F4tw hyp.toHypF_4_4g
  letI := fK
  haveI := finK
  haveI := charK
  haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := inferInstanceAs (CharP K 2)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := hscope
  obtain ⟨Φ, -⟩ := burnsideF4h_ree_exists_iso hK
  have hU2 := CFSG.Quasithin.H13.F431.TwoF4.isSylowTwoOf_Ug hK
  have hU : ChF.IsSylowOf 2 (burnsideF4h_ree_system hK).U ⊤ := hU2
  exact burnsideF45_facts45L_of_system hyp hp hm (burnsideF45_parabolics hyp.toHypF_4_4g)
    (Φ.trans marking) (burnsideF4h_ree_system hK) rfl hU
    (fun i => burnsideF45_bn_modelBase (burnsideF4h_ree_system hK) hp hU i)

end F4tw

end CFSG.ASVolI
