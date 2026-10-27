module

public import CFSG.Quasithin.MS93.S4LCoreD
public import CFSG.Quasithin.MS93.S4L42B
public import CFSG.Quasithin.MS93.S4L461D

public section

namespace CFSG.Quasithin.MS93.S4L.Core

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

section Def

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] noncomputable def wCore (β : Vtx X) : Subgroup X.Universal :=
  ⨅ δ ∈ X.treeGraph.neighborSet β, centerOf (Vv X δ)

@[expose] noncomputable def eCore (β : Vtx X) : Subgroup X.Universal :=
  ⨆ δ ∈ X.treeGraph.neighborSet β, Vv X δ

variable {X}

theorem wCore_le_centerOf {β δ : Vtx X} (hβδ : X.treeGraph.Adj β δ) :
    wCore X β ≤ centerOf (Vv X δ) :=
  iInf₂_le (f := fun δ (_ : δ ∈ X.treeGraph.neighborSet β) => centerOf (Vv X δ)) δ hβδ

theorem vv_le_eCore {β δ : Vtx X} (hβδ : X.treeGraph.Adj β δ) : Vv X δ ≤ eCore X β :=
  le_iSup₂_of_le (f := fun δ (_ : δ ∈ X.treeGraph.neighborSet β) => Vv X δ) δ hβδ le_rfl

theorem stab_le_normalizer_wCore (β : Vtx X) :
    stab X β ≤ Subgroup.normalizer (wCore X β : Set X.Universal) := by
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  rintro _ ⟨y, hy, rfl⟩
  refine Subgroup.mem_iInf.mpr fun δ => Subgroup.mem_iInf.mpr fun hδ => ?_
  have hgβ : g • β = β := (mem_stab X).mp hg
  have hδ₀ : X.treeGraph.Adj β (g⁻¹ • δ) := by
    have := (adj_smul X g⁻¹ β δ).mpr hδ
    rwa [inv_smul_eq_iff.mpr hgβ.symm] at this
  have hy₀ : y ∈ centerOf (Vv X (g⁻¹ • δ)) := wCore_le_centerOf hδ₀ hy
  have hmap : (centerOf (Vv X (g⁻¹ • δ))).map (MulAut.conj g).toMonoidHom =
      centerOf (Vv X δ) := by
    have hv : Vv X δ = (Vv X (g⁻¹ • δ)).map (MulAut.conj g).toMonoidHom := by
      have := vi_smul X g (g⁻¹ • δ) 2
      rwa [smul_inv_smul] at this
    rw [hv, PU.centerOf_map (MulAut.conj g).injective]
  rw [← hmap]
  exact Subgroup.mem_map_of_mem _ hy₀

end Def

section Main

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem wCore_le_uloc_sup_dloc (h14 : MS14AS) (hSQ : SQTKQuot) (h : PUHyp M T L)
    (hU : IsSL3U M T L) (hC : CentHyp (puAmalgam h.le)) (hb4 : critDist (puAmalgam h.le) = 4)
    {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    wCore (puAmalgam h.le) β ≤ Uloc h.le L α ⊔ Dloc h.le L α := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  obtain ⟨α₁, hc₁⟩ := exists_isCritical_of_isMVtx _ h20 hα
  obtain ⟨g, hg, hgβ⟩ := exists_mem_stab_smul _ (adj_geo_one_of_isCritical _ hb0 hc₁) hαβ
  have hgα : g • α = α := (mem_stab _).mp hg
  set α' := g • α₁ with hα'def
  have hc : IsCritical (puAmalgam h.le) α α' := by
    have := (isCritical_smul _ g α α₁).mpr hc₁
    rwa [hgα] at this
  have hgeo : geo (puAmalgam h.le) α α' 1 = β := by
    rw [← hgα, hα'def, geo_smul]
    exact hgβ
  set δ := geo (puAmalgam h.le) α α' 2 with hδdef
  have hδ : IsMVtx _ δ := isMVtx_geo_two' hb4 hc
  have hβδ : (puAmalgam h.le).treeGraph.Adj β δ := by
    rw [← hgeo]
    exact adj_geo_crit hb4 hc (i := 1) (by omega)
  have hdδα : (puAmalgam h.le).treeGraph.dist δ α = 2 := by
    rw [tdist_comm]
    exact dist_geo_crit hb4 hc (by omega)
  obtain ⟨n, F, _, _, φ, hcard, hφs, hφ⟩ := S34F.exists_natural_flat h hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard
  obtain ⟨ψ, hψs, hψ⟩ := S34F.exists_natural_flat_at h hφs hφ hα
  have hYf : Vv (puAmalgam h.le) δ ≤ S34F.flat h α := vv_le_flat_of_dist_two h hU hb4 hδ hdδα
  have hβδs : Qv (puAmalgam h.le) β ≤ stab _ δ := qv_le_stab_of_adj _ hβδ
  have hQαβ : Qv (puAmalgam h.le) α ≤ Qv _ β := qv_le_qv _ h20 hα hαβ
  have hQY : Qv (puAmalgam h.le) α ≤
      Subgroup.normalizer (Vv (puAmalgam h.le) δ : Set (puAmalgam h.le).Universal) :=
    (hQαβ.trans hβδs).trans (stab_le_normalizer_vv h δ)
  have hY2 : IsPGroup 2 ↥(Vv (puAmalgam h.le) δ) :=
    (isPGroup_qv_of_isMVtx h hδ).to_le (vv_le_qv h hb hδ)
  have hα'M : IsMVtx _ α' := hc.isMVtx_right _ h20
  have hZα'δ : ZM (puAmalgam h.le) α' ≤ Vv _ δ := by
    have hd : (puAmalgam h.le).treeGraph.dist δ α' ≤ 2 := by
      rw [hδdef, dist_geo_crit_right hb4 hc (by omega)]
    have : Zv (puAmalgam h.le) α' ≤ Vv _ δ := le_iSup₂_of_le (f := fun x (_ : x ∈
      {x : Vtx (puAmalgam h.le) | (puAmalgam h.le).treeGraph.dist δ x ≤ 2}) =>
        Zv (puAmalgam h.le) x) α' hd le_rfl
    rwa [zv_of_isMVtx _ hα'M] at this
  have hYQ : ¬ Vv (puAmalgam h.le) δ ≤ Qv _ α := fun hle =>
    (ms22_iii _ h20 hb0 hC hc).2.2 (hZα'δ.trans hle)
  intro w hw
  have hwN : w ∈ centerOf (Vv (puAmalgam h.le) α) := wCore_le_centerOf hαβ.symm hw
  have hwB : w ∈ Bloc h.le L α := centerOf_vv_le_bloc_of_isSL3U h hU hC h14 hSQ hb4 hα hwN
  have hwQ : w ∈ Qv (puAmalgam h.le) α := vv_le_qv h hb hα hwN.1
  have hwL : ∀ l ∈ Ltil h.le L α, ⁅l, w⁆ ∈ ZM (puAmalgam h.le) α := by
    intro l hl
    have := ((mem_bloc_iff h hb hα).mp hwB).2 l hl
    rw [← commutatorElement_inv]
    exact inv_mem this
  have hwδ : w ∈ centerOf (Vv (puAmalgam h.le) δ) := wCore_le_centerOf hβδ hw
  have hYw : ∀ y ∈ Vv (puAmalgam h.le) δ, y * w = w * y := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp hwδ.2 y hy)
  exact S4L.mem_uloc_sup_dloc_flat h hU hα hψs hψ hwQ hwL hYf hYw hQY hY2 hYQ

theorem uloc_inf_centralizer_le_wCore (h : PUHyp M T L) {α β : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    Uloc h.le L α ⊓ Subgroup.centralizer (eCore (puAmalgam h.le) β : Set _) ≤
      wCore (puAmalgam h.le) β := by
  intro u hu
  refine Subgroup.mem_iInf.mpr fun δ => Subgroup.mem_iInf.mpr fun hδ => ?_
  have hβδ : (puAmalgam h.le).treeGraph.Adj β δ := hδ
  have hZV : ZM (puAmalgam h.le) α ≤ Vv _ δ := by
    have hd : (puAmalgam h.le).treeGraph.dist δ α ≤ 2 := by
      have htri := dist_triangle (puAmalgam h.le) δ β α
      rw [tdist_comm _ δ β, dist_eq_one_of_adj _ hβδ, dist_eq_one_of_adj _ hαβ.symm] at htri
      exact htri
    have : Zv (puAmalgam h.le) α ≤ Vv _ δ := le_iSup₂_of_le (f := fun x (_ : x ∈
      {x : Vtx (puAmalgam h.le) | (puAmalgam h.le).treeGraph.dist δ x ≤ 2}) =>
        Zv (puAmalgam h.le) x) α hd le_rfl
    rwa [zv_of_isMVtx _ hα] at this
  refine ⟨hZV (S34F.uloc_le_zm' h hα hu.1), ?_⟩
  exact Subgroup.centralizer_le (vv_le_eCore hβδ) hu.2

theorem eCore_le (h : PUHyp M T L) (hU : IsSL3U M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    eCore (puAmalgam h.le) β ≤ Qv _ β ⊓ S34F.flat h α := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  refine iSup₂_le fun δ hδ => ?_
  have hβδ : (puAmalgam h.le).treeGraph.Adj β δ := hδ
  have hδM : IsMVtx (puAmalgam h.le) δ := by
    have h1 := (isMVtx_iff_of_adj _ hαβ).mp hα
    have h2 := isMVtx_iff_of_adj _ hβδ
    tauto
  refine le_inf ((vv_le_qv h hb hδM).trans (qv_le_qv _ h.hyp20 hδM hβδ.symm)) ?_
  by_cases hδα : δ = α
  · rw [hδα]
    exact (vv_le_qv h hb hα).trans (S43F.qv_le_flat h hα)
  · exact vv_le_flat_of_dist_two h hU hb4 hδM (dist_eq_two_of_adj_adj _ hβδ.symm hαβ.symm hδα)

theorem sl3Full_of_b4 (h14 : MS14AS) (hSQ : SQTKQuot) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hU : IsSL3U M T L) (hC : CentHyp (puAmalgam h.le))
    (hb4 : critDist (puAmalgam h.le) = 4) : IsSL3Full M T L := by
  have hα := PU.isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hWT : wCore (puAmalgam h.le) (baseB _) ≤ Qv (puAmalgam h.le) (baseB _) :=
    (wCore_le_centerOf hαβ.symm).trans (inf_le_left.trans
      ((vv_le_qv h (by omega) hα).trans (qv_le_qv _ h.hyp20 hα hαβ)))
  have hcen := qv_le_centralizer_of_le_uloc_sup_dloc h hmin hU hWT
    (stab_le_normalizer_wCore _) (wCore_le_uloc_sup_dloc h14 hSQ h hU hC hb4 hα hαβ)
  have hE := eCore_le h hU hb4 hα hαβ
  exact sl3Full_of_qv_le_centralizer h hU (hE.trans inf_le_left) (hE.trans inf_le_right)
    (hcen.trans (Subgroup.centralizer_le (uloc_inf_centralizer_le_wCore h hα hαβ)))

end Main

end CFSG.Quasithin.MS93.S4L.Core
