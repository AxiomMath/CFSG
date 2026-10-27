module

public import CFSG.Quasithin.MS93.S46I466aQC2
public import CFSG.Quasithin.MS93.S46I466aQSec
public import CFSG.Quasithin.MS93.S4AFMain

public section

namespace CFSG.Quasithin.MS93.S46.QMix

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46.I466b
open scoped commutatorElement

section Bloc

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem not_zm_geo_two_le_bloc (h43 : S43) (hmin : PUMin M T L) (hfull : IsSL3Full M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) {δ δ' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) δ δ')
    (hVQ : ⁅Vv (puAmalgam h.le) δ, Qv _ δ⁆ ≤ ZM _ δ) :
    ¬ ZM (puAmalgam h.le) (geo _ δ δ' 2) ≤ Bloc h.le L δ := by
  have hC := centHyp_of_gen23 h hfull
  have hδ := hc.1
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  intro hle
  apply ms22_v _ h.hyp20 hb0 hC (h43 G M T L h hmin hb2 hfull) hc
  rw [xm_eq_zm h hfull hδ, stab_eq_ltil_sup_qv h hfull hδ]
  set y := geo (puAmalgam h.le) δ δ' 2 with hydef
  have hd : (puAmalgam h.le).treeGraph.dist δ y = 2 := dist_geo_crit hb4 hc (by norm_num)
  have hy : IsMVtx (puAmalgam h.le) y := isMVtx_geo_two' hb4 hc
  have hyV : ZM (puAmalgam h.le) y ≤ Vv _ δ := by
    have := zv_le_vv_of_dist h (le_of_eq hd)
    rwa [zv_of_isMVtx _ hy] at this
  have crit : ∀ g : (puAmalgam h.le).Universal, g ∈ stab (puAmalgam h.le) δ →
      (∀ x ∈ ZM (puAmalgam h.le) y, ⁅x⁻¹, g⁆ ∈ ZM (puAmalgam h.le) δ) →
      (ZM (puAmalgam h.le) y ⊔ ZM _ δ).map (MulAut.conj g).toMonoidHom ≤ ZM _ y ⊔ ZM _ δ := by
    intro g hg hx
    rw [Subgroup.map_sup]
    refine sup_le ?_ ((map_conj_eq_of_mem_normalizer (stab_le_normalizer_zm _ δ hg)).le.trans
      le_sup_right)
    rintro _ ⟨x, hxy, rfl⟩
    have e : g * x * g⁻¹ = x * ⁅x⁻¹, g⁆ := by rw [commutatorElement_def]; group
    show g * x * g⁻¹ ∈ _
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hxy) (Subgroup.mem_sup_right (hx x hxy))
  refine sup_le (le_normalizer_of_map_conj_le fun l hl => crit l (ltil_le_stab h δ hl) ?_)
    (le_normalizer_of_map_conj_le fun q hq => crit q (qv_le_stab _ δ hq) ?_)
  · intro x hx
    exact commutator_bloc_le h hb2 hδ (Subgroup.commutator_mem_commutator (hle (inv_mem hx)) hl)
  · intro x hx
    exact hVQ (Subgroup.commutator_mem_commutator (hyV (inv_mem hx)) hq)

theorem exists_isCritical_geo_two_eq (h43 : S43) (hmin : PUMin M T L) (hfull : IsSL3Full M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) {x δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) x δ) :
    ∃ ν, IsCritical (puAmalgam h.le) (geo _ x δ 2) ν ∧ geo _ (geo _ x δ 2) ν 2 = x := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hxy : (puAmalgam h.le).treeGraph.dist x (geo _ x δ 2) = 2 :=
    dist_geo_crit hb4 hc (by norm_num)
  have hyx : (puAmalgam h.le).treeGraph.dist (geo _ x δ 2) x = 2 := by
    rw [tdist_comm]; exact hxy
  have hVxy : ¬ Vv (puAmalgam h.le) x ≤ Qv _ (geo _ x δ 2) := by
    have := h43 G M T L h hmin hb hfull x δ hc
    rwa [geo_rev_two hb4 hc] at this
  by_contra hno
  apply hVxy
  refine (vv_le_critGen_sup h.hyp20 (centHyp_of_gen23 h hfull) hb4 hc.1 hyx).trans
    (sup_le ?_ le_rfl)
  exact iSup₂_le fun μ hμ => (hno ⟨μ, hμ⟩).elim

end Bloc

section Partner

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (hb4 : critDist (puAmalgam h.le) = 4)
  (hS : ∀ α β : Vtx (puAmalgam h.le), IsMVtx _ α → (puAmalgam h.le).treeGraph.Adj α β →
    (Qv _ α).relIndex (Qv _ β) < Fintype.card F ^ 2)
  (hVQ : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x → ⁅Vv (puAmalgam h.le) x, Qv _ x⁆ ≤ ZM _ x)
  (hVV : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x → ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ ZM _ x)
include h hφ hb4 hS hVQ hVV

theorem exists_orbit_partner (h43 : S43) (hmin : PUMin M T L) {x δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) x δ) :
    ∃ g ∈ stab (puAmalgam h.le) (geo _ x δ 2), IsCritical (puAmalgam h.le) x (g • x) ∧
      geo (puAmalgam h.le) x (g • x) 2 = geo _ x δ 2 := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hC := centHyp_of_gen23 h hfull
  have h20 := h.hyp20
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hx : IsMVtx (puAmalgam h.le) x := hc.1
  set y := geo (puAmalgam h.le) x δ 2 with hydef
  have hy : IsMVtx (puAmalgam h.le) y := isMVtx_geo_two' hb4 hc
  have hxy : (puAmalgam h.le).treeGraph.dist x y = 2 := dist_geo_crit hb4 hc (by norm_num)
  have hyx : (puAmalgam h.le).treeGraph.dist y x = 2 := by rw [tdist_comm]; exact hxy
  obtain ⟨ν, hcν, hgν⟩ : ∃ ν, IsCritical (puAmalgam h.le) y ν ∧ geo _ y ν 2 = x :=
    exists_isCritical_geo_two_eq h h43 hmin hfull hb4 hc
  have hZB : ¬ ZM (puAmalgam h.le) x ≤ Bloc h.le L y := by
    have := not_zm_geo_two_le_bloc h h43 hmin hfull hb4 hcν (hVQ y hy)
    rwa [hgν] at this
  by_contra hno
  push Not at hno
  apply hZB
  have hall : ∀ g ∈ stab (puAmalgam h.le) y, ZM (puAmalgam h.le) (g • x) ≤ Qv _ x := by
    intro g hg
    by_contra hZ
    have hgx : IsMVtx (puAmalgam h.le) (g • x) := (isMVtx_smul _ g x).mpr hx
    have hgy : g • y = y := (mem_stab _).mp hg
    have hd1 : (puAmalgam h.le).treeGraph.dist y (g • x) = 2 := by
      rw [← hgy, dist_smul]; exact hyx
    have hd2 : (puAmalgam h.le).treeGraph.dist x (g • x) ≤ 4 := by
      have := dist_triangle _ x y (g • x)
      omega
    have hd3 : 3 < (puAmalgam h.le).treeGraph.dist (g • x) x := by
      by_contra hle
      push Not at hle
      exact hZ (zm_le_qv_of_dist_le_three hb4 hgx hle)
    have hd : (puAmalgam h.le).treeGraph.dist x (g • x) = 4 := by
      rw [tdist_comm] at hd3
      omega
    have hcr : IsCritical (puAmalgam h.le) (g • x) x :=
      ⟨hgx, by rw [tdist_comm, hd, hb4], hZ⟩
    apply hno g hg (ms22_iii _ h20 hb0 hC hcr)
    exact (eq_geo_of_dist _ hxy (by rw [hxy, hd1, hd])).symm
  have hZxV : ZM (puAmalgam h.le) x ≤ Vv _ y := by
    have := zv_le_vv_of_dist h (le_of_eq hyx)
    rwa [zv_of_isMVtx _ hx] at this
  have hWQ : conjCl (stab (puAmalgam h.le) y) (ZM _ x) ⊔ ZM _ y ≤ Qv _ x := by
    refine sup_le (iSup₂_le fun g hg => ?_) (zm_le_qv_of_dist_le_three hb4 hy (by omega))
    rw [← zm_smul]
    exact hall g hg
  have hWV : conjCl (stab (puAmalgam h.le) y) (ZM _ x) ⊔ ZM _ y ≤ Vv _ y := by
    refine sup_le (iSup₂_le fun g hg => ?_) (zm_le_vv h hy)
    exact (Subgroup.map_mono hZxV).trans
      (map_conj_eq_of_mem_normalizer (stab_le_normalizer_vv h y hg)).le
  have hWs : conjCl (stab (puAmalgam h.le) y) (ZM _ x) ⊔ ZM _ y ≤ stab _ y :=
    hWV.trans ((vv_le_qv h hb hy).trans (qv_le_stab _ y))
  have hWn : stab (puAmalgam h.le) y ≤ Subgroup.normalizer
      ((conjCl (stab (puAmalgam h.le) y) (ZM _ x) ⊔ ZM _ y : Subgroup _) :
        Set (puAmalgam h.le).Universal) := by
    refine le_normalizer_of_map_conj_le fun g hg => ?_
    rw [Subgroup.map_sup]
    exact sup_le_sup (map_conj_eq_of_mem_normalizer (le_normalizer_conjCl _ _ hg)).le
      (map_conj_eq_of_mem_normalizer (stab_le_normalizer_zm _ y hg)).le
  have hZxW : ZM (puAmalgam h.le) x ≤ conjCl (stab (puAmalgam h.le) y) (ZM _ x) ⊔ ZM _ y :=
    fun z hz => Subgroup.mem_sup_left (map_conj_le_conjCl (one_mem _) ⟨z, hz, by simp⟩)
  have hZyW : ZM (puAmalgam h.le) y ≤ conjCl (stab (puAmalgam h.le) y) (ZM _ x) ⊔ ZM _ y :=
    le_sup_right
  have hcν' := ms22_iii _ h20 hb0 hC hcν
  obtain ⟨t, htZ, htQ⟩ := Set.not_subset.mp hcν'.2.2
  have hZνs : ZM (puAmalgam h.le) ν ≤ stab _ y := zm_le_stab_of_isCritical _ h20 hb0 hcν
  have ht2 : t ^ 2 ∈ Qv (puAmalgam h.le) y := by
    rw [sq_eq_one_of_mem_zv h hfull (show t ∈ Zv (puAmalgam h.le) ν by
      rw [zv_of_isMVtx _ hcν'.1]; exact htZ)]
    exact one_mem _
  have hCt : ∀ c ∈ ((conjCl (stab (puAmalgam h.le) y) (ZM _ x) ⊔ ZM _ y) ⊓ Qv _ ν) ⊔ ZM _ y,
      ⁅c, t⁆ ∈ ZM (puAmalgam h.le) y := by
    have hle : ⁅((conjCl (stab (puAmalgam h.le) y) (ZM _ x) ⊔ ZM _ y) ⊓ Qv _ ν) ⊔ ZM _ y,
        ZM (puAmalgam h.le) ν⁆ ≤ ZM _ y := by
      refine commutator_sup_le_of ((inf_le_left.trans hWs).trans (stab_le_normalizer_zm _ y))
        Subgroup.le_normalizer ?_
        (Subgroup.le_normalizer_iff_commutator_le_left.mp (hZνs.trans
          (stab_le_normalizer_zm _ y)))
      calc ⁅(conjCl (stab (puAmalgam h.le) y) (ZM _ x) ⊔ ZM _ y) ⊓ Qv _ ν, ZM _ ν⁆
          ≤ ⁅Qv (puAmalgam h.le) ν, ZM _ ν⁆ := Subgroup.commutator_mono inf_le_right le_rfl
        _ = ⁅ZM (puAmalgam h.le) ν, Qv _ ν⁆ := Subgroup.commutator_comm _ _
        _ = ⊥ := commutator_zm_qv _ h20 hcν'.1
        _ ≤ ZM _ y := bot_le
    exact fun c hc => hle (Subgroup.commutator_mem_commutator hc htZ)
  have hidx : (((conjCl (stab (puAmalgam h.le) y) (ZM _ x) ⊔ ZM _ y) ⊓ Qv _ ν) ⊔ ZM _ y).relIndex
      (conjCl (stab (puAmalgam h.le) y) (ZM _ x) ⊔ ZM _ y) < Fintype.card F := by
    set W := conjCl (stab (puAmalgam h.le) y) (ZM _ x) ⊔ ZM _ y with hWdef
    have : Finite ↥W := finite_of_le_stab h hy hWs
    have : Finite ↥((W ⊓ Qv (puAmalgam h.le) ν) ⊔ ZM _ y) :=
      finite_of_le_stab h hy ((sup_le inf_le_left hZyW).trans hWs)
    have : Finite ↥(ZM (puAmalgam h.le) y) := finite_of_le_stab h hy (hZyW.trans hWs)
    have hxτ : (puAmalgam h.le).treeGraph.Adj x (geo _ ν y 1) := by
      rw [geo_rev_one hb4 hcν, ← hgν]
      exact adj_geo_crit hb4 hcν (i := 2) (by norm_num)
    have hντ : (puAmalgam h.le).treeGraph.Adj ν (geo _ ν y 1) :=
      adj_geo_one_of_isCritical _ hb0 hcν'
    have : Finite ↥(Qv (puAmalgam h.le) (geo _ ν y 1)) :=
      finite_of_le_stab h hcν'.1 (qv_le_stab_of_adj _ hντ.symm)
    have hWτ : W ≤ Qv _ (geo _ ν y 1) := hWQ.trans (qv_le_qv _ h20 hx hxτ)
    have h1 : (Qv (puAmalgam h.le) ν).relIndex W < Fintype.card F ^ 2 :=
      lt_of_le_of_lt (Subgroup.relIndex_le_of_le_right hWτ relIndex_ne_zero_of_finite')
        (hS ν _ hcν'.1 hντ)
    obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hcν'.1
    obtain ⟨hE, -⟩ := card_natImage_zm_of_lt h hφ hC hcν' (hS ν _ hcν'.1 hντ) hψ
    rw [card_natImage_eq_relIndex h hφ hcν'.1 hψ
      (zm_le_stab_of_isCritical _ h20 hb0 hcν')] at hE
    have h2 : Fintype.card F ≤ (W ⊓ Qv (puAmalgam h.le) ν).relIndex ((W ⊓ Qv _ ν) ⊔ ZM _ y) := by
      calc Fintype.card F = (Qv (puAmalgam h.le) ν).relIndex (ZM _ y) := hE.symm
        _ = (W ⊓ Qv (puAmalgam h.le) ν).relIndex (ZM _ y) := by
            rw [← Subgroup.inf_relIndex_right (W ⊓ Qv _ ν) (ZM _ y), inf_assoc,
              inf_eq_right.mpr (inf_le_right.trans hZyW), Subgroup.inf_relIndex_right]
        _ ≤ (W ⊓ Qv (puAmalgam h.le) ν).relIndex ((W ⊓ Qv _ ν) ⊔ ZM _ y) :=
            Subgroup.relIndex_le_of_le_right le_sup_right relIndex_ne_zero_of_finite'
    have htow := Subgroup.relIndex_mul_relIndex (W ⊓ Qv (puAmalgam h.le) ν)
      ((W ⊓ Qv _ ν) ⊔ ZM _ y) W le_sup_left (sup_le inf_le_left hZyW)
    rw [Subgroup.inf_relIndex_left] at htow
    by_contra hge
    push Not at hge
    have := Nat.mul_le_mul h2 hge
    rw [htow, ← sq] at this
    omega
  have hsec := commutator_stab_le_of_section h hφ hy hWs hWn (stab_le_normalizer_zm _ y)
    le_sup_right (sup_le inf_le_left hZyW)
    (fun a ha => sq_mem_zm_of_mem_vv h hfull (hVV y hy) (hWV ha))
    ((Subgroup.commutator_mono hWV hWV).trans (hVV y hy))
    ((Subgroup.commutator_mono hWV le_rfl).trans (hVQ y hy)) (hZνs htZ) htQ ht2 hCt hidx
  intro z hz
  refine (mem_bloc_iff h hb hy).mpr ⟨hWV (hZxW hz), fun l hl => ?_⟩
  exact hsec (Subgroup.commutator_mem_commutator (hZxW hz) (ltil_le_stab h y hl))

end Partner

end CFSG.Quasithin.MS93.S46.QMix
