module

public import CFSG.Quasithin.MS93.S45Q4PB
import CFSG.Quasithin.MS93.S4A42Coc
public import CFSG.Quasithin.MS93.S45Q4PA

public section

namespace CFSG.Quasithin.MS93.S45Q4

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S45 CFSG.Quasithin.Fan86.Univ
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : S45.Ctx M T L φ)
include c

theorem exists_isCritical_of_isStraight {x x' : Vtx (puAmalgam c.hyp.le)}
    (hc : IsCritical (puAmalgam c.hyp.le) x x') (hs : IsStraight (puAmalgam c.hyp.le) x x') :
    ∃ t ∈ stab (puAmalgam c.hyp.le) x,
      IsCritical (puAmalgam c.hyp.le) (t • geo _ x x' 2) (geo _ x' x 2) := by
  have hd := c.dist_of_isCritical hc
  obtain ⟨γ, hγa, hγZ⟩ := c.exists_adj_not_le_normalizer hc
  obtain ⟨t, ht, -, htZ⟩ := c.c444 _ _ hc hs γ hγa hγZ
  rw [← zm_smul] at htZ
  have htx : t • x = x := (mem_stab _).mp ht
  have hM : IsMVtx (puAmalgam c.hyp.le) (t • geo _ x x' 2) := by
    rw [isMVtx_smul, isMVtx_geo _ (by omega)]
    exact ⟨fun _ => even_two, fun _ => hc.1⟩
  have h1 : (puAmalgam c.hyp.le).treeGraph.dist (t • geo _ x x' 2) x = 2 := by
    have := dist_smul (puAmalgam c.hyp.le) t (geo _ x x' 2) x
    rw [htx, tdist_comm _ (geo _ x x' 2), dist_geo _ (by omega)] at this
    exact this
  have h2 : (puAmalgam c.hyp.le).treeGraph.dist x (geo _ x' x 2) = 6 := by
    rw [tdist_comm, dist_geo_right _ (by rw [tdist_comm]; omega), tdist_comm, hd]
  have h3 := dist_triangle (puAmalgam c.hyp.le) (t • geo _ x x' 2) x (geo _ x' x 2)
  rw [h1, h2] at h3
  refine ⟨t, ht, hM, ?_, htZ⟩
  rw [c.b8]
  by_contra hne
  exact htZ (zm_le_qv_of_dist_lt _ hM (by rw [c.b8]; omega))

theorem false_of_zh_smul_eq {α β δ ν : Vtx (puAmalgam c.hyp.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam c.hyp.le).treeGraph.Adj α β) (hδ : IsMVtx _ δ)
    {g : (puAmalgam c.hyp.le).Universal} (hg : g ∈ stab (puAmalgam c.hyp.le) α)
    (hN : stab (puAmalgam c.hyp.le) α ⊓
        Subgroup.normalizer (Qv (puAmalgam c.hyp.le) β : Set (puAmalgam c.hyp.le).Universal) ≤
      Subgroup.normalizer (ZM (puAmalgam c.hyp.le) δ : Set (puAmalgam c.hyp.le).Universal))
    (hZ : ZH (puAmalgam c.hyp.le) (g • β) = ZH _ β) (hc : IsCritical (puAmalgam c.hyp.le) δ ν)
    (hd : (puAmalgam c.hyp.le).treeGraph.dist (g • δ) ν < 8) : False := by
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc c.hyp c.via hα
  have hgα : g • α = α := (mem_stab _).mp hg
  have hαgβ : (puAmalgam c.hyp.le).treeGraph.Adj α (g • β) := by
    rw [← hgα]; exact (adj_smul _ g _ _).mpr hαβ
  have hU : (Usup (puAmalgam c.hyp.le) α β).map (MulAut.conj g).toMonoidHom = Usup _ α β := by
    rw [← usup_smul, hgα]
    exact (c.usup_eq_iff_zh_eq hψ hα hαgβ hαβ).mpr hZ
  have hgT := mem_normalizer_qv_of_usup c hα hαβ hg (mem_normalizer_of_map_conj_eq hU)
  have hZ2 : ZM (puAmalgam c.hyp.le) (g • δ) = ZM _ δ := by
    rw [zm_smul]; exact map_conj_eq_of_mem_normalizer (hN ⟨hg, hgT⟩)
  apply hc.2.2
  rw [← hZ2]
  exact zm_le_qv_of_dist_lt _ ((isMVtx_smul _ g _).mpr hδ) (by rw [c.b8]; exact hd)

theorem commutator_zm_le_of_smul {α μ δ ν : Vtx (puAmalgam c.hyp.le)} (hα : IsMVtx _ α)
    {S : Subgroup (puAmalgam c.hyp.le).Universal} {g : (puAmalgam c.hyp.le).Universal}
    (hg : g ∈ stab (puAmalgam c.hyp.le) α)
    (hK1 : ⁅Vv (puAmalgam c.hyp.le) α, Vv _ μ⁆ ≤ Zloc c.hyp.le L α)
    (hK2 : ⁅Vv (puAmalgam c.hyp.le) α, Vv _ μ⁆ ≤ S) (hδ : IsMVtx _ δ)
    (hdδ : (puAmalgam c.hyp.le).treeGraph.dist α δ ≤ 2) (hν : IsMVtx _ ν)
    (hdν : (puAmalgam c.hyp.le).treeGraph.dist (g • μ) ν ≤ 2) :
    ⁅ZM (puAmalgam c.hyp.le) δ, ZM _ ν⁆ ≤ S := by
  have h := c.hyp
  have hVg : (Vv (puAmalgam h.le) α).map (MulAut.conj g).toMonoidHom = Vv _ α :=
    map_conj_eq_of_mem_normalizer (stab_le_normalizer_vv h _ hg)
  have key : ∀ y ∈ ⁅Vv (puAmalgam h.le) α, Vv _ μ⁆, g * y * g⁻¹ = y := fun y hy => by
    have hyc : y ∈ Subgroup.centralizer (stab (puAmalgam h.le) α : Set _) :=
      zloc_le_centralizer_stab h c.full hα (hK1 hy)
    rw [(Subgroup.mem_centralizer_iff.mp hyc) g hg, mul_inv_cancel_right]
  have hKg : (⁅Vv (puAmalgam h.le) α, Vv _ μ⁆).map (MulAut.conj g).toMonoidHom =
      ⁅Vv (puAmalgam h.le) α, Vv _ μ⁆ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show g * y * g⁻¹ ∈ _
      rw [key y hy]; exact hy
    · intro hx
      exact ⟨x, hx, key x hx⟩
  have hK : ⁅Vv (puAmalgam h.le) α, Vv _ (g • μ)⁆ = ⁅Vv (puAmalgam h.le) α, Vv _ μ⁆ := by
    calc ⁅Vv (puAmalgam h.le) α, Vv _ (g • μ)⁆
        = ⁅(Vv (puAmalgam h.le) α).map (MulAut.conj g).toMonoidHom,
            (Vv (puAmalgam h.le) μ).map (MulAut.conj g).toMonoidHom⁆ := by
          rw [hVg, show Vv (puAmalgam h.le) (g • μ) = (Vv _ μ).map _ from vi_smul _ g _ 2]
      _ = (⁅Vv (puAmalgam h.le) α, Vv _ μ⁆).map (MulAut.conj g).toMonoidHom :=
          (Subgroup.map_commutator _ _ _).symm
      _ = _ := hKg
  refine (Subgroup.commutator_mono (c.zm_le_vv_of_le hδ hdδ)
    (c.zm_le_vv_of_le hν hdν)).trans ?_
  rw [hK]; exact hK2

theorem zm_le_normalizer_zm {δ β ε ν : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    (hδβ : (puAmalgam c.hyp.le).treeGraph.Adj δ β) (hc : IsCritical (puAmalgam c.hyp.le) δ ν)
    (hR : ⁅ZM (puAmalgam c.hyp.le) δ, ZM _ ν⁆ ≤ Usup _ δ β)
    (hN : stab (puAmalgam c.hyp.le) δ ⊓
        Subgroup.normalizer (Qv (puAmalgam c.hyp.le) β : Set (puAmalgam c.hyp.le).Universal) ≤
      Subgroup.normalizer (ZM (puAmalgam c.hyp.le) ε : Set (puAmalgam c.hyp.le).Universal)) :
    ZM (puAmalgam c.hyp.le) ν ≤
      Subgroup.normalizer (ZM (puAmalgam c.hyp.le) ε : Set (puAmalgam c.hyp.le).Universal) := by
  have h := c.hyp
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hδ
  have hle : ZM (puAmalgam h.le) ν ≤
      Subgroup.normalizer (Usup (puAmalgam h.le) δ β : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    have hUZ : Usup (puAmalgam h.le) δ β ≤ ZM _ δ := by
      rw [c.usup_eq_uloc_inf_centralizer hψ hδ hδβ]
      exact inf_le_left.trans (uloc_le_zm h c.full hδ)
    refine (Subgroup.commutator_mono le_rfl hUZ).trans ?_
    rw [Subgroup.commutator_comm]
    exact hR
  intro z hz
  have hzs : z ∈ stab (puAmalgam h.le) δ := zm_le_stab_of_isCritical _ h.hyp20 c.bpos hc hz
  exact hN ⟨hzs, mem_normalizer_qv_of_usup c hδ hδβ hzs (hle hz)⟩

theorem inv_mul_conj_mem_zh {x x' ν : Vtx (puAmalgam c.hyp.le)}
    (hc : IsCritical (puAmalgam c.hyp.le) x x')
    (hn : ZM (puAmalgam c.hyp.le) ν ≤
      Subgroup.normalizer (ZM (puAmalgam c.hyp.le) x : Set (puAmalgam c.hyp.le).Universal))
    (hνQ : ZM (puAmalgam c.hyp.le) ν ≤ Qv _ x') :
    ∀ y ∈ ZM (puAmalgam c.hyp.le) x, ∀ z ∈ ZM (puAmalgam c.hyp.le) ν,
      y⁻¹ * (z * y * z⁻¹) ∈ ZH (puAmalgam c.hyp.le) (geo _ x x' 1) := by
  have h := c.hyp
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hc.1
  have hxs : ZM (puAmalgam h.le) x ≤ stab _ x' :=
    zm_le_stab_of_isCritical _ h.hyp20 c.bpos (c.isCritical_symm hc)
  intro y hy z hz
  rw [← c.zm_inf_qv hc hψ]
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hy)
    ((Subgroup.mem_normalizer_iff.mp (hn hz) y).mp hy), ?_⟩
  have hyN := stab_le_normalizer_qv _ _ (hxs hy)
  have h1 : y⁻¹ * z * y ∈ Qv (puAmalgam h.le) x' := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hyN) z).mp (hνQ hz)
    simpa using this
  have e : y⁻¹ * (z * y * z⁻¹) = (y⁻¹ * z * y) * z⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hνQ hz))

theorem relIndex_le_of_zh_ne {q : ℕ → Vtx (puAmalgam c.hyp.le)} (hq : IsNBPath _ q 4)
    (hq0 : IsMVtx _ (q 0)) {g : (puAmalgam c.hyp.le).Universal}
    (hg : g ∈ stab (puAmalgam c.hyp.le) (q 0)) (hB : Bend q g)
    (hH2 : Hloc c.hyp.le L (q 2) = Usup (puAmalgam c.hyp.le) (q 0) (q 1))
    (hZ1 : ZH (puAmalgam c.hyp.le) (g • q 1) ≠ ZH _ (q 1)) :
    (Vv (puAmalgam c.hyp.le) (q 2) ⊓ Qv _ (g • q 4)).relIndex (Vv _ (q 2)) ≤ Fintype.card F := by
  have h := c.hyp
  have h20 := h.hyp20
  have hgα : g • q 0 = q 0 := (mem_stab _).mp hg
  have hM2 : IsMVtx (puAmalgam h.le) (q 2) :=
    (hq.isMVtx_iff (i := 2) (by omega)).mpr ⟨fun _ => even_two, fun _ => hq0⟩
  have hM4 : IsMVtx (puAmalgam h.le) (q 4) :=
    (hq.isMVtx_iff (i := 4) le_rfl).mpr ⟨fun _ => by decide, fun _ => hq0⟩
  have hgM2 : IsMVtx (puAmalgam h.le) (g • q 2) := (isMVtx_smul _ g _).mpr hM2
  have hgM4 : IsMVtx (puAmalgam h.le) (g • q 4) := (isMVtx_smul _ g _).mpr hM4
  have hu : IsNBPath (puAmalgam h.le) (fun i => g • q i) 4 := isNBPath_smul hq g
  have ha01 : (puAmalgam h.le).treeGraph.Adj (q 0) (q 1) := hq.adj 0 (by omega)
  have ha0g1 : (puAmalgam h.le).treeGraph.Adj (q 0) (g • q 1) := by
    rw [← hgα]; exact (adj_smul _ g _ _).mpr ha01
  have hga12 : (puAmalgam h.le).treeGraph.Adj (g • q 1) (g • q 2) := hu.adj 1 (by omega)
  have hga34 : (puAmalgam h.le).treeGraph.Adj (g • q 3) (g • q 4) := hu.adj 3 (by omega)
  obtain ⟨ψ₀, -, hψ₀⟩ := exists_natural_Uloc h c.via hq0
  have hH2' : Hloc c.hyp.le L (g • q 2) = Usup (puAmalgam h.le) (q 0) (g • q 1) := by
    rw [hloc_smul h, hH2, ← usup_smul, hgα]
  have hne01 : Usup (puAmalgam h.le) (q 0) (q 1) ≠ Usup _ (q 0) (g • q 1) := fun heq =>
    hZ1 ((c.usup_eq_iff_zh_eq hψ₀ hq0 ha01 ha0g1).mp heq).symm
  have hcard01 := c.card_usup_inf_usup hψ₀ hq0 ha01 ha0g1 hne01
  have hVV : ⁅Vv (puAmalgam h.le) (g • q 2), Vv _ (q 2)⁆ ≤
      Usup (puAmalgam h.le) (q 0) (q 1) ⊓ Usup _ (q 0) (g • q 1) := by
    refine le_inf ?_ ?_
    · rw [← hH2, Subgroup.commutator_comm]
      exact c.commutator_vv_le_hloc hM2 (β := q 1) (hq.adj 1 (by omega)).symm
        (vi_le_qv _ (by rw [hB.d_g2_2, c.b8]; norm_num))
        (vi_le_centralizer_vi _ h20 c.bpos (i := 1) (j := 2) (by rw [hB.d_1_g2, c.b8]; norm_num))
    · rw [← hH2']
      exact c.commutator_vv_le_hloc hgM2 (β := g • q 1) hga12.symm
        (vi_le_qv _ (by rw [tdist_comm, hB.d_g2_2, c.b8]; norm_num))
        (vi_le_centralizer_vi _ h20 c.bpos (i := 1) (j := 2) (by rw [hB.d_g1_2, c.b8]; norm_num))
  have hfin01 : Finite ↥(Usup (puAmalgam h.le) (q 0) (q 1) ⊓ Usup _ (q 0) (g • q 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard01]; exact Fintype.card_ne_zero)
  have hXc : Nat.card ↥⁅Uloc c.hyp.le L (g • q 4), Vv (puAmalgam h.le) (q 2)⁆ ≤
      Fintype.card F := by
    have hle : ⁅Uloc c.hyp.le L (g • q 4), Vv (puAmalgam h.le) (q 2)⁆ ≤
        Usup (puAmalgam h.le) (q 0) (q 1) ⊓ Usup _ (q 0) (g • q 1) :=
      (Subgroup.commutator_mono ((uloc_le_zm h c.full hgM4).trans
        (c.zm_le_vv_of_le hgM4 (by rw [hu.dist_eq' (i := 2) (j := 4) (by omega) le_rfl])))
          le_rfl).trans hVV
    have := Subgroup.card_le_of_le hle
    rwa [hcard01] at this
  exact relIndex_inf_qv_le c hgM4 hga34.symm (vi_le_qv _ (by rw [hB.d_2_g3, c.b8]; norm_num)) hXc

theorem not_usup_le_vv {q : ℕ → Vtx (puAmalgam c.hyp.le)} (hq : IsNBPath _ q 4)
    (hq0 : IsMVtx _ (q 0)) {g : (puAmalgam c.hyp.le).Universal} (hB : Bend q g)
    (hcrit' : IsCritical (puAmalgam c.hyp.le) (q 4) (g • q 4))
    (hstr' : IsStraight (puAmalgam c.hyp.le) (q 4) (g • q 4))
    (hH4 : Hloc c.hyp.le L (q 4) = Usup (puAmalgam c.hyp.le) (q 2) (q 3))
    (hZ13 : ZH (puAmalgam c.hyp.le) (q 1) ≠ ZH _ (q 3)) {t : (puAmalgam c.hyp.le).Universal}
    (ht : t ∈ stab (puAmalgam c.hyp.le) (g • q 4)) :
    ¬ Usup (puAmalgam c.hyp.le) (t • g • q 2) (t • g • q 3) ≤ Vv _ (q 2) := by
  intro hle
  have h := c.hyp
  have h20 := h.hyp20
  have hM2 : IsMVtx (puAmalgam h.le) (q 2) :=
    (hq.isMVtx_iff (i := 2) (by omega)).mpr ⟨fun _ => even_two, fun _ => hq0⟩
  have hgM2 : IsMVtx (puAmalgam h.le) (g • q 2) := (isMVtx_smul _ g _).mpr hM2
  have hu : IsNBPath (puAmalgam h.le) (fun i => g • q i) 4 := isNBPath_smul hq g
  have hga12 : (puAmalgam h.le).treeGraph.Adj (g • q 1) (g • q 2) := hu.adj 1 (by omega)
  have hga23 : (puAmalgam h.le).treeGraph.Adj (g • q 2) (g • q 3) := hu.adj 2 (by omega)
  have hHg4 : Hloc c.hyp.le L (g • q 4) = Usup (puAmalgam h.le) (g • q 2) (g • q 3) := by
    rw [hloc_smul h, hH4, ← usup_smul]
  have hUν : Usup (puAmalgam h.le) (t • g • q 2) (t • g • q 3) = Usup _ (g • q 2) (g • q 3) := by
    rw [usup_smul, ← hHg4, map_conj_eq_of_mem_normalizer (c.stab_le_normalizer_hloc _ ht)]
  rw [hUν] at hle
  obtain ⟨t', ht', hcν⟩ := exists_isCritical_of_isStraight c hcrit' hstr'
  rw [hB.geo'2, hB.geo2] at hcν
  have hcν' := c.isCritical_symm hcν
  have ht'4 : t' • q 4 = q 4 := (mem_stab _).mp ht'
  have d_ν4 : (puAmalgam h.le).treeGraph.dist (t' • q 2) (q 4) = 2 := by
    have := dist_smul (puAmalgam h.le) t' (q 2) (q 4)
    rw [ht'4, hq.dist_eq' (i := 2) (j := 4) (by omega) le_rfl] at this
    exact this
  have hdν' : (puAmalgam h.le).treeGraph.dist (g • q 2) (t' • q 2) = 8 :=
    c.dist_of_isCritical hcν'
  have hgeoμ : geo (puAmalgam h.le) (g • q 2) (t' • q 2) 1 = g • q 1 := by
    symm
    apply eq_geo_one _ hga12.symm
    have h1 := dist_triangle (puAmalgam h.le) (g • q 1) (q 4) (t' • q 2)
    have h2 := dist_triangle (puAmalgam h.le) (g • q 2) (g • q 1) (t' • q 2)
    rw [hB.d_g1_4, tdist_comm _ (q 4), d_ν4] at h1
    rw [dist_eq_one_of_adj _ hga12.symm, hdν'] at h2
    rw [hdν']
    omega
  have hcen : Vv (puAmalgam h.le) (q 2) ≤
      Subgroup.centralizer (ZM (puAmalgam h.le) (t' • q 2) : Set _) := by
    refine c.vi_le_centralizer_zm hcν.1 ?_
    have h1 := dist_triangle (puAmalgam h.le) (q 2) (q 4) (t' • q 2)
    rw [hq.dist_eq' (i := 2) (j := 4) (by omega) le_rfl, tdist_comm _ (q 4), d_ν4] at h1
    omega
  obtain ⟨ψ₂, -, hψ₂⟩ := exists_natural_Uloc h c.via hgM2
  have hfix := c.fixN_natImage_zm hcν' hψ₂
  rw [hgeoμ] at hfix
  have hZs : ZM (puAmalgam h.le) (t' • q 2) ≤ stab _ (g • q 2) :=
    zm_le_stab_of_isCritical _ h20 c.bpos hcν'
  have hsub : Usup (puAmalgam h.le) (g • q 2) (g • q 3) ≤ Usup _ (g • q 2) (g • q 1) := by
    intro x hx
    have hxU : x ∈ Uloc c.hyp.le L (g • q 2) := by
      rw [c.usup_eq_uloc_inf_centralizer hψ₂ hgM2 hga23] at hx; exact hx.1
    have h1 := (S4A.mem_centralizer_iff_natVec hψ₂ hZs ⟨x, hxU⟩).mp (hcen (hle hx))
    rw [hfix] at h1
    exact (c.mem_usup_iff hψ₂ hgM2 hga12.symm ⟨x, hxU⟩).mpr h1
  have hcard3 := c.card_usup hψ₂ hgM2 hga12.symm
  have hfin3 : Finite ↥(Usup (puAmalgam h.le) (g • q 2) (g • q 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard3]; exact pow_ne_zero _ Fintype.card_ne_zero)
  have heq : Usup (puAmalgam h.le) (g • q 2) (g • q 3) = Usup _ (g • q 2) (g • q 1) :=
    Subgroup.eq_of_le_of_card_ge hsub (by rw [hcard3, c.card_usup hψ₂ hgM2 hga23])
  have hZeq := (c.usup_eq_iff_zh_eq hψ₂ hgM2 hga23 hga12.symm).mp heq
  rw [zh_smul, zh_smul] at hZeq
  exact hZ13 (Subgroup.map_injective (MulAut.conj g).injective hZeq).symm

theorem zm_smul_le_qv_of {q : ℕ → Vtx (puAmalgam c.hyp.le)} (hq : IsNBPath _ q 4)
    (hq0 : IsMVtx _ (q 0)) (hs : ∃ k ∈ stab (puAmalgam c.hyp.le) (q 2), k • q 4 = q 0)
    (hK1 : ⁅Vv (puAmalgam c.hyp.le) (q 0), Vv _ (q 4)⁆ ≤ Zloc c.hyp.le L (q 0))
    (hK2 : ⁅Vv (puAmalgam c.hyp.le) (q 0), Vv _ (q 4)⁆ ≤ Usup _ (q 2) (q 3))
    (hH2 : Hloc c.hyp.le L (q 2) = Usup (puAmalgam c.hyp.le) (q 0) (q 1))
    (hH4 : Hloc c.hyp.le L (q 4) = Usup (puAmalgam c.hyp.le) (q 2) (q 3))
    (hN2 : stab (puAmalgam c.hyp.le) (q 0) ⊓
        Subgroup.normalizer (Qv (puAmalgam c.hyp.le) (q 1) : Set (puAmalgam c.hyp.le).Universal) ≤
      Subgroup.normalizer (ZM (puAmalgam c.hyp.le) (q 2) : Set (puAmalgam c.hyp.le).Universal))
    (hN4 : stab (puAmalgam c.hyp.le) (q 2) ⊓
        Subgroup.normalizer (Qv (puAmalgam c.hyp.le) (q 3) : Set (puAmalgam c.hyp.le).Universal) ≤
      Subgroup.normalizer (ZM (puAmalgam c.hyp.le) (q 4) : Set (puAmalgam c.hyp.le).Universal))
    (hZ13 : ZH (puAmalgam c.hyp.le) (q 1) ≠ ZH _ (q 3))
    {g : (puAmalgam c.hyp.le).Universal} (hg : g ∈ stab (puAmalgam c.hyp.le) (q 0)) :
    ZM (puAmalgam c.hyp.le) (g • q 4) ≤ Qv _ (q 4) := by
  have h := c.hyp
  have h20 := h.hyp20
  by_contra hcon
  have hgα : g • q 0 = q 0 := (mem_stab _).mp hg
  have hM2 : IsMVtx (puAmalgam h.le) (q 2) :=
    (hq.isMVtx_iff (i := 2) (by omega)).mpr ⟨fun _ => even_two, fun _ => hq0⟩
  have hM4 : IsMVtx (puAmalgam h.le) (q 4) :=
    (hq.isMVtx_iff (i := 4) le_rfl).mpr ⟨fun _ => by decide, fun _ => hq0⟩
  have hgM2 : IsMVtx (puAmalgam h.le) (g • q 2) := (isMVtx_smul _ g _).mpr hM2
  have hgM4 : IsMVtx (puAmalgam h.le) (g • q 4) := (isMVtx_smul _ g _).mpr hM4
  have hu : IsNBPath (puAmalgam h.le) (fun i => g • q i) 4 := isNBPath_smul hq g
  have hdq : ∀ i j, i ≤ j → j ≤ 4 → (puAmalgam h.le).treeGraph.dist (q i) (q j) = j - i :=
    fun i j hij hj => hq.dist_eq' hij hj
  have hdu : ∀ i j, i ≤ j → j ≤ 4 →
      (puAmalgam h.le).treeGraph.dist (g • q i) (g • q j) = j - i :=
    fun i j hij hj => hu.dist_eq' hij hj
  have ha01 : (puAmalgam h.le).treeGraph.Adj (q 0) (q 1) := hq.adj 0 (by omega)
  have ha23 : (puAmalgam h.le).treeGraph.Adj (q 2) (q 3) := hq.adj 2 (by omega)
  have hga23 : (puAmalgam h.le).treeGraph.Adj (g • q 2) (g • q 3) := hu.adj 2 (by omega)
  have hga34 : (puAmalgam h.le).treeGraph.Adj (g • q 3) (g • q 4) := hu.adj 3 (by omega)
  have hd8 : (puAmalgam h.le).treeGraph.dist (g • q 4) (q 4) = 8 := by
    have h1 := dist_triangle (puAmalgam h.le) (g • q 4) (q 0) (q 4)
    have h2 : (puAmalgam h.le).treeGraph.dist (g • q 4) (q 0) = 4 := by
      rw [tdist_comm, ← hgα]; exact hdu 0 4 (by omega) le_rfl
    rw [h2, hdq 0 4 (by omega) le_rfl] at h1
    by_contra hne
    exact hcon (zm_le_qv_of_dist_lt _ hgM4 (by rw [c.b8]; omega))
  have h11 : g • q 1 ≠ q 1 := by
    intro heq
    have h1 := dist_triangle (puAmalgam h.le) (g • q 4) (q 1) (q 4)
    have h2 : (puAmalgam h.le).treeGraph.dist (g • q 4) (q 1) = 3 := by
      rw [tdist_comm, ← heq]; exact hdu 1 4 (by omega) le_rfl
    rw [h2, hdq 1 4 (by omega) le_rfl, hd8] at h1
    omega
  have hB := bend_of hq hgα h11
  have hcrit : IsCritical (puAmalgam h.le) (g • q 4) (q 4) := ⟨hgM4, by rw [hd8, c.b8], hcon⟩
  have hcrit' := c.isCritical_symm hcrit
  obtain ⟨k, hk, hkq⟩ := hs
  obtain ⟨hstr, hstr'⟩ := isStraight_of_bend hB hg hk hkq
  obtain ⟨t, ht, hc2⟩ := exists_isCritical_of_isStraight c hcrit hstr
  rw [hB.geo2, hB.geo'2] at hc2
  have hc2' := c.isCritical_symm hc2
  have ht4 : t • g • q 4 = g • q 4 := (mem_stab _).mp ht
  have d_ν_g4 : (puAmalgam h.le).treeGraph.dist (t • g • q 2) (g • q 4) = 2 := by
    have := dist_smul (puAmalgam h.le) t (g • q 2) (g • q 4)
    rw [ht4, hdu 2 4 (by omega) le_rfl] at this
    exact this
  by_cases hZ1 : ZH (puAmalgam h.le) (g • q 1) = ZH _ (q 1)
  · refine false_of_zh_smul_eq c hq0 ha01 hM2 hg hN2 hZ1 hc2' ?_
    have h1 := dist_triangle (puAmalgam h.le) (g • q 2) (g • q 4) (t • g • q 2)
    rw [hdu 2 4 (by omega) le_rfl, tdist_comm _ (g • q 4), d_ν_g4] at h1
    omega
  have hR := commutator_zm_le_of_smul c hq0 hg hK1 hK2 hM2
    (by rw [hdq 0 2 (by omega) (by omega)]) hc2.1 (by rw [tdist_comm, d_ν_g4])
  have hZn := zm_le_normalizer_zm c hM2 ha23 hc2' hR hN4
  have hZνQ : ZM (puAmalgam h.le) (t • g • q 2) ≤ Qv _ (g • q 4) :=
    zm_le_qv_of_dist_lt _ hc2.1 (by rw [d_ν_g4, c.b8]; norm_num)
  have hZZ := inv_mul_conj_mem_zh c hcrit' hZn hZνQ
  rw [hB.geo'1] at hZZ
  have hYi := relIndex_le_of_zh_ne c hq hq0 hg hB hH2 hZ1
  have hν1 : (puAmalgam h.le).treeGraph.Adj (t • g • q 2) (t • g • q 3) :=
    (adj_smul _ t _ _).mpr hga23
  have hν1' : (puAmalgam h.le).treeGraph.Adj (g • q 4) (t • g • q 3) := by
    rw [← ht4]; exact (adj_smul _ t _ _).mpr hga34.symm
  have hdν : (puAmalgam h.le).treeGraph.dist (t • g • q 2) (q 2) = 8 := c.dist_of_isCritical hc2
  have hgeoν : geo (puAmalgam h.le) (t • g • q 2) (q 2) 1 = t • g • q 3 := by
    symm
    apply eq_geo_one _ hν1
    have h1 := dist_triangle (puAmalgam h.le) (t • g • q 3) (g • q 4) (q 2)
    have h2 := dist_triangle (puAmalgam h.le) (t • g • q 2) (t • g • q 3) (q 2)
    rw [tdist_comm _ (t • g • q 3) (g • q 4), dist_eq_one_of_adj _ hν1', hB.d_g4_2] at h1
    rw [dist_eq_one_of_adj _ hν1, hdν] at h2
    rw [hdν]
    omega
  have hYT : Vv (puAmalgam h.le) (q 2) ⊓ Qv _ (g • q 4) ≤
      Qv _ (geo (puAmalgam h.le) (t • g • q 2) (q 2) 1) := by
    rw [hgeoν]; exact inf_le_right.trans (qv_le_qv _ h20 hgM4 hν1')
  have hZY : ZM (puAmalgam h.le) (q 2) ≤ Vv _ (q 2) ⊓ Qv _ (g • q 4) :=
    le_inf (zm_le_vv h hM2)
      (zm_le_qv_of_dist_lt _ hM2 (by rw [tdist_comm, hB.d_g4_2, c.b8]; norm_num))
  have hW : ¬ Usup (puAmalgam h.le) (t • g • q 2) (geo _ (t • g • q 2) (q 2) 1) ≤
      Vv _ (q 2) := by
    rw [hgeoν]; exact not_usup_le_vv c hq hq0 hB hcrit' hstr' hH4 hZ13 ht
  have hYb : Vv (puAmalgam h.le) (q 2) ⊓ Qv _ (g • q 4) ≤ ZM _ (q 2) ⊔ Qv _ (t • g • q 2) :=
    le_zm_sup_qv c hc2' inf_le_left hYT hZY hW
  obtain ⟨z, hzZ, hzQ⟩ := Set.not_subset.mp hc2.2.2
  apply hcrit'.2.2
  intro y hy
  have hyV : y ∈ Vv (puAmalgam h.le) (q 2) :=
    c.zm_le_vv_of_le hM4 (by rw [hdq 2 4 (by omega) le_rfl]) hy
  have hBl : y⁻¹ * (z * y * z⁻¹) ∈ Bloc c.hyp.le L (q 2) :=
    zm_le_bloc h (by rw [c.b8]; norm_num) hM2 (zh_le_zm _ ha23 (hZZ y hy z hzZ))
  exact (mem_of_mem_bloc c hc2' inf_le_left hYi hYb hzZ hzQ hyV hBl).2

end CFSG.Quasithin.MS93.S45Q4
