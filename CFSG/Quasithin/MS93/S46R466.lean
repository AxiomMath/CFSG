module

public import CFSG.Quasithin.MS93.S46ROrb
public import CFSG.Quasithin.MS93.S46I466aQ4
public import CFSG.Quasithin.MS93.S46I466aQC1
public import CFSG.Quasithin.MS93.S46I466aQMu
public import CFSG.Quasithin.MS93.S46I466aQPt

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem commutator_vv_inf_qv_vOrb_le (c : Hyp46 M T L φ) {x y : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx _ x) (hy : IsMVtx _ y) (hyx : (puAmalgam c.pu.le).treeGraph.dist y x = 2)
    (hC1 : ⁅Qv (puAmalgam c.pu.le) y, Ltil c.pu.le L y⁆ ≤ Vv _ y)
    (hI : ⁅Vv (puAmalgam c.pu.le) y, Vv _ y⁆ ≤ Zloc c.pu.le L y) :
    ⁅vOrb (puAmalgam c.pu.le) y x ⊔ ZM (puAmalgam c.pu.le) y,
      Vv (puAmalgam c.pu.le) x ⊓ Qv _ y⁆ ≤ Zloc c.pu.le L y := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have hZn : stab (puAmalgam c.pu.le) y ≤
      Subgroup.normalizer (Zloc c.pu.le L y : Set (puAmalgam c.pu.le).Universal) :=
    X3.le_normalizer_of_le_centralizer (zloc_le_centralizer_stab c.pu hfull hy)
  have hOs : vOrb (puAmalgam c.pu.le) y x ≤ stab _ y := by
    refine iSup₂_le fun g hg => ?_
    rw [zm_smul]
    rintro _ ⟨z, hz, rfl⟩
    have hzs : z ∈ stab (puAmalgam c.pu.le) y :=
      (zm_le_qv_of_dist_le_three c.b4 hx (by rw [tdist_comm, hyx]; omega)).trans
        (qv_le_stab _ y) hz
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hzs) (Subgroup.inv_mem _ hg)
  refine QMix.commutator_sup_le_of (hOs.trans hZn)
    ((zm_le_qv_of_dist_le_three c.b4 hy (by simp)).trans ((qv_le_stab _ y).trans hZn)) ?_ ?_
  · refine I467.commutator_biSup_le_of (fun g hg => ?_) (fun g hg => ?_)
    · rw [Subgroup.commutator_comm]
      exact QMix.commutator_vv_inf_qv_zm_smul_le c.pu hfull hb hy hx hyx hC1 hI hg
    · exact (zm_smul_le_vOrb hg).trans (hOs.trans hZn)
  · have h0 : ⁅ZM (puAmalgam c.pu.le) y, Qv _ y⁆ = ⊥ := commutator_zm_qv _ c.pu.hyp20 hy
    exact (Subgroup.commutator_mono le_rfl inf_le_right).trans (h0 ▸ bot_le)

theorem vOrb_sup_le_qv_of_abelian (c : Hyp46 M T L φ) {x ρ γ : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx _ x) (hxρ : (puAmalgam c.pu.le).treeGraph.Adj x ρ)
    (hργ : (puAmalgam c.pu.le).treeGraph.Adj ρ γ) (hxγ : x ≠ γ)
    (hab : ⁅vOrb (puAmalgam c.pu.le) x γ ⊔ ZM (puAmalgam c.pu.le) x,
      vOrb (puAmalgam c.pu.le) x γ ⊔ ZM (puAmalgam c.pu.le) x⁆ = ⊥) :
    vOrb (puAmalgam c.pu.le) x γ ⊔ ZM (puAmalgam c.pu.le) x ≤ Qv (puAmalgam c.pu.le) γ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have hγ : IsMVtx (puAmalgam c.pu.le) γ := by
    have h1 := isMVtx_iff_of_adj _ hxρ
    have h2 := isMVtx_iff_of_adj _ hργ
    tauto
  have hd : (puAmalgam c.pu.le).treeGraph.dist x γ = 2 := dist_eq_two_of_adj_adj _ hxρ hργ hxγ
  have hNV := vOrb_sup_le_vv' (L := L) c hx hγ hd.le
  have hNT : vOrb (puAmalgam c.pu.le) x γ ⊔ ZM (puAmalgam c.pu.le) x ≤ Qv _ ρ :=
    hNV.trans ((vv_le_qv c.pu hb hx).trans (qv_le_qv _ c.pu.hyp20 hx hxρ))
  have hNC : vOrb (puAmalgam c.pu.le) x γ ⊔ ZM (puAmalgam c.pu.le) x ≤
      Subgroup.centralizer (ZM (puAmalgam c.pu.le) γ : Set (puAmalgam c.pu.le).Universal) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 : ⁅v, z⁆ ∈ (⊥ : Subgroup (puAmalgam c.pu.le).Universal) :=
      hab ▸ Subgroup.commutator_mem_commutator hv (zm_le_vOrb_sup x γ hz)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  rw [← centHyp_of_gen23 c.pu hfull γ ρ hγ hργ.symm]
  exact le_inf hNT hNC

theorem false_of_orbit (h14 : MS14AS) (hSQ : SQTKQuot) (h43 : S43) (h463 : I463) (h465 : I465)
    (c : Hyp46 M T L φ)
    (hS : ∀ α β : Vtx (puAmalgam c.pu.le), IsMVtx _ α → (puAmalgam c.pu.le).treeGraph.Adj α β →
      (Qv _ α).relIndex (Qv _ β) < Fintype.card F ^ 2)
    (hI : ∀ x : Vtx (puAmalgam c.pu.le), IsMVtx _ x →
      ⁅Vv (puAmalgam c.pu.le) x, Vv _ x⁆ ≤ Zloc c.pu.le L x) : False := by
  have hVQ : ∀ x : Vtx (puAmalgam c.pu.le), IsMVtx _ x →
      ⁅Vv (puAmalgam c.pu.le) x, Qv _ x⁆ ≤ ZM _ x := fun x hx => by
    obtain ⟨β, hxβ⟩ := exists_adj (puAmalgam c.pu.le) x
    exact (h465 G M T L F φ c x β hx hxβ).2.2
  have hVV : ∀ x : Vtx (puAmalgam c.pu.le), IsMVtx _ x →
      ⁅Vv (puAmalgam c.pu.le) x, Vv _ x⁆ ≤ ZM _ x := fun x hx => (h463 G M T L F φ c x hx).2
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hC := centHyp_of_gen23 c.pu hfull
  have h20 := c.pu.hyp20
  have hb4 := c.b4
  have hb : 2 < critDist (puAmalgam c.pu.le) := by omega
  have hb0 : 0 < critDist (puAmalgam c.pu.le) := by omega
  obtain ⟨α, α', hc⟩ := exists_isCritical _ h20
  set β := geo (puAmalgam c.pu.le) α α' 1 with hβdef
  set γ := geo (puAmalgam c.pu.le) α α' 2 with hγdef
  have hα : IsMVtx (puAmalgam c.pu.le) α := hc.1
  have hγ : IsMVtx (puAmalgam c.pu.le) γ := isMVtx_geo_two' hb4 hc
  have hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β := adj_geo_one_of_isCritical _ hb0 hc
  have hβγ : (puAmalgam c.pu.le).treeGraph.Adj β γ := adj_geo_crit hb4 hc (i := 1) (by omega)
  have hdαγ : (puAmalgam c.pu.le).treeGraph.dist α γ = 2 := dist_geo_crit hb4 hc (by omega)
  have hdγα : (puAmalgam c.pu.le).treeGraph.dist γ α = 2 := by rw [tdist_comm]; exact hdαγ
  have hαγ : α ≠ γ := by
    rintro h
    rw [h] at hdαγ
    simp at hdαγ
  obtain ⟨γ', hc', hγ'⟩ := QMix.exists_isCritical_geo_two_eq c.pu h43 c.min hfull hb4 hc
  have hC1α := QMix.commutator_qv_ltil_le_vv c.pu c.via hb4 hS hVQ h43 c.min hc
  have hC1γ := QMix.commutator_qv_ltil_le_vv c.pu c.via hb4 hS hVQ h43 c.min hc'
  set V₁ := vOrb (puAmalgam c.pu.le) α γ ⊔ ZM (puAmalgam c.pu.le) α with hV₁def
  set V₀ := vOrb (puAmalgam c.pu.le) γ α ⊔ ZM (puAmalgam c.pu.le) γ with hV₀def
  have hV₁V : V₁ ≤ Vv (puAmalgam c.pu.le) α := vOrb_sup_le_vv' (L := L) c hα hγ hdαγ.le
  have hV₀V : V₀ ≤ Vv (puAmalgam c.pu.le) γ := vOrb_sup_le_vv' (L := L) c hγ hα hdγα.le
  have hV₁T : V₁ ≤ Qv (puAmalgam c.pu.le) β :=
    hV₁V.trans ((vv_le_qv c.pu hb hα).trans (qv_le_qv _ h20 hα hαβ))
  have hV₀T : V₀ ≤ Qv (puAmalgam c.pu.le) β :=
    hV₀V.trans ((vv_le_qv c.pu hb hγ).trans (qv_le_qv _ h20 hγ hβγ.symm))
  have hV₁Q : ¬ V₁ ≤ Qv (puAmalgam c.pu.le) γ := by
    obtain ⟨g, hg, hcg, -⟩ :=
      QMix.exists_orbit_partner c.pu c.via hb4 hS hVQ hVV h43 c.min hc'
    rw [hγ'] at hg
    have hcg' := ms22_iii _ h20 hb0 hC hcg
    intro hle
    exact hcg'.2.2 ((zm_smul_le_vOrb hg).trans (le_sup_left.trans hle))
  have hV₀Q : ¬ V₀ ≤ Qv (puAmalgam c.pu.le) α := by
    obtain ⟨g, hg, hcg, -⟩ :=
      QMix.exists_orbit_partner c.pu c.via hb4 hS hVQ hVV h43 c.min hc
    have hcg' := ms22_iii _ h20 hb0 hC hcg
    intro hle
    exact hcg'.2.2 ((zm_smul_le_vOrb hg).trans (le_sup_left.trans hle))
  have hZβα : ZH (puAmalgam c.pu.le) β ≤ ZM _ α := zh_le_zm _ hαβ
  have hZβγ : ZH (puAmalgam c.pu.le) β ≤ ZM _ γ := zh_le_zm _ hβγ.symm
  have hcomm₁ : ⁅V₁ ⊓ Qv (puAmalgam c.pu.le) γ, V₀⁆ ≤ ZM (puAmalgam c.pu.le) α := by
    have h1 := commutator_vv_inf_qv_vOrb_le c hα hγ hdγα hC1γ (hI γ hγ)
    rw [Subgroup.commutator_comm] at h1
    exact (Subgroup.commutator_mono (inf_le_inf_right _ hV₁V) le_rfl).trans
      (h1.trans ((zloc_le_zh c.pu hfull hγ hβγ.symm).trans hZβα))
  have hcomm₀ : ⁅V₀ ⊓ Qv (puAmalgam c.pu.le) α, V₁⁆ ≤ ZM (puAmalgam c.pu.le) γ := by
    have h1 := commutator_vv_inf_qv_vOrb_le c hγ hα hdαγ hC1α (hI α hα)
    rw [Subgroup.commutator_comm] at h1
    exact (Subgroup.commutator_mono (inf_le_inf_right _ hV₀V) le_rfl).trans
      (h1.trans ((zloc_le_zh c.pu hfull hα hαβ).trans hZβγ))
  have hZγα : ZM (puAmalgam c.pu.le) γ ≤ Qv _ α :=
    zm_le_qv_of_dist_le_three hb4 hγ (by rw [hdγα]; omega)
  have hZαγ : ZM (puAmalgam c.pu.le) α ≤ Qv _ γ :=
    zm_le_qv_of_dist_le_three hb4 hα (by rw [hdαγ]; omega)
  have hsq₀ : ∀ a ∈ V₀, a ^ 2 ∈ Qv (puAmalgam c.pu.le) α := fun a ha =>
    hZγα (hVV γ hγ (sq_mem_commutator_vv c.pu hb0 (hV₀V ha)))
  have hco₀ : ∀ a ∈ V₀, ∀ b ∈ V₀, ⁅a, b⁆ ∈ Qv (puAmalgam c.pu.le) α := fun a ha b hb' =>
    hZγα (hVV γ hγ (Subgroup.commutator_mem_commutator (hV₀V ha) (hV₀V hb')))
  have hsq₁ : ∀ a ∈ V₁, a ^ 2 ∈ Qv (puAmalgam c.pu.le) γ := fun a ha =>
    hZαγ (hVV α hα (sq_mem_commutator_vv c.pu hb0 (hV₁V ha)))
  have hco₁ : ∀ a ∈ V₁, ∀ b ∈ V₁, ⁅a, b⁆ ∈ Qv (puAmalgam c.pu.le) γ := fun a ha b hb' =>
    hZαγ (hVV α hα (Subgroup.commutator_mem_commutator (hV₁V ha) (hV₁V hb')))
  have hfinα := finite_stab c.pu hα
  have hfinγ := finite_stab c.pu hγ
  have hfinV₁ : Finite ↥V₁ := Finite.of_injective _ (Subgroup.inclusion_injective
    (hV₁V.trans ((vv_le_qv c.pu hb hα).trans (qv_le_stab _ α))))
  have hfinV₀ : Finite ↥V₀ := Finite.of_injective _ (Subgroup.inclusion_injective
    (hV₀V.trans ((vv_le_qv c.pu hb hγ).trans (qv_le_stab _ γ))))
  have hVsα : Vv (puAmalgam c.pu.le) α ≤ stab _ α := (vv_le_qv c.pu hb hα).trans (qv_le_stab _ α)
  have hVsγ : Vv (puAmalgam c.pu.le) γ ≤ stab _ γ := (vv_le_qv c.pu hb hγ).trans (qv_le_stab _ γ)
  have hZsα : ZM (puAmalgam c.pu.le) α ≤ stab _ α :=
    (zm_le_qv_self _ hα hb0).trans (qv_le_stab _ α)
  have hZsγ : ZM (puAmalgam c.pu.le) γ ≤ stab _ γ :=
    (zm_le_qv_self _ hγ hb0).trans (qv_le_stab _ γ)
  by_cases hab : (Qv (puAmalgam c.pu.le) γ).relIndex V₁ ≤ (Qv (puAmalgam c.pu.le) α).relIndex V₀
  ·
    have hC₀A : ⁅(V₁ ⊓ Qv (puAmalgam c.pu.le) γ) ⊔ ZM (puAmalgam c.pu.le) α, V₀⁆ ≤
        ZM (puAmalgam c.pu.le) α := by
      refine QMix.commutator_sup_le_of
        ((inf_le_left.trans (hV₁V.trans hVsα)).trans (stab_le_normalizer_zm _ α))
        (hZsα.trans (stab_le_normalizer_zm _ α)) hcomm₁ ?_
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((hV₀T.trans (qv_le_stab_of_adj _ hαβ.symm)).trans (stab_le_normalizer_zm _ α))
    have hidx : ((V₁ ⊓ Qv (puAmalgam c.pu.le) γ) ⊔ ZM (puAmalgam c.pu.le) α).relIndex V₁ ≤
        (Qv (puAmalgam c.pu.le) α).relIndex V₀ := by
      refine (Subgroup.relIndex_le_of_le_left le_sup_left (by
        rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)).trans ?_
      rw [Subgroup.inf_relIndex_left]
      exact hab
    have hN := commutator_le_uloc_of_orbit_offender h14 hSQ h463 c hα hαβ hβγ hαγ hV₀T hV₀Q hsq₀
      hco₀ le_sup_right (sup_le inf_le_left le_sup_right) hC₀A hidx
    have hbot : ⁅V₁, V₁⁆ = ⊥ := by
      rw [eq_bot_iff, ← uloc_inf_zloc c.pu hfull α]
      exact le_inf hN ((Subgroup.commutator_mono hV₁V hV₁V).trans (hI α hα))
    exact hV₁Q (vOrb_sup_le_qv_of_abelian c hα hαβ hβγ hαγ hbot)
  ·
    have hab' := le_of_lt (not_le.mp hab)
    have hC₀A : ⁅(V₀ ⊓ Qv (puAmalgam c.pu.le) α) ⊔ ZM (puAmalgam c.pu.le) γ, V₁⁆ ≤
        ZM (puAmalgam c.pu.le) γ := by
      refine QMix.commutator_sup_le_of
        ((inf_le_left.trans (hV₀V.trans hVsγ)).trans (stab_le_normalizer_zm _ γ))
        (hZsγ.trans (stab_le_normalizer_zm _ γ)) hcomm₀ ?_
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((hV₁T.trans (qv_le_stab_of_adj _ hβγ)).trans (stab_le_normalizer_zm _ γ))
    have hidx : ((V₀ ⊓ Qv (puAmalgam c.pu.le) α) ⊔ ZM (puAmalgam c.pu.le) γ).relIndex V₀ ≤
        (Qv (puAmalgam c.pu.le) γ).relIndex V₁ := by
      refine (Subgroup.relIndex_le_of_le_left le_sup_left (by
        rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)).trans ?_
      rw [Subgroup.inf_relIndex_left]
      exact hab'
    have hN := commutator_le_uloc_of_orbit_offender h14 hSQ h463 c hγ hβγ.symm hαβ.symm hαγ.symm
      hV₁T hV₁Q hsq₁ hco₁ le_sup_right (sup_le inf_le_left le_sup_right) hC₀A hidx
    have hbot : ⁅V₀, V₀⁆ = ⊥ := by
      rw [eq_bot_iff, ← uloc_inf_zloc c.pu hfull γ]
      exact le_inf hN ((Subgroup.commutator_mono hV₀V hV₀V).trans (hI γ hγ))
    exact hV₀Q (vOrb_sup_le_qv_of_abelian c hγ hβγ.symm hαβ.symm hαγ.symm hbot)

theorem s466aQ4_of_orbit (h14 : MS14AS) (hSQ : SQTKQuot) (h43 : S43) (h462 : I462)
    (h463 : I463) (h464 : I464) (h465 : I465) : S466aQ4 := by
  intro G _ _ M T L F _ _ φ c α β hα hαβ hq
  by_contra hne
  have hlt : (Qv (puAmalgam c.pu.le) α).relIndex (Qv _ β) < Fintype.card F ^ 2 :=
    lt_of_le_of_ne (relIndex_qv_le_sq h464 h465 c hα hαβ) hne
  have hS : ∀ α' β' : Vtx (puAmalgam c.pu.le), IsMVtx _ α' →
      (puAmalgam c.pu.le).treeGraph.Adj α' β' →
        (Qv _ α').relIndex (Qv _ β') < Fintype.card F ^ 2 := fun α' β' hα' hα'β' => by
    rw [relIndex_qv_eq_of_edge c.pu hα hαβ hα' hα'β']
    exact hlt
  exact false_of_orbit h14 hSQ h43 h463 h465 c hS
    (fun z hz => commutator_vv_le_zloc_of h43 h462 h463 h464 h465 c hq hS hz)

end CFSG.Quasithin.MS93.S46R
