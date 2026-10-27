module

public import CFSG.Quasithin.MS93.S46KCTLin
public import CFSG.Quasithin.MS93.S46KCTGrp
public import CFSG.Quasithin.MS93.S46KCTwo

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46.I466b CFSG.Quasithin.MS93.S468
  CFSG.Quasithin.MS93.S46.KCT
open scoped commutatorElement Matrix

theorem kc4612TwoCfg_of_i469Cfg (h463 : I463) (h464 : I464) (h465 : I465) (h466b : I466b)
    (h467 : I467) {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F]
    [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (h469 : I469Cfg M T L φ) :
    KC4612TwoCfg M T L φ := by
  intro c α β γ hα hαβ hβγ hZγ ψ hψs hψU hψT hq k hk z hz
  have hchar : CharP F 2 := charP_two_of_isSL3FullVia c.via
  have hb4 := c.b4
  have hb : 2 < critDist (puAmalgam c.pu.le) := by omega
  have h20 := c.pu.hyp20
  have hβH : ¬ IsMVtx (puAmalgam c.pu.le) β := (isMVtx_iff_of_adj _ hαβ).mp hα
  have hγ : IsMVtx (puAmalgam c.pu.le) γ := by
    have h1 := isMVtx_iff_of_adj _ hαβ
    have h2 := isMVtx_iff_of_adj _ hβγ
    tauto
  have hαγ : α ≠ γ := by
    rintro rfl
    exact hZγ (zm_le_bloc c.pu hb hα)
  have h464' : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ →
      (puAmalgam c.pu.le).treeGraph.Adj δ ρ → Usup (puAmalgam c.pu.le) δ ρ ≤ ZH _ ρ :=
    fun δ ρ hδ hδρ => h464 G M T L F φ c δ ρ hδ hδρ
  obtain ⟨-, -, hodd, -⟩ := h469 c α β hα hαβ
  have hVQ : Vv (puAmalgam c.pu.le) α ≤ Qv _ α := vv_le_qv c.pu hb hα
  have hZV : ZM (puAmalgam c.pu.le) α ≤
      Subgroup.centralizer (Vv (puAmalgam c.pu.le) α : Set (puAmalgam c.pu.le).Universal) :=
    (zm_le_centralizer_qv _ h20 hα).trans (Subgroup.centralizer_le hVQ)
  have hVV : ⁅Vv (puAmalgam c.pu.le) α, Vv _ α⁆ ≤ ZM _ α := (h463 G M T L F φ c α hα).2
  have hzβ : z ∈ Vv (puAmalgam c.pu.le) β := zm_le_vv_of_adj hβγ hγ hz
  have hzα : z ∈ Vv (puAmalgam c.pu.le) α := vv_le_vv_of_adj c.pu hα hαβ hzβ
  obtain ⟨e, he⟩ := hk
  rcases eq_zero_or_eq_one hq e with rfl | rfl
  ·
    rw [rootElt_zero] at he
    have hkQ : (k : (puAmalgam c.pu.le).Universal) ∈ Qv _ α :=
      (toSL3_eq_one_iff_mem_qv c.pu c.via hα hψU k).mp he.symm
    exact (h465 G M T L F φ c α β hα hαβ).2.2 (Subgroup.commutator_mem_commutator hzα hkQ)
  have hkS : toSL3 ψ k ∈ (stabX0 : Subgroup (SL3 F)) := he ▸ rootElt_two_one_mem_stabX0 1
  have hkN := mem_normalizer_qv_of_toSL3_mem c.pu c.via hα hαβ hψU hψT hkS
  have hkV : (k : (puAmalgam c.pu.le).Universal) ∈
      Subgroup.normalizer (Vv (puAmalgam c.pu.le) β : Set (puAmalgam c.pu.le).Universal) :=
    normalizer_qv_le_normalizer_vv c.pu hβH hkN
  set u := ⁅(k : (puAmalgam c.pu.le).Universal), z⁆ with hu
  have hkz : (k : (puAmalgam c.pu.le).Universal) * z * (k : (puAmalgam c.pu.le).Universal)⁻¹ ∈
      Vv (puAmalgam c.pu.le) β := (Subgroup.mem_normalizer_iff.mp hkV z).mp hzβ
  have huβ : u ∈ Vv (puAmalgam c.pu.le) β := by
    rw [hu, commutatorElement_def]
    exact Subgroup.mul_mem _ hkz (Subgroup.inv_mem _ hzβ)
  have huS : u ∈ vStar c.pu.le L α := by
    have hzS : z ∈ vStar c.pu.le L α := by
      have := zm_smul_le_vStar c hαβ hβγ hZγ (Subgroup.one_mem _) (g := 1)
      rw [one_smul] at this
      exact this hz
    have hkzS : (k : (puAmalgam c.pu.le).Universal) * z * (k : (puAmalgam c.pu.le).Universal)⁻¹ ∈
        vStar c.pu.le L α := by
      refine zm_smul_le_vStar c hαβ hβγ hZγ k.2 ?_
      rw [zm_smul]
      exact ⟨z, hz, rfl⟩
    rw [hu, commutatorElement_def]
    exact Subgroup.mul_mem _ hkzS (Subgroup.inv_mem _ hzS)
  have huC : u ∈ Subgroup.centralizer
      (Vv (puAmalgam c.pu.le) α : Set (puAmalgam c.pu.le).Universal) := by
    rw [← Subgroup.zpowers_le, Subgroup.le_centralizer_iff, vv_eq_iSup_vv hα]
    refine iSup₂_le fun β' hβ' => ?_
    have hαβ' : (puAmalgam c.pu.le).treeGraph.Adj α β' := hβ'
    rw [← Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    have hβ'H : ¬ IsMVtx (puAmalgam c.pu.le) β' := (isMVtx_iff_of_adj _ hαβ').mp hα
    have hyα : y ∈ Vv (puAmalgam c.pu.le) α := vv_le_vv_of_adj c.pu hα hαβ' hy
    obtain ⟨g, hgα, hgβ⟩ := exists_smul_edge_of_isMVtx _ hα hαβ hα hαβ'
    have hgs : g ∈ stab (puAmalgam c.pu.le) α := hgα
    set P : SL3 F := toSL3 ψ ⟨g, hgs⟩ with hP
    set f : Fin 3 → F := ((P⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 with hfdef
    by_cases hf : f 1 = 0 ∧ f 2 = 0
    ·
      have hf0 : f 0 = 1 := by
        rcases eq_zero_or_eq_one hq (f 0) with h0 | h0
        · refine absurd ?_ (KC2.row_ne_zero (P⁻¹))
          funext j
          fin_cases j
          · exact h0
          · exact hf.1
          · exact hf.2
        · exact h0
      have hPS : P⁻¹ ∈ (stabX0 : Subgroup (SL3 F)) := by
        intro v
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        rw [← hfdef]
        simp [hf0, hf.1, hf.2]
      have hgN : g ∈ Subgroup.normalizer
          (Qv (puAmalgam c.pu.le) β : Set (puAmalgam c.pu.le).Universal) :=
        mem_normalizer_qv_of_toSL3_mem c.pu c.via hα hαβ hψU hψT (k := ⟨g, hgs⟩)
          (by simpa [hP] using Subgroup.inv_mem _ hPS)
      have hV' : Vv (puAmalgam c.pu.le) β' = Vv _ β := by
        rw [← hgβ]
        exact vv_smul_eq_of_mem_normalizer c.pu hβH hgN
      rw [hV'] at hy
      exact Subgroup.mem_centralizer_iff.mp
        (vv_le_centralizer_of_not_isMVtx h20 hb hβH huβ) y hy
    ·
      set cv : Fin 3 → F := ![0, f 2, f 1] with hcv
      set hv : Fin 3 → F := ((P⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ cv with hhv
      have hv0 : hv 0 = 0 := by
        have e : hv 0 = f 1 * f 2 + f 2 * f 1 := by
          simp only [hhv, hcv, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
          rw [← hfdef]
          simp
        rw [e, mul_comm (f 2), CharTwo.add_self_eq_zero]
      have hB : rootElt 1 0 (hv 1) * rootElt 2 0 (hv 2) ∈
          natImage ψ (Qv (puAmalgam c.pu.le) β) := by
        rw [hψT]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (rootElt_mem_rootGroup 1 0 _))
          (Subgroup.mem_sup_right (rootElt_mem_rootGroup 2 0 _))
      obtain ⟨b, hbT, hbe⟩ := mem_natImage.mp hB
      set k₁ : ↥(stab (puAmalgam c.pu.le) α) := ⟨g, hgs⟩ * b * ⟨g, hgs⟩⁻¹ with hk₁
      have hk₁T : (k₁ : (puAmalgam c.pu.le).Universal) ∈ Qv (puAmalgam c.pu.le) β' := by
        rw [← hgβ, qv_smul]
        exact ⟨b, hbT, by simp [hk₁]⟩
      have hA : ((toSL3 ψ k₁ : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
          1 + Matrix.vecMulVec cv f := by
        have e1 : toSL3 ψ k₁ = P * (rootElt 1 0 (hv 1) * rootElt 2 0 (hv 2)) * P⁻¹ := by
          rw [hk₁, map_mul, map_mul, map_inv, hbe]
        have e2 : (P : Matrix (Fin 3) (Fin 3) F) *ᵥ hv = cv := by
          rw [hhv, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
            Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
        rw [e1, coe_conj_rootElt_mul_rootElt P hv hv0, e2]
      have hk₁S : toSL3 ψ k₁ ∈ (stabX0 : Subgroup (SL3 F)) := mem_stabX0_of_coe hA
      set d : ↥(stab (puAmalgam c.pu.le) α) := k₁⁻¹ * k with hd
      have hdS : toSL3 ψ d ∈ (stabX0 : Subgroup (SL3 F)) := by
        rw [hd, map_mul, map_inv]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hk₁S) hkS
      have hd3 : (d : (puAmalgam c.pu.le).Universal) ^ 3 ∈ Qv (puAmalgam c.pu.le) β := by
        have := mem_qv_of_toSL3_mem c.pu c.via hα hαβ hψU hψT (k := d ^ 3) (by
          rw [map_pow, hd, map_mul, map_inv, ← he]
          exact cube_mem hq hA hf)
        simpa using this
      have hdz : ⁅(d : (puAmalgam c.pu.le).Universal), z⁆ ∈ ZH (puAmalgam c.pu.le) β :=
        commutator_mem_zh_of_cube c hα hαβ hψU hψT h464' hodd hdS hd3 hzβ
      have hzT : z ∈ Qv (puAmalgam c.pu.le) β' := by
        refine zm_le_qv_of_dist_le_three hb4 hγ ?_ hz
        have h1 := dist_triangle _ γ α β'
        have h2 : (puAmalgam c.pu.le).treeGraph.dist γ α = 2 := by
          rw [tdist_comm]
          exact dist_eq_two_of_adj_adj _ hαβ hβγ hαγ
        rw [h2, dist_eq_one_of_adj _ hαβ'] at h1
        exact h1
      have hE : Commute ⁅(k₁ : (puAmalgam c.pu.le).Universal), z⁆ y :=
        commute_commutator hVV hZV (vv_le_vv_of_adj c.pu hα hαβ')
          (commutator_vv_qv_le_zh c.pu h464' hβ'H) (zh_le_zm _ hαβ') (zh_le_centralizer _ β')
          ((qv_le_stab _ β').trans (stab_le_normalizer_vv c.pu β')) hk₁T
          (stab_le_normalizer_vv c.pu α k₁.2) hzα hzT hy
      have hw : (k₁ : (puAmalgam c.pu.le).Universal) * ⁅(d : (puAmalgam c.pu.le).Universal), z⁆ *
          (k₁ : (puAmalgam c.pu.le).Universal)⁻¹ ∈ ZM (puAmalgam c.pu.le) α :=
        (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_zm _ α k₁.2) _).mp
          (zh_le_zm _ hαβ hdz)
      have hwy : Commute ((k₁ : (puAmalgam c.pu.le).Universal) *
          ⁅(d : (puAmalgam c.pu.le).Universal), z⁆ * (k₁ : (puAmalgam c.pu.le).Universal)⁻¹) y :=
        (Subgroup.mem_centralizer_iff.mp (hZV hw) y hyα).symm
      have hue : u = ((k₁ : (puAmalgam c.pu.le).Universal) *
          ⁅(d : (puAmalgam c.pu.le).Universal), z⁆ * (k₁ : (puAmalgam c.pu.le).Universal)⁻¹) *
          ⁅(k₁ : (puAmalgam c.pu.le).Universal), z⁆ := by
        have hk : (k : (puAmalgam c.pu.le).Universal) =
            (k₁ : (puAmalgam c.pu.le).Universal) * (d : (puAmalgam c.pu.le).Universal) := by
          rw [hd]
          simp
        rw [hu, hk]
        simp only [commutatorElement_def]
        group
      rw [hue]
      exact ((hwy.mul_left hE).eq).symm
  have huB : u ∈ Bloc c.pu.le L α := by
    rw [h467 G M T L F φ c α hα]
    exact ⟨vv_le_vv_of_adj c.pu hα hαβ huβ, huC⟩
  have hfin := vStar_inf_bloc_le_cfg h463 h465 h466b h467 h469 c hα ⟨huS, huB⟩
  rw [← commutatorElement_inv]
  exact Subgroup.inv_mem _ hfin

theorem kc4612Two_of_i469 (h463 : I463) (h464 : I464) (h465 : I465) (h466b : I466b)
    (h467 : I467) (h469 : I469) : KC4612Two :=
  fun G _ _ M T L F _ _ φ => kc4612TwoCfg_of_i469Cfg h463 h464 h465 h466b h467 (h469 G M T L F φ)

end CFSG.Quasithin.MS93.S46
