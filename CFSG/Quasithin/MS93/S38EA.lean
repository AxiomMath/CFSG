module

public import CFSG.Quasithin.MS93.S38EAPU
public import CFSG.Quasithin.MS93.S38EAT
public import CFSG.Quasithin.MS93.S38EStmtA
public import CFSG.Quasithin.MS93.S38EAFin

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93 CFSG.Open
  CFSG.Quasithin.MS93.S38EA
open scoped commutatorElement

theorem d6Case_holds : D6Case := by
  intro G _ _ M T L h _ _ hcase _ hnSp4 hD hCU _ hb hstar h8 α' hc hgeo lam hlam1 hlamc hK
  have hS := endSetup_base h hD hCU hb hstar h8 hc hgeo
  have he4 := e_eq_four h hD hcase hnSp4 hc hgeo
  have hirr := hS.irrSec lam hlam1 (Or.inr he4) hlamc
  have h4 := index_fixV_eS_eq_four hS lam hlam1 hirr he4
  have hinj := wRho_eq_one_of h hS lam hlam1 hb h8 hc hirr he4
  have hA0 := eW_le_kW h hS lam hlam1 hb h8 hc hirr he4 hD hcase hnSp4 hgeo
  have hm0 := m0_eq_bot hS lam hlam1 hinj hirr he4 hA0 hK
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hd : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb
  have hV : ¬ Vv (puAmalgam h.le) (baseA _) ≤ Qv _ (geo _ (baseA _) α' 2) := by
    have h1 := h8 _ α' hc
    have e : geo _ α' (baseA _) 2 = geo _ (baseA _) α' 2 := by
      have := geo_symm _ (u := baseA (puAmalgam h.le)) (w := α') (i := 2) (by omega)
      rwa [hd] at this
    rwa [e] at h1
  have hμ : IsMVtx _ (geo _ (baseA _) α' 2) := isMVtx_geo_two _ h.hyp20 (by omega) hc
  have hαμ : (puAmalgam h.le).treeGraph.dist (baseA _) (geo _ (baseA _) α' 2) = 2 :=
    dist_geo _ (by omega)
  obtain ⟨ρ, hρ, hρμ⟩ : ∃ ρ, (puAmalgam h.le).treeGraph.dist (baseA _) ρ ≤ 2 ∧
      ¬ Zv _ ρ ≤ Qv _ (geo _ (baseA _) α' 2) := by
    by_contra hcon
    push Not at hcon
    exact hV (iSup₂_le fun ρ hρ => hcon ρ hρ)
  obtain ⟨γ, hγ, hdγ, hle⟩ := exists_zv_le_zm _ hc.1 hρ
  have hγμ : ¬ ZM _ γ ≤ Qv _ (geo _ (baseA _) α' 2) := fun h' => hρμ (hle.trans h')
  have hdγμ : (puAmalgam h.le).treeGraph.dist γ (geo _ (baseA _) α' 2) = 4 := by
    have h1 : 4 ≤ (puAmalgam h.le).treeGraph.dist γ (geo _ (baseA _) α' 2) := by
      by_contra hlt
      exact hγμ (zm_le_qv_of_dist_lt _ hγ (by omega))
    have h2 := dist_triangle _ γ (baseA _) (geo _ (baseA _) α' 2)
    rw [tdist_comm _ γ (baseA _)] at h2
    omega
  have hcγ : IsCritical _ γ (geo _ (baseA _) α' 2) := ⟨hγ, by rw [hdγμ, hb], hγμ⟩
  have hge := four_le_card_commutator_zm h hcase hnSp4 hb hcγ
  have hBμ : (puAmalgam h.le).treeGraph.dist (baseB _) (geo _ (baseA _) α' 2) ≤ 1 := by
    have := dist_geo_geo (puAmalgam h.le) (u := baseA _) (w := α') (i := 1) (j := 2)
      (by norm_num) (by omega)
    rw [hgeo] at this
    omega
  have hZ : ZM _ (geo _ (baseA _) α' 2) ≤ Vi (puAmalgam h.le) (baseB _) 1 :=
    le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam h.le) |
      (puAmalgam h.le).treeGraph.dist (baseB _) ρ ≤ 1}) => Zv _ ρ) _ hBμ
      (zv_of_isMVtx _ hμ).ge
  have hle2 := card_commutator_le_two hS lam hlam1 (vb_le_vv h) (tb_le_normalizer_vb h)
    (vv_le_of_vb_le h) hK ⟨by omega, by omega⟩ h4 hm0
    (commutator_vi_one_eq_bot _ h.hyp20 hb2 (baseB _)) hZ
  have hsub : ⁅ZM _ γ, ZM _ (geo _ (baseA _) α' 2)⁆ ≤
      ⁅Vv (puAmalgam h.le) (baseA _), ZM _ (geo _ (baseA _) α' 2)⁆ :=
    Subgroup.commutator_mono (zm_le_vv _ hγ hdγ) le_rfl
  have : Finite ↥(stab (puAmalgam h.le) (baseA _)) := hS.finite
  have : Finite ↥⁅Vv (puAmalgam h.le) (baseA _), ZM _ (geo _ (baseA _) α' 2)⁆ :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      ((Subgroup.commutator_mono le_rfl (zm_le_vv _ hμ hαμ.le)).trans
        ((EndSetup.comm_le_self _).trans hS.v_le)))
  have := Subgroup.card_le_of_le hsub
  omega

end CFSG.Quasithin.MS93.S38E
