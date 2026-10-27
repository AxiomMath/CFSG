module

public import CFSG.Quasithin.MS93.Sec2Basic

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ SimpleGraph

open scoped commutatorElement

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem zm_le_qv_geo_one (h : Hyp20 X) (hb : 0 < critDist X) {α α' : Vtx X}
    (hc : IsCritical X α α') : ZM X α' ≤ Qv X (geo X α α' 1) := by
  have hd : X.treeGraph.dist α α' = critDist X := hc.2.1
  refine zm_le_qv_of_dist_lt X (hc.isMVtx_right X h) ?_
  rw [dist_comm, dist_geo_right X (by omega)]
  omega

theorem adj_geo_one_of_isCritical (hb : 0 < critDist X) {α α' : Vtx X}
    (hc : IsCritical X α α') : X.treeGraph.Adj α (geo X α α' 1) :=
  adj_geo_one X (hc.2.1 ▸ hb)

theorem zm_le_stab_of_isCritical (h : Hyp20 X) (hb : 0 < critDist X) {α α' : Vtx X}
    (hc : IsCritical X α α') : ZM X α' ≤ stab X α :=
  (zm_le_qv_geo_one X h hb hc).trans
    (qv_le_stab_of_isMVtx X h hc.1 (adj_geo_one_of_isCritical X hb hc))

private theorem commutator_sup_le {G : Type*} [Group G] {A B Q : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hBQ : B ≤ Subgroup.centralizer (Q : Set G)) :
    ⁅A ⊔ B, Q⁆ ≤ ⁅A, Q⁆ := by
  rw [Subgroup.commutator_le]
  intro y hy q hq
  have hy' : y ∈ ((A ⊔ B : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hAB] at hy'
  obtain ⟨a, ha, b, hb, hab⟩ := hy'
  have hab' : a * b = y := hab
  rw [← hab', commutatorElement_mul_left_eq_conj_mul]
  have hbq : ⁅b, q⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (hBQ hb) q hq).symm
  rw [hbq, mul_one, mul_inv_cancel, one_mul]
  exact Subgroup.commutator_mem_commutator ha hq

theorem ms21_vi (h : Hyp20 X) (hb : 0 < critDist X) {α α' δ : Vtx X}
    (hc : IsCritical X α α') (hδ : X.treeGraph.dist α δ = 2) (hZδ : ZM X δ ≤ Qv X α)
    (hcomm : ⁅ZM X δ, ZM X α'⁆ ≤ ⁅⁅ZM X δ, Qv X α⁆, ZM X α'⁆ ⊔ ZM X α) :
    ZM X α' ≤ Subgroup.normalizer ((ZM X δ ⊔ ZM X α : Subgroup X.Universal) : Set X.Universal) ∧
      ZM X α' ≤ Subgroup.normalizer
        ((⁅ZM X δ, Qv X α⁆ ⊔ ZM X α : Subgroup X.Universal) : Set X.Universal) := by
  set β := geo X α α' 1
  have hα : IsMVtx X α := hc.1
  have hαβ : X.treeGraph.Adj α β := adj_geo_one_of_isCritical X hb hc
  have hβ : ¬ IsMVtx X β := (isMVtx_iff_of_adj X hαβ).mp hα
  have hZ'β : ZM X α' ≤ Qv X β := zm_le_qv_geo_one X h hb hc
  have hZ'α : ZM X α' ≤ stab X α := zm_le_stab_of_isCritical X h hb hc
  have hQβ : Qv X α ≤ Qv X β := qv_le_qv X h hα hαβ
  have hZα : ZM X α ≤ Qv X α := zm_le_qv_self X hα hb
  have hQδ : Qv X α ≤ Subgroup.normalizer (ZM X δ : Set X.Universal) :=
    (qv_le_stab_of_dist_le_two X h hα hδ.le).trans (stab_le_normalizer_zm X δ)
  have hQα : Qv X α ≤ Subgroup.normalizer (ZM X α : Set X.Universal) :=
    (qv_le_stab X α).trans (stab_le_normalizer_zm X α)
  have hZ'Q : ZM X α' ≤ Subgroup.normalizer (Qv X α : Set X.Universal) :=
    hZ'α.trans (stab_le_normalizer_qv X α)
  have hZ'Zα : ZM X α' ≤ Subgroup.normalizer (ZM X α : Set X.Universal) :=
    hZ'α.trans (stab_le_normalizer_zm X α)
  set W := ZM X δ ⊔ ZM X α with hW
  set P := Qv X β
  set Y := ⨆ z ∈ ZM X α', W.map (MulAut.conj z).toMonoidHom with hY
  have hWP : W ≤ P := sup_le (hZδ.trans hQβ) (hZα.trans hQβ)
  have hQW : Qv X α ≤ Subgroup.normalizer (W : Set X.Universal) := le_normalizer_sup hQδ hQα
  have hWY : W ≤ Y := le_iSup₂_of_le (1 : X.Universal) (ZM X α').one_mem (map_conj_one W).ge
  have hPP : P ≤ Subgroup.normalizer (P : Set X.Universal) := Subgroup.le_normalizer
  have hYP : Y ≤ P := iSup₂_le fun z hz => by
    calc W.map (MulAut.conj z).toMonoidHom ≤ P.map (MulAut.conj z).toMonoidHom :=
          Subgroup.map_mono hWP
      _ = P := map_conj_eq_of_mem_normalizer (hPP (hZ'β hz))
  have hconjW : ∀ z ∈ ZM X α', W.map (MulAut.conj z).toMonoidHom =
      (ZM X δ).map (MulAut.conj z).toMonoidHom ⊔ ZM X α := fun z hz => by
    rw [hW, Subgroup.map_sup, map_conj_eq_of_mem_normalizer (hZ'Zα hz)]
  have hcY : ⁅⁅ZM X δ, Qv X α⁆, ZM X α'⁆ ≤ ⁅Y, Qv X α⁆ := by
    rw [Subgroup.commutator_le]
    intro w hw z hz
    have h1 : ⁅ZM X δ, Qv X α⁆ ≤ ⁅Y, Qv X α⁆ :=
      Subgroup.commutator_mono_left (le_sup_left.trans hWY)
    have h2 : z * w⁻¹ * z⁻¹ ∈ ⁅Y, Qv X α⁆ := by
      have hm : z * w⁻¹ * z⁻¹ ∈ (⁅ZM X δ, Qv X α⁆).map (MulAut.conj z).toMonoidHom :=
        conj_mem_map_conj (Subgroup.inv_mem _ hw)
      rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hZ'Q hz)] at hm
      refine Subgroup.commutator_mono_left ?_ hm
      exact (le_sup_left.trans (hconjW z hz).ge).trans (le_iSup₂_of_le z hz le_rfl)
    have : ⁅w, z⁆ = w * (z * w⁻¹ * z⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact Subgroup.mul_mem _ (h1 hw) h2
  have hYle : Y ≤ W ⊔ ⁅Y, Qv X α⁆ := by
    refine iSup₂_le fun z hz => ?_
    rw [hconjW z hz]
    refine sup_le ?_ (le_sup_right.trans le_sup_left)
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (MulAut.conj z).toMonoidHom x = ⁅z, x⁆ * x := by
      simp [commutatorElement_def]
    rw [hx']
    refine Subgroup.mul_mem _ ?_ (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx))
    have hzx : ⁅z, x⁆ ∈ ⁅ZM X δ, ZM X α'⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hz hx
    have := hcomm hzx
    exact (sup_le (hcY.trans le_sup_right) (le_sup_right.trans le_sup_left)) this
  have hYW : Y = W :=
    eq_of_le_sup_commutator (isNilpotent_qv X h hβ) hWP hYP (hQβ) hQW hWY hYle
  have hN : ZM X α' ≤ Subgroup.normalizer (W : Set X.Universal) :=
    le_normalizer_of_map_conj_le fun z hz =>
      calc W.map (MulAut.conj z).toMonoidHom ≤ Y := le_iSup₂_of_le z hz le_rfl
        _ = W := hYW
  refine ⟨hN, le_normalizer_of_map_conj_le fun z hz => ?_⟩
  have hδz : (ZM X δ).map (MulAut.conj z).toMonoidHom ≤ W := by
    calc _ ≤ W.map (MulAut.conj z).toMonoidHom := Subgroup.map_mono le_sup_left
      _ = W := map_conj_eq_of_mem_normalizer (hN hz)
  rw [Subgroup.map_sup, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hZ'Q hz),
    map_conj_eq_of_mem_normalizer (hZ'Zα hz)]
  refine sup_le_sup_right ?_ _
  calc ⁅(ZM X δ).map (MulAut.conj z).toMonoidHom, Qv X α⁆ ≤ ⁅W, Qv X α⁆ :=
        Subgroup.commutator_mono_left hδz
    _ ≤ ⁅ZM X δ, Qv X α⁆ := commutator_sup_le (hZδ.trans (qv_le_stab X α) |>.trans
        (stab_le_normalizer_zm X α)) (zm_le_centralizer_qv X h hα)

theorem ms21_vii {α β α' : Vtx X}
    (hgen : stab X α = (⨆ g ∈ stab X α, (ZM X α').map (MulAut.conj g).toMonoidHom) ⊔ Qv X β)
    {X₁ X₂ : Subgroup X.Universal}
    (h₁ : Qv X β ≤ Subgroup.normalizer (X₁ : Set X.Universal))
    (h₁' : ¬ stab X α ≤ Subgroup.normalizer (X₁ : Set X.Universal))
    (h₂ : Qv X β ≤ Subgroup.normalizer (X₂ : Set X.Universal))
    (h₂' : ¬ stab X α ≤ Subgroup.normalizer (X₂ : Set X.Universal)) :
    ∃ g ∈ stab X α,
      ¬ ZM X α' ≤ Subgroup.normalizer
        ((X₁.map (MulAut.conj g).toMonoidHom : Subgroup X.Universal) : Set X.Universal) ∧
      ¬ ZM X α' ≤ Subgroup.normalizer
        ((X₂.map (MulAut.conj g).toMonoidHom : Subgroup X.Universal) : Set X.Universal) :=
  exists_conj_not_le_normalizer hgen h₁ h₁' h₂ h₂'

end CFSG.Quasithin.MS93
