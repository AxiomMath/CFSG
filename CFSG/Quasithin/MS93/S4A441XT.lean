module

public import CFSG.Quasithin.MS93.S4A441XE
import CFSG.Quasithin.MS93.S4A44E1

public section

namespace CFSG.Quasithin.MS93.S4A.X441

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Geo

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem isCritical_smul_of_mem_stab (hb : 3 ≤ critDist X) {α α' : Vtx X}
    (hc : IsCritical X α α') {k : X.Universal} (hk : k ∈ stab X (geo X α α' 2))
    (hZ : ¬ ZM X (k • α) ≤ Qv X α') :
    IsCritical X (k • α) α' ∧ geo X (k • α) α' 1 = k • geo X α α' 1 ∧
      geo X (k • α) α' 2 = geo X α α' 2 ∧ geo X (k • α) α' 3 = geo X α α' 3 := by
  have hd : X.treeGraph.dist α α' = critDist X := hc.2.1
  have hαγ : X.treeGraph.dist α (geo X α α' 2) = 2 := dist_geo X (by omega)
  have hγα' : X.treeGraph.dist (geo X α α' 2) α' = critDist X - 2 := by
    rw [dist_geo_right X (by omega), hd]
  have hkγ : k • geo X α α' 2 = geo X α α' 2 := (mem_stab X).mp hk
  have hkαγ : X.treeGraph.dist (k • α) (geo X α α' 2) = 2 := by
    have := dist_smul X k α (geo X α α' 2)
    rwa [hkγ, hαγ] at this
  have hkα : IsMVtx X (k • α) := (isMVtx_smul X k α).mpr hc.1
  have hdk : X.treeGraph.dist (k • α) α' = critDist X := by
    have t := dist_triangle X (k • α) (geo X α α' 2) α'
    by_contra hne
    exact hZ (zm_le_qv_of_dist_lt X hkα (by omega))
  have hadd : X.treeGraph.dist (k • α) α' =
      X.treeGraph.dist (k • α) (geo X α α' 2) + X.treeGraph.dist (geo X α α' 2) α' := by
    omega
  have hadd₀ : X.treeGraph.dist α α' =
      X.treeGraph.dist α (geo X α α' 2) + X.treeGraph.dist (geo X α α' 2) α' := by
    omega
  refine ⟨⟨hkα, hdk, hZ⟩, ?_, ?_, ?_⟩
  · rw [geo_eq_of_dist_eq_add X hadd (k := 1) (by omega)]
    conv_lhs => rw [← hkγ]
    rw [geo_smul X k α (geo X α α' 2) 1, geo_eq_of_dist_eq_add X hadd₀ (k := 1) (by omega)]
  · have := geo_of_dist_eq_add X hadd (k := 0) (by omega)
    rwa [hkαγ, add_zero, geo_zero] at this
  · have h1 := geo_of_dist_eq_add X hadd (k := 1) (by omega)
    have h2 := geo_of_dist_eq_add X hadd₀ (k := 1) (by omega)
    rw [hkαγ] at h1
    rw [hαγ] at h2
    exact h1.trans h2.symm

end Geo

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)

theorem exists_isSecD_smul {F : Type} [Field F] {γ : Vtx 𝔛}
    {ψ : ↥(stab 𝔛 γ) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab 𝔛 γ) (Uloc h.le L γ) ⊥ ψ false 1) {dual : Bool}
    {W C : Subgroup 𝔘} (hs : L441.IsSecD h.le L γ ψ dual W C) (g : 𝔘) :
    ∃ ψ' : ↥(stab 𝔛 (g • γ)) →* ↥(StatedSL 3 F), Function.Surjective ψ' ∧
      IsSumOfNaturalModulesVia (stab 𝔛 (g • γ)) (Uloc h.le L (g • γ)) ⊥ ψ' false 1 ∧
      L441.IsSecD h.le L (g • γ) ψ' dual (W.map (MulAut.conj g).toMonoidHom)
        (C.map (MulAut.conj g).toMonoidHom) := by
  set e : 𝔘 →* 𝔘 := (MulAut.conj g).toMonoidHom
  have hei : Function.Injective e := (MulAut.conj g).injective
  have hstab : stab 𝔛 (g • γ) = (stab 𝔛 γ).map e := stab_smul _ g γ
  have hUeq : Uloc h.le L (g • γ) = (Uloc h.le L γ).map e := uloc_smul h g γ
  have hDeq : Dloc h.le L (g • γ) = (Dloc h.le L γ).map e := dloc_smul h g γ
  have hQeq : Qv 𝔛 (g • γ) = (Qv 𝔛 γ).map e := qv_smul _ g γ
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := hs
  have hU' := isSumOfNaturalModulesVia_map hψ e hei
  rw [Subgroup.map_bot] at hU'
  have hW' := isSumOfNaturalModulesVia_map hs4 e hei
  set eK : ↥(stab 𝔛 (g • γ)) ≃* ↥((stab 𝔛 γ).map e) := MulEquiv.subgroupCongr hstab
  have hnU : stab 𝔛 (g • γ) ≤ Subgroup.normalizer (Uloc h.le L (g • γ) : Set 𝔘) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) _
  have hnW : stab 𝔛 (g • γ) ≤ Subgroup.normalizer (W.map e : Set 𝔘) := by
    rw [hstab]
    exact hW'.1
  refine ⟨(ψ.comp ((stab 𝔛 γ).equivMapOfInjective e hei).symm.toMonoidHom).comp
    eK.toMonoidHom, ?_, ?_, ?_⟩
  · rw [MonoidHom.coe_comp, MonoidHom.coe_comp]
    exact (hψs.comp (MulEquiv.surjective _)).comp (MulEquiv.surjective eK)
  · exact isSumOfNaturalModulesVia_of_equiv hU' eK (MulEquiv.subgroupCongr hUeq) hnU bot_le
      (fun v => by simp) (fun a u v huv => huv)
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hUeq]
      exact Subgroup.map_mono hs1
    · rw [hstab, hUeq, hDeq, ← Subgroup.map_commutator, ← Subgroup.map_sup]
      exact Subgroup.map_mono hs2
    · rw [hQeq, hUeq, hDeq, ← Subgroup.map_commutator, ← Subgroup.map_sup]
      exact Subgroup.map_mono hs3
    · exact isSumOfNaturalModulesVia_of_equiv hW' eK (MulEquiv.refl _) hnW hW'.2.1
        (fun v => Iff.rfl) (fun a u v huv => huv)
    · rintro _ ⟨w, hw, rfl⟩ x hx hxC
      rw [hstab] at hx
      obtain ⟨x₀, hx₀, rfl⟩ := hx
      have e1 : (e w)⁻¹ * (e x₀ * e w * (e x₀)⁻¹) = e (w⁻¹ * (x₀ * w * x₀⁻¹)) := by
        simp only [map_mul, map_inv]
      rw [e1] at hxC ⊢
      rw [Subgroup.mem_map_iff_mem hei] at hxC
      rw [hUeq, hDeq, ← Subgroup.map_sup, Subgroup.mem_map_iff_mem hei]
      exact hs5 w hw x₀ hx₀ hxC

end Vertex

end CFSG.Quasithin.MS93.S4A.X441
