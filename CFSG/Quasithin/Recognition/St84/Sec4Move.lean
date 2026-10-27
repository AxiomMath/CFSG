module

public import CFSG.Quasithin.Recognition.St84.Sec4Local
public import CFSG.Quasithin.Recognition.St84.TransportMap
public import CFSG.Quasithin.Recognition.F112RShapes
public import CFSG.Quasithin.Background.SpecialPGroupMulEquiv
public import CFSG.Quasithin.Background.F9Sixteen
public import CFSG.Quasithin.Recognition.St84.Sec4TreeTransfer
public import CFSG.Quasithin.Recognition.St84.Sec4TreeData

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

private theorem natSec_conjSub_iff {L K E : Subgroup G} {g : G} :
    NatSec (conjSub g L) (conjSub g K) (conjSub g E) ↔ NatSec L K E := by
  simpa only [conjSub] using
    (NatSec.map_iff (MulAut.conj g).toMonoidHom (MulEquiv.injective _))

private theorem isSpecialPGroup_conjSub {P : Subgroup G} {p : ℕ} {g : G}
    (h : IsSpecialPGroup p ↥P) : IsSpecialPGroup p ↥(conjSub g P) :=
  IsSpecialPGroup.of_mulEquiv
    (Subgroup.equivMapOfInjective P (MulAut.conj g).toMonoidHom (MulEquiv.injective _)) h

private theorem isSpecialPow_conjSub {P : Subgroup G} {p q w : ℕ} {g : G}
    (h : IsSpecialPow p q w ↥P) : IsSpecialPow p q w ↥(conjSub g P) :=
  IsSpecialPow.of_mulEquiv
    (Subgroup.equivMapOfInjective P (MulAut.conj g).toMonoidHom (MulEquiv.injective _)) h

theorem TreeSp44Data.smul {X Y : Setup Γ G} (g : G) (h0 : g • X.vert 0 = Y.vert 0)
    (h1 : g • X.vert 1 = Y.vert 1) (d : X.TreeSp44Data) : Y.TreeSp44Data := by
  have hL0 : Y.L 0 = conjSub g (X.L 0) := L_smul X Y h0
  have hL1 : Y.L 1 = conjSub g (X.L 1) := L_smul X Y h1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [S_smul X Y h0 h1, card_conjSub]
    exact d.card_S
  · rw [Gi_smul X Y h0, Gi_smul X Y h1, ← conjSub_inf, card_conjSub]
    exact d.card_edge
  · rw [hL0, pCoreOf_conjSub]
    exact F7.isElemAbelian_conjSub d.elem_left
  · rw [hL0, pCoreOf_conjSub, card_conjSub]
    exact d.card_left
  · rw [hL0, centerOf_conjSub, card_conjSub]
    exact d.center_left
  · rw [hL0, centerOf_conjSub, pCoreOf_conjSub]
    exact (natSec_conjSub_iff (g := g)).mpr d.nat_left
  · rw [hL0, pCoreOf_conjSub, conjSub_commutator]
    exact congrArg (conjSub g) d.indec_left
  · rw [hL1, pCoreOf_conjSub]
    exact F7.isElemAbelian_conjSub d.elem_right
  · rw [hL1, pCoreOf_conjSub, card_conjSub]
    exact d.card_right
  · rw [hL1, centerOf_conjSub, card_conjSub]
    exact d.center_right
  · rw [hL1, centerOf_conjSub, pCoreOf_conjSub]
    exact (natSec_conjSub_iff (g := g)).mpr d.nat_right
  · rw [hL1, pCoreOf_conjSub, conjSub_commutator]
    exact congrArg (conjSub g) d.indec_right
  · rw [hL0, hL1, pCoreOf_conjSub, pCoreOf_conjSub, ← conjSub_inf, card_conjSub]
    exact d.card_inf

theorem TreeSp44Data.congr {X Y : Setup Γ G} (h0 : X.vert 0 = Y.vert 0)
    (h1 : X.vert 1 = Y.vert 1) (d : X.TreeSp44Data) : Y.TreeSp44Data :=
  TreeSp44Data.smul (X := X) (Y := Y) (g := 1) (by simpa using h0) (by simpa using h1) d

theorem TreeSp44Data.swap {X : Setup Γ G} (d : X.TreeSp44Data) : X.swap.TreeSp44Data := by
  have hG0 : X.swap.Gi 0 = X.Gi 1 := by rw [swap_Gi]; norm_num
  have hG1 : X.swap.Gi 1 = X.Gi 0 := by rw [swap_Gi]; norm_num
  have hL0 : X.swap.L 0 = X.L 1 := by rw [swap_L]; norm_num
  have hL1 : X.swap.L 1 = X.L 0 := by rw [swap_L]; norm_num
  have hS : X.swap.S = X.S := swap_S X
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hS]; exact d.card_S
  · rw [hG0, hG1, inf_comm]; exact d.card_edge
  · rw [hL0]; exact d.elem_right
  · rw [hL0]; exact d.card_right
  · rw [hL0]; exact d.center_right
  · rw [hL0]; exact d.nat_right
  · rw [hL0]; exact d.indec_right
  · rw [hL1]; exact d.elem_left
  · rw [hL1]; exact d.card_left
  · rw [hL1]; exact d.center_left
  · rw [hL1]; exact d.nat_left
  · rw [hL1]; exact d.indec_left
  · rw [hL0, hL1, inf_comm]; exact d.card_inf

theorem TreeG24Data.smul {X Y : Setup Γ G} (g : G) (h0 : g • X.vert 0 = Y.vert 0)
    (h1 : g • X.vert 1 = Y.vert 1) (d : X.TreeG24Data) : Y.TreeG24Data := by
  have hL0 : Y.L 0 = conjSub g (X.L 0) := L_smul X Y h0
  have hL1 : Y.L 1 = conjSub g (X.L 1) := L_smul X Y h1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [S_smul X Y h0 h1, card_conjSub]
    exact d.card_S
  · rw [Gi_smul X Y h0, Gi_smul X Y h1, ← conjSub_inf, card_conjSub]
    exact d.card_edge
  · rw [hL0, pCoreOf_conjSub]
    exact isSpecialPow_conjSub d.special_left
  · simp only [hL0, pCoreOf_conjSub, centerOf_conjSub]
    exact congrArg (conjSub g) d.center_left
  · rw [hL0, pCoreOf_conjSub, conjSub_commutator]
    exact congrArg (conjSub g) d.indec_left
  · rw [hL1, pCoreOf_conjSub, card_conjSub]
    exact d.card_right
  · rw [hL1, pCoreOf_conjSub]
    exact isSpecialPGroup_conjSub d.special_right
  · rw [hL1, pCoreOf_conjSub, centerOf_conjSub, card_conjSub]
    exact d.card_center_right
  · rw [hL1, pCoreOf_conjSub, centerOf_conjSub, ← conjSub_bot]
    exact (natSec_conjSub_iff (g := g)).mpr d.natZ_right
  · obtain ⟨W, hZW, hWQ, hcard, hcomm, hnat⟩ := d.mid_right
    refine ⟨conjSub g W, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hL1, pCoreOf_conjSub, centerOf_conjSub]
      exact conjSub_mono g hZW
    · rw [hL1, pCoreOf_conjSub]
      exact conjSub_mono g hWQ
    · rw [card_conjSub]
      exact hcard
    · rw [hL1, conjSub_commutator, pCoreOf_conjSub, centerOf_conjSub]
      exact conjSub_mono g hcomm
    · rw [hL1, pCoreOf_conjSub]
      exact (natSec_conjSub_iff (g := g)).mpr hnat
  · rw [hL0, hL1, pCoreOf_conjSub, pCoreOf_conjSub, ← conjSub_inf, card_conjSub]
    exact d.card_inf

theorem TreeG24Extra.smul {X Y : Setup Γ G} (g : G) (h0 : g • X.vert 0 = Y.vert 0)
    (h1 : g • X.vert 1 = Y.vert 1) (d : X.TreeG24Extra) : Y.TreeG24Extra := by
  have hGi0 : Y.Gi 0 = conjSub g (X.Gi 0) := Gi_smul X Y h0
  have hL0 : Y.L 0 = conjSub g (X.L 0) := L_smul X Y h0
  have hL1 : Y.L 1 = conjSub g (X.L 1) := L_smul X Y h1
  have hQ0 : pCoreOf 2 (Y.L 0) = conjSub g (pCoreOf 2 (X.L 0)) := by
    rw [hL0, pCoreOf_conjSub]
  have hC0 : centerOf (pCoreOf 2 (Y.L 0)) =
      conjSub g (centerOf (pCoreOf 2 (X.L 0))) := by
    rw [hQ0, centerOf_conjSub]
  refine ⟨?_, ?_, ?_⟩
  · intro Z hZ hZle hN
    set Z' : Subgroup G := conjSub g⁻¹ Z with hZ'def
    have hZ0 : centerOf (pCoreOf 2 (X.L 0)) ≤ Z' := by
      rw [hZ'def]
      have h := hZ
      rw [hC0] at h
      exact (conjSub_le_iff g).mp h
    have hZle0 : Z' ≤ pCoreOf 2 (X.L 0) := by
      rw [hZ'def]
      have h := hZle
      rw [hQ0] at h
      exact (le_conjSub_iff g).mp h
    have hN0 : X.Gi 0 ≤ Subgroup.normalizer (Z' : Set G) := by
      have h := hN
      rw [hGi0] at h
      have h2 := conjSub_mono (g := g⁻¹) h
      rw [conjSub_conjSub_inv, ← conjSub_normalizer, ← hZ'def] at h2
      exact h2
    rcases d.irr_left Z' hZ0 hZle0 hN0 with h | h
    · left
      calc Z = conjSub g Z' := by rw [hZ'def, conjSub_inv_conjSub]
        _ = conjSub g (centerOf (pCoreOf 2 (X.L 0))) := by rw [h]
        _ = centerOf (pCoreOf 2 (Y.L 0)) := hC0.symm
    · right
      calc Z = conjSub g Z' := by rw [hZ'def, conjSub_inv_conjSub]
        _ = conjSub g (pCoreOf 2 (X.L 0)) := by rw [h]
        _ = pCoreOf 2 (Y.L 0) := hQ0.symm
  · obtain ⟨E, hZE, hEQ, hrel, hnorm, hcomm, hnat⟩ := d.orth_left
    refine ⟨conjSub g E, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hC0]
      exact conjSub_mono g hZE
    · rw [hQ0]
      exact conjSub_mono g hEQ
    · rw [hC0, CFSG.Quasithin.F9.relIndex_conjSub]
      exact hrel
    · rw [hL0]
      exact conjSub_le_normalizer hnorm
    · obtain ⟨l, hl, e, he, hle⟩ := hcomm
      refine ⟨g * l * g⁻¹, ?_, g * e * g⁻¹, ?_, ?_⟩
      · rw [hL0]
        exact mul_mem_conjSub hl
      · exact mul_mem_conjSub he
      · intro hmem
        rw [hC0] at hmem
        refine hle ?_
        have hmem' := mem_conjSub.mp hmem
        have heq : g⁻¹ * ⁅g * l * g⁻¹, g * e * g⁻¹⁆ * g = ⁅l, e⁆ := by
          simp only [commutatorElement_def]
          group
        rwa [heq] at hmem'
    · intro hmem
      rw [hC0, hL0] at hmem
      exact hnat ((natSec_conjSub_iff (g := g)).mp hmem)
  · rw [hL1, pCoreOf_conjSub, conjSub_commutator]
    exact congrArg (conjSub g) d.comm_right

theorem relCent_S_smul {X Y : Setup Γ G} (g : G) (h0 : g • X.vert 0 = Y.vert 0)
    (h1 : g • X.vert 1 = Y.vert 1)
    (h : relCent (pCoreOf 2 (X.L 0)) (centerOf (pCoreOf 2 (X.L 0))) X.S =
      centerOf (pCoreOf 2 (X.L 1))) :
    relCent (pCoreOf 2 (Y.L 0)) (centerOf (pCoreOf 2 (Y.L 0))) Y.S =
      centerOf (pCoreOf 2 (Y.L 1)) := by
  rw [L_smul X Y h0, L_smul X Y h1, S_smul X Y h0 h1, pCoreOf_conjSub, pCoreOf_conjSub,
    centerOf_conjSub, centerOf_conjSub,
    ← conjSub_relCent g (le_normalizer_centerOf_self _), h]

theorem TreeG24Transfer.smul {X Y : Setup Γ G} (g : G) (h0 : g • X.vert 0 = Y.vert 0)
    (h1 : g • X.vert 1 = Y.vert 1) (d : X.TreeG24Transfer) : Y.TreeG24Transfer := by
  refine ⟨relCent_S_smul g h0 h1 d.relCent_S, ?_⟩
  intro k hk hk3 x hx
  have hL0 : Y.L 0 = conjSub g (X.L 0) := L_smul X Y h0
  have hL1 : Y.L 1 = conjSub g (X.L 1) := L_smul X Y h1
  rw [hL1] at hk
  rw [hL1, pCoreOf_conjSub] at hx
  rw [hL0, pCoreOf_conjSub]
  obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
  have hk' : g⁻¹ * k * g ∈ X.L 1 := mem_conjSub.mp hk
  have hx' : g⁻¹ * x * g ∈ pCoreOf 2 (X.L 1) := mem_conjSub.mp hxQ
  have hk3' : orderOf (g⁻¹ * k * g) = 3 := by
    rw [← hk3]
    exact (SemiconjBy.orderOf_eq g⁻¹ (by simp only [SemiconjBy]; group)).symm
  have hxC' : g⁻¹ * x * g ∈ Subgroup.centralizer ({g⁻¹ * k * g} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro h rfl
    have hxk : k * x = x * k := Subgroup.mem_centralizer_iff.mp hxC k (Set.mem_singleton k)
    calc g⁻¹ * k * g * (g⁻¹ * x * g) = g⁻¹ * (k * x) * g := by group
      _ = g⁻¹ * (x * k) * g := by rw [hxk]
      _ = g⁻¹ * x * g * (g⁻¹ * k * g) := by group
  exact mem_conjSub.mpr (d.cent_right _ hk' hk3' (Subgroup.mem_inf.mpr ⟨hx', hxC'⟩))

end Setup

end CFSG.Quasithin.St84
