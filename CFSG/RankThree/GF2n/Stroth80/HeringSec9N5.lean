module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Nat
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Lin
public import CFSG.RankThree.GF2n.Stroth80.HeringSec6NbarGe
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec92Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem exists_trivial_on_WV (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) (hn5 : n = 5) :
    ∃ C : Subgroup G, C ≤ LB M Q B ∧
      (∀ l, l ∈ C ↔ l ∈ LB M Q B ∧
        ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅l, w⁆ ∈ Vt M (LB M Q B) B Z t) ∧
      C.relIndex (LB M Q B) ≤ Nat.card Z := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  obtain ⟨K, fK, finK, chK, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ₀, hφπ, hφQ, -⟩ := exists_actionHom_H0 hc.hyp h
  haveI : Finite M₀.E := Module.finite_of_finite K
  set V := Vt M (LB M Q B) B Z t with hV
  set W := Wt Q V with hW
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hWQ : W ≤ Q := inf_le_left
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hVW : V ≤ W := HS6.Vt_le_Wt h34 hc hs5
  have hZW : Z ≤ W := hZV.trans hVW
  have hMQ : ∀ m ∈ M, ∀ x ∈ Q, m * x * m⁻¹ ∈ Q := fun m hm x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) x).mp hx
  let Wm : Submodule K M₀.E := imgSub M₀ W (fun c e he => smul_mem_img_Wt M₀ h.reg hVQ c he)
  let Vm : Submodule K M₀.E := imgSub M₀ V (fun c e he => hc.smul_mem_img_Vt h t c he)
  have hVmWm : Vm ≤ Wm := M₀.img_mono hVW
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hKq : Nat.card K = Nat.card Z := h.card
  have hcW : Nat.card W = Nat.card Z ^ 7 := by
    have := Sec9Hyp.card_W h34 hs
    rw [hn5] at this
    simpa using this
  have hcV : Nat.card V = Nat.card Z ^ 5 := hs.card_V
  have hW2 := M₀.card_eq hWQ hZW
  have hV2 := M₀.card_eq hVQ hZV
  have hcWm : Nat.card (M₀.img W) = Nat.card Z ^ 6 := by
    refine Nat.eq_of_mul_eq_mul_left hZpos ?_
    rw [← hW2, hcW]
    ring
  have hcVm : Nat.card (M₀.img V) = Nat.card Z ^ 4 := by
    refine Nat.eq_of_mul_eq_mul_left hZpos ?_
    rw [← hV2, hcV]
    ring
  have hcard : Nat.card Wm = Nat.card K ^ 2 * Nat.card Vm := by
    have e1 : Nat.card Wm = Nat.card (M₀.img W) :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))
    have e2 : Nat.card Vm = Nat.card (M₀.img V) :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))
    rw [e1, e2, hcWm, hcVm, hKq]
    ring
  set α : ↥(LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E) := φ₀.comp (Subgroup.inclusion hc.LB_le_H0) with hα
  have hΓ : IsPGroup 2 α.range := hc.isPGroup_range_LB φ₀ hφQ
  have hαπ : ∀ (l : ↥(LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((l : G) * x * (l : G)⁻¹) = α l (M₀.π x) := fun l x hx =>
    hφπ ⟨(l : G), hc.LB_le_H0 l.2⟩ x hx
  have hlR : ∀ l : ↥(LB M Q B), (l : G) ∈ Rt M (LB M Q B) t := fun l =>
    le_Rt (M := M) (LB M Q B) ht l.2
  have hS : ∀ (l : ↥(LB M Q B)), ∀ s ∈ Wm, α l s ∈ Wm := by
    rintro l _ ⟨w, hwW, hwQ, rfl⟩
    have hw' : (l : G) * w * (l : G)⁻¹ ∈ W := sec9_conj_mem_Wt hc ht (hlR l) hwW
    rw [← hαπ l w hwQ]
    exact M₀.pi_mem_img hw' (hWQ hw')
  have hT : ∀ (l : ↥(LB M Q B)), ∀ t' ∈ Vm, α l t' ∈ Vm := by
    rintro l _ ⟨v, hvV, hvQ, rfl⟩
    have hv' : (l : G) * v * (l : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht (hlR l)) v).mp hvV
    rw [← hαπ l v hvQ]
    exact M₀.pi_mem_img hv' (hVQ hv')
  obtain ⟨C, hC, hidx⟩ := index_le_two_dim Wm Vm hVmWm hcard α hΓ hS hT
  have hdict : ∀ (l : ↥(LB M Q B)) (w : G), w ∈ W →
      ⁅(l : G), w⁆ ∈ Q ∧ M₀.π ⁅(l : G), w⁆ = α l (M₀.π w) - M₀.π w := by
    intro l w hw
    have hwQ := hWQ hw
    have h1 : (l : G) * w * (l : G)⁻¹ ∈ Q := hMQ l (hc.LB_le_M l.2) w hwQ
    have e : ⁅(l : G), w⁆ = ((l : G) * w * (l : G)⁻¹) * w⁻¹ := by
      simp only [commutatorElement_def]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact Q.mul_mem h1 (Q.inv_mem hwQ)
    · rw [e, M₀.π_mul _ h1 _ (Q.inv_mem hwQ), Tim79.QuadModel.pi_inv M₀ hwQ, hαπ l w hwQ]
      abel
  have hiff : ∀ (l : ↥(LB M Q B)), (l ∈ C ↔ ∀ w ∈ W, ⁅(l : G), w⁆ ∈ V) := by
    intro l
    rw [hC l]
    constructor
    · intro hl w hw
      obtain ⟨hQc, hπ⟩ := hdict l w hw
      have h2 := hl (M₀.π w) (M₀.pi_mem_img hw (hWQ hw))
      rw [← hπ] at h2
      exact (M₀.mem_img_iff hZV hQc).mp h2
    · rintro hl _ ⟨w, hwW, hwQ, rfl⟩
      obtain ⟨hQc, hπ⟩ := hdict l w hwW
      rw [← hπ]
      exact M₀.pi_mem_img (hl w hwW) hQc
  refine ⟨C.map (LB M Q B).subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨c, -, rfl⟩
    exact c.2
  · intro l
    constructor
    · rintro ⟨c, hcC, rfl⟩
      exact ⟨c.2, (hiff c).mp hcC⟩
    · rintro ⟨hl, hlw⟩
      exact ⟨⟨l, hl⟩, (hiff ⟨l, hl⟩).mpr hlw, rfl⟩
  · have hsub : (C.map (LB M Q B).subtype).subgroupOf (LB M Q B) = C := by
      unfold Subgroup.subgroupOf
      exact Subgroup.comap_map_eq_self_of_injective Subtype.val_injective C
    rw [Subgroup.relIndex, hsub, hKq] at *
    exact hidx

end HS9

theorem sec95N5_of (h34 : Stroth34Statement) (h91 : Stroth91Statement)
    (hA : Sec9AExistsStatement) : Sec95N5Statement := by
  intro G _ _ M Q Z B hc n t hs hn5
  obtain ⟨C, hCL, hC, hidx⟩ := HS9.exists_trivial_on_WV h34 hs hn5
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hNW := (h91.2.1 G M Q Z B hc n t hs r hr _ _ rfl rfl).2
  have hq := HS9.relIndex_LB_CN h34 hs
  by_contra hno
  push Not at hno
  have hCN : C ≤ hc.CN t := fun x hx => by
    by_contra hxN
    obtain ⟨w, hw, hnot⟩ := hno x ((hC x).mp hx).1 hxN
    exact hnot (((hC x).mp hx).2 w hw)
  have hLN : hc.CN t ⊓ LB M Q B ≤ C := fun x hx => (hC x).mpr ⟨hx.2, hNW x hx.1⟩
  have hCeq : C = hc.CN t ⊓ LB M Q B := le_antisymm (le_inf hCN hCL) hLN
  have h1 : C.relIndex (LB M Q B) = Nat.card Z ^ 2 := by
    rw [hCeq, Subgroup.inf_relIndex_right, hq]
  have hq4 := hc.hyp.q4
  rw [h1] at hidx
  nlinarith [hidx]

end CFSG.RankThree.GF2n.Stroth80
