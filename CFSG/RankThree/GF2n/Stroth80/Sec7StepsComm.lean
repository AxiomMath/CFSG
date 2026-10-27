module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsModel
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndBridge
public import CFSG.RankThree.GF2n.Stroth80.Sec5Main

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_N_comm_W_le_V (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) :
    ∀ k ∈ hc.CN t, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅k, w⁆ ∈ Vt M (LB M Q B) B Z t := by
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  exact (h52a G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane _ _ _ _ rfl rfl rfl rfl).2

theorem sec7_V_le_W (h310chi : Stroth310ChiStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
  have h := (h310chi G M Q Z B hc n t hs.toSec5 (Or.inr hs.omegaNat)).2
  rw [h]
  exact hc.Vt_le_Q1 hs.toSec5.mem

theorem comm_N_of_vanish (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (hK : Sec7CRWStatement) (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {y : G} (hyM : y ∈ M) (hyt : ⁅y, t⁆ ∈ Q)
    (hyV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅y, v⁆ ∈ Z)
    (hyW : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅y, w⁆ ∈ Vt M (LB M Q B) B Z t) :
    ∀ k ∈ hc.CN t, ⁅k, y⁆ ∈ Z0 := by
  intro k hk
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS⟩ := tensorSetup_of_34 h34 G M Q Z B hc n hs.toSec5.width
    hs.toSec5.n_gt hs.toSec5.noA2 hs.toSec5.gen
  obtain ⟨hkR, hkV⟩ := Ctx.mem_CN.mp hk
  have hkM : k ∈ M := hc.Rt_le_M t hkR
  have hQn : ∀ m ∈ M, m ∈ Subgroup.normalizer (Q : Set G) := fun m hm => hc.hyp.Q_normal.2 hm
  have hyR : conjSubgroup y (Rt M (LB M Q B) t) = Rt M (LB M Q B) t := endg_F0_Rt hc hyM hyt
  have hyN : y ∈ Subgroup.normalizer (Rt M (LB M Q B) t : Set G) := conjSubgroup_eq_self_iff.mp hyR
  have hyVn : y ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    conjSubgroup_eq_self_iff.mp (endg_F0_Vt hc hyM hyt)
  have hkVn : k ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    hc.Rt_normalizes_Vt ht hkR
  have hkcR : ⁅k, y⁆ ∈ Rt M (LB M Q B) t := by
    have h1 : y * k⁻¹ * y⁻¹ ∈ Rt M (LB M Q B) t :=
      (Subgroup.mem_normalizer_iff.mp hyN k⁻¹).mp ((Rt M (LB M Q B) t).inv_mem hkR)
    have e : ⁅k, y⁆ = k * (y * k⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact (Rt M (LB M Q B) t).mul_mem hkR h1
  refine hK G M Q Z B hc n t hs Z0 hZ0 _ hkcR ?_
  have hVW := sec7_V_le_W h310chi hc hs
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hWc : ∀ {l : G}, l ∈ Subgroup.normalizer (Q : Set G) →
      l ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) →
      (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), l * w * l⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t)) ∧
      (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), l⁻¹ * w * l ∈ Wt Q (Vt M (LB M Q B) B Z t)) := by
    intro l hlQ hlV
    refine ⟨fun w hw => conj_mem_Wt hlQ hlV hw, fun w hw => ?_⟩
    have := conj_mem_Wt (Subgroup.inv_mem _ hlQ) (Subgroup.inv_mem _ hlV) hw
    simpa using this
  obtain ⟨hkW, hkW'⟩ := hWc (hQn k hkM) hkVn
  obtain ⟨hyW1, hyW'⟩ := hWc (hQn y hyM) hyVn
  exact commutator_comm_mem_Z (hQn) hS.conj sec39_Z_le_Vt hVW hWQ hkM hyM hkW hkW' hyW1 hyW'
    hkV hyV (sec7_N_comm_W_le_V h52a hA hc hs k hk) hyW

theorem sec7Centre_of_mp_mpr (hMp : Sec7CentreMpStatement) (hMpr : Sec7CentreMprStatement) :
    Sec7CentreStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 x
  exact ⟨fun hx => hMp G M Q Z B hc n t hs Z0 hZ0 x hx, fun ⟨hxL, hxW⟩ =>
    hMpr G M Q Z B hc n t hs Z0 hZ0 x hxL hxW⟩

end CFSG.RankThree.GF2n.Stroth80
