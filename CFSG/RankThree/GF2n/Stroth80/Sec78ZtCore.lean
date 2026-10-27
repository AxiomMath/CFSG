module

public import CFSG.RankThree.GF2n.Stroth80.Sec78Z0Data
public import CFSG.RankThree.GF2n.Stroth80.Sec83Card
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec311Conj
public import CFSG.RankThree.GF2n.Stroth80.Sec311Main
public import CFSG.RankThree.GF2n.Stroth80.Sec78CardUt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7ctr_Rt_eq_sup (hc : Ctx M Q Z B) {t r : G} (hr : Sec7A hc t r) :
    Rt M (LB M Q B) t = conjSubgroup 1 (LB M Q B) ⊔ conjSubgroup r (LB M Q B) := by
  rw [conjSubgroup_one, ← hc.LB_conj (hc.Rt_le_M t hr.mem)]
  exact hr.gen

theorem sec7ctr_zt_core (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) {r : G}
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZL : Z0 ≤ LB M Q B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G))
    (hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B)
    (hchi : IsChiIso Q (Rt M (LB M Q B) t) (Wt Q (Vt M (LB M Q B) B Z t))
      (Vt M (LB M Q B) B Z t) Z t)
    (hVgen : Vt M (LB M Q B) B Z t ≤ Z ⊔ ⨆ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ B)
    (hW : ∀ s ∈ Z0, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, w⁆ ∈ Z)
    {s : G} (hsZ : s ∈ Z0) (hsQ : s ∉ Q) :
    Rt M (LB M Q B) t ≤ Rt M (LB M Q B) s ∧
      Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t := by
  have ht : t ∈ LB M Q B := hs.mem
  have hsL : s ∈ LB M Q B := hZL hsZ
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hsR : s ∈ Rt M (LB M Q B) t := hZ0.le hsZ
  have hrM : r ∈ M := hRM hr.mem
  have hsconj : ∀ ρ ∈ Rt M (LB M Q B) t, s ∈ conjSubgroup ρ (LB M Q B) := fun ρ hρ =>
    sec7ctr_Z0_le_conj_LB hc hZ0 hZL hρ hsZ
  have hRle : Rt M (LB M Q B) t ≤ Rt M (LB M Q B) s := by
    rw [sec7ctr_Rt_eq_sup hc hr]
    refine sup_le ?_ ?_
    · rw [conjSubgroup_one]
      exact le_Rt (M := M) (LB M Q B) hsL
    · exact conjSubgroup_le_Rt hrM (hsconj r hr.mem)
  have hVle : Vt M (LB M Q B) B Z t ≤ Vt M (LB M Q B) B Z s := by
    refine hVgen.trans (sup_le sec39_Z_le_Vt (iSup₂_le fun ρ hρ => ?_))
    exact sec39_conjB_le_Vt (hRM hρ) (hsconj ρ hρ)
  have hnotQBs : ¬ Vt M (LB M Q B) B Z s ≤ QB B := fun h => hnotQB (hVle.trans h)
  obtain ⟨hVU, -⟩ := hc.Vt_eq_Ut_and_Wt_eq_Q1_of_not_le_QB h35 hsL hsQ hnotQBs
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hZW : Z ≤ Wt Q (Vt M (LB M Q B) B Z t) := fun z hz =>
    ⟨hc.Z_le_Q hz, Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (hc.hyp.toHyp79.V_central hz (hVQ hv)).symm⟩
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hsc : ∀ ρ ∈ Rt M (LB M Q B) t, ⁅ρ⁻¹, s⁆ ∈ Q := fun ρ hρ => by
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hZ0.comm_mem hsZ ((Rt M (LB M Q B) t).inv_mem hρ))
  have hWs : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅w, s⁆ ∈ Z := fun w hw => by
    rw [← commutatorElement_inv]
    exact Z.inv_mem (hW s hsZ w hw)
  have hUt := sec7ctr_card_Ut_le hc hRM hsR hsc hZW hWQ hWs
  haveI : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hVQ hv)))
  have hcardχ := card_mul_card_of_isChiIso hchi hWQ hZV
  have hWpos : 0 < Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) := Nat.card_pos
  have hcard : Nat.card ↥(Vt M (LB M Q B) B Z s) ≤ Nat.card ↥(Vt M (LB M Q B) B Z t) := by
    rw [hVU]
    refine Nat.le_of_mul_le_mul_right ?_ hWpos
    calc Nat.card ↥(Ut Q Z s) * Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t))
        ≤ Nat.card ↥Z * Nat.card ↥Q := hUt
      _ = Nat.card ↥(Vt M (LB M Q B) B Z t) *
          Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) := by
        rw [mul_comm, hcardχ, mul_comm]
  exact ⟨hRle, (Subgroup.eq_of_le_of_card_ge hVle hcard).symm⟩

theorem sec7ctr_Rt_le_of_56 (hc : Ctx M Q Z B) {t s : G}
    (h56 : ∀ m ∈ M, conjSubgroup m B ⊔ Z ≤ Vt M (LB M Q B) B Z t →
      ∃ r ∈ Rt M (LB M Q B) t, conjSubgroup m B ⊔ Z = conjSubgroup r B ⊔ Z)
    (ht : t ∈ LB M Q B) (hV : Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t) :
    Rt M (LB M Q B) s ≤ Rt M (LB M Q B) t := by
  refine iSup₂_le fun m hm => iSup_le fun hsm => ?_
  have hBm : conjSubgroup m B ⊔ Z ≤ Vt M (LB M Q B) B Z t := by
    rw [← hV]
    exact sup_le (sec39_conjB_le_Vt hm hsm) sec39_Z_le_Vt
  obtain ⟨ρ, hρ, hBZ⟩ := h56 m hm hBm
  rw [hc.conj_LB_eq_of_conj_BZ hm (hc.Rt_le_M t hρ) hBZ]
  exact hc.conj_LB_le_Rt ht hρ

theorem sec7ctr_Vgen_of_56 {t : G}
    (h56 : ∀ m ∈ M, conjSubgroup m B ⊔ Z ≤ Vt M (LB M Q B) B Z t →
      ∃ r ∈ Rt M (LB M Q B) t, conjSubgroup m B ⊔ Z = conjSubgroup r B ⊔ Z) :
    Vt M (LB M Q B) B Z t ≤ Z ⊔ ⨆ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ B := by
  unfold Vt
  refine sup_le le_sup_left (iSup₂_le fun m hm => iSup_le fun htm => ?_)
  have hBm : conjSubgroup m B ⊔ Z ≤ Vt M (LB M Q B) B Z t :=
    sup_le (sec39_conjB_le_Vt hm htm) sec39_Z_le_Vt
  obtain ⟨ρ, hρ, hBZ⟩ := h56 m hm hBm
  have h1 : conjSubgroup m B ≤ conjSubgroup ρ B ⊔ Z := hBZ ▸ le_sup_left
  refine h1.trans (sup_le ?_ le_sup_left)
  exact le_sup_of_le_right (le_iSup₂_of_le ρ hρ le_rfl)

end CFSG.RankThree.GF2n.Stroth80
