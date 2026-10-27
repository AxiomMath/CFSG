module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16t_insp_of_case168_7 (D : Data G) (hSg : UC6S846.SigmaStd D) {V L : Subgroup G}
    (h : Hyp125 D ⊥ V) (h7 : Case168_7 D ⊥ V h.isElemAbelian L)
    (hcomm : ⁅oddBar D.M ⊥ V h.isElemAbelian,
      barSub ⊥ V h.isElemAbelian (E3.wClos V D.k D.T)⁆ = ⊥) : Insp1613U D V := by
  classical
  have hV := h.isElemAbelian
  obtain ⟨⟨e⟩, hS, -, hsig⟩ := h7
  have h7σ : 7 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 7
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Finite (MulAut (Vtil ⊥ V hV)) := MulEquiv.finite_left
  have hP := h.pairFacts
  have hMst : D.M ≤ stabTil ⊥ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  obtain ⟨E, hEM, hEel, hEcard⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank (M := D.M) (by norm_num) (k := 3)
      (hSg.three_le 7 h7σ)
  have hEst : E ≤ stabTil ⊥ V := hEM.trans hMst
  obtain ⟨-, hFnorm, hFself⟩ := s16c167_cfg10_fstar_facts (Mbar D.M ⊥ V hV)
  have hEbM : barSub ⊥ V hV E ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hEM
  have hEb : IsElemAbelian 7 (barSub ⊥ V hV E) :=
    (hEel.subgroupOf (stabTil ⊥ V)).map (actTil ⊥ V hV)
  have hEbN : barSub ⊥ V hV E ≤
      normalizer (fstarBar D.M ⊥ V hV : Set (MulAut (Vtil ⊥ V hV))) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro f
    refine ⟨fun hf => hFnorm x (hEbM hx) f hf, fun hf => ?_⟩
    have h1 := hFnorm x⁻¹ ((Mbar D.M ⊥ V hV).inv_mem (hEbM hx)) _ hf
    rw [show x⁻¹ * (x * f * x⁻¹) * x⁻¹⁻¹ = f by group] at h1
    exact h1
  have hcardEb := s16n9b_card_le_mul_card_inf_centralizer (p := 7) (U := fstarBar D.M ⊥ V hV)
    hEbN hEb (b := 7) fun A hA => s16n9b_case7_card_le_seven hS e hA
  set Q : Subgroup (MulAut (Vtil ⊥ V hV)) :=
    barSub ⊥ V hV E ⊓ centralizer (fstarBar D.M ⊥ V hV : Set (MulAut (Vtil ⊥ V hV))) with hQ
  have hQEb : Q ≤ barSub ⊥ V hV E := inf_le_left
  have hid := s16c7_card_mul_card_preBarSub hV hEst hQEb
  set B : Subgroup G := preBarSub E ⊥ V hV Q with hB
  have hBE : B ≤ E := inf_le_left
  have hBcard : 49 ≤ Nat.card B := by
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    rw [hEcard] at hid
    have h1 : 7 ^ 3 * Nat.card Q ≤ (7 * Nat.card B) * Nat.card Q :=
      calc 7 ^ 3 * Nat.card Q = Nat.card B * Nat.card (barSub ⊥ V hV E) := hid
        _ ≤ Nat.card B * (7 * Nat.card Q) := Nat.mul_le_mul_left _ hcardEb
        _ = (7 * Nat.card B) * Nat.card Q := by ring
    have h2 := Nat.le_of_mul_le_mul_right h1 hQpos
    omega
  have hBel : IsElemAbelian 7 B := hEel.mono hBE
  have hBnc : ¬ IsCyclic B :=
    s16c7_not_isCyclic_of_elemAbelian (by norm_num) hBel (by omega)
  obtain ⟨X, hXF, hXM, hXcard, hXn, hXc⟩ :=
    s16c1610_center_fstar (Mb := Mbar D.M ⊥ V hV) (p := 7) (center_eq_bot_of_isL3 hS) e
  have hXodd : X ≤ oddBar D.M ⊥ V hV :=
    s16c13bc_le_oddBar hV hXM hXn (by rw [hXcard]; decide)
  have hXZ : X ≤ (Subgroup.center ↥(fstarBar D.M ⊥ V hV)).map (fstarBar D.M ⊥ V hV).subtype :=
    fun x hx => ⟨⟨x, hXF hx⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hXc g g.2 x hx), rfl⟩
  have hZcard : Nat.card ((Subgroup.center ↥(fstarBar D.M ⊥ V hV)).map
      (fstarBar D.M ⊥ V hV).subtype) ≤ Nat.card X := by
    rw [Subgroup.card_map_of_injective (fstarBar D.M ⊥ V hV).subtype_injective, hXcard]
    exact s16n9b_case7_card_center_le hS e
  have hXeq := Subgroup.eq_of_le_of_card_ge hXZ hZcard
  have hQX : Q ≤ X := by
    intro q hq
    have hqC := hq.2
    have hqF : q ∈ fstarBar D.M ⊥ V hV :=
      hFself q (hEbM hq.1) fun f hf => (Subgroup.mem_centralizer_iff.1 hqC f hf).symm
    rw [hXeq]
    exact ⟨⟨q, hqF⟩, Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (Subgroup.mem_centralizer_iff.1 hqC g g.2), rfl⟩
  have hBpre : B ≤ preBarSub D.M ⊥ V hV (oddBar D.M ⊥ V hV) := by
    intro g hg
    obtain ⟨hgE, hgst, hgQ⟩ := (mem_preBarSub E ⊥ V hV Q).1 hg
    exact (mem_preBarSub D.M ⊥ V hV _).2 ⟨hEM hgE, hgst, hXodd (hQX hgQ)⟩
  have hWT : E3.wClos V D.k D.T ≤ D.T := E3.wClos_le_of_forall fun A hA => hA.1
  refine ⟨V ⊓ centralizer (E3.wClos V D.k D.T : Set G), s16c167_fixV_wClos_ne_bot D h, le_rfl,
    7, h7σ, B, le_inf (hBE.trans hEM) ?_, hBel.isPGroup, hBnc⟩
  exact s16c167_normalizes_fixV hV hP.le_normalizer (hWT.trans D.sylowM.le) hcomm hBpre

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
