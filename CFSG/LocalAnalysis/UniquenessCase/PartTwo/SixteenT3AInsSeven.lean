module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAAux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Gen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg9Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsNoInv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16t_a_insp_of_case168_7 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1214 : F12.R1214 D) (hSg : UC6S846.SigmaStd D) {V L : Subgroup G}
    (h : Hyp125 D ⊥ V) (h7 : Case168_7 D ⊥ V h.isElemAbelian L) : Insp1613U D V := by
  classical
  have hV := h.isElemAbelian
  obtain ⟨⟨e⟩, hS, hsum, hsig⟩ := h7
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
  have hBpre : B ≤ preBarSub D.M ⊥ V hV X := by
    intro g hg
    obtain ⟨hgE, hgst, hgQ⟩ := (mem_preBarSub E ⊥ V hV Q).1 hg
    exact (mem_preBarSub D.M ⊥ V hV X).2 ⟨hEM hgE, hgst, hQX hgQ⟩
  have hXnormal : (X.subgroupOf (Mbar D.M ⊥ V hV)).Normal :=
    ⟨fun n hn g => hXn g g.2 n hn⟩
  have hX1 : X ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hXcard
    omega
  have hfixX : fixV X = ⊥ :=
    s16c1610_fixV_eq_bot D hx h61 h127 h1214 h hXM hXnormal hX1 (by rw [hXcard]; decide)
  haveI : Nontrivial ↥X := Finite.one_lt_card_iff_nontrivial.mp (by rw [hXcard]; norm_num)
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥X)
  have hgen : ∀ x : ↥X, x ∈ Subgroup.zpowers z := fun x => mem_zpowers_of_prime_card hXcard hz1
  have hzord : (z : MulAut (Vtil ⊥ V hV)) ^ 7 = 1 := by
    have h1 : z ^ Nat.card ↥X = 1 := pow_card_eq_one'
    rw [hXcard] at h1
    simpa using congrArg Subtype.val h1
  have hfix : ∀ v : Vtil ⊥ V hV, (z : MulAut (Vtil ⊥ V hV)) v = v → v = 1 := by
    intro v hv
    have hzs : (z : MulAut (Vtil ⊥ V hV)) ∈ MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) v := by
      rw [MulAction.mem_stabilizer_iff]
      exact hv
    have hXs : X ≤ MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) v := by
      intro x hx'
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨x, hx'⟩)
      have hxj : x = (z : MulAut (Vtil ⊥ V hV)) ^ j := by
        simpa using (congrArg Subtype.val hj).symm
      rw [hxj]
      exact Subgroup.zpow_mem _ hzs j
    have hvX : v ∈ fixV X := mem_fixV.2 fun x hx' => MulAction.mem_stabilizer_iff.1 (hXs hx')
    rw [hfixX] at hvX
    exact Subgroup.mem_bot.1 hvX
  have hrk : rk (Vtil ⊥ V hV) = 9 := by
    have h9 := s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
    rwa [rk_top] at h9
  have hcommX : ⁅X, barSub ⊥ V hV (E3.wClos V D.k D.T)⁆ = ⊥ := by
    refine eq_bot_iff.2 (Subgroup.commutator_le.2 fun x hx' w hw => ?_)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have hwM : w ∈ Mbar D.M ⊥ V hV := s16c13bcA_wBar_le_mbar D hV hw
    have hzw : w * (z : MulAut (Vtil ⊥ V hV)) * w⁻¹ ∈
        Subgroup.zpowers (z : MulAut (Vtil ⊥ V hV)) := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
        (hgen ⟨w * (z : MulAut (Vtil ⊥ V hV)) * w⁻¹, hXn w hwM z z.2⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨j, by simpa using congrArg Subtype.val hj⟩
    obtain ⟨k, hk⟩ := s16c13bcA_wBar_isPGroup D hV ⟨w, hw⟩
    have hw2 : w ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hcomm1 : Commute (z : MulAut (Vtil ⊥ V hV)) w := by
      rcases s16t_a_conj_eq_or_inv hzord hzw hw2 with h1 | h1
      · exact (mul_inv_eq_iff_eq_mul.1 h1).symm
      · exact (s16t_a_false_of_inverted (s15_Infra_vtil_sq_eq_one ⊥ V hV)
          (by rw [hrk]; decide) hzord hfix h1).elim
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨x, hx'⟩)
    have hxj : x = (z : MulAut (Vtil ⊥ V hV)) ^ j := by
      simpa using (congrArg Subtype.val hj).symm
    rw [hxj]
    exact Commute.zpow_left hcomm1 j
  have hWT : E3.wClos V D.k D.T ≤ D.T := E3.wClos_le_of_forall fun A hA => hA.1
  refine ⟨V ⊓ centralizer (E3.wClos V D.k D.T : Set G), s16c167_fixV_wClos_ne_bot D h, le_rfl,
    7, h7σ, B, le_inf (hBE.trans hEM) ?_, hBel.isPGroup, hBnc⟩
  exact s16c167_normalizes_fixV hV hP.le_normalizer (hWT.trans D.sylowM.le) hcommX hBpre

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
