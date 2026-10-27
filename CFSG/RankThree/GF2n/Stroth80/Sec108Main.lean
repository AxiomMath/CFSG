module

public import CFSG.RankThree.GF2n.Stroth80.Sec108LeviBridge
public import CFSG.RankThree.GF2n.Stroth80.Sec108Q4
public import CFSG.RankThree.GF2n.Stroth80.Sec108Closure
public import CFSG.RankThree.GF2n.Stroth80.Sec108Cover
public import CFSG.RankThree.GF2n.Stroth80.HeringSec65NBar
public import CFSG.RankThree.GF2n.Stroth80.Sec10Stmt
public import CFSG.GroupTheory.StronglyClosedTI.Endgame
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.LargeEvenClassification.MinimalNormalFactors
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreLocalIntersections
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreLocality
public import CFSG.Quasithin.Vol2.Ch10SecD33
public import CFSG.Quasithin.Vol2.Ch10SecDClA
public import CFSG.Quasithin.Vol2.Ch11SecA11Main
public import CFSG.Quasithin.Vol2.Ch11SecAKA2
public import CFSG.Quasithin.Vol2.Ch11SecDFacts
public import CFSG.Quasithin.Vol2.Ch11SecDFacts3
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartD
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4E
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4F
public import CFSG.Quasithin.Vol2.Ch11SecSMain
public import CFSG.Quasithin.Vol2.Ch11SecSShape2
public import CFSG.Quasithin.Vol2.Ch11SecSSym2
public import CFSG.Quasithin.Vol2.Ch11SecSSym3
public import CFSG.Quasithin.Vol2.KGNatSL3NatFixed
public import CFSG.Quasithin.Vol2.KGNatSL3NatPoint

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix

section Endgame

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G} [(Q.subgroupOf M).Normal]

private theorem Sec108Data.bar_root_sup_Q (D : Sec108Data hc t Y) :
    bar M Q (Y ⊔ Q) = bar M Q Y := by
  refine le_antisymm ?_ (HS6.bar_mono le_sup_left)
  intro x hx
  obtain ⟨g, hg, -, rfl⟩ :=
    (HS6.mem_bar (M := M) (Q := Q) (S := Y ⊔ Q) (y := x)).mp hx
  obtain ⟨y, hy, w, hw, rfl⟩ := D.exists_root_mul hg
  have hyM : y ∈ M := ((smith_1_12 D.sit).1).trans inf_le_left hy
  have hwM : w ∈ M := hc.hyp.Q_normal.1 hw
  have hw1 : HS6.piM M Q w = 1 := (HS6.piM_eq_one_iff hwM).mpr hw
  rw [show HS6.piM M Q (y * w) = HS6.piM M Q y from by
    rw [HS6.piM_mul hyM hwM, hw1, mul_one]]
  exact HS6.piM_mem_bar hy hyM

theorem Sec108Data.bar_CN_mul_self (D : Sec108Data hc t Y) :
    ∀ x ∈ bar M Q (hc.CN t), x * x = 1 := by
  intro x hx
  simpa [pow_two] using D.isElemAbelian_bar_CN.2 x hx

theorem Sec108Data.bar_root_mul_self (D : Sec108Data hc t Y) : ∀ y ∈ bar M Q Y, y * y = 1 :=
  fun y hy => D.bar_CN_mul_self y (HS6.bar_mono D.root_le_CN hy)

theorem Sec108Data.card_bar_root (D : Sec108Data hc t Y) : Nat.card (bar M Q Y) = Nat.card Z := by
  rw [card_bar_eq_of_inf_eq_bot ((smith_1_12 D.sit).1.trans inf_le_left) (smith_1_12 D.sit).2]
  obtain ⟨g, hg⟩ := D.sit.conj
  rw [hg, card_conjSubgroup]

theorem Sec108Data.four_le_card_bar_root (D : Sec108Data hc t Y) : 4 ≤ Nat.card (bar M Q Y) := by
  rw [D.card_bar_root]
  exact hc.hyp.q4

theorem Sec108Data.two_mul_card_bar_root_lt (D : Sec108Data hc t Y) :
    2 * Nat.card (bar M Q Y) < Nat.card (bar M Q (hc.CN t)) := by
  rw [D.card_bar_root, D.card_bar_CN]
  have hq3 : 2 < Nat.card Z ^ 3 := by
    have h : 4 ^ 3 ≤ Nat.card Z ^ 3 := Nat.pow_le_pow_left hc.hyp.q4 3
    norm_num at h ⊢
    omega
  calc 2 * Nat.card Z = Nat.card Z * 2 := by rw [mul_comm]
    _ < Nat.card Z * Nat.card Z ^ 3 := Nat.mul_lt_mul_of_pos_left hq3 Nat.card_pos
    _ = Nat.card Z ^ 3 * Nat.card Z := by rw [mul_comm]
    _ = Nat.card Z ^ 4 := by rw [← pow_succ]

theorem Sec108Data.bar_root_TI (D : Sec108Data hc t Y) :
    ∀ y ∈ bar M Q Y, y ≠ 1 → ∀ g : Mbar M Q, g * y = y * g →
      g ∈ Subgroup.normalizer (bar M Q Y : Set (Mbar M Q)) := by
  intro y hy hy1 g hg
  obtain ⟨y₀, hy₀Y, hy₀M, rfl⟩ :=
    (HS6.mem_bar (M := M) (Q := Q) (S := Y) (y := y)).mp hy
  obtain ⟨g₀, hg₀M, rfl⟩ := HS6.exists_piM (M := M) (Q := Q) g
  have hy₀1 : y₀ ≠ 1 := by
    rintro rfl
    exact hy1 (HS6.piM_one (M := M) (Q := Q))
  have hcomm : HS6.piM M Q (g₀ * y₀ * g₀⁻¹) = HS6.piM M Q y₀ := by
    rw [HS6.piM_mul (M.mul_mem hg₀M hy₀M) (M.inv_mem hg₀M),
      HS6.piM_mul hg₀M hy₀M, HS6.piM_inv hg₀M, hg]
    group
  have hmem : y₀⁻¹ * (g₀ * y₀ * g₀⁻¹) ∈ Q := by
    have h1 : HS6.piM M Q (y₀⁻¹ * (g₀ * y₀ * g₀⁻¹)) = 1 := by
      rw [HS6.piM_mul (M.inv_mem hy₀M)
        (M.mul_mem (M.mul_mem hg₀M hy₀M) (M.inv_mem hg₀M)),
        HS6.piM_inv hy₀M, hcomm, inv_mul_cancel]
    exact (HS6.piM_eq_one_iff (M.mul_mem (M.inv_mem hy₀M)
      (M.mul_mem (M.mul_mem hg₀M hy₀M) (M.inv_mem hg₀M)))).mp h1
  have hnorm : g₀ ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) :=
    D.mem_normalizer_root_of_conj hg₀M hy₀Y hy₀Y hy₀1 hmem
  have hYM : Y ≤ M := ((smith_1_12 D.sit).1).trans inf_le_left
  rw [← D.bar_root_sup_Q,
    ← HS6.bar_normalizer (M := M) (Q := Q) hc.hyp.Q_normal.1 le_sup_right
      (sup_le hYM hc.hyp.Q_normal.1)]
  exact HS6.piM_mem_bar ⟨hnorm, hg₀M⟩ hg₀M

theorem Sec108Data.normalizer_bar_root_eq_CN (D : Sec108Data hc t Y) :
    Subgroup.normalizer (bar M Q Y : Set (Mbar M Q)) =
      Subgroup.normalizer (bar M Q (hc.CN t) : Set (Mbar M Q)) := by
  have hYM : Y ≤ M := ((smith_1_12 D.sit).1).trans inf_le_left
  have hYMQ : Y ⊔ Q ≤ M := sup_le hYM hc.hyp.Q_normal.1
  have hQCN : Q ≤ hc.CN t := hc.Q_le_CN D.good.1.mem_LB
  have hCNM : hc.CN t ≤ M := fun x hx => hc.Rt_le_M t (Ctx.mem_CN.mp hx).1
  have hnorm : Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) ⊓ M =
      Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) ⊓ M := by
    ext g
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hgY, hgM⟩
      exact ⟨(D.mem_normalizer_root_iff_CN hgM).mp hgY, hgM⟩
    · rintro ⟨hgN, hgM⟩
      exact ⟨(D.mem_normalizer_root_iff_CN hgM).mpr hgN, hgM⟩
  calc Subgroup.normalizer (bar M Q Y : Set (Mbar M Q))
      = Subgroup.normalizer (bar M Q (Y ⊔ Q) : Set (Mbar M Q)) := by rw [D.bar_root_sup_Q]
    _ = bar M Q (Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) ⊓ M) :=
        (HS6.bar_normalizer (M := M) (Q := Q) hc.hyp.Q_normal.1 le_sup_right hYMQ).symm
    _ = bar M Q (Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) ⊓ M) := by rw [hnorm]
    _ = Subgroup.normalizer (bar M Q (hc.CN t) : Set (Mbar M Q)) :=
        HS6.bar_normalizer (M := M) (Q := Q) hc.hyp.Q_normal.1 hQCN hCNM

end Endgame

theorem stroth108Core_of_inputs
    (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) (hAS : Tim79a.AschbacherSeitzStatement)
    (hGold : ComponentClassification.Asc76X.GoldschmidtTheoremA)
    (hOut : ∀ (L : Type) [Group L] [Finite L] [IsSimpleGroup L], goldschmidtSimpleType L →
      ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC.OutCyc L)
    (hHJ : Tim79a.AschbacherHJRepresentationStatement)
    (hM12 : ComponentClassification.RankTwoClassical.M12AutThreeFive) :
    Stroth108CoreStatement := by
  intro G _ _ M Q Z B hc t H hdeg ht
  obtain ⟨Y, D⟩ := Sec108Data.exists_root h34 h311a hspread H hdeg ht
  haveI := hc.normal_Q_in_M
  obtain ⟨AM⟩ := Smith81.Smith23E1.ActionModel.nonempty hc.hyp
  obtain ⟨ρ, μ, T, hL⟩ := D.exists_levi108 AM
  rcases hL.normal_or hAS Sec108.sec108OddCoverStatement with hX | ⟨hq, hexc⟩
  · obtain ⟨S, hYS, hsc⟩ := D.exists_sylow_stronglyClosed (hL.normalizer_le_of_normal hX)
    exact GroupTheory.StronglyClosedTI.false_of_stronglyClosed_TI hGold hOut hc.pCore_two_Mbar S
      hYS D.bar_root_mul_self D.four_le_card_bar_root D.bar_root_TI hsc D.bar_CN_mul_self
      D.normalizer_bar_root_eq_CN.le D.two_mul_card_bar_root_lt
  · refine hL.not_exception hHJ hM12 hq ?_ hexc
    rw [D.card_bar_LB, ← AM.glob.card, hq]
    norm_num

end CFSG.RankThree.GF2n.Stroth80
