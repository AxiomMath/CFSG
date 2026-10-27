module

public import CFSG.RankThree.GF2n.Stroth80.Sec37Geom
public import CFSG.RankThree.GF2n.Stroth80.Sec37CommTrans
public import CFSG.RankThree.GF2n.Stroth80.Sec37CommStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec34Trans

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tim37

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

omit [Finite G] in
theorem card_bar_mul_card_of_le [(Q.subgroupOf M).Normal] {S : Subgroup G} (hQS : Q ≤ S)
    (hSM : S ≤ M) : Nat.card (bar M Q S) * Nat.card Q = Nat.card S := by
  have hQM : Q ≤ M := hQS.trans hSM
  have hle : Q.subgroupOf M ≤ S.subgroupOf M := fun x hx => hQS hx
  have hS' : Nat.card (S.subgroupOf M) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv
  have hQ' : Nat.card ((Q.subgroupOf M).subgroupOf (S.subgroupOf M)) = Nat.card Q :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv)
  have h1 := Subgroup.card_ker_mul_card_range
    ((QuotientGroup.mk' (Q.subgroupOf M)).domRestrict (S.subgroupOf M))
  rw [MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk', hQ',
    hS'] at h1
  rw [Nat.mul_comm]
  exact h1

theorem card_bar_LB_eq [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hno : NoA2 Q Z (LB M Q B)) (hn : 1 ≤ n) :
    Nat.card (bar M Q (LB M Q B)) = Nat.card Z ^ (n - 1) := by
  have h33 := (hc.card_of_3_3 hw hn hno (stroth_3_3 hc hw hn)).1
  have h := card_bar_mul_card_of_le (M := M) (S := LB M Q B) le_sup_left hc.LB_le_M
  have h2 : Nat.card (bar M Q (LB M Q B)) * Nat.card Q = Nat.card Z ^ (n - 1) * Nat.card Q := by
    rw [h, h33, Nat.mul_comm]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2

theorem isWC_bar_LB_of_isTIMod [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B))
    (hTI : IsTIMod M Q (LB M Q B)) : IsWC (bar M Q (LB M Q B)) :=
  isWC_of_corBHyp (corBHyp_of_ti_of_weaklyClosed hc.isElemAbelian_bar_LB
    (isTI_bar_of_isTIMod le_sup_left hTI)
    (weaklyClosed_bar_of_weaklyClosed le_sup_left hc.LB_le_M
      fun _ hm h => hc.weaklyClosed_of_3_1 hw hn hno hm h))

theorem weaklyClosed_normalizer_bar_LB [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (x : Mbar M Q)
    (hx : conjSubgroup x (bar M Q (LB M Q B)) ≤
      Subgroup.normalizer ((bar M Q (LB M Q B) : Subgroup (Mbar M Q)) : Set (Mbar M Q))) :
    conjSubgroup x (bar M Q (LB M Q B)) = bar M Q (LB M Q B) := by
  have h := weaklyClosed_bar_of_weaklyClosed (le_sup_left : Q ≤ LB M Q B) hc.LB_le_M
    (fun _ hm h => hc.weaklyClosed_of_3_1 hw hn hno hm h) x⁻¹ (by rwa [inv_inv])
  rwa [inv_inv] at h

theorem stroth37Commuting_of_dichotomy (h34 : Stroth34Statement)
    (hD : Form2DichotomyStatement) (hE : Eleven37Statement)
    (hF2 : CFSG.LargeExtraspecial.S4.Form2StrongStmt) : Stroth37CommutingStatement := by
  intro G _ _ M Q Z B hc n hw hn hno hgen hTI m hm hcomm
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hcard : Nat.card (bar M Q (LB M Q B)) = Nat.card Z ^ (n - 1) :=
    card_bar_LB_eq hc hw hno (by omega)
  have h16 : 16 ≤ Nat.card (bar M Q (LB M Q B)) := by
    rw [hcard]
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ Nat.card Z ^ 2 := Nat.pow_le_pow_left hq4 2
      _ ≤ Nat.card Z ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  rcases hD hF2 (Mbar M Q) (bar M Q (LB M Q B)) (isWC_bar_LB_of_isTIMod hc hw hn hno hTI)
      hc.normal_isPGroup_two_Mbar_eq_bot (weaklyClosed_normalizer_bar_LB hc hw hn hno) h16 with
    h2 | hmeet | ⟨h16', h11⟩
  · exact Tim37.commuting_of_twoTrans hc hw hn hno h2 hm hcomm
  · exact (Tim37.false_of_meet h34 hc hw hn hno hgen hmeet).elim
  · exfalso
    have hZ16 : Nat.card Z ^ (n - 1) = 16 := by rw [← hcard]; exact h16'
    have hn3 : n = 3 := by
      by_contra hne
      have h64 : 64 ≤ Nat.card Z ^ (n - 1) :=
        calc 64 = 4 ^ 3 := by norm_num
          _ ≤ Nat.card Z ^ 3 := Nat.pow_le_pow_left hq4 3
          _ ≤ Nat.card Z ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    subst hn3
    have hZ2 : Nat.card Z ^ 2 = 16 := hZ16
    have hZ4 : Nat.card Z = 4 := by
      have h' : Nat.card Z ^ 2 = 4 ^ 2 := by norm_num [hZ2]
      exact Nat.pow_left_injective (by norm_num) h'
    refine hE G M Q Z B hc hw hZ4 ?_
    rw [bar_Lgen_eq_normalClosure hc]
    exact h11

end CFSG.RankThree.GF2n.Stroth80.Tim37
