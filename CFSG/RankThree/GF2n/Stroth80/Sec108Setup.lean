module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Six
public import CFSG.RankThree.GF2n.Stroth80.Sec10SevenChi
public import CFSG.RankThree.GF2n.Stroth80.Sec103Inv
public import CFSG.RankThree.GF2n.Stroth80.Sec4Model

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure Sec108Data (hc : Ctx M Q Z B) (t : G) (Y : Subgroup G) : Prop where
  h34 : Stroth34Statement
  h311a : Stroth311aStatement
  hspread : StrothNoA2SpreadStatement
  hyp : Sec10Hyp hc 6
  deg3 : ∀ s : G, Good101 M Q Z B s → SLMNat hc s 3
  good : Good103 M Q Z B t
  sit : Sit M Q Z Y t

theorem Sec108Data.exists_root (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} (H : Sec10Hyp hc 6)
    (hdeg : ∀ s : G, Good101 M Q Z B s → SLMNat hc s 3) {t : G} (ht : Good103 M Q Z B t) :
    ∃ Y : Subgroup G, Sec108Data hc t Y := by
  obtain ⟨Y, hs⟩ := Good101.exists_sit hc ht.1
  exact ⟨Y, h34, h311a, hspread, H, hdeg, ht, hs⟩

variable {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

theorem Sec108Data.slm (D : Sec108Data hc t Y) : SLMNat hc t 3 :=
  D.deg3 t D.good.1

theorem Sec108Data.noSL2 (D : Sec108Data hc t Y) :
    ∀ s : G, Good101 M Q Z B s → ¬ SLMNat hc s 2 := by
  intro s hs h2
  have h3 := D.deg3 s hs
  have hEq := SLMNat.unique h2 h3
  norm_num at hEq

theorem Sec108Data.no_fuse (D : Sec108Data hc t Y) :
    ∀ y ∈ Q, ∀ z ∈ Z, y * t * y⁻¹ = t * z → z = 1 :=
  Good103.no_fuse_of_noSL2 D.h34 D.h311a D.hspread D.hyp D.noSL2 D.good

theorem Sec108Data.card_Ut (D : Sec108Data hc t Y) : Nat.card (Ut Q Z t) = Nat.card Z ^ 7 := by
  have h := Good103.card_Ut_eq D.h34 D.h311a D.hspread D.hyp D.good D.slm
  simpa using h

theorem Sec108Data.inf_centralizer_eq (D : Sec108Data hc t Y) :
    Q ⊓ Subgroup.centralizer ({t} : Set G) = Ut Q Z t := by
  have ht2 : t ^ 2 = 1 := by
    rw [pow_two]
    exact D.sit.x_sq
  have hUC : Ut Q Z t ≤ Subgroup.centralizer ({t} : Set G) :=
    Ctx.Ut_le_centralizer D.h34 hc (D.hyp.toSec5 D.good.1.mem_LB D.good.1.2.2.1)
      (SLMNat.toSLNat D.slm (by norm_num)) ht2
  have hUtQ : Ut Q Z t ≤ Q := hc.Ut_le_Q D.good.1.2.1
  have hle : Ut Q Z t ≤ Q ⊓ Subgroup.centralizer ({t} : Set G) := le_inf hUtQ hUC
  have hcount := Ctx.card_centralizer_mul_card_Ut hc D.good.1.mem_LB D.no_fuse
  have hQcard : Nat.card Q = Nat.card Z ^ 13 := by
    have hw := D.hyp.width
    unfold Width at hw
    simpa using hw
  have hCcard : Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) = Nat.card Z ^ 7 := by
    have hEq : Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) * Nat.card Z ^ 7 =
        Nat.card Z ^ 7 * Nat.card Z ^ 7 := by
      calc Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) * Nat.card Z ^ 7
          = Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) * Nat.card (Ut Q Z t) := by
              rw [D.card_Ut]
        _ = Nat.card Q * Nat.card Z := hcount
        _ = Nat.card Z ^ 13 * Nat.card Z := by rw [hQcard]
        _ = Nat.card Z ^ 7 * Nat.card Z ^ 7 := by
              rw [← pow_succ, show 13 + 1 = 7 + 7 by norm_num, pow_add]
    exact Nat.eq_of_mul_eq_mul_right (pow_pos Nat.card_pos 7) hEq
  have hcardle : Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) ≤ Nat.card (Ut Q Z t) := by
    rw [hCcard, D.card_Ut]
  exact (Subgroup.eq_of_le_of_card_ge hle hcardle).symm

theorem Sec108Data.inf_centralizer_le (D : Sec108Data hc t Y) :
    Q ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.centralizer (Y : Set G) := by
  rw [← Kx_eq D.sit (smith_1_12 D.sit)]
  exact Kx_le_centralizer_X D.sit (smith_1_12 D.sit)

theorem Sec108Data.card_Vt (D : Sec108Data hc t Y) :
    Nat.card (Vt M (LB M Q B) B Z t) = Nat.card Z ^ 4 := by
  have h := SLMNat.card_Vt D.slm
  simpa using h

theorem Sec108Data.card_inf_QB_root (D : Sec108Data hc t Y) :
    Nat.card ↥(Q ⊓ QB Y) = Nat.card Z ^ 3 := by
  have h := Good103.card_inf_QB_eq_pow (m := 3) hc D.good D.sit D.card_Vt
  simpa using h

theorem Sec108Data.card_inf_QB (D : Sec108Data hc t Y) : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ 7 := by
  have h := (card_LB_of_ctx D.h34 hc D.hyp.width D.hyp.n_gt D.hyp.noA2 D.hyp.gen).2
  simpa using h

theorem Sec108Data.card_bar_LB [(Q.subgroupOf M).Normal] (D : Sec108Data hc t Y) :
    Nat.card (bar M Q (LB M Q B)) = Nat.card Z ^ 5 := by
  have hbar := bar_card_mul_card_of_le (M := M) (S := LB M Q B) le_sup_left hc.LB_le_M
  have hLB := (card_LB_of_ctx D.h34 hc D.hyp.width D.hyp.n_gt D.hyp.noA2 D.hyp.gen).1
  have hQcard : Nat.card Q = Nat.card Z ^ 13 := by
    have hw := D.hyp.width
    unfold Width at hw
    simpa using hw
  have hEq : Nat.card (bar M Q (LB M Q B)) * Nat.card Q = Nat.card Z ^ 5 * Nat.card Q := by
    rw [hbar, hLB, hQcard, show 6 - 1 = 5 by norm_num]
    ring
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hEq

theorem Sec108Data.root_le_LB (D : Sec108Data hc t Y) : Y ≤ LB M Q B := by
  have hYQB : Y ≤ QB B := D.good.1.root_le_QB hc D.sit
  have hYM : Y ≤ M := (smith_1_12 D.sit).1.trans inf_le_left
  intro y hy
  unfold LB
  exact Subgroup.mem_sup_right ⟨hYQB hy, hYM hy⟩

theorem Sec108Data.Rt_le_H0 (D : Sec108Data hc t Y) :
    Rt M (LB M Q B) t ≤ H0 M Z :=
  hc.Rt_le_H0 t

theorem Sec108Data.t_mem_H0 (D : Sec108Data hc t Y) : t ∈ H0 M Z :=
  hc.LB_le_H0 D.good.1.mem_LB

theorem Sec108Data.comm_Rt_root_mem (D : Sec108Data hc t Y) :
    ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Y, ⁅r, y⁆ ∈ Q := by
  intro r hr y hy
  by_cases hy1 : y = 1
  · simpa [hy1] using Q.one_mem
  have hy101 : Good101 M Q Z B y :=
    D.good.1.of_mem_root_good101 D.h34 D.hspread D.hyp D.sit hy hy1
  have h102 := stroth_10_2 (stroth_5_7 D.h34 D.hspread) G M Q Z B hc 6 y D.hyp hy101
  have hRy : Rt M (LB M Q B) y = Rt M (LB M Q B) t :=
    D.good.1.Rt_eq_of_mem_root D.h34 D.hspread D.hyp D.sit hy hy1
  have hrY : r ∈ Rt M (LB M Q B) y := by rwa [hRy]
  have hQR : Q ≤ Rt M (LB M Q B) y := by rw [h102]; exact le_sup_left
  have hKR : Rt M (LB M Q B) y ⊓ Subgroup.centralizer ({y} : Set G) ≤
      Rt M (LB M Q B) y := inf_le_left
  haveI : (Q.subgroupOf (Rt M (LB M Q B) y)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQR).mpr
      (fun x hx => hc.hyp.Q_normal.2 (hc.Rt_le_M y hx))
  have hmem : (⟨r, hrY⟩ : ↥(Rt M (LB M Q B) y)) ∈
      (Q.subgroupOf (Rt M (LB M Q B) y)) ⊔
        ((Rt M (LB M Q B) y ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf
          (Rt M (LB M Q B) y)) := by
    rw [← Subgroup.subgroupOf_sup hQR hKR]
    exact Subgroup.mem_subgroupOf.mpr (h102 ▸ hrY)
  obtain ⟨q, hq, c, hcC, hqc⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  have hqQ : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq
  have hcCG : (c : G) ∈ Subgroup.centralizer ({y} : Set G) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hcC)).2
  have hqcG : (q : G) * (c : G) = r := by
    simpa using congrArg Subtype.val hqc
  have hcy : (c : G) * y = y * (c : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp hcCG
  have hcomm_c : ⁅(c : G), y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcy
  have hyM : y ∈ M := (Subgroup.mem_inf.mp ((smith_1_12 D.sit).1 hy)).1
  have hqconj : y * (q : G)⁻¹ * y⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hyM) (q : G)⁻¹).mp
      (Q.inv_mem hqQ)
  have hcomm_q : ⁅(q : G), y⁆ ∈ Q := by
    have h := Q.mul_mem hqQ hqconj
    simpa only [commutatorElement_def, mul_assoc] using h
  rw [← hqcG, commutatorElement_mul_left_eq_conj_mul, hcomm_c]
  simpa using hcomm_q

private theorem swap_good101 {g : G} (hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B)
    (hgZ : conjSubgroup g Z = Y) (hgB : conjSubgroup g B = B) {s : G}
    (hs : Good101 (conjSubgroup g M) (conjSubgroup g Q) Y B s) :
    Good101 M Q Z B (g⁻¹ * s * g) := by
  have h := Good101.conjG (hc := hcY) hs g⁻¹
  rw [← hgZ, ← hgB] at h
  simpa only [conjSubgroup_conjSubgroup, inv_inv, inv_mul_cancel, conjSubgroup_one] using h

private theorem swap_deg3 (D : Sec108Data hc t Y) {g : G}
    (hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B)
    (hgZ : conjSubgroup g Z = Y) (hgB : conjSubgroup g B = B) :
    ∀ s : G, Good101 (conjSubgroup g M) (conjSubgroup g Q) Y B s → SLMNat hcY s 3 := by
  intro s hs
  have hs' : Good101 M Q Z B (g⁻¹ * s * g) := swap_good101 hcY hgZ hgB hs
  have h3 := SLMNat.conjG (D.deg3 (g⁻¹ * s * g) hs') g
  rw [show g * (g⁻¹ * s * g) * g⁻¹ = s by group] at h3
  exact SLMNat.of_eq h3 hcY rfl rfl hgZ hgB

theorem Sec108Data.swap (D : Sec108Data hc t Y) :
    ∃ g : G, conjSubgroup g Z = Y ∧ conjSubgroup g B = B ∧
      ∃ hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B,
        ∀ z ∈ Z, z ≠ 1 → Sec108Data hcY z Z := by
  obtain ⟨g, hgZ, hgB, hcY, H', hrest⟩ :=
    Good103.exists_swap D.h34 D.hspread D.hyp D.good D.sit D.slm
  refine ⟨g, hgZ, hgB, hcY, fun z hz hz1 => ?_⟩
  obtain ⟨hsz, h103, -, -⟩ := hrest z hz hz1
  exact ⟨D.h34, D.h311a, D.hspread, H', swap_deg3 D hcY hgZ hgB, h103, hsz⟩

end CFSG.RankThree.GF2n.Stroth80
