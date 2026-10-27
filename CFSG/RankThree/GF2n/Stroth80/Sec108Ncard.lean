module

public import CFSG.RankThree.GF2n.Stroth80.Sec108Setup
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarDict

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

private theorem Sec108Data.QB_inf_M_eq_of_swap (D : Sec108Data hc t Y) {g : G}
    (hgZ : conjSubgroup g Z = Y)
    (hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B)
    {z : G} (Dz : Sec108Data hcY z Z) :
    QB Y = conjSubgroup g Q ∧ QB Y ⊓ M = Ut (conjSubgroup g Q) Y z := by
  have hQY : QB Y = conjSubgroup g Q := by
    rw [← hgZ]
    exact Smith81.QB_conj_eq hc.hyp g
  have hK : Kx (conjSubgroup g Q) Z = conjSubgroup g Q ⊓ M := by
    unfold Kx
    rw [hc.hyp.normalizer_Z.1]
  refine ⟨hQY, ?_⟩
  calc
    QB Y ⊓ M = conjSubgroup g Q ⊓ M := by rw [hQY]
    _ = Kx (conjSubgroup g Q) Z := hK.symm
    _ = conjSubgroup g Q ⊓ Subgroup.centralizer ({z} : Set G) :=
        Kx_eq Dz.sit (smith_1_12 Dz.sit)
    _ = Ut (conjSubgroup g Q) Y z := Dz.inf_centralizer_eq

theorem Sec108Data.card_QB_inf_M (D : Sec108Data hc t Y) :
    Nat.card ↥(QB Y ⊓ M) = Nat.card Z ^ 7 := by
  obtain ⟨g, hgZ, -, hcY, hrest⟩ := D.swap
  obtain ⟨z, hz, hz1⟩ := hc.hyp.exists_ne_one_mem_Z
  have hDz := hrest z hz hz1
  have heq := (D.QB_inf_M_eq_of_swap hgZ hcY hDz).2
  rw [heq, hDz.card_Ut, ← hgZ, card_conjSubgroup]

theorem Sec108Data.isElemAbelian_QB_inf_M (D : Sec108Data hc t Y) :
    IsElemAbelian 2 (QB Y ⊓ M) := by
  obtain ⟨g, hgZ, -, hcY, hrest⟩ := D.swap
  obtain ⟨z, hz, hz1⟩ := hc.hyp.exists_ne_one_mem_Z
  have hDz := hrest z hz hz1
  rw [(D.QB_inf_M_eq_of_swap hgZ hcY hDz).2]
  exact Ctx.isElemAbelian_Ut D.h34 hcY
    (hDz.hyp.toSec5 hDz.good.1.mem_LB hDz.good.1.2.2.1)
    (SLMNat.toSLNat hDz.slm (by norm_num))

private theorem Sec108Data.card_Q (D : Sec108Data hc t Y) : Nat.card Q = Nat.card Z ^ 13 := by
  have hw := D.hyp.width
  unfold Width at hw
  simpa using hw

private theorem Sec108Data.card_bar_sup_QB [(Q.subgroupOf M).Normal]
    (D : Sec108Data hc t Y) :
    Nat.card (bar M Q (Q ⊔ (QB Y ⊓ M))) = Nat.card Z ^ 4 := by
  have hQcard : Nat.card Q = Nat.card Z ^ 13 := D.card_Q
  have hPcard : Nat.card ↥(QB Y ⊓ M) = Nat.card Z ^ 7 := D.card_QB_inf_M
  have hQYcard : Nat.card ↥(Q ⊓ QB Y) = Nat.card Z ^ 3 := D.card_inf_QB_root
  have hinf : Q ⊓ (QB Y ⊓ M) = Q ⊓ QB Y := by
    rw [← inf_assoc, inf_eq_left.mpr (inf_le_left.trans hc.hyp.Q_normal.1)]
  have hsup := card_sup_mul_card_inf_of_normalizer (A := Q) (C := QB Y ⊓ M)
    (inf_le_right.trans hc.hyp.Q_normal.2)
  rw [hinf, hQYcard, hQcard, hPcard] at hsup
  have h20 : Nat.card Z ^ 13 * Nat.card Z ^ 7 = Nat.card Z ^ 17 * Nat.card Z ^ 3 := by
    rw [← pow_add, ← pow_add]
  rw [h20] at hsup
  have hScard : Nat.card ↥(Q ⊔ (QB Y ⊓ M)) = Nat.card Z ^ 17 :=
    Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.card_pos (α := ↥Z)) 3) hsup
  have hbar := bar_card_mul_card_of_le (M := M) (Q := Q)
    (S := Q ⊔ (QB Y ⊓ M)) le_sup_left (sup_le hc.hyp.Q_normal.1 inf_le_right)
  have hmain : Nat.card (bar M Q (Q ⊔ (QB Y ⊓ M))) * Nat.card Z ^ 13 =
      Nat.card Z ^ 17 := by
    rw [← hQcard, hbar, hScard]
  have h4 : Nat.card Z ^ 17 = Nat.card Z ^ 4 * Nat.card Z ^ 13 := by
    rw [← pow_add]
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.card_pos (α := ↥Z)) 13) (hmain.trans h4)

private theorem Sec108Data.card_bar_LB_inf_CN_ge [(Q.subgroupOf M).Normal]
    (D : Sec108Data hc t Y) {A : Subgroup G} (hcA : Ctx M Q Z A)
    (HA : Sec10Hyp hcA 6) (htA : Good103 M Q Z A t) (hslA : SLMNat hcA t 3) :
    Nat.card Z ^ 3 ≤ Nat.card (bar M Q (LB M Q A ⊓ hcA.CN t)) := by
  have hQcard : Nat.card Q = Nat.card Z ^ 13 := D.card_Q
  have hbound := Sec10Hyp.card_LB_le_mul_card_LB_inf_CN D.h34 HA htA.1 hslA
  have hLBcard := (card_LB_of_ctx D.h34 hcA HA.width HA.n_gt HA.noA2 HA.gen).1
  have h16 : Nat.card Z ^ 16 ≤ Nat.card ↥(LB M Q A ⊓ hcA.CN t) := by
    have h1 : Nat.card Z ^ 2 * Nat.card Z ^ 16 ≤
        Nat.card Z ^ 2 * Nat.card ↥(LB M Q A ⊓ hcA.CN t) := by
      calc Nat.card Z ^ 2 * Nat.card Z ^ 16 = Nat.card Z ^ 18 := by
            rw [← pow_add]
        _ = Nat.card ↥(LB M Q A) := by
            rw [hLBcard, hQcard, ← pow_add]
        _ ≤ Nat.card Z ^ 2 * Nat.card ↥(LB M Q A ⊓ hcA.CN t) := hbound
    exact Nat.le_of_mul_le_mul_left h1 (pow_pos (Nat.card_pos (α := ↥Z)) 2)
  have hQle : Q ≤ LB M Q A ⊓ hcA.CN t :=
    le_inf sec39_Q_le_LB (Ctx.Q_le_CN hcA htA.1.mem_LB)
  have hbar := bar_card_mul_card_of_le (M := M) (Q := Q)
    (S := LB M Q A ⊓ hcA.CN t) hQle (inf_le_left.trans hcA.LB_le_M)
  have hmain : Nat.card Z ^ 13 * Nat.card Z ^ 3 ≤
      Nat.card (bar M Q (LB M Q A ⊓ hcA.CN t)) * Nat.card Z ^ 13 := by
    rw [← hQcard, hbar, hQcard]
    calc Nat.card Z ^ 13 * Nat.card Z ^ 3 = Nat.card Z ^ 16 := by
          rw [← pow_add]
      _ ≤ Nat.card ↥(LB M Q A ⊓ hcA.CN t) := h16
  exact Nat.le_of_mul_le_mul_left (by simpa [mul_comm] using hmain)
    (pow_pos (Nat.card_pos (α := ↥Z)) 13)

private theorem bar_inf_le_bar_inf [(Q.subgroupOf M).Normal] {A B' : Subgroup G}
    (hQA : Q ≤ A) : bar M Q A ⊓ bar M Q B' ≤ bar M Q (A ⊓ B') := by
  intro x hx
  obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨a, haA, hamk⟩ := Subgroup.mem_map.mp hxA
  obtain ⟨b, hbB, hbmk⟩ := Subgroup.mem_map.mp hxB
  have hab : QuotientGroup.mk' (Q.subgroupOf M) a =
      QuotientGroup.mk' (Q.subgroupOf M) b := hamk.trans hbmk.symm
  have hq : ((a : M)⁻¹ * b : M) ∈ Q.subgroupOf M := QuotientGroup.eq.mp hab
  have hqG : ((a : G)⁻¹ * (b : G)) ∈ Q := by
    simpa using (Subgroup.mem_subgroupOf.mp hq)
  have haG : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp haA
  have hbG : (b : G) ∈ B' := Subgroup.mem_subgroupOf.mp hbB
  refine Subgroup.mem_map.mpr ⟨b, ?_, hbmk⟩
  refine Subgroup.mem_subgroupOf.mpr ⟨?_, hbG⟩
  have hb : (b : G) = (a : G) * ((a : G)⁻¹ * (b : G)) := by group
  rw [hb]
  exact A.mul_mem haG (hQA hqG)

private theorem Sec108Data.card_bar_LB_inf_LB_le [(Q.subgroupOf M).Normal]
    (D : Sec108Data hc t Y) {h : G} (hhM : h ∈ M)
    (hCV : conjSubgroup h B ≤ Vt M (LB M Q B) B Z t)
    (hCne : conjSubgroup h B ≠ B)
    (hCZ : (conjSubgroup h B ⊔ Z) ⊓ (B ⊔ Z) = Z)
    (htQC : t ∈ QB (conjSubgroup h B)) :
    Nat.card (bar M Q (LB M Q (conjSubgroup h B) ⊓ LB M Q B)) ≤
      Nat.card Z ^ 2 := by
  let A := conjSubgroup h B
  have hcA : Ctx M Q Z A := hc.conj_of_mem hhM
  have HA : Sec10Hyp hcA 6 := D.hyp.conj_of_mem hhM
  have htA : Good103 M Q Z A t := D.good.conj_of_mem hc hhM htQC
  have hslA : SLMNat hcA t 3 := (SLMNat.conj_of_mem_iff hhM).mpr D.slm
  have hCQt : Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) ≤
      Nat.card Z ^ (6 + 1) := by
    rw [D.inf_centralizer_eq, D.card_Ut]
  have hQB : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (6 + 1) := by
    simpa using D.card_inf_QB
  have hQBA : Nat.card ↥(Q ⊓ QB A) = Nat.card Z ^ (6 + 1) := by
    have h1 : Q ⊓ QB A = conjSubgroup h (Q ⊓ QB B) := by
      rw [show A = conjSubgroup h B from rfl, QB_conj]
      conv_lhs =>
        rw [show Q = conjSubgroup h Q from (hc.conj_Q_eq hhM).symm]
      rw [← conjSubgroup_inf]
    rw [h1, card_conjSubgroup, D.card_inf_QB]
  have hAex : ∃ k : G, A = conjSubgroup k Z := by
    obtain ⟨g₀, hg₀⟩ := hc.conj
    exact ⟨h * g₀, by rw [show A = conjSubgroup h B from rfl, hg₀, conjSubgroup_mul]⟩
  have hLB := Good103.card_LB_inf_LB_le_of_second_root D.h34 hcA D.hyp D.good htQC
    hCQt hAex hCV hCne hCZ hQB hQBA
  have hQle : Q ≤ LB M Q A ⊓ LB M Q B := le_inf sec39_Q_le_LB sec39_Q_le_LB
  have hbar := bar_card_mul_card_of_le (M := M) (Q := Q)
    (S := LB M Q A ⊓ LB M Q B) hQle (inf_le_left.trans hcA.LB_le_M)
  have hle : Nat.card (bar M Q (LB M Q A ⊓ LB M Q B)) * Nat.card Q ≤
      Nat.card Z ^ 2 * Nat.card Q := by
    rw [hbar]
    exact hLB
  exact Nat.le_of_mul_le_mul_right hle (Nat.card_pos (α := ↥Q))

private theorem Sec108Data.card_sup_bar_LB_ge [(Q.subgroupOf M).Normal]
    (D : Sec108Data hc t Y) {h : G} (hhM : h ∈ M)
    (hCV : conjSubgroup h B ≤ Vt M (LB M Q B) B Z t)
    (hCne : conjSubgroup h B ≠ B)
    (hCZ : (conjSubgroup h B ⊔ Z) ⊓ (B ⊔ Z) = Z)
    (htQC : t ∈ QB (conjSubgroup h B)) :
    Nat.card Z ^ 4 ≤
      Nat.card ↥(bar M Q (LB M Q (conjSubgroup h B) ⊓ hc.CN t) ⊔
        bar M Q (LB M Q B ⊓ hc.CN t)) := by
  let C := conjSubgroup h B
  let X := bar M Q (LB M Q C ⊓ hc.CN t)
  let Yb := bar M Q (LB M Q B ⊓ hc.CN t)
  have hX_ge : Nat.card Z ^ 3 ≤ Nat.card X := by
    have hCN : (hc.conj_of_mem hhM).CN t = hc.CN t := Ctx.CN_conj_eq hc hhM t
    have h := D.card_bar_LB_inf_CN_ge (A := C) (hc.conj_of_mem hhM)
      (D.hyp.conj_of_mem hhM) (D.good.conj_of_mem hc hhM htQC)
      ((SLMNat.conj_of_mem_iff hhM).mpr D.slm)
    rw [hCN] at h
    exact h
  have hY_ge : Nat.card Z ^ 3 ≤ Nat.card Yb :=
    D.card_bar_LB_inf_CN_ge (A := B) hc D.hyp D.good D.slm
  have hXY : Nat.card ↥(X ⊓ Yb) ≤ Nat.card Z ^ 2 := by
    have hle : X ⊓ Yb ≤ bar M Q (LB M Q C ⊓ LB M Q B) :=
      (inf_le_inf (bar_mono' inf_le_left) (bar_mono' inf_le_left)).trans
        (bar_inf_le_bar_inf sec39_Q_le_LB)
    exact (Subgroup.card_le_of_le hle).trans
      (D.card_bar_LB_inf_LB_le hhM hCV hCne hCZ htQC)
  have hprod := card_mul_card_le_card_inf_mul_card_of_le
    (H := X) (K := Yb) (C := X ⊔ Yb) le_sup_left le_sup_right
  have hstep : Nat.card Z ^ 3 * Nat.card Z ^ 3 ≤
      Nat.card Z ^ 2 * Nat.card ↥(X ⊔ Yb) := by
    calc Nat.card Z ^ 3 * Nat.card Z ^ 3
        ≤ Nat.card ↥X * Nat.card ↥Yb := Nat.mul_le_mul hX_ge hY_ge
      _ ≤ Nat.card ↥(X ⊓ Yb) * Nat.card ↥(X ⊔ Yb) := hprod
      _ ≤ Nat.card Z ^ 2 * Nat.card ↥(X ⊔ Yb) := Nat.mul_le_mul_right _ hXY
  have h6 : Nat.card Z ^ 3 * Nat.card Z ^ 3 = Nat.card Z ^ 2 * Nat.card Z ^ 4 := by
    rw [← pow_add, ← pow_add]
  rw [h6] at hstep
  exact Nat.le_of_mul_le_mul_left hstep (pow_pos (Nat.card_pos (α := ↥Z)) 2)

private theorem Sec108Data.second_root_data [(Q.subgroupOf M).Normal]
    (D : Sec108Data hc t Y) :
    ∃ h ∈ M,
      conjSubgroup h B ≤ Vt M (LB M Q B) B Z t ∧
        (conjSubgroup h B ⊔ Z) ⊓ (B ⊔ Z) = Z ∧
        t ∈ QB (conjSubgroup h B) ∧ conjSubgroup h B ≠ B ∧
        Nat.card Z ^ 3 ≤ Nat.card (bar M Q (LB M Q (conjSubgroup h B) ⊓ hc.CN t)) ∧
        Nat.card (bar M Q (LB M Q (conjSubgroup h B) ⊓ LB M Q B)) ≤ Nat.card Z ^ 2 := by
  have hV : Nat.card Z ^ 2 < Nat.card ↥(Vt M (LB M Q B) B Z t) := by
    rw [D.card_Vt]
    exact Nat.pow_lt_pow_right (by have := hc.hyp.q4; omega) (by norm_num)
  obtain ⟨h, hhM, hCle, hCne, -, htQC, hCZ⟩ :=
    Good103.exists_conj_le_inf (hc := hc) D.good D.sit hV
  have hCV : conjSubgroup h B ≤ Vt M (LB M Q B) B Z t := by
    rw [Good103.Vt_eq D.good D.sit]
    exact le_sup_of_le_left hCle
  have hCN : (hc.conj_of_mem hhM).CN t = hc.CN t := Ctx.CN_conj_eq hc hhM t
  have hX_ge : Nat.card Z ^ 3 ≤
      Nat.card (bar M Q (LB M Q (conjSubgroup h B) ⊓ hc.CN t)) := by
    have h := D.card_bar_LB_inf_CN_ge (A := conjSubgroup h B) (hc.conj_of_mem hhM)
      (D.hyp.conj_of_mem hhM) (D.good.conj_of_mem hc hhM htQC)
      ((SLMNat.conj_of_mem_iff hhM).mpr D.slm)
    rwa [hCN] at h
  exact ⟨h, hhM, hCV, hCZ, htQC, hCne, hX_ge,
    D.card_bar_LB_inf_LB_le hhM hCV hCne hCZ htQC⟩

theorem Sec108Data.card_bar_CN [(Q.subgroupOf M).Normal]
    (D : Sec108Data hc t Y) :
    Nat.card (bar M Q (hc.CN t)) = Nat.card Z ^ 4 := by
  obtain ⟨h, hhM, hCV, hCZ, htQC, hCne, -, -⟩ := D.second_root_data
  have hge := (D.card_sup_bar_LB_ge hhM hCV hCne hCZ htQC).trans
    (Subgroup.card_le_of_le (sup_le (bar_mono' inf_le_right) (bar_mono' inf_le_right)))
  have hle : Nat.card (bar M Q (hc.CN t)) ≤ Nat.card Z ^ 4 :=
    (Subgroup.card_le_of_le
      (bar_mono' (D.hyp.CN_le_sup D.h34 D.h311a D.hspread D.good D.sit))).trans
      (le_of_eq D.card_bar_sup_QB)
  exact le_antisymm hle hge

theorem Sec108Data.CN_eq (D : Sec108Data hc t Y) :
    hc.CN t = Q ⊔ (QB Y ⊓ M) := by
  haveI := hc.normal_Q_in_M
  have hle := D.hyp.CN_le_sup D.h34 D.h311a D.hspread D.good D.sit
  have hNcard : Nat.card ↥(hc.CN t) =
      Nat.card (bar M Q (hc.CN t)) * Nat.card Q :=
    (bar_card_mul_card_of_le (Ctx.Q_le_CN hc D.good.1.mem_LB)
      (fun x hx => hc.Rt_le_M t (Ctx.mem_CN.mp hx).1)).symm
  have hScard : Nat.card ↥(Q ⊔ (QB Y ⊓ M)) =
      Nat.card (bar M Q (Q ⊔ (QB Y ⊓ M))) * Nat.card Q :=
    (bar_card_mul_card_of_le (M := M) (Q := Q) (S := Q ⊔ (QB Y ⊓ M)) le_sup_left
      (sup_le hc.hyp.Q_normal.1 inf_le_right)).symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hScard, hNcard, D.card_bar_sup_QB, D.card_bar_CN]

private theorem bar_sup_eq_bar_right [(Q.subgroupOf M).Normal] {P : Subgroup G}
    (hQM : Q ≤ M) (hPM : P ≤ M) :
    bar M Q (Q ⊔ P) = bar M Q P := by
  unfold bar
  rw [Subgroup.subgroupOf_sup hQM hPM, Subgroup.map_sup]
  have hbot : (Q.subgroupOf M).map (QuotientGroup.mk' (Q.subgroupOf M)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    exact (QuotientGroup.eq_one_iff x).mpr hx
  rw [hbot]
  simp

theorem Sec108Data.isElemAbelian_bar_CN [(Q.subgroupOf M).Normal]
    (D : Sec108Data hc t Y) :
    IsElemAbelian 2 (bar M Q (hc.CN t)) := by
  rw [D.CN_eq, bar_sup_eq_bar_right hc.hyp.Q_normal.1 inf_le_right]
  exact (D.isElemAbelian_QB_inf_M.subgroupOf M).map
    (QuotientGroup.mk' (Q.subgroupOf M))

end CFSG.RankThree.GF2n.Stroth80
