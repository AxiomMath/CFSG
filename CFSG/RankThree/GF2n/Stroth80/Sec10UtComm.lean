module

public import CFSG.RankThree.GF2n.Stroth80.Sec10CardU
public import CFSG.RankThree.GF2n.Stroth80.Sec10Sigma
public import CFSG.RankThree.GF2n.Stroth80.Sec10Swap
public import CFSG.RankThree.GF2n.Smith81.Sec220Local

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem Vt_le_Ut (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) :
    Vt M (LB M Q B) B Z t ≤ Ut Q Z t := by
  rw [(stroth_10_5 h34 h311a hspread) G M Q Z B hc n t H ht]
  exact sup_le_sup_right (Subgroup.commutator_mono inf_le_left le_rfl) Z

private theorem pow_five_lt_pow_three_mul {q : ℕ} (hq : 4 ≤ q) : q ^ 5 < q ^ 3 * q ^ 3 := by
  have hlt : q ^ 5 < q ^ 6 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  calc q ^ 5 < q ^ 6 := hlt
    _ = q ^ 3 * q ^ 3 := by rw [show 6 = 3 + 3 by norm_num, pow_add]

theorem Good103.Ut_QB_le_QB_inf_M (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) {m : ℕ} (hm : SLMNat hc t m) (hm2 : 2 ≤ m)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {z₀ : G} (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1) :
    Ut (QB Y) Y z₀ ≤ QB Y ⊓ M := by
  obtain ⟨g, hgZ, -, hcY, H', hswap⟩ := Good103.exists_swap h34 hspread H ht hs hm
  obtain ⟨hs', -, -, hsl'⟩ := hswap z₀ hz₀ hz₀1
  have hQB : QB Y = conjSubgroup g Q := by
    rw [← hgZ]
    exact QB_conj_eq hs.hyp g
  rw [hQB]
  refine le_inf (hcY.Ut_le_Q hs'.memM) ?_
  intro x hx
  refine centralizer_le_M hs.hyp hz₀ hz₀1 ?_
  have hzLB : z₀ ∈ LB (conjSubgroup g M) (conjSubgroup g Q) B :=
    Subgroup.mem_sup_right ⟨(Ctx.Z_le_QB hc).1 hz₀, hs'.memM⟩
  exact (hcY.Ut_le_centralizer h34 (H'.toSec5 hzLB hs'.notQ)
    (SLMNat.toSLNat hsl' hm2) (by rw [pow_two]; exact Sit.x_sq hs')) hx

theorem Good103.card_Ut_QB (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) {m : ℕ} (hm : SLMNat hc t m)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {z₀ : G} (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1) :
    Nat.card ↥(Ut (QB Y) Y z₀) = Nat.card Z ^ (2 * m + 1) := by
  obtain ⟨g, hgZ, -, hcY, H', hswap⟩ := Good103.exists_swap h34 hspread H ht hs hm
  obtain ⟨-, hgood', -, hsl'⟩ := hswap z₀ hz₀ hz₀1
  have hQB : QB Y = conjSubgroup g Q := by
    rw [← hgZ]
    exact QB_conj_eq hs.hyp g
  rw [hQB, Good103.card_Ut_eq h34 h311a hspread H' hgood' hsl']
  rw [← hgZ, card_conjSubgroup]

private theorem conj_mem_Ut_QB {t : G} {Y : Subgroup G} (hs : Sit M Q Z Y t) {z₀ r : G}
    (hrt : r * t * r⁻¹ = t) (hrz : r * z₀ * r⁻¹ = z₀) {d : G} (hd : d ∈ Ut (QB Y) Y z₀) :
    r * d * r⁻¹ ∈ Ut (QB Y) Y z₀ := by
  have hYconj : IsZConjugate Z Y := hs.conj
  have hYeq : conjSubgroup r Y = Y := by
    refine IsZConjugate.eq_of_mem hs.hyp (hYconj.conj r) hYconj hs.ne_one ?_ hs.mem
    rw [mem_conjSubgroup, show r⁻¹ * t * r = t by
      calc r⁻¹ * t * r = r⁻¹ * (r * t * r⁻¹) * r := by rw [hrt]
        _ = t := by group]
    exact hs.mem
  have hQBYeq : conjSubgroup r (QB Y) = QB Y := by
    rw [← QB_conj r Y, hYeq]
  have hconj := Ut_conj_of_normalizes hQBYeq hYeq z₀
  rw [hrz] at hconj
  have hmem : r * d * r⁻¹ ∈ conjSubgroup r (Ut (QB Y) Y z₀) := by
    rw [mem_conjSubgroup]
    rw [show r⁻¹ * (r * d * r⁻¹) * r = d by group]
    exact hd
  rwa [← hconj] at hmem

private theorem sup_inf_QB_Y_centralizes_Ut (h34 : Stroth34Statement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {d : G} (hd : d ∈ (Q ⊓ QB Y) ⊔ Y) {x : G}
    (hx : x ∈ Ut Q Z t) : x * d = d * x := by
  have hxQ : x ∈ Q := hc.Ut_le_Q ht.1.2.1 hx
  have hxc : x ∈ Subgroup.centralizer ({t} : Set G) :=
    (hc.Ut_le_centralizer h34 (H.toSec5 ht.1.mem_LB ht.1.2.2.1) (hm.toSLNat (by norm_num))
      (by rw [pow_two]; exact Sit.x_sq hs)) hx
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxc
  have hYconj : IsZConjugate Z Y := hs.conj
  have hxnormY : conjSubgroup x Y = Y := by
    refine IsZConjugate.eq_of_mem hs.hyp (hYconj.conj x) hYconj hs.ne_one ?_ hs.mem
    rw [mem_conjSubgroup, show x⁻¹ * t * x = t by
      calc x⁻¹ * t * x = x⁻¹ * (x * t * x⁻¹) * x := by rw [hxt]; group
        _ = t := by group]
    exact hs.mem
  have hA : (Q ⊓ QB Y : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((smith_1_13 hs).2.2.2.2 a ha x ⟨hxQ, hxc⟩)
  have hY : Y ≤ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    have hyM : y ∈ M := ((smith_1_12 hs).1 hy).1
    have hyx : y * x * y⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hyM) x).mp hxQ
    have hxy : x * y * x⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp hxnormY) y).mp hy
    have hcommQ : ⁅x, y⁆ ∈ Q := by
      have h : y * x⁻¹ * y⁻¹ ∈ Q := by
        have := Q.inv_mem hyx
        rwa [show (y * x * y⁻¹)⁻¹ = y * x⁻¹ * y⁻¹ by group] at this
      simpa only [commutatorElement_def, mul_assoc] using Q.mul_mem hxQ h
    have hcommY : ⁅x, y⁆ ∈ Y := by
      rw [commutatorElement_def]
      exact Y.mul_mem hxy (Y.inv_mem hy)
    have hbot : ⁅x, y⁆ = 1 := by
      have hmem : ⁅x, y⁆ ∈ Y ⊓ Q := ⟨hcommY, hcommQ⟩
      rwa [(smith_1_12 hs).2, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp hbot).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (sup_le hA hY hd)).symm

private theorem sup_inf_QB_Z_centralizes_Ut_QB (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2) {Y : Subgroup G}
    (hs : Sit M Q Z Y t) {z₀ : G} (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1) {d : G}
    (hd : d ∈ (Q ⊓ QB Y) ⊔ Z) {x : G} (hx : x ∈ Ut (QB Y) Y z₀) : x * d = d * x := by
  have hxL : x ∈ Lx M Y :=
    Good103.Ut_QB_le_QB_inf_M h34 hspread H ht hm (by norm_num) hs hz₀ hz₀1 hx
  have hxH0 : x ∈ H0 M Z := (Lx_le_H0 hs (smith_1_12 hs)) hxL
  have hA : (Q ⊓ QB Y : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp ((smith_1_13 hs).2.2.1 hxL)) a ha)
  have hZ : Z ≤ Subgroup.centralizer ({x} : Set G) := by
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hxH0.2) z hz)
  exact (Subgroup.mem_centralizer_singleton_iff.mp (sup_le hA hZ hd)).symm

private theorem centralizes_Ut_or_mem_Ut_QB (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {z₀ : G} (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1)
    {d : G} (hd : d ∈ Ut (QB Y) Y z₀) :
    (∀ x ∈ Ut Q Z t, x * d = d * x) ∨ ∀ a ∈ Q ⊓ QB Y, ∃ x ∈ Ut Q Z t, ⁅x, d⁆ = a := by
  obtain ⟨g, hgZ, -, hcY, H', hswap⟩ := Good103.exists_swap h34 hspread H ht hs hm
  obtain ⟨-, hgood', hVt, hsl'⟩ := hswap z₀ hz₀ hz₀1
  have hQB : QB Y = conjSubgroup g Q := by
    rw [← hgZ]
    exact QB_conj_eq hs.hyp g
  have hD : Ut (QB Y) Y z₀ ≤ QB Y ⊓ M :=
    Good103.Ut_QB_le_QB_inf_M h34 hspread H ht hm (by norm_num) hs hz₀ hz₀1
  have hD₀ : (Q ⊓ QB Y) ⊔ Y ≤ Ut (QB Y) Y z₀ := by
    rw [← hVt, hQB]
    exact Vt_le_Ut h34 h311a hspread H' hgood'
  have hDnorm : ∀ r ∈ Rt M (LB M Q B) t ⊓ Subgroup.centralizer ({t} : Set G),
      ∀ d ∈ Ut (QB Y) Y z₀, r * d * r⁻¹ ∈ Ut (QB Y) Y z₀ := by
    intro r hr d hd
    refine conj_mem_Ut_QB hs ?_ ?_ hd
    · rw [← Subgroup.mem_centralizer_iff.mp hr.2 t rfl, mul_inv_cancel_right]
    · rw [← Subgroup.mem_centralizer_iff.mp (Ctx.Rt_le_H0 hc t hr.1).2 z₀ hz₀,
        mul_inv_cancel_right]
  have hD₀U : ∀ d ∈ (Q ⊓ QB Y) ⊔ Y, ∀ x ∈ Ut Q Z t, x * d = d * x := by
    intro d hd x hx
    exact sup_inf_QB_Y_centralizes_Ut h34 H ht hm hs hd hx
  have hDcard : Nat.card ↥(Ut (QB Y) Y z₀) = Nat.card Z ^ 5 := by
    rw [Good103.card_Ut_QB h34 h311a hspread H ht hm hs hz₀ hz₀1]
  have hD₀card : Nat.card ↥((Q ⊓ QB Y) ⊔ Y) = Nat.card Z ^ 3 := by
    rw [← hVt, SLMNat.card_Vt hsl', ← hgZ, card_conjSubgroup]
  have hcard : Nat.card ↥(Ut (QB Y) Y z₀) <
      Nat.card Z ^ 3 * Nat.card ↥((Q ⊓ QB Y) ⊔ Y) := by
    rw [hDcard, hD₀card]
    exact pow_five_lt_pow_three_mul hc.hyp.q4
  exact (Good103.comm_Ut_or_of_SL2 h34 h311a hspread H ht hm hs
    (D := Ut (QB Y) Y z₀) (D₀ := (Q ⊓ QB Y) ⊔ Y) hD hD₀ hDnorm hD₀U hcard).1 d hd

private theorem card_commutators_le_of_mem_Ut_QB (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2)
    {Y : Subgroup G} (hs : Sit M Q Z Y t) {z₀ : G} (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1)
    {d : G} (hd : d ∈ Ut (QB Y) Y z₀) :
    Nat.card {c : G // ∃ x ∈ Ut Q Z t, ⁅d, x⁆ = c} ≤ Nat.card Y := by
  obtain ⟨g, hgZ, -, hcY, H', hswap⟩ := Good103.exists_swap h34 hspread H ht hs hm
  obtain ⟨hs', hgood', -, hsl'⟩ := hswap z₀ hz₀ hz₀1
  have hQB : QB Y = conjSubgroup g Q := by
    rw [← hgZ]
    exact QB_conj_eq hs.hyp g
  have hD : Ut Q Z t ≤ QB Z ⊓ conjSubgroup g M := by
    rw [QB_Z_eq hc]
    refine le_inf (hc.Ut_le_Q ht.1.2.1) ?_
    intro x hx
    refine centralizer_le_M hs'.hyp hs.mem hs.ne_one ?_
    exact (hc.Ut_le_centralizer h34 (H.toSec5 ht.1.mem_LB ht.1.2.2.1)
      (hm.toSLNat (by norm_num)) (by rw [pow_two]; exact Sit.x_sq hs)) hx
  have hD₀ : Vt M (LB M Q B) B Z t ≤ Ut Q Z t :=
    Vt_le_Ut h34 h311a hspread H ht
  have hDnorm : ∀ r ∈ Rt (conjSubgroup g M) (LB (conjSubgroup g M) (conjSubgroup g Q) B)
      z₀ ⊓ Subgroup.centralizer ({z₀} : Set G), ∀ d ∈ Ut Q Z t, r * d * r⁻¹ ∈ Ut Q Z t := by
    intro r hr d hd
    rw [← QB_Z_eq hc] at hd ⊢
    refine conj_mem_Ut_QB hs' ?_ ?_ hd
    · rw [← Subgroup.mem_centralizer_iff.mp hr.2 z₀ rfl, mul_inv_cancel_right]
    · rw [← Subgroup.mem_centralizer_iff.mp (Ctx.Rt_le_H0 hcY z₀ hr.1).2 t hs.mem,
        mul_inv_cancel_right]
  have hD₀U : ∀ d ∈ Vt M (LB M Q B) B Z t, ∀ x ∈ Ut (conjSubgroup g Q) Y z₀,
      x * d = d * x := by
    intro d hd x hx
    rw [← hQB] at hx
    rw [Good103.Vt_eq ht hs] at hd
    exact sup_inf_QB_Z_centralizes_Ut_QB h34 hspread H ht hm hs hz₀ hz₀1 hd hx
  have hYcard : Nat.card Y = Nat.card Z := by
    rw [← hgZ, card_conjSubgroup]
  have hDcard : Nat.card ↥(Ut Q Z t) = Nat.card Z ^ 5 := by
    rw [Good103.card_Ut_eq h34 h311a hspread H ht hm]
  have hD₀card : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ 3 := by
    rw [SLMNat.card_Vt hm]
  have hcard : Nat.card ↥(Ut Q Z t) <
      Nat.card Y ^ 3 * Nat.card ↥(Vt M (LB M Q B) B Z t) := by
    rw [hDcard, hD₀card, hYcard]
    exact pow_five_lt_pow_three_mul hc.hyp.q4
  have hd' : d ∈ Ut (conjSubgroup g Q) Y z₀ := by
    rwa [hQB] at hd
  exact (Good103.comm_Ut_or_of_SL2 (hc := hcY) h34 h311a hspread H' hgood' hsl' hs'
    (Y := Z) (D := Ut Q Z t) (D₀ := Vt M (LB M Q B) B Z t) hD hD₀ hDnorm hD₀U hcard).2 d hd'

theorem Good103.comm_Ut_Ut_QB (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) (hm : SLMNat hc t 2) {Y : Subgroup G}
    (hs : Sit M Q Z Y t) {z₀ : G} (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1) :
    ∀ x ∈ Ut Q Z t, ∀ d ∈ Ut (QB Y) Y z₀, x * d = d * x := by
  intro x hx d hd
  rcases centralizes_Ut_or_mem_Ut_QB h34 h311a hspread H ht hm hs hz₀ hz₀1 hd with h | h
  · exact h x hx
  · exfalso
    have hinj : Function.Injective (fun a : ↥(Q ⊓ QB Y) =>
        (⟨a.1⁻¹, by
          obtain ⟨u, hu, hua⟩ := h a.1 a.2
          exact ⟨u, hu, by rw [← commutatorElement_inv, hua]⟩⟩ :
          {c : G // ∃ u ∈ Ut Q Z t, ⁅d, u⁆ = c})) := by
      intro a b hab
      exact Subtype.ext (inv_injective (congrArg Subtype.val hab))
    have hQcard : Nat.card ↥(Q ⊓ QB Y) = Nat.card Z ^ 2 :=
      Good103.card_inf_QB_eq_pow hc ht hs (SLMNat.card_Vt hm)
    have hYcard : Nat.card Y = Nat.card Z := by
      obtain ⟨g, hg⟩ := hs.conj
      rw [hg, card_conjSubgroup]
    have hle : Nat.card Z ^ 2 ≤ Nat.card Z := by
      calc Nat.card Z ^ 2 = Nat.card ↥(Q ⊓ QB Y) := hQcard.symm
        _ ≤ Nat.card {c : G // ∃ u ∈ Ut Q Z t, ⁅d, u⁆ = c} :=
            Nat.card_le_card_of_injective _ hinj
        _ ≤ Nat.card Y := card_commutators_le_of_mem_Ut_QB h34 h311a hspread H ht hm hs hz₀ hz₀1 hd
        _ = Nat.card Z := hYcard
    have hlt : Nat.card Z < Nat.card Z ^ 2 := by
      simpa using Nat.pow_lt_pow_right (by have := hc.hyp.q4; omega : 1 < Nat.card Z)
        (by norm_num : 1 < 2)
    omega

end CFSG.RankThree.GF2n.Stroth80
