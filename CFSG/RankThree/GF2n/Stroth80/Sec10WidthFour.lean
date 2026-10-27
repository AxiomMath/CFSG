module

public import CFSG.RankThree.GF2n.Stroth80.Sec10CQt
public import CFSG.RankThree.GF2n.Stroth80.Sec10CentQ1
public import CFSG.RankThree.GF2n.Stroth80.Sec10UtComm
public import CFSG.RankThree.GF2n.Smith81.LinLane

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem inf_QB_le_Ut_QB (hc : Ctx M Q Z B) {Y : Subgroup G} {g : G}
    {t z₀ : G} (hs : Sit M Q Z Y t) (hs' : Sit (conjSubgroup g M) (conjSubgroup g Q) Y Z z₀)
    (hQB : QB Y = conjSubgroup g Q)
    (hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B) (H' : Sec10Hyp hcY 4)
    (hU'card : Nat.card ↥(Ut (conjSubgroup g Q) Y z₀) = Nat.card Y ^ (4 + 1)) :
    QB B ⊓ (QB Y ⊓ M) ≤ Ut (QB Y) Y z₀ := by
  have hzLB : z₀ ∈ LB (conjSubgroup g M) (conjSubgroup g Q) B :=
    Subgroup.mem_sup_right ⟨(Ctx.Z_le_QB hc).1 hs'.mem, hs'.memM⟩
  have hQ1U' : Q1 hcY z₀ = Ut (conjSubgroup g Q) Y z₀ :=
    hcY.Q1_eq_Ut_of_card_Ut H'.width hzLB hU'card
  intro x hx
  have hxM : x ∈ M := hx.2.2
  have hxQ : x ∈ conjSubgroup g Q := hQB ▸ hx.2.1
  have hxzZ : ⁅x, z₀⁆ ∈ Z := by
    rw [commutatorElement_def]
    exact Z.mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hxM) z₀).mp hs'.mem)
      (Z.inv_mem hs'.mem)
  have hzxQB : ⁅z₀, x⁆ ∈ conjSubgroup g Q := by
    rw [commutatorElement_def]
    exact (conjSubgroup g Q).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hcY.hyp.Q_normal.2 hs'.memM) x).mp hxQ)
      ((conjSubgroup g Q).inv_mem hxQ)
  have hxzQB : ⁅x, z₀⁆ ∈ conjSubgroup g Q := by
    have e : ⁅x, z₀⁆ = (⁅z₀, x⁆)⁻¹ := by
      rw [← commutatorElement_inv x z₀, inv_inv]
    rw [e]
    exact (conjSubgroup g Q).inv_mem hzxQB
  have hxz1 : ⁅x, z₀⁆ = 1 := by
    have hmem : ⁅x, z₀⁆ ∈ Z ⊓ QB Y := ⟨hxzZ, hQB.symm ▸ hxzQB⟩
    rw [Z_inf_QB_eq_bot hs (smith_1_12 hs)] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hzx1 : ⁅z₀, x⁆ = 1 := by
    rw [← commutatorElement_inv x z₀, hxz1, inv_one]
  have hxQ1 : x ∈ Q1 hcY z₀ :=
    (hcY.mem_Q1_iff hs'.memM).mpr ⟨hxQ, by rw [hzx1]; exact Y.one_mem⟩
  rwa [hQB, ← hQ1U']

private theorem card_inf_QB_inf_QB_inf_M_inf_Q_le (hc : Ctx M Q Z B) {t : G}
    (ht : Good103 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) (hm : SLMNat hc t 2) :
    Nat.card ↥((QB B ⊓ (QB Y ⊓ M)) ⊓ Q) ≤ Nat.card Z ^ 2 := by
  have hQinf : Nat.card ↥(Q ⊓ QB Y) = Nat.card Z ^ 2 :=
    Good103.card_inf_QB_eq_pow hc ht hs (SLMNat.card_Vt hm)
  have hle : (QB B ⊓ (QB Y ⊓ M)) ⊓ Q ≤ Q ⊓ QB Y :=
    le_inf inf_le_right (inf_le_left.trans (inf_le_right.trans inf_le_left))
  calc Nat.card ↥((QB B ⊓ (QB Y ⊓ M)) ⊓ Q) ≤ Nat.card ↥(Q ⊓ QB Y) :=
        Nat.card_le_card_of_injective (Subgroup.inclusion hle)
          (Subgroup.inclusion_injective _)
    _ = Nat.card Z ^ 2 := hQinf

private theorem comm_mem_Z_of_mem_inf_QB (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} (H : Sec10Hyp hc 4) {t : G} (ht : Good103 M Q Z B t)
    (hm : SLMNat hc t 2) {Y : Subgroup G} (hs : Sit M Q Z Y t) {z₀ : G}
    (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1) {P : Subgroup G}
    (hPU : P ≤ Ut (QB Y) Y z₀) (hQ1U : Q1 hc t = Ut Q Z t)
    {x e : G} (hx : x ∈ P) (he : e ∈ Q1 hc t) : ⁅x, e⁆ ∈ Z := by
  have heU : e ∈ Ut Q Z t := by rw [← hQ1U]; exact he
  have hxU : x ∈ Ut (QB Y) Y z₀ := hPU hx
  have hcomm : e * x = x * e :=
    Good103.comm_Ut_Ut_QB h34 h311a hspread H ht hm hs hz₀ hz₀1 e heU x hxU
  have h1 : ⁅x, e⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm
  rw [h1]
  exact Z.one_mem

theorem Good103.not_SLMNat_two_of_width_four (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B}
    (H : Sec10Hyp hc 4) {t : G} (ht : Good103 M Q Z B t) : ¬ SLMNat hc t 2 := by
  intro hm
  obtain ⟨Y, hs⟩ := Good101.exists_sit hc ht.1
  obtain ⟨z₀, hz₀, hz₀1⟩ := Smith81.exists_ne_one_mem_Z hc.hyp
  obtain ⟨g, hgZ, hgB, hcY, H', hswap⟩ := Good103.exists_swap h34 hspread H ht hs hm
  obtain ⟨hs', hgood', -, hsl'⟩ := hswap z₀ hz₀ hz₀1
  have hQB : QB Y = conjSubgroup g Q := by
    rw [← hgZ]
    exact QB_conj_eq hs.hyp g
  let P : Subgroup G := QB B ⊓ (QB Y ⊓ M)
  have hBY : B ≤ QB Y :=
    hc.hyp.le_QB_of_mem_QB hc.conj hs.conj hs.mem hs.ne_one ht.1.2.2.2.1
  have hBYne : B ≠ Y := by
    intro hEq
    exact ht.1.2.2.1 (hc.le (hEq.symm ▸ hs.mem))
  have hlow : Nat.card Z ^ 4 ≤ Nat.card ↥P := by
    have h := H.pow_le_card_QB_inf_QB_inf hspread hc hs.conj hBYne hBY
    simpa [P, inf_assoc] using h
  have hUcard : Nat.card ↥(Ut Q Z t) = Nat.card Z ^ (4 + 1) := by
    rw [Good103.card_Ut_eq h34 h311a hspread H ht hm]
  have hQ1U : Q1 hc t = Ut Q Z t := hc.Q1_eq_Ut_of_card_Ut H.width ht.1.mem_LB hUcard
  have hU'card : Nat.card ↥(Ut (conjSubgroup g Q) Y z₀) = Nat.card Y ^ (4 + 1) := by
    rw [Good103.card_Ut_eq h34 h311a hspread H' hgood' hsl']
  have hPU : P ≤ Ut (QB Y) Y z₀ :=
    inf_QB_le_Ut_QB hc hs hs' hQB hcY H' hU'card
  have hPinfQ : Nat.card ↥(P ⊓ Q) ≤ Nat.card Z ^ 2 :=
    card_inf_QB_inf_QB_inf_M_inf_Q_le hc ht hs hm
  have hPQ1 : ∀ x ∈ P, ∀ e ∈ Q1 hc t, ⁅x, e⁆ ∈ Z :=
    fun x hx e he =>
      comm_mem_Z_of_mem_inf_QB h34 h311a hspread H ht hm hs hz₀ hz₀1 hPU hQ1U hx he
  have hPinf : P ≤ QB B ⊓ M :=
    le_inf inf_le_left (inf_le_right.trans inf_le_right)
  have hR := Good101.card_le_of_centralizes_Q1 hspread H ht.1 hs hc hBY hPinf hPQ1
  have hup : Nat.card ↥P ≤ Nat.card Z ^ 3 := by
    calc Nat.card ↥P ≤ Nat.card Z * Nat.card ↥(P ⊓ Q) := hR
      _ ≤ Nat.card Z * Nat.card Z ^ 2 := Nat.mul_le_mul_left _ hPinfQ
      _ = Nat.card Z ^ 3 := by ring
  have hlt : Nat.card Z ^ 3 < Nat.card Z ^ 4 :=
    Nat.pow_lt_pow_right (by have := hc.hyp.q4; omega) (by norm_num)
  omega

end CFSG.RankThree.GF2n.Stroth80
