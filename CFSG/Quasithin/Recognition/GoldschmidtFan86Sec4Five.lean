module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4NoChar
public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocPU

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan41_2 (F : FanTree Γ G) {a b c : V} (hab : Γ.Adj a b) (hac : a ≠ c) {L : Subgroup G}
    (hL : L ∈ LamSet Γ G a b c) (h5 : valence Γ a = 5) :
    ∃ x ∈ L ⊓ MulAction.stabilizer G a, orderOf x = 5 ∧
      ∀ g ∈ L ⊓ MulAction.stabilizer G a, g * x * g⁻¹ ∈ Subgroup.zpowers x := by
  obtain ⟨Lt, hLt, hle⟩ := fan41_max F hL
  set Ga := MulAction.stabilizer G a with hGa
  set Gb := MulAction.stabilizer G b with hGb
  set H : Subgroup G := Lt ⊓ Ga with hH
  set R : Subgroup G := H ⊓ Gb with hR
  have hRH : R ≤ H := inf_le_left
  obtain ⟨hfinH, htrH, hcardH, hR2⟩ := lamSet_setup F hab hLt.1
  rw [h5] at hcardH
  let e : ↥(R.subgroupOf H) ≃* ↥R := Subgroup.subgroupOfEquivOfLe hRH
  have hP2 : IsPGroup 2 ↥(R.subgroupOf H) := hR2.of_equiv e.symm
  have hcardP : Nat.card ↥(R.subgroupOf H) = Nat.card ↥R := Nat.card_congr e.toEquiv
  have hcard : Nat.card ↥H = 5 * Nat.card ↥(R.subgroupOf H) := by rw [hcardP, hcardH]
  have hno : ∀ K : Subgroup ↥H, K ≤ R.subgroupOf H →
      (K.subgroupOf (R.subgroupOf H)).Characteristic → K.Normal → K = ⊥ :=
    fun K hK hchar hN => fan41_noChar_subtype F hab hac hLt K hK hchar hN
  have h5p : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 5
    (by rw [hcard]; exact dvd_mul_right _ _)
  have hnorm : (Subgroup.zpowers x).Normal :=
    sylow_normal_of_no_char_normal (H := ↥H) (P := R.subgroupOf H) (p := 5) (by norm_num)
      (by norm_num) (by norm_num) hP2 hx hcard hno
  have hLaH : L ⊓ Ga ≤ H := hle
  obtain ⟨hfinL, htrL, hcardL, -⟩ := lamSet_setup F hab hL
  rw [h5] at hcardL
  have hdvdL : 5 ∣ Nat.card ↥(L ⊓ Ga) := by
    rw [hcardL]
    exact dvd_mul_right _ _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(L ⊓ Ga)) 5 hdvdL
  have hy' : orderOf (y : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hy
  let yH : ↥H := ⟨(y : G), hLaH y.2⟩
  have hyH : orderOf yH = 5 := by
    have : orderOf (yH : G) = orderOf yH := Subgroup.orderOf_coe yH
    rw [← this]
    exact hy'
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP2
  have hcardH2 : Nat.card ↥H = 5 * 2 ^ k := by rw [hcard, hk]
  have hxcard : Nat.card ↥(Subgroup.zpowers x) = 5 := by rw [Nat.card_zpowers, hx]
  have hzeq : Subgroup.zpowers yH = Subgroup.zpowers x :=
    zpowers_eq_of_normal (by norm_num) (by norm_num) hyH hcardH2 hnorm hxcard
  have hnormy : (Subgroup.zpowers yH).Normal := hzeq ▸ hnorm
  refine ⟨(y : G), y.2, hy', fun g hg => ?_⟩
  have := hnormy.conj_mem yH (Subgroup.mem_zpowers yH) ⟨g, hLaH hg⟩
  have hmap := Subgroup.mem_map_of_mem H.subtype this
  rw [MonoidHom.map_zpowers] at hmap
  exact hmap
