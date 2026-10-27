module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Orient
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Rk2A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

namespace Sec526

variable {G : Type} [Group G] [Finite G]

theorem inf_centerOf_ne_bot {Q N : Subgroup G} (hQ : IsPGroup 2 Q) (hNQ : N ≤ Q)
    (hn : Q ≤ Subgroup.normalizer (N : Set G)) (hN : N ≠ ⊥) : N ⊓ centerOf Q ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := N.subgroupOf Q with hH
  have : H.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNQ).mpr hn
  have : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hH0 : H ≠ ⊥ := by
    intro h0
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hNQ hx⟩ : ↥Q) ∈ H := hx
    rw [h0, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have h1 := Group.IsNilpotent.inf_center_ne_bot_of_normal hH0
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
  have hxH := (Subgroup.mem_inf.mp x.2).1
  have hxZ := (Subgroup.mem_inf.mp x.2).2
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨((x : ↥Q) : G), ?_, ?_⟩, fun h => hx1 ?_⟩
  · exact Subgroup.mem_subgroupOf.mp hxH
  · refine ⟨(x : ↥Q).2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have := Subgroup.mem_center_iff.mp hxZ ⟨y, hy⟩
    exact congrArg Subtype.val this
  · have h2 : ((x : ↥Q) : G) = 1 := congrArg (fun z : ↥(N ⊓ centerOf Q) => (z : G)) h
    exact Subtype.ext (Subtype.ext h2)

theorem false_of_card_le_of_special {L R₀ : Subgroup G} {k f w : ℕ} (hk : 2 ≤ k) (hfk : f ≤ k)
    (hperf : ⁅L, L⁆ = L) (hL : IsL2Quot k (oTwoQuot ↥L)) (hR₀Q : R₀ ≤ pCoreOf 2 L)
    (hLR : L ≤ Subgroup.normalizer (R₀ : Set G)) (h1 : ⁅R₀, L⁆ ≠ ⊥)
    (hsp : IsSpecialPow 2 (2 ^ f) w ↥(pCoreOf 2 L)) (hcard : Nat.card R₀ ≤ 2 ^ (2 * k)) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf' : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  set Q := pCoreOf 2 L with hQdef
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 L
  have hQL : Q ≤ L := pCoreOf_le 2 L
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 L
  have hR₀1 : R₀ ≠ ⊥ := fun h0 => h1 (by rw [h0, Subgroup.commutator_bot_left])
  set W := R₀ ⊓ centerOf Q with hWdef
  have hW1 : W ≠ ⊥ := inf_centerOf_ne_bot hQ2 hR₀Q (hQL.trans hLR) hR₀1
  have hWR : W ≤ R₀ := inf_le_left
  have hLZ : L ≤ Subgroup.normalizer ((centerOf Q : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hgQ := Subgroup.mem_normalizer_iff.mp (hLQ hg)
    constructor
    · rintro ⟨hxQ, hxC⟩
      refine ⟨(hgQ x).mp hxQ, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have hy' : g⁻¹ * y * g ∈ Q := by
        have := (hgQ (g⁻¹ * y * g)).mpr (by simpa [mul_assoc] using hy)
        simpa [mul_assoc] using this
      have := Subgroup.mem_centralizer_iff.mp hxC _ hy'
      calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
        _ = g * x * g⁻¹ * y := by group
    · rintro ⟨hxQ, hxC⟩
      refine ⟨(hgQ x).mpr hxQ, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have hy' : g * y * g⁻¹ ∈ Q := (hgQ y).mp hy
      have := Subgroup.mem_centralizer_iff.mp hxC _ hy'
      have e1 : g * (y * x) * g⁻¹ = g * (x * y) * g⁻¹ := by
        calc g * (y * x) * g⁻¹ = (g * y * g⁻¹) * (g * x * g⁻¹) := by group
          _ = (g * x * g⁻¹) * (g * y * g⁻¹) := this
          _ = g * (x * y) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel e1)
  have hLW : L ≤ Subgroup.normalizer (W : Set G) :=
    (le_inf hLR hLZ).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hR₀2 : IsPGroup 2 R₀ := hQ2.to_le hR₀Q
  obtain ⟨d, hd⟩ := hR₀2.exists_card_eq
  have hW2 : IsPGroup 2 W := hR₀2.to_le hWR
  obtain ⟨a, ha⟩ := hW2.exists_card_eq
  have hWZ : Nat.card W ≤ 2 ^ f := by
    have := Subgroup.card_le_of_le (inf_le_right : W ≤ centerOf Q)
    rw [card_centerOf_eq, hsp.2.2] at this
    exact this
  have ha1 : 1 ≤ a := by
    by_contra h0
    have : a = 0 := by omega
    rw [this, pow_zero] at ha
    exact hW1 (Subgroup.eq_bot_of_card_eq W ha)
  have haf : a ≤ f := by
    rw [ha] at hWZ
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hWZ
  have hd2 : d ≤ 2 * k := by
    rw [hd] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard
  have hdvd : Nat.card W ∣ Nat.card R₀ := Subgroup.card_dvd_of_le hWR
  have had : a ≤ d := by
    rw [ha, hd] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have hWbot : ⁅W, L⁆ ≤ ⊥ := by
    have : ((⊥ : Subgroup G).subgroupOf W).Normal := by
      rw [Subgroup.bot_subgroupOf]
      infer_instance
    exact commutator_le_of_isL2Quot (f := a) hk (by omega) hperf' hL hLW
      (fun g _ => Subgroup.mem_normalizer_iff.mpr fun x => by simp)
      bot_le (by rw [Subgroup.card_bot, mul_one, ha])
  have hWn : (W.subgroupOf R₀).Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hxc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2.2
    have hgQ : (g : G) ∈ Q := hR₀Q g.2
    have hgx := hxc g hgQ
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hgx, mul_inv_cancel_right]
    exact hx
  have hRW : ⁅R₀, L⁆ ≤ W :=
    commutator_le_of_isL2Quot (f := d - a) hk (by omega) hperf' hL hLR hLW hWR (hWn := hWn)
      (by rw [hd, ha, ← pow_add, Nat.sub_add_cancel had])
  apply h1
  refine commutator_eq_bot_of_perfect hperf (le_bot_iff.mp ?_)
  exact (Subgroup.commutator_mono hRW le_rfl).trans hWbot

theorem not_isShort2_of_card
    {L R₀ : Subgroup G} {k : ℕ}
    (hk : 2 ≤ k) (hperf : ⁅L, L⁆ = L) (hL : IsL2Quot k (oTwoQuot ↥L))
    (hR₀Q : R₀ ≤ pCoreOf 2 L) (hLR : L ≤ Subgroup.normalizer (R₀ : Set G)) (h1 : ⁅R₀, L⁆ ≠ ⊥)
    (hcard : Nat.card R₀ * 2 ^ (2 * k) ≤ Nat.card (pCoreOf 2 L)) : ¬ IsShort2 L := by
  have h16 : 16 ≤ 2 ^ (2 * k) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpos : 0 < Nat.card R₀ := Nat.card_pos
  have h2 : 2 * Nat.card R₀ < Nat.card (pCoreOf 2 L) := by nlinarith
  exact not_isShort2_of_two hperf hR₀Q hLR h1
    (not_commutator_le_of_isL2Quot hk (Subgroup.isPerfect_iff.mpr hperf) hL hR₀Q hLR h2)

end Sec526

end CFSG.Quasithin.H13
